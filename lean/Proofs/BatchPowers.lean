/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.BatchLookup
public import Proofs.BatchFinish
public import Proofs.Optimization

/-! # One checkpoint dictionary shared by independent trajectories -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
open scoped BigOperators

variable {n r M a : ℕ}

def batchBudget (n s N r L : ℕ) : ℕ :=
  r * L * s + (n + 1) ^ 3 * (r * L + N / L + 1)

def batchConstructionCost (n s M r L : ℕ) : ℕ :=
  r * (2 * L * s) +
    256 * (M + r * (2 * L + 1) + 1) *
      (Nat.clog 2 (M + r * (2 * L + 1) + 1) + n + (1 + n) + 3) ^ 3 +
    r * ((2 * L + 1) * (4 * (1 + ((n + 2) + n))) + 2 * L * s +
      200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 +
      40000 * (L * s + (n + 1) ^ 3 * (L + 1)) + 4 * n)

/-- A shared dictionary followed by separate short corrections and repetition fallbacks. -/
theorem synthesis_batched_long (c : Circuit Boolean.signature n n)
    (s : Set (State a → Bool)) (init : State a → Fin r → State n)
    (hi : ∀ member bit, (fun x => init x member bit) ∈ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s)
    (T L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) (hT : 2 * L ≤ T)
    (cp : Fin M → State n) (hcp : Function.Injective cp)
    (hcover : ∀ x : State n, Repeats (c.eval Boolean.interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval Boolean.interpretation)^[t] x = cp j) :
    Synthesis Boolean.interpretation s
      (Set.range fun bit : Fin (r * n) => fun x =>
        let pair := (finProdFinEquiv (m := r) (n := n)).symm bit
        (c.eval Boolean.interpretation)^[T] (init x pair.1) pair.2)
      (r * (2 * L * c.size) +
        256 * (M + r * (2 * L + 1) + 1) *
          (Nat.clog 2 (M + r * (2 * L + 1) + 1) + n + (1 + n) + 3) ^ 3 +
        r * ((2 * L + 1) * (4 * (1 + ((n + 2) + n))) + 2 * L * c.size +
          200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 +
          40000 * (L * c.size + (n + 1) ^ 3 * (L + 1)) + 4 * n)) := by
  let f := c.eval Boolean.interpretation
  let K := 2 * L
  let trace := fun member j x => f^[j] (init x member)
  let orbit := fun member => Synthesis.stages (fun j => wires (trace member j)) K
  have hp (member : Fin r) : Synthesis Boolean.interpretation s (orbit member) (K * c.size) :=
    synthesis_orbit Boolean.interpretation c s (fun x => init x member) (hi member) K
  have hall := Synthesis.iUnion orbit (fun _ => K * c.size) hp
  have hall' : Synthesis Boolean.interpretation s (⋃ member, orbit member) (r * (K * c.size)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] using hall
  let s1 := s ∪ ⋃ member, orbit member
  have hpre (member : Fin r) (j : Fin (K + 1)) (bit : Fin n) :
      (fun x => trace member j.val x bit) ∈ s1 := by
    exact Or.inr (Set.mem_iUnion.mpr ⟨member, Set.mem_iUnion.mpr ⟨j.val,
      Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr j.isLt, ⟨bit, rfl⟩⟩⟩⟩)
  let Q := r * (K + 1)
  let queries : State a → Fin (Q * n) → Bool := fun x bit =>
    let qb := (finProdFinEquiv (m := Q) (n := n)).symm bit
    let mt := (finProdFinEquiv (m := r) (n := K + 1)).symm qb.1
    trace mt.1 mt.2.val x qb.2
  have hquery (x : State a) (member : Fin r) (j : Fin (K + 1)) (bit : Fin n) :
      queries x (finProdFinEquiv (finProdFinEquiv (member, j), bit)) =
        f^[j.val] (init x member) bit := by
    simp only [queries, Equiv.symm_apply_apply, trace]
  obtain ⟨lookup, hm, hv, _, hlookup⟩ :=
    SharedLookup.fixed_dictionary (Q := Q) cp (fun j => f^[T - K] (cp j)) hcp
  have hdict := Synthesis.circuit (I := Boolean.interpretation) (s := s1) lookup queries
    (fun bit => hpre _ _ _)
  let result := fun x => lookup.eval Boolean.interpretation (queries x)
  let s2 := s1 ∪ wires result
  let flags := fun member x (j : Fin (K + 1)) =>
    result x (finProdFinEquiv (finProdFinEquiv (member, j), (0 : Fin (1 + n))))
  let payloads := fun member x (j : Fin (K + 1)) (bit : Fin n) =>
    result x (finProdFinEquiv (finProdFinEquiv (member, j), Fin.natAdd 1 bit))
  obtain ⟨fallback, hfall, hfs⟩ := repetition_fallback c T L hL hLN hT
  let finished := fun member x => finishHit (w := n + 2) f K (flags member x)
    (payloads member x) (fallback.eval Boolean.interpretation (init x member))
  have hfinish (member : Fin r) : Synthesis Boolean.interpretation s2 (wires (finished member))
      ((K + 1) * (4 * (1 + ((n + 2) + n))) + K * c.size +
        200 * (K + 1) * (n + (n + 2) + 1) ^ 2 + fallback.size + 4 * n) := by
    have hf := Synthesis.circuit (I := Boolean.interpretation) (s := s2) fallback
      (fun x => init x member) (fun bit => Or.inl (Or.inl (hi member bit)))
    exact synthesis_finishHit c s2 K (flags member) (payloads member) _
      (fun j => Or.inr ⟨_, rfl⟩) (fun j bit => Or.inr ⟨_, rfl⟩)
      (fun b => Or.inl (Or.inl (hc b))) hf
  have hcorrect (member : Fin r) (x : State a) : finished member x = f^[T] (init x member) := by
    have hfit : K < 2 ^ (n + 2) := by
      dsimp [K]
      simp only [Nat.pow_succ]
      have := Nat.one_le_two_pow (n := n)
      lia
    apply finishHit_correct f T K _ _ _ _ hfit hT
    · intro j hj
      obtain ⟨source, hsource⟩ := (hm (queries x) (finProdFinEquiv (member, j))).mp hj
      have hq : (fun bit => queries x (finProdFinEquiv (finProdFinEquiv (member, j), bit))) =
          f^[j.val] (init x member) := by
        funext bit
        exact hquery x member j bit
      rw [hq] at hsource
      funext bit
      have hout := hv (queries x) (finProdFinEquiv (member, j)) source
        (by rwa [hq]) bit
      change payloads member x j bit = _ at hout
      rw [hout, hsource]
    · intro hnone
      apply hfall
      rcases hcover (init x member) with hr | ⟨t, ht, source, hs⟩
      · exact hr
      · exfalso
        apply hnone
        let j : Fin (K + 1) := ⟨t, by dsimp [K]; lia⟩
        refine ⟨j, (hm (queries x) (finProdFinEquiv (member, j))).mpr ⟨source, ?_⟩⟩
        funext bit
        rw [hquery]
        exact congrFun hs.symm bit
  have hfam := Synthesis.iUnion (fun member => wires (finished member))
    (fun _ => (K + 1) * (4 * (1 + ((n + 2) + n))) + K * c.size +
      200 * (K + 1) * (n + (n + 2) + 1) ^ 2 + fallback.size + 4 * n) hfinish
  have hout := hall'.trans (hdict.trans hfam)
  apply hout.mono Set.Subset.rfl ?_ ?_
  · rintro _ ⟨bit, rfl⟩
    let pair := (finProdFinEquiv (m := r) (n := n)).symm bit
    exact Set.mem_iUnion.mpr ⟨pair.1, ⟨pair.2, by
      funext x
      exact congrFun (hcorrect pair.1 x) pair.2⟩⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    dsimp only [K, Q] at hlookup ⊢
    have hh := Nat.mul_le_mul_left r hfs
    lia

theorem batch_cost (n s M r L : ℕ) (hr : 0 < r) (hrN : r ≤ 2 ^ n)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) (hM : M ≤ 2 ^ n / L) :
    2 + batchConstructionCost n s M r L ≤
      1000000 * batchBudget n s (2 ^ n) r L := by
  let d := Nat.clog 2 (M + r * (2 * L + 1) + 1)
  have hN : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hMN : M ≤ 2 ^ n := hM.trans (Nat.div_le_self _ _)
  have hd : d ≤ 2 * n + 3 := by
    apply Nat.clog_le_of_le_pow
    have he : 2 ^ (2 * n + 3) = 8 * (2 ^ n) ^ 2 := by
      rw [show 2 * n + 3 = n * 2 + 3 by lia, pow_add, pow_mul]
      norm_num
      ring
    rw [he]
    have hp := Nat.mul_le_mul hrN hLN
    nlinarith
  have hw : (d + n + (1 + n) + 3) ^ 3 ≤ 343 * (n + 1) ^ 3 := by
    have h : d + n + (1 + n) + 3 ≤ 7 * (n + 1) := by lia
    have := Nat.pow_le_pow_left h 3
    nlinarith
  have hrec : M + r * (2 * L + 1) + 1 ≤ 2 ^ n / L + 3 * (r * L) + 1 := by
    nlinarith
  have hdict := Nat.mul_le_mul hrec hw
  have hshort : (2 * L + 1) * (4 * (1 + ((n + 2) + n))) +
      200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 4 * n ≤
        6000 * L * (n + 1) ^ 3 := by
    have hs : (n + (n + 2) + 1) ^ 2 ≤ 9 * (n + 1) ^ 2 := by nlinarith
    have hh := Nat.mul_le_mul (show 2 * L + 1 ≤ 3 * L by lia) hs
    nlinarith [Nat.zero_le (L * n ^ 3), Nat.zero_le (L * n ^ 2)]
  have htail := Nat.mul_le_mul_left r hshort
  have hrL : r ≤ r * L := by nlinarith
  have hrLb := Nat.mul_le_mul_right ((n + 1) ^ 3) hrL
  unfold batchConstructionCost batchBudget
  change 2 + (r * (2 * L * s) +
    256 * (M + r * (2 * L + 1) + 1) * (d + n + (1 + n) + 3) ^ 3 + _) ≤ _
  nlinarith [Nat.zero_le (r * L * s), Nat.zero_le ((2 ^ n / L) * (n + 1) ^ 3),
    Nat.zero_le (r * L * n ^ 3)]

/-- The shared fixed-power tradeoff, with the dictionary paid for only once. -/
theorem batched_fixed_power (c : Circuit Boolean.signature n n) (r T L : ℕ)
    (hr : 0 < r) (hrN : r ≤ 2 ^ n) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (r * n) (r * n),
      (∀ x member bit, out.eval Boolean.interpretation x (finProdFinEquiv (member, bit)) =
        (c.eval Boolean.interpretation)^[T]
          (fun i => x (finProdFinEquiv (member, i))) bit) ∧
      out.size ≤ 1000000 * batchBudget n c.size (2 ^ n) r L := by
  classical
  let init : State (r * n) → Fin r → State n := fun x member bit =>
    x (finProdFinEquiv (member, bit))
  by_cases ht : T < 2 * L
  · let step := Circuit.parallelFinVector r n (fun member =>
      c.mapInputs (fun bit => finProdFinEquiv (member, bit)))
    have hstep (x : State (r * n)) (member : Fin r) :
        (fun bit => step.eval Boolean.interpretation x (finProdFinEquiv (member, bit))) =
          c.eval Boolean.interpretation (init x member) := by
      funext bit
      simp [step, Circuit.eval_parallelFinVector, init]
      rfl
    have hi (t : ℕ) (x : State (r * n)) (member : Fin r) :
        (fun bit => (step.eval Boolean.interpretation)^[t] x
          (finProdFinEquiv (member, bit))) =
            (c.eval Boolean.interpretation)^[t] (init x member) := by
      induction t with
      | zero => rfl
      | succ t ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        rw [hstep, ← ih]
    refine ⟨step.iterate T, ?_, ?_⟩
    · intro x member bit
      rw [(unroll_spec step Boolean.interpretation T).1]
      exact congrFun (hi T x member) bit
    · have hsize : step.size = r * c.size := by simp [step]
      rw [(unroll_spec step Boolean.interpretation T).2, hsize]
      unfold batchBudget
      have h := Nat.mul_le_mul_right (r * c.size) (show T ≤ 2 * L by lia)
      nlinarith [Nat.zero_le ((n + 1) ^ 3 * (r * L + 2 ^ n / L + 1))]
  obtain ⟨H, _, hcard, hcover⟩ := exists_checkpoints (c.eval Boolean.interpretation)
    Finset.univ (fun _ _ => Finset.mem_univ _) hL
  let cp : Fin H.card → State n := fun j => (H.equivFin.symm j).val
  have hcp : Function.Injective cp := by
    intro i j h
    exact H.equivFin.symm.injective (Subtype.ext h)
  have hcov (x : State n) : Repeats (c.eval Boolean.interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval Boolean.interpretation)^[t] x = cp j := by
    rcases hcover x (Finset.mem_univ _) with hrep | ⟨t, ht, hmem⟩
    · exact Or.inl hrep
    · exact Or.inr ⟨t, ht, H.equivFin ⟨_, hmem⟩, by simp [cp]⟩
  let constants : Set (State (r * n) → Bool) := {fun _ => false, fun _ => true}
  let src := inputs (r * n) ∪ constants
  have hc (b : Bool) : (fun _ : State (r * n) => b) ∈ src := by
    cases b <;> simp [src, constants]
  have hconst : Synthesis Boolean.interpretation (inputs (r * n)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have hs := synthesis_batched_long c src init (fun member bit => Or.inl ⟨_, rfl⟩) hc
    T L hL hLN (by lia) cp hcp hcov
  obtain ⟨out, hout, hsize⟩ := (hconst.trans hs).exists_circuit_outputs
  refine ⟨out, ?_, hsize.trans ?_⟩
  · intro x member bit
    simpa only [Equiv.symm_apply_apply] using congrFun (hout x) (finProdFinEquiv (member, bit))
  · apply batch_cost n c.size H.card r L hr hrN hL hLN
    apply (Nat.le_div_iff_mul_le hL).mpr
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using hcard

noncomputable def optimizedBatchBudget (n s N r : ℕ) : ℝ :=
  (r * (s + (n + 1) ^ 3) : ℕ) +
    Real.sqrt ((n + 1 : ℝ) ^ 3 * N * (r * (s + (n + 1) ^ 3) : ℕ))

theorem batchBudget_optimized (n s r : ℕ) (hr : 0 < r) :
    ∃ L : ℕ, 0 < L ∧ L ≤ 2 ^ n ∧
      (batchBudget n s (2 ^ n) r L : ℝ) ≤
        3 * optimizedBatchBudget n s (2 ^ n) r := by
  have hb : (n + 1) ^ 3 ≤ r * (s + (n + 1) ^ 3) := by
    have h := Nat.mul_le_mul_right (s + (n + 1) ^ 3) hr
    lia
  obtain ⟨L, hL, hLN, h⟩ := optimize_tradeoff (r * (s + (n + 1) ^ 3)) ((n + 1) ^ 3)
    (2 ^ n) (2 ^ n) (by positivity) hb le_rfl (by positivity)
  refine ⟨L, hL, hLN, ?_⟩
  have he : batchBudget n s (2 ^ n) r L =
      (r * (s + (n + 1) ^ 3)) * L + (n + 1) ^ 3 * (2 ^ n / L + 1) := by
    unfold batchBudget
    ring
  simpa [he, optimizedBatchBudget, Nat.cast_add, Nat.cast_pow] using h

theorem batched_fixed_power_optimized (c : Circuit Boolean.signature n n) (r T : ℕ)
    (hr : 0 < r) (hrN : r ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (r * n) (r * n),
      (∀ x member bit, out.eval Boolean.interpretation x (finProdFinEquiv (member, bit)) =
        (c.eval Boolean.interpretation)^[T]
          (fun i => x (finProdFinEquiv (member, i))) bit) ∧
      (out.size : ℝ) ≤ 3000000 * optimizedBatchBudget n c.size (2 ^ n) r := by
  obtain ⟨L, hL, hLN, ho⟩ := batchBudget_optimized n c.size r hr
  obtain ⟨out, hout, hs⟩ := batched_fixed_power c r T L hr hrN hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ 1000000 * (batchBudget n c.size (2 ^ n) r L : ℝ) := by
    exact_mod_cast hs
  linarith

end IteratedFunctions
