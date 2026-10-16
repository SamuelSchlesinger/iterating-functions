/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CycleProjection
public import Proofs.LabelCircuits
public import Proofs.LinearArithmetic

/-!
# Transient depth with one checkpoint dictionary

The original and projected orbits agree exactly from cycle entry onward.
Scan a short prefix of both. If they still disagree at its end, every prefix
checkpoint is transient, and its stored depth plus its index is the answer.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
open scoped BigOperators

variable {n M : ℕ}

noncomputable def shortDepth (f : State n → State n) (K : ℕ) (x : State n) :
    BitVec (n + 2) :=
  firstIndex fun j : Fin (K + 1) => decide (f^[j.val] x = f^[j.val] (cycleProjection f x))

theorem shortDepth_spec (f : State n → State n) (K : ℕ) (x : State n)
    (hK : transientDepth f x ≤ K) :
    shortDepth f K x = BitVec.ofNat (n + 2) (transientDepth f x) := by
  let j : Fin (K + 1) := ⟨transientDepth f x, by lia⟩
  apply firstIndex_spec _ j
  · exact decide_eq_true ((iterate_eq_projection_iff f x _).mpr le_rfl)
  · intro i hi
    apply decide_eq_false
    intro he
    have := (iterate_eq_projection_iff f x i.val).mp he
    change i.val < transientDepth f x at hi
    lia

def checkpointDepthCost (n s M L : ℕ) : ℕ :=
  2 + 40000 * powerBudget n s (2 ^ n) L + 4 * L * s +
    256 * (M + (2 * L + 1) + 1) *
      (Nat.clog 2 (M + (2 * L + 1) + 1) + n + (1 + (n + 2)) + 3) ^ 3 +
    (2 * L + 1) * (6 * n + 1 + 28 * (n + 2) + 1) + 4 * (n + 2)

theorem depth_from_checkpoints (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) (cp : Fin M → State n) (hcp : Function.Injective cp)
    (hcover : ∀ x : State n, Repeats (c.eval Boolean.interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval Boolean.interpretation)^[t] x = cp j) :
    ∃ out : Circuit Boolean.signature n (n + 2),
      (∀ x, word (out.eval Boolean.interpretation x) =
        BitVec.ofNat (n + 2) (transientDepth (c.eval Boolean.interpretation) x)) ∧
      out.size ≤ checkpointDepthCost n c.size M L := by
  let f := c.eval Boolean.interpretation
  let K := 2 * L
  let W := n + 2
  let constants : Set (State n → Bool) := {fun _ => false, fun _ => true}
  let src := inputs n ∪ constants
  have hc (b : Bool) : (fun _ : State n => b) ∈ src := by
    cases b <;> simp [src, constants]
  have hconst : Synthesis Boolean.interpretation (inputs n) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  obtain ⟨project, hp, hps⟩ := fixed_power n c (Nat.factorial (2 ^ n)) L hL hLN
  have heval : project.eval Boolean.interpretation = cycleProjection f := by
    funext x
    simpa only [cycleProjection, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      using hp x
  have hproject : Synthesis Boolean.interpretation src
      (wires (cycleProjection f)) project.size := by
    simpa only [heval, wires, Function.id_def] using
      Synthesis.circuit (I := Boolean.interpretation) (s := src) project id
        (fun bit => Or.inl ⟨bit, rfl⟩)
  let s1 := src ∪ wires (cycleProjection f)
  let trace := fun j x => f^[j] x
  let projected := fun j x => f^[j] (cycleProjection f x)
  have hx := synthesis_orbit Boolean.interpretation c s1 id
    (fun bit => Or.inl (Or.inl ⟨bit, rfl⟩)) K
  have hz := synthesis_orbit Boolean.interpretation c s1 (cycleProjection f)
    (fun bit => Or.inr ⟨bit, rfl⟩) K
  let s2 := s1 ∪ (Synthesis.stages (fun j => wires (trace j)) K ∪
    Synthesis.stages (fun j => wires (projected j)) K)
  have htrace (j : Fin (K + 1)) (bit : Fin n) : (fun x => trace j.val x bit) ∈ s2 :=
    Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨j.val, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr j.isLt, ⟨bit, rfl⟩⟩⟩))
  have hprojected (j : Fin (K + 1)) (bit : Fin n) :
      (fun x => projected j.val x bit) ∈ s2 :=
    Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j.val, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr j.isLt, ⟨bit, rfl⟩⟩⟩))
  let queries : State n → State ((K + 1) * n) := fun x bit =>
    let p := (finProdFinEquiv (m := K + 1) (n := n)).symm bit
    trace p.1.val x p.2
  have hquery (x : State n) (j : Fin (K + 1)) :
      (fun bit => queries x (finProdFinEquiv (j, bit))) = f^[j.val] x := by
    funext bit
    simp only [queries, Equiv.symm_apply_apply, trace]
  let payload := fun i : Fin M => fun bit : Fin W =>
    (BitVec.ofNat W (transientDepth f (cp i))).getLsbD bit.val
  obtain ⟨lookup, hm, hv, _, hlookup⟩ := SharedLookup.fixed_dictionary
    (Q := K + 1) cp payload hcp
  have hd := Synthesis.circuit (I := Boolean.interpretation) (s := s2) lookup queries
    (fun bit => htrace _ _)
  let result := fun x => lookup.eval Boolean.interpretation (queries x)
  let equal := fun x (j : Fin (K + 1)) => decide (trace j.val x = projected j.val x)
  have heq := Synthesis.family (I := Boolean.interpretation) (s := s2)
    (fun j x => equal x j) (fun _ => 6 * n + 1) (fun j =>
      synthesis_bits_eq s2 (trace j.val) (projected j.val)
        (by rintro _ ⟨bit, rfl⟩; exact htrace j bit)
        (by rintro _ ⟨bit, rfl⟩; exact hprojected j bit))
  let s3 := s2 ∪ (wires result ∪ Set.range (fun j x => equal x j))
  let flags := fun x (j : Fin (K + 1)) => result x (finProdFinEquiv (j, (0 : Fin (1 + W))))
  let records := fun x (j : Fin (K + 1)) (bit : Fin W) =>
    result x (finProdFinEquiv (j, Fin.natAdd 1 bit))
  let corrected := fun j x => word (records x j) + BitVec.ofNat W j.val
  have hcorrect (j : Fin (K + 1)) : Synthesis Boolean.interpretation s3
      (wordWires (corrected j)) (20 * W + 1) :=
    synthesis_add_linear s3 (fun x => word (records x j)) (fun _ => BitVec.ofNat W j.val)
      (fun bit => by
        simp only [word_bit]
        exact Or.inr (Or.inl ⟨_, rfl⟩))
      (fun bit => Or.inl (Or.inl (Or.inl (hc ((BitVec.ofNat W j.val).getLsbD bit.val)))))
  have hall := Synthesis.iUnion (fun j => wordWires (corrected j)) (fun _ => 20 * W + 1)
    hcorrect
  let s4 := s3 ∪ ⋃ j, wordWires (corrected j)
  have hselect := synthesis_chooseRecord s4 flags
    (fun x j bit => (corrected j x).getLsbD bit.val) (fun _ _ => false)
    (fun j => Or.inl (Or.inr (Or.inl ⟨_, rfl⟩)))
    (fun j bit => Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨bit, rfl⟩⟩))
    (fun _ => Or.inl (Or.inl (Or.inl (Or.inl (hc false)))))
  let selected := fun x => word (chooseRecord (flags x)
    (fun j (bit : Fin W) => (corrected j x).getLsbD bit.val) (fun _ => false) (K + 1))
  have hselected : Synthesis Boolean.interpretation s4 (wordWires selected)
      ((K + 1) * (4 * W)) := by
    simpa only [selected, wordWires, word_bit] using hselect
  have hshort := synthesis_firstIndex (w := W) s4 equal
    (fun j => Or.inl (Or.inr (Or.inr ⟨j, rfl⟩)))
    (fun b => Or.inl (Or.inl (Or.inl (Or.inl (hc b)))))
  let s5 := s4 ∪ (wordWires selected ∪ wordWires (fun x => firstIndex (w := W) (equal x)))
  let last : Fin (K + 1) := ⟨K, Nat.lt_succ_self K⟩
  have hfinal := synthesis_word_mux s5 (fun x => firstIndex (w := W) (equal x))
    selected (fun x => equal x last)
    (Or.inl (Or.inl (Or.inr (Or.inr ⟨last, rfl⟩))))
    (fun bit => Or.inr (Or.inr ⟨bit, rfl⟩)) (fun bit => Or.inr (Or.inl ⟨bit, rfl⟩))
  have h := hconst.trans (hproject.trans ((hx.union hz).trans
    ((hd.union heq).trans (hall.trans ((hselected.union hshort).trans hfinal)))))
  obtain ⟨out, ho, hs⟩ := h.exists_circuit_outputs
  refine ⟨out, fun x => ?_, hs.trans ?_⟩
  · rw [ho x, word_bits]
    by_cases hK : transientDepth f x ≤ K
    · have he : equal x last = true :=
        decide_eq_true ((iterate_eq_projection_iff f x K).mpr hK)
      simp only [he, ite_true]
      exact shortDepth_spec f K x hK
    · have he : equal x last = false := decide_eq_false
        (fun hh => hK ((iterate_eq_projection_iff f x K).mp hh))
      simp only [he, Bool.false_eq_true, ite_false]
      have hex : ∃ j : Fin (K + 1), j.val < K + 1 ∧ flags x j = true := by
        rcases hcover x with ⟨i, j, hij, hj, hrep⟩ | ⟨t, ht, i, hi⟩
        · have hdepth := depth_add_cycleLength_le_repeat f x hij hrep
          dsimp [K] at hK
          lia
        · let j : Fin (K + 1) := ⟨t, by dsimp [K]; lia⟩
          exact ⟨j, j.isLt, (hm (queries x) j).mpr
            ⟨i, by rw [hquery]; exact hi.symm⟩⟩
      obtain ⟨j, _, hj, hchosen⟩ := chooseRecord_spec (flags x)
        (fun j (bit : Fin W) => (corrected j x).getLsbD bit.val) (fun _ => false) (K + 1) hex
      change selected x = _
      dsimp only [selected]
      rw [hchosen, word_bits]
      obtain ⟨i, hi⟩ := (hm (queries x) j).mp hj
      rw [hquery] at hi
      have hrecord : records x j = payload i := by
        funext bit
        exact hv (queries x) j i (by rwa [hquery]) bit
      have hjμ : j.val ≤ transientDepth f x := by have := j.isLt; lia
      have hdepth : transientDepth f (cp i) + j.val = transientDepth f x := by
        rw [hi, transientDepth_iterate, Nat.sub_add_cancel hjμ]
      dsimp only [corrected]
      rw [hrecord]
      simp only [payload, word_bits, ← BitVec.ofNat_add, hdepth]
      rfl
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul] at hs ⊢
    unfold checkpointDepthCost
    dsimp only [K, W] at hlookup ⊢
    lia

set_option maxRecDepth 4096 in
theorem checkpointDepthCost_le (n s M L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n)
    (hM : M ≤ 2 ^ n / L) :
    checkpointDepthCost n s M L ≤ 1000000 * powerBudget n s (2 ^ n) L := by
  let d := Nat.clog 2 (M + (2 * L + 1) + 1)
  have hN : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hMN : M ≤ 2 ^ n := hM.trans (Nat.div_le_self _ _)
  have hd : d ≤ n + 3 := by
    apply Nat.clog_le_of_le_pow
    simp only [Nat.pow_succ]
    lia
  have hw : (d + n + (1 + (n + 2)) + 3) ^ 3 ≤ 729 * (n + 1) ^ 3 := by
    have h := Nat.pow_le_pow_left (show d + n + (1 + (n + 2)) + 3 ≤ 9 * (n + 1) by lia) 3
    nlinarith
  have hr : M + (2 * L + 1) + 1 ≤ 2 ^ n / L + 4 * L := by lia
  have hdict := Nat.mul_le_mul hr hw
  have hpoly : 6 * n + 1 + 28 * (n + 2) + 1 ≤ 60 * (n + 1) ^ 3 := by
    nlinarith [Nat.zero_le (n ^ 3)]
  have hscan := Nat.mul_le_mul (show 2 * L + 1 ≤ 3 * L by lia) hpoly
  dsimp only [d] at hdict
  unfold checkpointDepthCost powerBudget
  nlinarith [Nat.zero_le (L * s), Nat.zero_le (L * n ^ 3),
    Nat.zero_le ((2 ^ n / L) * (n + 1) ^ 3)]

/-- Exact transient depth in the same square-root tradeoff as one fixed iterate. -/
theorem checkpoint_depth_circuit (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n (n + 2),
      (∀ x, word (out.eval Boolean.interpretation x) =
        BitVec.ofNat (n + 2) (transientDepth (c.eval Boolean.interpretation) x)) ∧
      out.size ≤ 1000000 * powerBudget n c.size (2 ^ n) L := by
  classical
  obtain ⟨H, hcard, hcover⟩ := exists_checkpoints_finite (c.eval Boolean.interpretation) hL
  let cp : Fin H.card → State n := fun j => (H.equivFin.symm j).val
  have hcp : Function.Injective cp := fun _ _ h => H.equivFin.symm.injective (Subtype.ext h)
  have hcov (x : State n) : Repeats (c.eval Boolean.interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval Boolean.interpretation)^[t] x = cp j := by
    rcases hcover x with hr | ⟨t, ht, hm⟩
    · exact Or.inl hr
    · exact Or.inr ⟨t, ht, H.equivFin ⟨_, hm⟩, by simp [cp]⟩
  obtain ⟨out, ho, hs⟩ := depth_from_checkpoints c L hL hLN cp hcp hcov
  exact ⟨out, ho, hs.trans (checkpointDepthCost_le _ _ _ _ hL hLN (by simpa using hcard))⟩

theorem checkpoint_depth_optimized (c : Circuit Boolean.signature n n) :
    ∃ out : Circuit Boolean.signature n (n + 2),
      (∀ x, word (out.eval Boolean.interpretation x) =
        BitVec.ofNat (n + 2) (transientDepth (c.eval Boolean.interpretation) x)) ∧
      (out.size : ℝ) ≤ 3000000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, hopt⟩ := powerBudget_optimized n c.size (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := checkpoint_depth_circuit c L hL hLN
  refine ⟨out, ho, ?_⟩
  have hs' : (out.size : ℝ) ≤ 1000000 * (powerBudget n c.size (2 ^ n) L : ℝ) := by
    exact_mod_cast hs
  linarith

end IteratedFunctions
