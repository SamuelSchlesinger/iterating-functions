/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.LabelEncoding
public import Proofs.BatchLookup
public import Proofs.Optimization
public import Proofs.Applications

/-! # Square-root circuits for canonical functional-graph labels -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
open scoped BigOperators

variable {n M : ℕ}
noncomputable local instance labelCircuitsStateOrder : LinearOrder (State n) := stateOrder n

abbrev labelWidth (n : ℕ) : ℕ := n + ((n + 3) + (n + 3))

def labelConstructionCost (n s M L : ℕ) : ℕ :=
  2 + 2 * L * s +
    256 * (M + (2 * L + 1) + 1) *
      (Nat.clog 2 (M + (2 * L + 1) + 1) + n + (1 + labelWidth n) + 3) ^ 3 +
    (2 * L + 1) * (300 * (n + 4) ^ 3) +
    ((2 * L + 1) * (30 * (n + (n + 3) + 1)) + 300 * (n + 4) ^ 3) +
    (2 * L + 1) * (4 * labelWidth n)

theorem cyclic_labels_from_checkpoints (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) (cp : Fin M → State n) (hcp : Function.Injective cp)
    (hcover : ∀ x : State n, Repeats (c.eval Boolean.interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval Boolean.interpretation)^[t] x = cp j) :
    ∃ out : Circuit Boolean.signature n (labelWidth n),
      (∀ x, x ∈ Function.periodicPts (c.eval Boolean.interpretation) →
        out.eval Boolean.interpretation x = canonicalLabel (c.eval Boolean.interpretation) x) ∧
      out.size ≤ labelConstructionCost n c.size M L := by
  let f := c.eval Boolean.interpretation
  let K := 2 * L
  let W := labelWidth n
  let constants : Set (State n → Bool) := {fun _ => false, fun _ => true}
  let src := inputs n ∪ constants
  have hc (b : Bool) : (fun _ : State n => b) ∈ src := by
    cases b <;> simp [src, constants]
  have hconst : Synthesis Boolean.interpretation (inputs n) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  let trace := fun j x => f^[j] x
  let stages := Synthesis.stages (fun j => wires (trace j)) K
  have horbit := synthesis_orbit Boolean.interpretation c src id (fun i => Or.inl ⟨i, rfl⟩) K
  let src1 := src ∪ stages
  have hp (j : Fin (K + 1)) (bit : Fin n) : (fun x => f^[j.val] x bit) ∈ src1 :=
    Or.inr (Set.mem_iUnion.mpr ⟨j.val, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr j.isLt, ⟨bit, rfl⟩⟩⟩)
  let queries : State n → State ((K + 1) * n) := fun x bit =>
    let p := (finProdFinEquiv (m := K + 1) (n := n)).symm bit
    f^[p.1.val] x p.2
  have hquery (x : State n) (j : Fin (K + 1)) :
      (fun bit => queries x (finProdFinEquiv (j, bit))) = f^[j.val] x := by
    funext bit
    simp only [queries, Equiv.symm_apply_apply]
  obtain ⟨lookup, hm, hv, _, hlookup⟩ :=
    SharedLookup.fixed_dictionary (Q := K + 1) cp (fun i => canonicalLabel f (cp i)) hcp
  have hd := Synthesis.circuit (I := Boolean.interpretation) (s := src1) lookup queries
    (fun bit => hp _ _)
  let result := fun x => lookup.eval Boolean.interpretation (queries x)
  let src2 := src1 ∪ wires result
  let flags := fun x (j : Fin (K + 1)) => result x (finProdFinEquiv (j, (0 : Fin (1 + W))))
  let records := fun x (j : Fin (K + 1)) (bit : Fin W) =>
    result x (finProdFinEquiv (j, Fin.natAdd 1 bit))
  let corrected := fun j x => correctLabel (records x j) j.val
  have hcorrect (j : Fin (K + 1)) :
      Synthesis Boolean.interpretation src2 (wires (corrected j)) (300 * (n + 4) ^ 3) :=
    synthesis_correctLabel src2 (fun x => records x j)
      (by rintro _ ⟨bit, rfl⟩; exact Or.inr ⟨_, rfl⟩)
      (fun b => Or.inl (Or.inl (hc b))) j.val
  have hall := Synthesis.iUnion (fun j => wires (corrected j)) (fun _ => 300 * (n + 4) ^ 3)
    hcorrect
  have hshort := synthesis_shortLabel src2 f id K (fun j bit => Or.inl (hp j bit))
    (fun b => Or.inl (Or.inl (hc b)))
  let src3 := src2 ∪ ((⋃ j, wires (corrected j)) ∪ wires (fun x => shortLabel f K x))
  have hselect := synthesis_chooseRecord src3 flags (fun x j => corrected j x)
    (fun x => shortLabel f K x) (fun j => Or.inl (Or.inr ⟨_, rfl⟩))
    (fun j bit => Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨j, ⟨bit, rfl⟩⟩)))
    (fun bit => Or.inr (Or.inr ⟨bit, rfl⟩))
  have h := hconst.trans (horbit.trans (hd.trans ((hall.union hshort).trans hselect)))
  obtain ⟨out, hout, hs⟩ := h.exists_circuit_outputs
  refine ⟨out, ?_, hs.trans ?_⟩
  · intro x hx
    rw [hout x]
    change chooseRecord (flags x) (fun j => corrected j x) (shortLabel f K x) (K + 1) =
      canonicalLabel f x
    by_cases hh : ∃ j, flags x j = true
    · obtain ⟨j, _, hj, he⟩ := chooseRecord_spec (flags x) (fun j => corrected j x)
        (shortLabel f K x) (K + 1) (by obtain ⟨j, hj⟩ := hh; exact ⟨j, j.isLt, hj⟩)
      rw [he]
      obtain ⟨i, hi⟩ := (hm (queries x) j).mp hj
      rw [hquery] at hi
      have hrecord : records x j = canonicalLabel f (cp i) := by
        funext bit
        exact hv (queries x) j i (by rwa [hquery]) bit
      change correctLabel (records x j) j.val = _
      rw [hrecord, hi]
      apply correctLabel_spec
      have hjK := j.isLt
      dsimp [K] at hjK
      simp only [Nat.pow_succ]
      have := Nat.one_le_two_pow (n := n)
      lia
    · have hnone : ∀ j, flags x j = false := fun j => Bool.eq_false_iff.mpr (fun hj => hh ⟨j, hj⟩)
      rw [chooseRecord_no_flags _ _ _ hnone]
      apply shortLabel_spec f K x hx
      rcases hcover x with ⟨i, j, hij, hj, he⟩ | ⟨t, ht, i, hi⟩
      · have hb := depth_add_cycleLength_le_repeat f x hij he
        dsimp [K]
        lia
      · exfalso
        apply hh
        let j : Fin (K + 1) := ⟨t, by dsimp [K]; lia⟩
        exact ⟨j, (hm (queries x) j).mpr ⟨i, by rw [hquery]; exact hi.symm⟩⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] at hs ⊢
    unfold labelConstructionCost
    dsimp only [K, W, labelWidth] at hlookup ⊢
    lia

set_option maxRecDepth 4096 in
theorem label_construction_cost (n s M L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n)
    (hM : M ≤ 2 ^ n / L) :
    labelConstructionCost n s M L ≤ 10000000 * powerBudget n s (2 ^ n) L := by
  let d := Nat.clog 2 (M + (2 * L + 1) + 1)
  have hN : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hMN : M ≤ 2 ^ n := hM.trans (Nat.div_le_self _ _)
  have hd : d ≤ n + 3 := by
    apply Nat.clog_le_of_le_pow
    simp only [Nat.pow_succ]
    lia
  have hw : (d + n + (1 + labelWidth n) + 3) ^ 3 ≤ 2197 * (n + 1) ^ 3 := by
    have hh : d + n + (1 + labelWidth n) + 3 ≤ 13 * (n + 1) := by dsimp [labelWidth]; lia
    have h := Nat.pow_le_pow_left hh 3
    nlinarith
  have hr : M + (2 * L + 1) + 1 ≤ 2 ^ n / L + 4 * L := by lia
  have hdict := Nat.mul_le_mul hr hw
  have hw4 : (n + 4) ^ 3 ≤ 64 * (n + 1) ^ 3 := by
    have h := Nat.pow_le_pow_left (show n + 4 ≤ 4 * (n + 1) by lia) 3
    nlinarith
  have hshort := Nat.mul_le_mul (show 2 * L + 1 ≤ 3 * L by lia) hw4
  dsimp only [d, labelWidth] at hdict
  unfold labelConstructionCost powerBudget
  dsimp only [labelWidth]
  nlinarith [Nat.zero_le (L * s), Nat.zero_le (L * n ^ 3),
    Nat.zero_le ((2 ^ n / L) * (n + 1) ^ 3)]

/-- Exact cycle labels on cyclic inputs, with the original square-root tradeoff. -/
theorem cyclic_label_circuit (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n (labelWidth n),
      (∀ x, x ∈ Function.periodicPts (c.eval Boolean.interpretation) →
        out.eval Boolean.interpretation x = canonicalLabel (c.eval Boolean.interpretation) x) ∧
      out.size ≤ 10000000 * powerBudget n c.size (2 ^ n) L := by
  classical
  obtain ⟨H, _, hcard, hcover⟩ := exists_checkpoints (c.eval Boolean.interpretation)
    Finset.univ (fun _ _ => Finset.mem_univ _) hL
  let cp : Fin H.card → State n := fun j => (H.equivFin.symm j).val
  have hcp : Function.Injective cp := fun _ _ h => H.equivFin.symm.injective (Subtype.ext h)
  have hcov (x : State n) : Repeats (c.eval Boolean.interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval Boolean.interpretation)^[t] x = cp j := by
    rcases hcover x (Finset.mem_univ _) with hr | ⟨t, ht, hm⟩
    · exact Or.inl hr
    · exact Or.inr ⟨t, ht, H.equivFin ⟨_, hm⟩, by simp [cp]⟩
  obtain ⟨out, hout, hs⟩ := cyclic_labels_from_checkpoints c L hL hLN cp hcp hcov
  refine ⟨out, hout, hs.trans (label_construction_cost _ _ _ _ hL hLN ?_)⟩
  apply (Nat.le_div_iff_mul_le hL).mpr
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using hcard

theorem factorial_iterate_periodic (f : State n → State n) (x : State n) :
    f^[Nat.factorial (2 ^ n)] x ∈ Function.periodicPts f := by
  apply (periodic_iterate_iff f x _).mpr
  have hd : transientDepth f x < 2 ^ n := by simpa using transientDepth_lt_card f x
  exact hd.le.trans (Nat.self_le_factorial _)

theorem canonicalLabel_factorial (f : State n → State n) (x : State n) :
    canonicalLabel f (f^[Nat.factorial (2 ^ n)] x) = canonicalLabel f x := by
  have hd := Nat.dvd_factorial (cycleLength_pos f x) (cycleLength_le_states f x)
  simp only [canonicalLabel, canonicalCycle_iterate, cycleLength_iterate, phase_shift,
    Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero,
    Nat.mod_eq_of_lt (phase_lt f x)]

/-- Canonical representative, exact period, and phase, for every initial state. -/
theorem cycle_label_circuit (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n (labelWidth n),
      out.Computes Boolean.interpretation (canonicalLabel (c.eval Boolean.interpretation)) ∧
      out.size ≤ 10040000 * powerBudget n c.size (2 ^ n) L := by
  obtain ⟨project, hp, hs⟩ := fixed_power n c (Nat.factorial (2 ^ n)) L hL hLN
  obtain ⟨labels, hl, hls⟩ := cyclic_label_circuit c L hL hLN
  refine ⟨labels.comp project, ?_, ?_⟩
  · intro x
    rw [Circuit.eval_comp, hp x, hl _ (factorial_iterate_periodic _ x), canonicalLabel_factorial]
  · rw [Circuit.size_comp]
    lia

theorem cycle_labels_optimized (c : Circuit Boolean.signature n n) :
    ∃ out : Circuit Boolean.signature n (labelWidth n),
      out.Computes Boolean.interpretation (canonicalLabel (c.eval Boolean.interpretation)) ∧
      (out.size : ℝ) ≤ 30120000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, ho⟩ := powerBudget_optimized n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := cycle_label_circuit c L hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ 10040000 * (powerBudget n c.size (2 ^ n) L : ℝ) := by
    exact_mod_cast hs
  linarith

end IteratedFunctions
