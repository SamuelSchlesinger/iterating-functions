/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ForestQuerySynthesis

/-! # Square-root-size transient reachability circuits -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n : ℕ}

def forestTransientCost (n s M E L : ℕ) : ℕ :=
  1000000 * powerBudget n s (2 ^ n) L + 6 * L * s +
    dictionaryCost n (forestRecordWidth n) M (2 * L + 2) +
    dictionaryCost n (forestRecordWidth n) E (2 * L + 1) +
    1100 * (2 * L + 1) * (n + 3)

/-- Two static dictionaries plus three short orbit prefixes answer transient reachability. -/
theorem forest_transient_from_tables (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) (H : Finset (State n))
    (hcover : ∀ x, Repeats (c.eval Boolean.interpretation) x L ∨
      ∃ t < 2 * L, (c.eval Boolean.interpretation)^[t] x ∈ H)
    (table : ForestEdgeTable (c.eval Boolean.interpretation) H L)
    (low high : State n → Fin (Nat.card (State n)))
    (hinterval : ∀ x y, (low y ≤ low x ∧ low x ≤ high y) ↔
      ∃ t ≤ transientDepth (c.eval Boolean.interpretation) x,
        (c.eval Boolean.interpretation)^[t] x = y) :
    ∃ out : Circuit Boolean.signature (n + n) 1,
      (∀ z, 0 < transientDepth (c.eval Boolean.interpretation) (inputRight z) →
        (out.eval Boolean.interpretation z 0 = true ↔
          ∃ t, (c.eval Boolean.interpretation)^[t] (inputLeft z) = inputRight z)) ∧
      out.size ≤ forestTransientCost n c.size
        (forestMarks (c.eval Boolean.interpretation) H).card table.count L := by
  classical
  let f := c.eval Boolean.interpretation
  let K := 2 * L
  let W := forestRecordWidth n
  let x : State (n + n) → State n := inputLeft
  let y : State (n + n) → State n := inputRight
  let src := inputs (n + n) ∪ {fun _ => false}
  have hx : wires x ⊆ src := by rintro _ ⟨bit, rfl⟩; exact Or.inl ⟨_, rfl⟩
  have hy : wires y ⊆ src := by rintro _ ⟨bit, rfl⟩; exact Or.inl ⟨_, rfl⟩
  obtain ⟨depth, hd, hds⟩ := checkpoint_depth_circuit c L hL hLN
  have hdy := synthesis_depthWord depth f hd src y hy (Or.inr rfl)
  have hpx := synthesis_prefix c src x hx K
  have hpy := synthesis_prefix c src y hy K
  let s1 := src ∪ (orbitPrefixWires f x K ∪ orbitPrefixWires f y K ∪
    wordWires (fun z => depthWord f (y z)))
  have avPX : orbitPrefixWires f x K ⊆ s1 := fun _ h => Or.inr (Or.inl (Or.inl h))
  have avPY : orbitPrefixWires f y K ⊆ s1 := fun _ h => Or.inr (Or.inl (Or.inr h))
  have avD : wordWires (fun z => depthWord f (y z)) ⊆ s1 := fun _ h => Or.inr (Or.inr h)
  let marksSet := forestMarks f H
  let cp : Fin marksSet.card → State n := fun j => (marksSet.equivFin.symm j).val
  have hcp : Function.Injective cp := fun _ _ h => marksSet.equivFin.symm.injective (Subtype.ext h)
  have hcpMem (j) : cp j ∈ forestMarks f H := (marksSet.equivFin.symm j).property
  let payload := forestRecord f low high
  let queries := fun z => forestMarkQuery f K (x z) (y z)
  have hqueries (j : Fin (K + 2)) : wires (fun z => queries z j) ⊆ s1 := by
    by_cases hj : j.val < K + 1
    · have he : (fun z => queries z j) = fun z => f^[j.val] (x z) := by
        funext z
        simp only [queries, forestMarkQuery, hj, ite_true]
      rw [he]
      exact fun _ h => avPX (Set.mem_iUnion.mpr ⟨⟨j.val, hj⟩, h⟩)
    · have he : (fun z => queries z j) = y := by
        funext z
        simp only [queries, forestMarkQuery, hj, ite_false]
      rw [he]
      exact fun _ h => Or.inl (hy h)
  obtain ⟨markFlags, markRecords, hm, hmv, hmarks⟩ := synthesis_dictionary_rows s1
    cp (fun j => payload (cp j)) hcp queries hqueries
  obtain ⟨keyFlags, keyRecords, hk, hkv, hkeys⟩ := synthesis_dictionary_rows s1
    table.key (fun j => payload (table.start j)) table.key_injective
    (fun z (j : Fin (K + 1)) => f^[j.val] (y z))
    (fun j _ h => avPY (Set.mem_iUnion.mpr ⟨j, h⟩))
  let s2 := s1 ∪ (dictionaryWires markFlags markRecords ∪ dictionaryWires keyFlags keyRecords)
  have hfinish := synthesis_forest_query c s2 x y markFlags markRecords keyFlags keyRecords
    (fun _ h => Or.inl (Or.inl (hy h))) (Or.inl (Or.inl (Or.inr rfl)))
    (fun _ h => Or.inl (avPX h)) (fun _ h => Or.inl (avD h))
    (fun _ h => Or.inr (Or.inl h)) (fun _ h => Or.inr (Or.inr h))
  have hfull := (Synthesis.const (s := inputs (n + n)) false).trans
    (((hpx.union hpy).union hdy).trans ((hmarks.union hkeys).trans hfinish))
  obtain ⟨out, ho, hs⟩ := hfull.exists_circuit
  refine ⟨out, fun z hz => ?_, hs.trans ?_⟩
  · rw [ho z]
    apply forestQueryResult_spec f H L hL hcover table low high hinterval (x z) (y z) hz
      (markFlags z) (markRecords z) (keyFlags z) (keyRecords z)
    · intro j
      rw [hm z j]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨cp i, hcpMem i, hi⟩
      · rintro ⟨a, ha, he⟩
        exact ⟨marksSet.equivFin ⟨a, ha⟩, by simpa only [cp, Equiv.symm_apply_apply] using he⟩
    · intro j a ha he
      have hh := hmv z j (marksSet.equivFin ⟨a, ha⟩)
        (by simpa only [cp, Equiv.symm_apply_apply] using he)
      simpa only [cp, Equiv.symm_apply_apply] using hh
    · exact hk z
    · exact hkv z
  · dsimp only [forestTransientCost, K, W, marksSet]
    nlinarith [Nat.zero_le (L * n)]

theorem forest_dictionary_cost_le (n s M Q L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n)
    (hM : M ≤ 2 * (2 ^ n / L)) (hQ : Q ≤ 2 * L + 2) :
    dictionaryCost n (forestRecordWidth n) M Q ≤ 7000000 * powerBudget n s (2 ^ n) L := by
  have hN : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hMN : M ≤ 2 * 2 ^ n := hM.trans (Nat.mul_le_mul_left _ (Nat.div_le_self _ _))
  have hd : Nat.clog 2 (M + Q + 1) ≤ n + 3 := by
    apply Nat.clog_le_of_le_pow
    simp only [Nat.pow_succ]
    lia
  have hw : (Nat.clog 2 (M + Q + 1) + n + (1 + forestRecordWidth n) + 3) ^ 3 ≤
      4096 * (n + 1) ^ 3 := by
    have hh := Nat.pow_le_pow_left
      (show Nat.clog 2 (M + Q + 1) + n + (1 + forestRecordWidth n) + 3 ≤
        16 * (n + 1) by dsimp only [forestRecordWidth]; lia) 3
    nlinarith only [hh]
  have hr : M + Q + 1 ≤ 6 * (L + 2 ^ n / L + 1) := by lia
  have hh := Nat.mul_le_mul_left 256 (Nat.mul_le_mul hr hw)
  have hb : (n + 1) ^ 3 * (L + 2 ^ n / L + 1) ≤ powerBudget n s (2 ^ n) L := by
    unfold powerBudget
    lia
  unfold dictionaryCost
  nlinarith only [hh, hb, Nat.zero_le (powerBudget n s (2 ^ n) L)]

theorem forestTransientCost_le (n s M E L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n)
    (hM : M ≤ 2 * (2 ^ n / L)) (hE : E ≤ 2 * (2 ^ n / L)) :
    forestTransientCost n s M E L ≤ 20000000 * powerBudget n s (2 ^ n) L := by
  have hm := forest_dictionary_cost_le n s M (2 * L + 2) L hL hLN hM le_rfl
  have he := forest_dictionary_cost_le n s E (2 * L + 1) L hL hLN hE (by lia)
  have hpoly : n + 3 ≤ 3 * (n + 1) ^ 3 := by nlinarith [Nat.zero_le (n ^ 3)]
  have hp := Nat.mul_le_mul (show 2 * L + 1 ≤ 3 * (L + 2 ^ n / L + 1) by lia) hpoly
  have hb : (n + 1) ^ 3 * (L + 2 ^ n / L + 1) ≤ powerBudget n s (2 ^ n) L := by
    unfold powerBudget
    lia
  have hs : L * s ≤ powerBudget n s (2 ^ n) L := by unfold powerBudget; lia
  unfold forestTransientCost
  nlinarith only [hm, he, hp, hb, hs, Nat.zero_le (powerBudget n s (2 ^ n) L)]

/-- For transient targets, reachability has the same tradeoff as a single fixed iterate. -/
theorem forest_transient_circuit (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (n + n) 1,
      (∀ z, 0 < transientDepth (c.eval Boolean.interpretation) (inputRight z) →
        (out.eval Boolean.interpretation z 0 = true ↔
          ∃ t, (c.eval Boolean.interpretation)^[t] (inputLeft z) = inputRight z)) ∧
      out.size ≤ 20000000 * powerBudget n c.size (2 ^ n) L := by
  classical
  let f := c.eval Boolean.interpretation
  obtain ⟨H, hcard, hcover⟩ := exists_checkpoints_finite f hL
  obtain ⟨table⟩ := exists_forest_edge_table f H L hL hcover
  obtain ⟨low, high, hinterval⟩ := exists_forest_intervals f
  obtain ⟨out, ho, hs⟩ := forest_transient_from_tables c L hL hLN H hcover table low high hinterval
  have hM : (forestMarks f H).card ≤ 2 * (2 ^ n / L) :=
    (forestMarks_card f H).trans (Nat.mul_le_mul_left 2 (by simpa using hcard))
  exact ⟨out, ho, hs.trans (forestTransientCost_le n c.size _ _ L hL hLN hM
    (table.card_le.trans hM))⟩

/-- Combine forest ancestry for transient targets with cycle identity for cyclic targets. -/
theorem forest_reachability_circuit (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (n + n) 1,
      (∀ z, out.eval Boolean.interpretation z 0 = true ↔
        ∃ t, (c.eval Boolean.interpretation)^[t] (inputLeft z) = inputRight z) ∧
      out.size ≤ 50000000 * powerBudget n c.size (2 ^ n) L := by
  let : LinearOrder (State n) := stateOrder n
  let f := c.eval Boolean.interpretation
  let x : State (n + n) → State n := inputLeft
  let y : State (n + n) → State n := inputRight
  obtain ⟨transient, ht, hts⟩ := forest_transient_circuit c L hL hLN
  obtain ⟨cyclic, hc, hcs⟩ := cyclicity_circuit c L hL hLN
  obtain ⟨labels, hl, hls⟩ := cycle_label_circuit c L hL hLN
  have hle : labels.eval Boolean.interpretation = canonicalLabel f := funext hl
  let src : Set (State (n + n) → Bool) := inputs (n + n)
  have hx : wires x ⊆ src := by rintro _ ⟨bit, rfl⟩; exact ⟨_, rfl⟩
  have hy : wires y ⊆ src := by rintro _ ⟨bit, rfl⟩; exact ⟨_, rfl⟩
  have htrans := Synthesis.circuit (I := Boolean.interpretation) (s := src) transient id
    (fun bit => ⟨bit, rfl⟩)
  have hcyclic := Synthesis.circuit (I := Boolean.interpretation) (s := src) cyclic y
    (fun bit => hy ⟨bit, rfl⟩)
  have hlx := Synthesis.circuit (I := Boolean.interpretation) (s := src) labels x
    (fun bit => hx ⟨bit, rfl⟩)
  have hly := Synthesis.circuit (I := Boolean.interpretation) (s := src) labels y
    (fun bit => hy ⟨bit, rfl⟩)
  let s1 := src ∪ (wires (transient.eval Boolean.interpretation) ∪
    wires (fun z => cyclic.eval Boolean.interpretation (y z)) ∪
    wires (fun z => labels.eval Boolean.interpretation (x z)) ∪
    wires (fun z => labels.eval Boolean.interpretation (y z)))
  let cx : State (n + n) → State n :=
    fun z => labelRepresentative (labels.eval Boolean.interpretation (x z))
  let cy : State (n + n) → State n :=
    fun z => labelRepresentative (labels.eval Boolean.interpretation (y z))
  have avx : wires cx ⊆ s1 := by
    rintro _ ⟨bit, rfl⟩
    exact Or.inr (Or.inl (Or.inr ⟨_, rfl⟩))
  have avy : wires cy ⊆ s1 := by
    rintro _ ⟨bit, rfl⟩
    exact Or.inr (Or.inr ⟨_, rfl⟩)
  have heq := synthesis_bits_eq s1 cx cy avx avy
  let s2 := s1 ∪ {fun z => decide (cx z = cy z)}
  have hmux := Synthesis.mux (s := s2)
    (show (fun z => cyclic.eval Boolean.interpretation (y z) 0) ∈ s2 from
      Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨0, rfl⟩)))))
    (Or.inr rfl)
    (show (fun z => transient.eval Boolean.interpretation z 0) ∈ s2 from
      Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨0, rfl⟩)))))
  obtain ⟨out, ho, hs⟩ := ((((htrans.union hcyclic).union hlx).union hly).trans
    (heq.trans hmux)).exists_circuit
  refine ⟨out, fun z => ?_, hs.trans ?_⟩
  · rw [ho z]
    change (if cyclic.eval Boolean.interpretation (y z) 0 then decide (cx z = cy z)
      else transient.eval Boolean.interpretation z 0) = true ↔ _
    by_cases hp : y z ∈ Function.periodicPts f
    · simp only [(hc (y z)).mpr hp, ite_true, decide_eq_true_eq]
      have hxEq : cx z = canonicalCycle f (x z) := by
        simp only [cx, hle, canonicalLabel, labelRepresentative_bits]
      have hyEq : cy z = canonicalCycle f (y z) := by
        simp only [cy, hle, canonicalLabel, labelRepresentative_bits]
      rw [hxEq, hyEq]
      exact (cyclic_reachable_iff f (x z) (y z) hp).symm
    · have hfalse : cyclic.eval Boolean.interpretation (y z) 0 = false :=
        Bool.eq_false_iff.mpr (fun hh => hp ((hc (y z)).mp hh))
      rw [hfalse]
      simp only [Bool.false_eq_true, ite_false]
      apply ht z
      have hne : transientDepth f (y z) ≠ 0 := fun hh =>
        hp ((transientDepth_eq_zero_iff f (y z)).mp hh)
      exact Nat.pos_of_ne_zero hne
  · have hb : n + 1 ≤ powerBudget n c.size (2 ^ n) L := by
      have hh := Nat.mul_le_mul_left ((n + 1) ^ 3)
        (show 1 ≤ L + 2 ^ n / L + 1 by lia)
      unfold powerBudget
      nlinarith [Nat.zero_le (n ^ 3)]
    lia

end IteratedFunctions
