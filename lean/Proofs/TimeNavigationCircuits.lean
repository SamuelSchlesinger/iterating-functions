/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.TimeNavigation
public import Proofs.ForestCircuits
public import Proofs.LongTime

/-!
# Input-time iteration with one scan of the checkpoint forest

The circuit reduces every query to a short walk from one selected state. A
transient target uses a scan of ancestry and depth labels. A cyclic target
uses a scan of phases on checkpoints of the same cycle. Neither branch uses
binary powering, so an `n`-bit time costs the same as one fixed power.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n a : ℕ}
noncomputable local instance timeNavigationStateOrder : LinearOrder (State n) := stateOrder n

abbrev walkWidth (n : ℕ) := n + (n + 3)

/-- A start state and the number of steps still to be walked. -/
def walkRecord (x : State n) (w : BitVec (n + 3)) : State (walkWidth n) :=
  Fin.append x (fun i => w.getLsbD i.val)

def walkBase (r : State (walkWidth n)) : State n := fun i => r (Fin.castAdd (n + 3) i)

def walkLength (r : State (walkWidth n)) : BitVec (n + 3) := word fun i => r (Fin.natAdd n i)

@[simp] theorem walkBase_record (x : State n) (w : BitVec (n + 3)) :
    walkBase (walkRecord x w) = x := by
  funext i
  simp only [walkBase, walkRecord, Fin.append_left]

@[simp] theorem walkLength_record (x : State n) (w : BitVec (n + 3)) :
    walkLength (walkRecord x w) = w := by
  simp only [walkLength, walkRecord, Fin.append_right, word_bits]

theorem walkRecord_wires (s : Set (State a → Bool)) (x : State a → State n)
    (w : State a → BitVec (n + 3)) (hx : wires x ⊆ s) (hw : wordWires w ⊆ s) :
    wires (fun z => walkRecord (x z) (w z)) ⊆ s := by
  rintro _ ⟨i, rfl⟩
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [walkRecord, Fin.append_left]
    exact hx ⟨k, rfl⟩
  · simp only [walkRecord, Fin.append_right]
    exact hw ⟨k, rfl⟩

/-- Select the state reached after the recorded number of steps. -/
def walkResult (f : State n → State n) (K : ℕ) (r : State (walkWidth n)) : State n :=
  selectBits (walkLength r) (fun j : Fin (K + 1) => f^[j.val] (walkBase r))

theorem walkResult_spec (f : State n → State n) (K : ℕ) (r : State (walkWidth n))
    (hK : K + 1 ≤ 2 ^ (n + 3)) (hw : (walkLength r).toNat ≤ K) :
    walkResult f K r = f^[(walkLength r).toNat] (walkBase r) := by
  have he : walkLength r =
      BitVec.ofNat (n + 3) (⟨(walkLength r).toNat, by lia⟩ : Fin (K + 1)).val := by
    apply BitVec.eq_of_toNat_eq
    simp
  unfold walkResult
  conv_lhs => rw [he]
  exact selectBits_eq hK (fun j : Fin (K + 1) => f^[j.val] (walkBase r)) _

theorem synthesis_walk (c : Circuit Boolean.signature n n) (s : Set (State a → Bool))
    (r : State a → State (walkWidth n)) (hr : wires r ⊆ s) (K : ℕ) :
    Synthesis Boolean.interpretation s
      (wires fun z => walkResult (c.eval Boolean.interpretation) K (r z))
      (K * c.size + n * ((K + 1) * (2 * (n + 3) + 3) + 1)) := by
  let f := c.eval Boolean.interpretation
  let base := fun z => walkBase (r z)
  have hb : wires base ⊆ s := by
    rintro _ ⟨bit, rfl⟩
    exact hr ⟨_, rfl⟩
  have hp := synthesis_prefix c s base hb K
  have hsel := synthesis_selectBits (s ∪ orbitPrefixWires f base K)
    (fun z => walkLength (r z)) (fun (j : Fin (K + 1)) z => f^[j.val] (base z))
    (fun i => by
      simp only [walkLength, word_bit]
      exact Or.inl (hr ⟨_, rfl⟩))
    (fun j bit => Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨bit, rfl⟩⟩))
  exact hp.trans hsel

/-- Whether a word exceeds the allowed walk length. -/
def overWalk (K : ℕ) (w : BitVec (n + 3)) : Bool := (BitVec.ofNat (n + 3) K).ult w

theorem overWalk_false (K : ℕ) (hK : K < 2 ^ (n + 3)) (w : BitVec (n + 3)) :
    overWalk K w = false ↔ w.toNat ≤ K := by
  simp [overWalk, BitVec.ult, Nat.mod_eq_of_lt hK]

theorem word_const_mem (s : Set (State a → Bool)) (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s)
    (v : BitVec (n + 3)) (i : Fin (n + 3)) : (fun _ : State a => v.getLsbD i.val) ∈ s :=
  hc _

/-- The ancestry, depth, and distance filter for one forest mark. -/
def ancestorFlag (K : ℕ) (q D lowA highA depthA : BitVec (n + 3)) : Bool :=
  !q.ult lowA && !highA.ult q && !depthA.ult D && !overWalk K (depthA - D)

theorem ancestorFlag_iff (K : ℕ) (hK : K < 2 ^ (n + 3)) (q D lowA highA depthA : BitVec (n + 3)) :
    ancestorFlag K q D lowA highA depthA = true ↔
      lowA.toNat ≤ q.toNat ∧ q.toNat ≤ highA.toNat ∧ D.toNat ≤ depthA.toNat ∧
        (depthA - D).toNat ≤ K := by
  simp only [ancestorFlag, Bool.and_eq_true, Bool.not_eq_true', overWalk_false K hK,
    BitVec.ult, decide_eq_false_iff_not, not_lt, and_assoc]

def ancestorRowCost (n : ℕ) : ℕ := 80 * (n + 3) + 20

theorem synthesis_ancestor_row (s : Set (State a → Bool)) (q D : State a → BitVec (n + 3))
    (hq : wordWires q ⊆ s) (hD : wordWires D ⊆ s) (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s)
    (cp : State n) (lowA highA depthA : BitVec (n + 3)) (K : ℕ) :
    Synthesis Boolean.interpretation s
      ({fun z => ancestorFlag K (q z) (D z) lowA highA depthA} ∪
        wires fun z => walkRecord cp (depthA - D z))
      (ancestorRowCost n) := by
  have hcw := word_const_mem (n := n) s hc
  have hsub := synthesis_sub_linear s (fun _ => depthA) D (hcw depthA) (fun i => hD ⟨i, rfl⟩)
  let s1 := s ∪ wordWires fun z => depthA - D z
  have old : s ⊆ s1 := fun _ h => Or.inl h
  have h1 := synthesis_ult s1 q (fun _ => lowA) (fun i => old (hq ⟨i, rfl⟩))
    (fun i => old (hcw lowA i))
  have h2 := synthesis_ult s1 (fun _ => highA) q (fun i => old (hcw highA i))
    (fun i => old (hq ⟨i, rfl⟩))
  have h3 := synthesis_ult s1 (fun _ => depthA) D (fun i => old (hcw depthA i))
    (fun i => old (hD ⟨i, rfl⟩))
  have h4 := synthesis_ult s1 (fun _ => BitVec.ofNat (n + 3) K) (fun z => depthA - D z)
    (fun i => old (hcw _ i)) (fun i => Or.inr ⟨i, rfl⟩)
  have hflag := ((h1.not.and h2.not).and h3.not).and h4.not
  have hbits : wires (fun z => walkRecord cp (depthA - D z)) ⊆ s1 :=
    walkRecord_wires s1 (fun _ => cp) (fun z => depthA - D z)
      (by rintro _ ⟨bit, rfl⟩; exact old (hc _)) (fun _ h => Or.inr h)
  exact (hsub.trans (hflag.union (Synthesis.of_subset hbits))).mono
    Set.Subset.rfl Set.Subset.rfl (by unfold ancestorRowCost; lia)

/-- The representative and phase-distance filter for one checkpoint on a cycle. -/
def cycleFlag (K : ℕ) (same : Bool) (p ph : BitVec (n + 3)) : Bool :=
  same && !p.ult ph && !overWalk K (p - ph)

theorem cycleFlag_iff (K : ℕ) (hK : K < 2 ^ (n + 3)) (same : Bool) (p ph : BitVec (n + 3)) :
    cycleFlag K same p ph = true ↔
      same = true ∧ ph.toNat ≤ p.toNat ∧ (p - ph).toNat ≤ K := by
  simp only [cycleFlag, Bool.and_eq_true, Bool.not_eq_true', overWalk_false K hK,
    BitVec.ult, decide_eq_false_iff_not, not_lt, and_assoc]

def cycleRowCost (n : ℕ) : ℕ := 70 * (n + 3) + 20

theorem synthesis_cycle_row (s : Set (State a → Bool)) (rep : State a → State n)
    (p : State a → BitVec (n + 3)) (hrep : wires rep ⊆ s) (hp : wordWires p ⊆ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s) (cp canon : State n) (ph : BitVec (n + 3))
    (K : ℕ) :
    Synthesis Boolean.interpretation s
      ({fun z => cycleFlag K (decide (canon = rep z)) (p z) ph} ∪
        wires fun z => walkRecord cp (p z - ph))
      (cycleRowCost n) := by
  have hcw := word_const_mem (n := n) s hc
  have hsub := synthesis_sub_linear s p (fun _ => ph) (fun i => hp ⟨i, rfl⟩) (hcw ph)
  let s1 := s ∪ wordWires fun z => p z - ph
  have old : s ⊆ s1 := fun _ h => Or.inl h
  have heq := synthesis_bits_eq s1 (fun _ => canon) rep
    (by rintro _ ⟨bit, rfl⟩; exact old (hc _)) (fun _ h => old (hrep h))
  have h1 := synthesis_ult s1 p (fun _ => ph) (fun i => old (hp ⟨i, rfl⟩))
    (fun i => old (hcw ph i))
  have h2 := synthesis_ult s1 (fun _ => BitVec.ofNat (n + 3) K) (fun z => p z - ph)
    (fun i => old (hcw _ i)) (fun i => Or.inr ⟨i, rfl⟩)
  have hflag := (heq.and h1.not).and h2.not
  have hbits : wires (fun z => walkRecord cp (p z - ph)) ⊆ s1 :=
    walkRecord_wires s1 (fun _ => cp) (fun z => p z - ph)
      (by rintro _ ⟨bit, rfl⟩; exact old (hc _)) (fun _ h => Or.inr h)
  exact (hsub.trans (hflag.union (Synthesis.of_subset hbits))).mono
    Set.Subset.rfl Set.Subset.rfl (by unfold cycleRowCost; lia)

/-- Everything after the row scan: choose the scan or the short fallback, then walk. -/
def selectWalkCost (n s K : ℕ) : ℕ :=
  (5 * (n + 3) + 2) + 4 * walkWidth n + (K * s + n * ((K + 1) * (2 * (n + 3) + 3) + 1))

theorem synthesis_select_walk (c : Circuit Boolean.signature n n) (s : Set (State a → Bool))
    (selected fallback : State a → State (walkWidth n)) (w : State a → BitVec (n + 3))
    (hs : wires selected ⊆ s) (hf : wires fallback ⊆ s) (hw : wordWires w ⊆ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s) (K : ℕ) :
    Synthesis Boolean.interpretation s
      (wires fun z => walkResult (c.eval Boolean.interpretation) K
        (if overWalk K (w z) then selected z else fallback z))
      (selectWalkCost n c.size K) := by
  have hcmp := synthesis_ult s (fun _ => BitVec.ofNat (n + 3) K) w
    (word_const_mem s hc _) (fun i => hw ⟨i, rfl⟩)
  let s1 := s ∪ {fun z => overWalk K (w z)}
  have hmux := synthesis_record_mux s1 (fun z => overWalk K (w z)) selected fallback
    (Or.inr rfl) (fun _ h => Or.inl (hs h)) (fun _ h => Or.inl (hf h))
  let chosen := fun z => if overWalk K (w z) = true then selected z else fallback z
  have hwalk := synthesis_walk c (s1 ∪ wires chosen) chosen (fun _ h => Or.inr h) K
  exact (hcmp.trans (hmux.trans hwalk)).mono Set.Subset.rfl Set.Subset.rfl
    (by unfold selectWalkCost; lia)

def transientWalkCost (n s M L : ℕ) : ℕ :=
  2 * L * s + dictionaryCost n (forestRecordWidth n) M (2 * L + 1) +
    (2 * L + 1) * (4 * forestRecordWidth n) + (42 * (n + 3) + 2) +
    M * (ancestorRowCost n + 4 * walkWidth n) + selectWalkCost n s (2 * L)

/-- Answer every time below the transient depth. Other times are unconstrained. -/
theorem exists_transient_walk (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) (s : Set (State a → Bool))
    (x : State a → State n) (t : State a → BitVec (n + 3))
    (hx : wires x ⊆ s) (ht : wordWires t ⊆ s)
    (hd : wordWires (fun z => depthWord (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s) :
    ∃ M, M ≤ 2 * (2 ^ n / L) ∧ ∃ T : State a → State n,
      (∀ z, (t z).toNat < transientDepth (c.eval Boolean.interpretation) (x z) →
        T z = (c.eval Boolean.interpretation)^[(t z).toNat] (x z)) ∧
      Synthesis Boolean.interpretation s (wires T) (transientWalkCost n c.size M L) := by
  classical
  let f := c.eval Boolean.interpretation
  let K := 2 * L
  have hKw : K < 2 ^ (n + 3) := by
    simp only [K, Nat.pow_succ]
    lia
  obtain ⟨H, hcard, hcover⟩ := exists_checkpoints_finite f hL
  obtain ⟨low, high, hinterval⟩ := exists_forest_intervals f
  have hM : (forestMarks f H).card ≤ 2 * (2 ^ n / L) :=
    (forestMarks_card f H).trans (Nat.mul_le_mul_left 2 (by simpa using hcard))
  let marksSet := forestMarks f H
  let cp : Fin marksSet.card → State n := fun j => (marksSet.equivFin.symm j).val
  have hcp : Function.Injective cp := fun _ _ h => marksSet.equivFin.symm.injective (Subtype.ext h)
  have hcpMem (j) : cp j ∈ forestMarks f H := (marksSet.equivFin.symm j).property
  have hcpIndex (b : State n) (hb : b ∈ forestMarks f H) : ∃ j, cp j = b :=
    ⟨marksSet.equivFin ⟨b, hb⟩, by simp only [cp, Equiv.symm_apply_apply]⟩
  let payload := forestRecord f low high
  have hz : (fun _ : State a => false) ∈ s := hc false
  have hp := synthesis_prefix c s x hx K
  let s1 := s ∪ orbitPrefixWires f x K
  have old1 : s ⊆ s1 := fun _ h => Or.inl h
  obtain ⟨flags, records, hm, hmv, hdict⟩ := synthesis_dictionary_rows s1
    cp (fun j => payload (cp j)) hcp (fun z (j : Fin (K + 1)) => f^[j.val] (x z))
    (fun j _ h => Or.inr (Set.mem_iUnion.mpr ⟨j, h⟩))
  let s2 := s1 ∪ dictionaryWires flags records
  have old2 : s1 ⊆ s2 := fun _ h => Or.inl h
  have hchoose := synthesis_chooseRecord (w := forestRecordWidth n) s2 flags records
    (fun _ _ => false) (fun j => Or.inr (Or.inl ⟨j, rfl⟩))
    (fun j bit => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨bit, rfl⟩⟩)))
    (fun _ => old2 (old1 hz))
  let hit := fun z => chooseRecord (flags z) (records z) (fun _ => false) (K + 1)
  let s3 := s2 ∪ wires hit
  have old3 : s ⊆ s3 := fun _ h => Or.inl (old2 (old1 h))
  have hq := (forestRecord_fields s3 hit (fun _ h => Or.inr h)).2.2.1
  have hsub := synthesis_sub_linear s3 (fun z => depthWord f (x z)) t
    (fun i => old3 (hd ⟨i, rfl⟩)) (fun i => old3 (ht ⟨i, rfl⟩))
  let D := fun z => depthWord f (x z) - t z
  let s4 := s3 ∪ wordWires D
  have old4 : s3 ⊆ s4 := fun _ h => Or.inl h
  let lowA := fun j => forestRecordLow (payload (cp j))
  let highA := fun j => forestRecordHigh (payload (cp j))
  let depthA := fun j => forestRecordDepth (payload (cp j))
  let q := fun z => forestRecordLow (hit z)
  have hrows := synthesis_flaggedRecords (w := walkWidth n) s4
    (fun j z => ancestorFlag K (q z) (D z) (lowA j) (highA j) (depthA j))
    (fun j z => walkRecord (cp j) (depthA j - D z)) (ancestorRowCost n)
    (old4 (old3 hz))
    (fun j => synthesis_ancestor_row s4 q D (fun _ h => old4 (hq h)) (fun _ h => Or.inr h)
      (fun b => old4 (old3 (hc b))) (cp j) (lowA j) (highA j) (depthA j) K)
  let selected := fun z => chooseRecord
    (fun j => ancestorFlag K (q z) (D z) (lowA j) (highA j) (depthA j))
    (fun j => walkRecord (cp j) (depthA j - D z)) (fun _ => false) marksSet.card
  let s5 := s4 ∪ wires selected
  have old5 : s ⊆ s5 := fun _ h => Or.inl (old4 (old3 h))
  have hfallback : wires (fun z => walkRecord (x z) (t z)) ⊆ s5 :=
    walkRecord_wires s5 x t (fun _ h => old5 (hx h)) (fun _ h => old5 (ht h))
  have hfinish := synthesis_select_walk c s5 selected (fun z => walkRecord (x z) (t z)) t
    (fun _ h => Or.inr h) hfallback (fun _ h => old5 (ht h)) (fun b => old5 (hc b)) K
  refine ⟨marksSet.card, hM, _, ?_, (hp.trans (hdict.trans (hchoose.trans (hsub.trans
    (hrows.trans hfinish))))).mono Set.Subset.rfl Set.Subset.rfl (le_of_eq ?_)⟩
  · intro z htz
    have hnotLong : ¬ K < (t z).toNat → overWalk K (t z) = false := fun h =>
      (overWalk_false K hKw _).mpr (by lia)
    by_cases hlong : K < (t z).toNat
    · have hover : overWalk K (t z) = true := by
        simp only [overWalk, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hKw,
          decide_eq_true_eq, hlong]
      obtain ⟨d, hd', hmem⟩ := exists_prefix_checkpoint f H L hcover hlong htz
      obtain ⟨i, hi⟩ := hcpIndex _ (subset_forestMarks f H hmem)
      have hdk : d < K + 1 := by simp only [K]; lia
      obtain ⟨j, -, hflag, hhit⟩ := chooseRecord_spec (flags z) (records z)
        (fun _ => false) (K + 1) ⟨⟨d, hdk⟩, hdk, (hm z ⟨d, hdk⟩).mpr ⟨i, hi⟩⟩
      obtain ⟨i', hi'⟩ := (hm z j).mp hflag
      have hrec : hit z = payload (cp i') := hhit.trans (hmv z j i' hi')
      have hq' : (q z).toNat = (low (f^[j.val] (x z))).val := by
        simp only [q, hrec, payload, hi', forestRecordLow_record]
      have hjt : j.val ≤ (t z).toNat := by have := j.isLt; lia
      have hle : t z ≤ depthWord f (x z) := by
        change (t z).toNat ≤ (depthWord f (x z)).toNat
        rw [depthWord_toNat]
        exact htz.le
      have hD : (D z).toNat = transientDepth f (x z) - (t z).toNat := by
        simp only [D, BitVec.toNat_sub_of_le hle, depthWord_toNat]
      obtain ⟨b, hbm, hb1, hb2, hb3, hb4⟩ := exists_forest_ancestor_mark f H L hL hcover
        low high hinterval (hi' ▸ hcpMem i') rfl hjt htz
      obtain ⟨e, rfl⟩ := hcpIndex b hbm
      have hfield (e) : (lowA e).toNat = (low (cp e)).val ∧
          (highA e).toNat = (high (cp e)).val ∧
          (depthA e).toNat = transientDepth f (cp e) := by
        simp only [lowA, highA, depthA, payload, forestRecordLow_record,
          forestRecordHigh_record, forestRecordDepth_record, depthWord_toNat, and_self]
      have hsubA (e) (hle : transientDepth f (x z) - (t z).toNat ≤ transientDepth f (cp e)) :
          (depthA e - D z).toNat =
            transientDepth f (cp e) - (transientDepth f (x z) - (t z).toNat) := by
        have hle' : D z ≤ depthA e := by
          change (D z).toNat ≤ (depthA e).toNat
          rw [hD, (hfield e).2.2]
          exact hle
        rw [BitVec.toNat_sub_of_le hle', hD, (hfield e).2.2]
      obtain ⟨e', -, hflag', hsel⟩ := chooseRecord_spec
        (fun j => ancestorFlag K (q z) (D z) (lowA j) (highA j) (depthA j))
        (fun j => walkRecord (cp j) (depthA j - D z)) (fun _ => false) marksSet.card
        ⟨e, e.isLt, (ancestorFlag_iff K hKw _ _ _ _ _).mpr
          ⟨by rw [hq', (hfield e).1]; exact hb1, by rw [hq', (hfield e).2.1]; exact hb2,
           by rw [hD, (hfield e).2.2]; exact hb3, by rw [hsubA e hb3]; exact hb4⟩⟩
      obtain ⟨f1, f2, f3, f4⟩ := (ancestorFlag_iff K hKw _ _ _ _ _).mp hflag'
      rw [hq', (hfield e').1] at f1
      rw [hq', (hfield e').2.1] at f2
      rw [hD, (hfield e').2.2] at f3
      have hwalk := forest_ancestor_walk f low high hinterval (h := f^[j.val] (x z)) rfl hjt htz
        f1 f2 f3
      simp only [hover, ite_true]
      change walkResult f K (selected z) = _
      rw [show selected z = _ from hsel, walkResult_spec f K _ (by lia) (by simpa using f4)]
      simp only [walkBase_record, walkLength_record]
      rw [hsubA e' f3]
      exact hwalk
    · simp only [hnotLong hlong, Bool.false_eq_true, ite_false]
      rw [walkResult_spec f K _ (by lia) (by simpa using (by lia : (t z).toNat ≤ K))]
      simp only [walkBase_record, walkLength_record]
      rfl
  · simp only [transientWalkCost, K, Nat.add_assoc]

def cycleWalkCost (n s M L : ℕ) : ℕ :=
  (20 * (n + 3) + 1) + 100 * (n + 4) ^ 3 + M * (cycleRowCost n + 4 * walkWidth n) +
    selectWalkCost n s (2 * L)

/-- Answer every time at least the transient depth, using one phase scan. -/
theorem exists_cycle_walk (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (s : Set (State a → Bool))
    (x : State a → State n) (t : State a → BitVec (n + 3))
    (ht : wordWires t ⊆ s)
    (hlen : wordWires (fun z => lengthWord (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hph : wordWires (fun z => phaseWord (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hrep : wires (fun z => canonicalCycle (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s) (hLN : L ≤ 2 ^ n)
    (hb : ∀ z, (t z).toNat < 2 * 2 ^ n) :
    ∃ M, M ≤ 2 ^ n / L ∧ ∃ Y : State a → State n,
      (∀ z, transientDepth (c.eval Boolean.interpretation) (x z) ≤ (t z).toNat →
        Y z = (c.eval Boolean.interpretation)^[(t z).toNat] (x z)) ∧
      Synthesis Boolean.interpretation s (wires Y) (cycleWalkCost n c.size M L) := by
  classical
  let f := c.eval Boolean.interpretation
  let K := 2 * L
  have hKw : K < 2 ^ (n + 3) := by
    simp only [K, Nat.pow_succ]
    lia
  obtain ⟨H, hcard, hcover⟩ := exists_checkpoints_finite f hL
  let P := H.filter fun a => a ∈ Function.periodicPts f
  have hPcard : P.card ≤ 2 ^ n / L :=
    (Finset.card_filter_le _ _).trans (by simpa using hcard)
  let cp : Fin P.card → State n := fun j => (P.equivFin.symm j).val
  have hcpMem (j) : cp j ∈ Function.periodicPts f :=
    (Finset.mem_filter.mp (P.equivFin.symm j).property).2
  have hcpIndex (b : State n) (hb : b ∈ H) (hp : b ∈ Function.periodicPts f) :
      ∃ j, cp j = b :=
    ⟨P.equivFin ⟨b, Finset.mem_filter.mpr ⟨hb, hp⟩⟩, by simp only [cp, Equiv.symm_apply_apply]⟩
  have hadd := synthesis_add_linear s (fun z => phaseWord f (x z)) t
    (fun i => hph ⟨i, rfl⟩) (fun i => ht ⟨i, rfl⟩)
  let sum := fun z => phaseWord f (x z) + t z
  let s1 := s ∪ wordWires sum
  have old1 : s ⊆ s1 := fun _ h => Or.inl h
  have hmod := synthesis_umod s1 sum (fun z => lengthWord f (x z)) (fun i => Or.inr ⟨i, rfl⟩)
    (fun i => old1 (hlen ⟨i, rfl⟩))
  let p := fun z => sum z % lengthWord f (x z)
  let s2 := s1 ∪ wordWires p
  have old2 : s ⊆ s2 := fun _ h => Or.inl (old1 h)
  let phA := fun j => phaseWord f (cp j)
  let rep := fun z => canonicalCycle f (x z)
  have hrows := synthesis_flaggedRecords (w := walkWidth n) s2
    (fun j z => cycleFlag K (decide (canonicalCycle f (cp j) = rep z)) (p z) (phA j))
    (fun j z => walkRecord (cp j) (p z - phA j)) (cycleRowCost n)
    (old2 (hc false))
    (fun j => synthesis_cycle_row s2 rep p (fun _ h => old2 (hrep h)) (fun _ h => Or.inr h)
      (fun b => old2 (hc b)) (cp j) (canonicalCycle f (cp j)) (phA j) K)
  let selected := fun z => chooseRecord
    (fun j => cycleFlag K (decide (canonicalCycle f (cp j) = rep z)) (p z) (phA j))
    (fun j => walkRecord (cp j) (p z - phA j)) (fun _ => false) P.card
  let s3 := s2 ∪ wires selected
  have old3 : s2 ⊆ s3 := fun _ h => Or.inl h
  have hfallback : wires (fun z => walkRecord (rep z) (p z)) ⊆ s3 :=
    walkRecord_wires s3 rep p (fun _ h => old3 (old2 (hrep h))) (fun _ h => old3 (Or.inr h))
  have hfinish := synthesis_select_walk c s3 selected (fun z => walkRecord (rep z) (p z)) p
    (fun _ h => Or.inr h) hfallback (fun _ h => old3 (Or.inr h)) (fun b => old3 (old2 (hc b))) K
  refine ⟨P.card, hPcard, _, ?_, (hadd.trans (hmod.trans (hrows.trans hfinish))).mono
    Set.Subset.rfl Set.Subset.rfl ?_⟩
  · intro z hdepth
    have hlt := phase_lt f (x z)
    have hl := cycleLength_le_states f (x z)
    have hpos := cycleLength_pos f (x z)
    have hsum : (sum z).toNat = phase f (x z) + (t z).toNat := by
      simp only [sum, BitVec.toNat_add, phaseWord_toNat]
      apply Nat.mod_eq_of_lt
      have := hb z
      simp only [Nat.pow_succ] at *
      lia
    have hpval : (p z).toNat = (phase f (x z) + (t z).toNat) % cycleLength f (x z) := by
      simp only [p, BitVec.toNat_umod, hsum, lengthWord_toNat]
    have hpl : (p z).toNat < cycleLength f (x z) := by
      rw [hpval]
      exact Nat.mod_lt _ hpos
    have htarget : f^[(t z).toNat] (x z) = f^[(p z).toNat] (rep z) := by
      rw [hpval]
      exact phase_spec f (x z) hdepth
    by_cases hlong : K < (p z).toNat
    · have hover : overWalk K (p z) = true := by
        simp only [overWalk, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hKw,
          decide_eq_true_eq, hlong]
      obtain ⟨b, hbH, hbP, hbc, hb1, hb2⟩ :=
        exists_cycle_checkpoint f H L hcover (x z) hlong hpl
      obtain ⟨e, rfl⟩ := hcpIndex b hbH hbP
      have hphA (e) : (phA e).toNat = phase f (cp e) := phaseWord_toNat f (cp e)
      have hsubA (e) (hle : phase f (cp e) ≤ (p z).toNat) :
          (p z - phA e).toNat = (p z).toNat - phase f (cp e) := by
        have hle' : phA e ≤ p z := by
          change (phA e).toNat ≤ (p z).toNat
          rw [hphA]
          exact hle
        rw [BitVec.toNat_sub_of_le hle', hphA]
      obtain ⟨e', -, hflag', hsel⟩ := chooseRecord_spec
        (fun j => cycleFlag K (decide (canonicalCycle f (cp j) = rep z)) (p z) (phA j))
        (fun j => walkRecord (cp j) (p z - phA j)) (fun _ => false) P.card
        ⟨e, e.isLt, (cycleFlag_iff K hKw _ _ _).mpr
          ⟨decide_eq_true hbc, by rw [hphA]; exact hb1, by rw [hsubA e hb1]; exact hb2⟩⟩
      obtain ⟨f1, f2, f3⟩ := (cycleFlag_iff K hKw _ _ _).mp hflag'
      rw [hphA] at f2
      have hwalk := cycle_mark_walk f (hcpMem e') (of_decide_eq_true f1) f2
      simp only [hover, ite_true]
      change walkResult f K (selected z) = _
      rw [show selected z = _ from hsel, walkResult_spec f K _ (by lia) (by simpa using f3)]
      simp only [walkBase_record, walkLength_record]
      rw [hsubA e' f2, hwalk]
      exact htarget.symm
    · have hover : overWalk K (p z) = false := (overWalk_false K hKw _).mpr (by lia)
      simp only [hover, Bool.false_eq_true, ite_false]
      rw [walkResult_spec f K _ (by lia) (by simpa using (by lia : (p z).toNat ≤ K))]
      simp only [walkBase_record, walkLength_record]
      exact htarget.symm
  · unfold cycleWalkCost
    lia

theorem forest_time_cost_le (n s M P L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n)
    (hM : M ≤ 2 * (2 ^ n / L)) (hP : P ≤ 2 ^ n / L) :
    transientWalkCost n s M L + cycleWalkCost n s P L + 4 * n + (5 * (n + 3) + 2) ≤
      20000000 * powerBudget n s (2 ^ n) L := by
  let Y := L + 2 ^ n / L + 1
  let C := (n + 1) ^ 3
  let B := powerBudget n s (2 ^ n) L
  have hsL : L * s ≤ B := by simp only [B, powerBudget]; lia
  have hYC : C * Y ≤ B := by simp only [B, powerBudget, C, Y]; lia
  have hY : 1 ≤ Y := by simp only [Y]; lia
  have hc2 : (n + 1) * (n + 1) ≤ C := by
    simp only [C]
    nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]
  have hc1 : n + 1 ≤ C := le_trans (by nlinarith) hc2
  have hprod {X Z b d : ℕ} (hX : X ≤ b * Y) (hZ : Z ≤ d * (n + 1)) :
      X * Z ≤ b * d * (C * Y) :=
    calc X * Z ≤ (b * Y) * (d * (n + 1)) := Nat.mul_le_mul hX hZ
      _ = b * d * ((n + 1) * Y) := by ring
      _ ≤ b * d * (C * Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc1)
  have hdict := forest_dictionary_cost_le n s M (2 * L + 1) L hL hLN hM (by lia)
  have a1 : (2 * L + 1) * (4 * forestRecordWidth n) ≤ 3 * 36 * (C * Y) :=
    hprod (by simp only [Y]; lia) (by dsimp only [forestRecordWidth]; lia)
  have a2 : M * (ancestorRowCost n + 4 * walkWidth n) ≤ 2 * 280 * (C * Y) :=
    hprod (by simp only [Y]; lia) (by dsimp only [ancestorRowCost, walkWidth]; lia)
  have a3 : P * (cycleRowCost n + 4 * walkWidth n) ≤ 1 * 280 * (C * Y) :=
    hprod (by simp only [Y]; lia) (by dsimp only [cycleRowCost, walkWidth]; lia)
  have a4 : n * ((2 * L + 1) * (2 * (n + 3) + 3) + 1) ≤ 28 * (C * Y) := by
    have hinner : (2 * L + 1) * (2 * (n + 3) + 3) + 1 ≤ 28 * Y * (n + 1) := by
      have h := Nat.mul_le_mul (show 2 * L + 1 ≤ 3 * Y by simp only [Y]; lia)
        (show 2 * (n + 3) + 3 ≤ 9 * (n + 1) by lia)
      nlinarith
    calc n * ((2 * L + 1) * (2 * (n + 3) + 3) + 1) ≤ (n + 1) * (28 * Y * (n + 1)) :=
          Nat.mul_le_mul (by lia) hinner
      _ = 28 * (((n + 1) * (n + 1)) * Y) := by ring
      _ ≤ 28 * (C * Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc2)
  have a5 : 100 * (n + 4) ^ 3 ≤ 6400 * (C * Y) := by
    have h := Nat.pow_le_pow_left (show n + 4 ≤ 4 * (n + 1) by lia) 3
    have hCY : C ≤ C * Y := Nat.le_mul_of_pos_right _ hY
    simp only [C] at hCY ⊢
    nlinarith
  have a6 : 200 * (n + 1) ≤ 200 * (C * Y) := by
    have hCY : C ≤ C * Y := Nat.le_mul_of_pos_right _ hY
    lia
  simp only [transientWalkCost, cycleWalkCost, selectWalkCost, walkWidth] at *
  nlinarith only [hsL, hYC, hdict, a1, a2, a3, a4, a5, a6, Nat.zero_le (C * Y)]

/-- Combine the two branches for a time word below twice the number of states. -/
theorem synthesis_forest_time (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) (s : Set (State a → Bool))
    (x : State a → State n) (t : State a → BitVec (n + 3))
    (hx : wires x ⊆ s) (ht : wordWires t ⊆ s)
    (hd : wordWires (fun z => depthWord (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hlen : wordWires (fun z => lengthWord (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hph : wordWires (fun z => phaseWord (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hrep : wires (fun z => canonicalCycle (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s)
    (hb : ∀ z, (t z).toNat < 2 * 2 ^ n) :
    Synthesis Boolean.interpretation s
      (wires fun z => (c.eval Boolean.interpretation)^[(t z).toNat] (x z))
      (20000000 * powerBudget n c.size (2 ^ n) L) := by
  let f := c.eval Boolean.interpretation
  obtain ⟨M, hM, T, hT, hTs⟩ := exists_transient_walk c L hL hLN s x t hx ht hd hc
  obtain ⟨P, hP, Y, hY, hYs⟩ := exists_cycle_walk c L hL s x t ht hlen hph hrep hc hLN hb
  have hcmp := synthesis_ult s t (fun z => depthWord f (x z))
    (fun i => ht ⟨i, rfl⟩) (fun i => hd ⟨i, rfl⟩)
  let s1 := s ∪ (wires T ∪ wires Y ∪ {fun z => (t z).ult (depthWord f (x z))})
  have hmux := synthesis_record_mux s1 (fun z => (t z).ult (depthWord f (x z))) T Y
    (Or.inr (Or.inr rfl)) (fun _ h => Or.inr (Or.inl (Or.inl h)))
    (fun _ h => Or.inr (Or.inl (Or.inr h)))
  have hall := ((hTs.union hYs).union hcmp).trans hmux
  have he : (fun z => if (t z).ult (depthWord f (x z)) = true then T z else Y z) =
      fun z => f^[(t z).toNat] (x z) := by
    funext z
    by_cases hlt : (t z).toNat < transientDepth f (x z)
    · have hu : (t z).ult (depthWord f (x z)) = true := by
        simpa [BitVec.ult] using hlt
      simp only [hu, ite_true]
      exact hT z hlt
    · have hu : (t z).ult (depthWord f (x z)) = false := by
        simpa [BitVec.ult] using hlt
      simp only [hu, Bool.false_eq_true, ite_false]
      exact hY z (by lia)
  rw [he] at hall
  apply hall.mono Set.Subset.rfl Set.Subset.rfl
  have hbudget := forest_time_cost_le n c.size M P L hL hLN hM hP
  lia

theorem canonicalLabel_field_wires (f : State n → State n) (s : Set (State a → Bool))
    (init : State a → State n) (hl : wires (fun z => canonicalLabel f (init z)) ⊆ s) :
    wires (fun z => canonicalCycle f (init z)) ⊆ s ∧
      wordWires (fun z => lengthWord f (init z)) ⊆ s ∧
      wordWires (fun z => phaseWord f (init z)) ⊆ s := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨bit, rfl⟩
    have h : (fun z => canonicalLabel f (init z) (Fin.castAdd ((n + 3) + (n + 3)) bit)) ∈ s :=
      hl ⟨_, rfl⟩
    simpa only [canonicalLabel, labelBits, Fin.append_left] using h
  · rintro _ ⟨bit, rfl⟩
    have h : (fun z => canonicalLabel f (init z) (Fin.natAdd n (Fin.castAdd (n + 3) bit))) ∈ s :=
      hl ⟨_, rfl⟩
    simpa only [canonicalLabel, labelBits, lengthWord, Fin.append_right, Fin.append_left] using h
  · rintro _ ⟨bit, rfl⟩
    have h : (fun z => canonicalLabel f (init z) (Fin.natAdd n (Fin.natAdd (n + 3) bit))) ∈ s :=
      hl ⟨_, rfl⟩
    simpa only [canonicalLabel, labelBits, phaseWord, Fin.append_right] using h

/-- Build the iterator once the input time has been compressed to a short word. -/
theorem forest_time_of_word (c : Circuit Boolean.signature n n) (m L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) (time : State (n + m) → BitVec (n + 3)) (cost : ℕ)
    (htime : Synthesis Boolean.interpretation
      ((inputs (n + m) ∪ {fun _ => false, fun _ => true}) ∪
        wires (fun z => canonicalLabel (c.eval Boolean.interpretation)
          (fun i : Fin n => z (Fin.castAdd m i))))
      (wordWires time) cost)
    (hb : ∀ z, (time z).toNat < 2 * 2 ^ n)
    (hv : ∀ z, (c.eval Boolean.interpretation)^[(time z).toNat]
        (fun i : Fin n => z (Fin.castAdd m i)) =
      (c.eval Boolean.interpretation)^[binaryValue (fun j => z (Fin.natAdd n j))]
        (fun i : Fin n => z (Fin.castAdd m i))) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      (∀ z, out.eval Boolean.interpretation z =
        (c.eval Boolean.interpretation)^[binaryValue (fun j => z (Fin.natAdd n j))]
          (fun i => z (Fin.castAdd m i))) ∧
      out.size ≤ 2 + 31040000 * powerBudget n c.size (2 ^ n) L + cost := by
  let f := c.eval Boolean.interpretation
  let init := fun z : State (n + m) => fun i : Fin n => z (Fin.castAdd m i)
  let constants : Set (State (n + m) → Bool) := {fun _ => false, fun _ => true}
  let src := inputs (n + m) ∪ constants
  have hc (b : Bool) : (fun _ : State (n + m) => b) ∈ src := by
    cases b <;> simp [src, constants]
  have hconst : Synthesis Boolean.interpretation (inputs (n + m)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  obtain ⟨labels, hl, hls⟩ := cycle_label_circuit c L hL hLN
  have heval : labels.eval Boolean.interpretation = canonicalLabel f := funext hl
  have hlabels : Synthesis Boolean.interpretation src
      (wires (fun z => canonicalLabel f (init z))) labels.size := by
    simpa only [heval, wires] using Synthesis.circuit (I := Boolean.interpretation)
      (s := src) labels init (fun i => Or.inl ⟨_, rfl⟩)
  let s1 := src ∪ wires (fun z => canonicalLabel f (init z))
  obtain ⟨hrep, hlen, hph⟩ := canonicalLabel_field_wires f s1 init (fun _ h => Or.inr h)
  let s2 := s1 ∪ wordWires time
  have old2 : s1 ⊆ s2 := fun _ h => Or.inl h
  have hinit : wires init ⊆ s2 := by
    rintro _ ⟨i, rfl⟩
    exact old2 (Or.inl (Or.inl ⟨_, rfl⟩))
  obtain ⟨depth, hd, hds⟩ := checkpoint_depth_circuit c L hL hLN
  have hdepth := synthesis_depthWord depth f hd s2 init hinit (old2 (Or.inl (hc false)))
  let s3 := s2 ∪ wordWires (fun z => depthWord f (init z))
  have old3 : s2 ⊆ s3 := fun _ h => Or.inl h
  have hforest := synthesis_forest_time c L hL hLN s3 init time
    (fun _ h => old3 (hinit h)) (fun _ h => old3 (Or.inr h)) (fun _ h => Or.inr h)
    (fun _ h => old3 (old2 (hlen h))) (fun _ h => old3 (old2 (hph h)))
    (fun _ h => old3 (old2 (hrep h))) (fun b => old3 (old2 (Or.inl (hc b)))) hb
  obtain ⟨out, ho, hs⟩ :=
    (hconst.trans (hlabels.trans (htime.trans (hdepth.trans hforest)))).exists_circuit_outputs
  refine ⟨out, fun z => (ho z).trans (hv z), hs.trans ?_⟩
  lia

/-- An `m`-bit time costs one fixed-power budget plus linear work per time bit. -/
theorem variable_time_navigated (c : Circuit Boolean.signature n n) (m L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      (∀ z, out.eval Boolean.interpretation z =
        (c.eval Boolean.interpretation)^[binaryValue (fun j => z (Fin.natAdd n j))]
          (fun i => z (Fin.castAdd m i))) ∧
      out.size ≤ 32000000 * powerBudget n c.size (2 ^ n) L + 200 * m * (n + 1) := by
  let f := c.eval Boolean.interpretation
  let init := fun z : State (n + m) => fun i : Fin n => z (Fin.castAdd m i)
  let bits := fun z : State (n + m) => fun j : Fin m => z (Fin.natAdd n j)
  let constants : Set (State (n + m) → Bool) := {fun _ => false, fun _ => true}
  let src := inputs (n + m) ∪ constants
  let s1 := src ∪ wires (fun z => canonicalLabel f (init z))
  have hc (b : Bool) : (fun _ : State (n + m) => b) ∈ s1 := by
    cases b <;> simp [s1, src, constants]
  have hbit (j : Fin m) : (fun z => bits z j) ∈ s1 := Or.inl (Or.inl ⟨_, rfl⟩)
  have hbudget : (n + 1) ^ 3 ≤ powerBudget n c.size (2 ^ n) L := by
    have h := Nat.mul_le_mul_left ((n + 1) ^ 3) (show 1 ≤ L + 2 ^ n / L + 1 by lia)
    unfold powerBudget
    lia
  have hlin : n + 1 ≤ (n + 1) ^ 3 := by nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]
  by_cases hnm : n < m
  · obtain ⟨_, hlen, _⟩ := canonicalLabel_field_wires f s1 init (fun _ h => Or.inr h)
    have htime := synthesis_compressedTime s1 f init bits hlen hbit hc
    obtain ⟨out, ho, hs⟩ := forest_time_of_word c m L hL hLN
      (fun z => compressedTimeWord f (init z) (bits z)) _ htime
      (fun z => by
        rw [compressedTimeWord_toNat f _ _ hnm]
        simpa using normalizedTime_lt f (init z) (binaryValue (bits z)))
      (fun z => by
        rw [compressedTimeWord_toNat f _ _ hnm]
        exact iterate_normalizedTime f (init z) (binaryValue (bits z)))
    refine ⟨out, ho, hs.trans ?_⟩
    have hfour : (n + 4) ^ 3 ≤ 64 * (n + 1) ^ 3 := by
      have h := Nat.pow_le_pow_left (show n + 4 ≤ 4 * (n + 1) by lia) 3
      nlinarith
    have hm := Nat.mul_le_mul_left m (show 51 * (n + 3) + 9 ≤ 200 * (n + 1) by lia)
    nlinarith only [hfour, hbudget, hlin, hm]
  · let time := fun z => (word (bits z)).setWidth (n + 3)
    have hword : wordWires (fun z => word (bits z)) ⊆ s1 := by
      rintro _ ⟨i, rfl⟩
      simp only [word_bit]
      exact hbit i
    have htime : Synthesis Boolean.interpretation s1 (wordWires time) 0 :=
      Synthesis.of_subset (resize_wires (v := n + 3) s1 _ hword (hc false))
    have hmn : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by lia)
    have hlt (z) : binaryValue (bits z) < 2 ^ m := by
      simpa only [word_toNat] using (word (bits z)).isLt
    have hval (z) : (time z).toNat = binaryValue (bits z) := by
      simp only [time, BitVec.toNat_setWidth, word_toNat]
      exact Nat.mod_eq_of_lt
        ((hlt z).trans_le (hmn.trans (Nat.pow_le_pow_right (by decide) (by lia))))
    obtain ⟨out, ho, hs⟩ := forest_time_of_word c m L hL hLN time 0 htime
      (fun z => by have := hlt z; rw [hval]; lia)
      (fun z => by rw [hval])
    refine ⟨out, ho, hs.trans ?_⟩
    nlinarith only [hbudget, hlin]

/-- The input-time bound at the optimized checkpoint spacing. -/
theorem variable_time_navigated_optimized (c : Circuit Boolean.signature n n) (m : ℕ) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      (∀ z, out.eval Boolean.interpretation z =
        (c.eval Boolean.interpretation)^[binaryValue (fun j => z (Fin.natAdd n j))]
          (fun i => z (Fin.castAdd m i))) ∧
      (out.size : ℝ) ≤ 96000000 * optimizedBudget n c.size (2 ^ n) + 200 * m * (n + 1) := by
  obtain ⟨L, hL, hLN, hopt⟩ := powerBudget_optimized n c.size (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := variable_time_navigated c m L hL hLN
  refine ⟨out, ho, ?_⟩
  have hs' : (out.size : ℝ) ≤ 32000000 * (powerBudget n c.size (2 ^ n) L : ℝ) +
      200 * m * (n + 1) := by exact_mod_cast hs
  nlinarith

end IteratedFunctions
