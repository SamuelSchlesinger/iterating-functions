/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ForestCircuitRecords

/-! # Exact semantics of the encoded forest query -/

@[expose] public section

namespace IteratedFunctions

variable {n K : ℕ}

def forestMarkQuery (f : State n → State n) (K : ℕ) (x y : State n)
    (j : Fin (K + 2)) : State n :=
  if j.val < K + 1 then f^[j.val] x else y

@[simp] theorem forestMarkQuery_prefix (f : State n → State n) (K : ℕ) (x y : State n)
    (j : Fin (K + 1)) : forestMarkQuery f K x y j.castSucc = f^[j.val] x := by
  simp only [forestMarkQuery, Fin.val_castSucc, j.isLt, ite_true]

@[simp] theorem forestMarkQuery_target (f : State n → State n) (K : ℕ) (x y : State n) :
    forestMarkQuery f K x y (Fin.last (K + 1)) = y := by
  simp only [forestMarkQuery, Fin.val_last, lt_self_iff_false, ite_false]

def forestHitFound (flags : Fin (K + 2) → Bool) : Bool :=
  decide (∃ j : Fin (K + 1), flags j.castSucc = true)

def forestHitRecord (flags : Fin (K + 2) → Bool)
    (records : Fin (K + 2) → State (forestRecordWidth n)) : State (forestRecordWidth n) :=
  chooseRecord (fun j : Fin (K + 1) => flags j.castSucc)
    (fun j => records j.castSucc) (fun _ => false) (K + 1)

noncomputable def forestEligible (f : State n → State n) (y : State n)
    (flags : Fin (K + 1) → Bool) (records : Fin (K + 1) → State (forestRecordWidth n))
    (j : Fin (K + 1)) : Bool :=
  flags j && !(forestRecordDepth (records j)).ult (depthWord f y)

noncomputable def forestKeyFound (f : State n → State n) (y : State n)
    (flags : Fin (K + 1) → Bool) (records : Fin (K + 1) → State (forestRecordWidth n)) : Bool :=
  decide (∃ j, forestEligible f y flags records j = true)

noncomputable def forestKeyRecord (f : State n → State n) (y : State n)
    (flags : Fin (K + 1) → Bool) (records : Fin (K + 1) → State (forestRecordWidth n)) :
    State (forestRecordWidth n) :=
  chooseRecord (forestEligible f y flags records) records (fun _ => false) (K + 1)

noncomputable def forestAnchorFound (f : State n → State n) (y : State n)
    (marks : Fin (K + 2) → Bool) (flags : Fin (K + 1) → Bool)
    (records : Fin (K + 1) → State (forestRecordWidth n)) : Bool :=
  marks (Fin.last (K + 1)) || forestKeyFound f y flags records

noncomputable def forestAnchorRecord (f : State n → State n) (y : State n)
    (marks : Fin (K + 2) → Bool) (markRecords : Fin (K + 2) → State (forestRecordWidth n))
    (flags : Fin (K + 1) → Bool) (records : Fin (K + 1) → State (forestRecordWidth n)) :
    State (forestRecordWidth n) :=
  if marks (Fin.last (K + 1)) then markRecords (Fin.last (K + 1))
  else forestKeyRecord f y flags records

def forestPrefixTest (f : State n → State n) (K : ℕ) (x y : State n) : Bool :=
  decide (∃ j : Fin (K + 1), f^[j.val] x = y)

theorem forestPrefixTest_spec (f : State n → State n) (K : ℕ) (x y : State n) :
    forestPrefixTest f K x y = true ↔ ∃ i ≤ K, f^[i] x = y := by
  simp only [forestPrefixTest, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j.val, by have := j.isLt; lia, hj⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i, by lia⟩, he⟩

def forestIntervalTest (h a : State (forestRecordWidth n)) : Bool :=
  !(forestRecordLow h).ult (forestRecordLow a) &&
    !(forestRecordHigh a).ult (forestRecordLow h)

noncomputable def forestQueryResult (f : State n → State n) (K : ℕ) (x y : State n)
    (marks : Fin (K + 2) → Bool) (markRecords : Fin (K + 2) → State (forestRecordWidth n))
    (flags : Fin (K + 1) → Bool) (records : Fin (K + 1) → State (forestRecordWidth n)) : Bool :=
  let h := forestHitRecord marks markRecords
  let a := forestAnchorRecord f y marks markRecords flags records
  forestPrefixTest f K x y ||
    (forestHitFound marks && forestAnchorFound f y marks flags records &&
      forestPrefixTest f K (forestRecordState a) y && forestIntervalTest h a)

theorem forestQueryResult_spec (f : State n → State n) (H : Finset (State n)) (L : ℕ)
    (hL : 0 < L) (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    (table : ForestEdgeTable f H L) (low high : State n → Fin (Nat.card (State n)))
    (hinterval : ∀ x y, (low y ≤ low x ∧ low x ≤ high y) ↔
      ∃ t ≤ transientDepth f x, f^[t] x = y)
    (x y : State n) (hy : 0 < transientDepth f y)
    (marks : Fin (2 * L + 2) → Bool)
    (markRecords : Fin (2 * L + 2) → State (forestRecordWidth n))
    (flags : Fin (2 * L + 1) → Bool)
    (records : Fin (2 * L + 1) → State (forestRecordWidth n))
    (hm : ∀ j, marks j = true ↔ ∃ a ∈ forestMarks f H, a = forestMarkQuery f (2 * L) x y j)
    (hmv : ∀ j a, a ∈ forestMarks f H → a = forestMarkQuery f (2 * L) x y j →
      markRecords j = forestRecord f low high a)
    (hk : ∀ j, flags j = true ↔ ∃ i, table.key i = f^[j.val] y)
    (hkv : ∀ j i, table.key i = f^[j.val] y → records j = forestRecord f low high (table.start i)) :
    forestQueryResult f (2 * L) x y marks markRecords flags records = true ↔
      ∃ t, f^[t] x = y := by
  let hrec := forestHitRecord marks markRecords
  let arec := forestAnchorRecord f y marks markRecords flags records
  let h := forestRecordState hrec
  let a := forestRecordState arec
  have hHit (hh : forestHitFound marks = true) :
      h ∈ forestMarks f H ∧ (∃ d ≤ 2 * L, f^[d] x = h) ∧
        hrec = forestRecord f low high h := by
    obtain ⟨j, _, hj, hsel⟩ := chooseRecord_spec
      (fun j : Fin (2 * L + 1) => marks j.castSucc)
      (fun j => markRecords j.castSucc) (fun _ => false) (2 * L + 1) (by
        obtain ⟨j, hj⟩ := of_decide_eq_true hh
        exact ⟨j, j.isLt, hj⟩)
    obtain ⟨b, hb, he⟩ := (hm j.castSucc).mp hj
    have hrecEq : hrec = forestRecord f low high b := hsel.trans (hmv j.castSucc b hb he)
    have hEq : h = b := by simp only [h, hrecEq, forestRecordState_record]
    rw [hEq]
    exact ⟨hb, ⟨j.val, by have := j.isLt; lia,
      (forestMarkQuery_prefix f (2 * L) x y j).symm.trans he.symm⟩, hrecEq⟩
  have hHitComplete (hh : ∃ d ≤ 2 * L, f^[d] x ∈ forestMarks f H) :
      forestHitFound marks = true := by
    obtain ⟨d, hd, hmem⟩ := hh
    apply decide_eq_true
    let j : Fin (2 * L + 1) := ⟨d, by lia⟩
    exact ⟨j, (hm j.castSucc).mpr ⟨_, hmem, (forestMarkQuery_prefix f _ _ _ j).symm⟩⟩
  have eligible (j : Fin (2 * L + 1)) : forestEligible f y flags records j = true ↔
      ∃ i, table.key i = f^[j.val] y ∧ transientDepth f y ≤ transientDepth f (table.start i) := by
    unfold forestEligible
    rw [Bool.and_eq_true]
    constructor
    · rintro ⟨hflag, hdep⟩
      obtain ⟨i, hi⟩ := (hk j).mp hflag
      rw [hkv j i hi] at hdep
      simp only [forestRecordDepth_record, BitVec.ult_eq_decide,
        depthWord_toNat, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hdep
      exact ⟨i, hi, hdep⟩
    · rintro ⟨i, hi, hdep⟩
      refine ⟨(hk j).mpr ⟨i, hi⟩, ?_⟩
      rw [hkv j i hi]
      simpa only [forestRecordDepth_record, BitVec.ult_eq_decide,
        depthWord_toNat, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] using hdep
  have hAnchor (ha : forestAnchorFound f y marks flags records = true) :
      ForestAnchor f H L y a ∧ arec = forestRecord f low high a := by
    by_cases hmY : marks (Fin.last (2 * L + 1)) = true
    · obtain ⟨b, hb, he⟩ := (hm _).mp hmY
      rw [forestMarkQuery_target] at he
      subst b
      have hrecEq : arec = forestRecord f low high y := by
        simp only [arec, forestAnchorRecord, hmY, ite_true]
        exact hmv _ y hb (forestMarkQuery_target f _ _ _).symm
      have haEq : a = y := by simp only [a, hrecEq, forestRecordState_record]
      rw [haEq]
      exact ⟨Or.inl ⟨hb, rfl⟩, hrecEq⟩
    · have hkey : forestKeyFound f y flags records = true := by
        simpa only [forestAnchorFound, Bool.or_eq_true, hmY,
          Bool.false_eq_true, false_or] using ha
      obtain ⟨j, _, hj, hsel⟩ := chooseRecord_spec (forestEligible f y flags records)
        records (fun _ => false) (2 * L + 1) (by
          obtain ⟨j, hj⟩ := of_decide_eq_true hkey
          exact ⟨j, j.isLt, hj⟩)
      obtain ⟨i, hi, hd⟩ := (eligible j).mp hj
      have hrecEq : arec = forestRecord f low high (table.start i) := by
        simp only [arec, forestAnchorRecord, hmY, forestKeyRecord]
        exact hsel.trans (hkv j i hi)
      have haEq : a = table.start i := by simp only [a, hrecEq, forestRecordState_record]
      rw [haEq]
      exact ⟨(table.anchor_iff y _).mpr (Or.inr ⟨i, j.val, rfl,
        by have := j.isLt; lia, hd, hi.symm⟩), hrecEq⟩
  have hAnchorComplete (ha : ∃ b, ForestAnchor f H L y b) :
      forestAnchorFound f y marks flags records = true := by
    obtain ⟨b, hb⟩ := ha
    rcases (table.anchor_iff y b).mp hb with ⟨hyM, _⟩ | ⟨i, k, rfl, hkL, hd, he⟩
    · simp only [forestAnchorFound, Bool.or_eq_true]
      exact Or.inl ((hm _).mpr ⟨y, hyM, (forestMarkQuery_target f _ _ _).symm⟩)
    · simp only [forestAnchorFound, Bool.or_eq_true]
      apply Or.inr
      apply decide_eq_true
      exact ⟨⟨k, by lia⟩, (eligible _).mpr ⟨i, he.symm, hd⟩⟩
  have htest (hh : forestHitFound marks = true)
      (ha : forestAnchorFound f y marks flags records = true) :
      forestIntervalTest hrec arec = true ↔ low a ≤ low h ∧ low h ≤ high a := by
    rw [forestIntervalTest, (hHit hh).2.2, (hAnchor ha).2]
    simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult_eq_decide,
      forestRecordLow_record, forestRecordHigh_record, decide_eq_false_iff_not, not_lt]
    rfl
  have hs := forest_navigation_spec f H L hL hcover low high hinterval x y h a hy
    (forestHitFound marks) (forestAnchorFound f y marks flags records)
    (fun hh => ⟨(hHit hh).1, (hHit hh).2.1⟩) hHitComplete
    (fun ha => (hAnchor ha).1) hAnchorComplete
  change (forestPrefixTest f (2 * L) x y ||
    (forestHitFound marks && forestAnchorFound f y marks flags records &&
      forestPrefixTest f (2 * L) a y && forestIntervalTest hrec arec)) = true ↔ _
  rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    forestPrefixTest_spec, forestPrefixTest_spec, hs]
  constructor
  · rintro (hshort | ⟨⟨⟨hh, ha⟩, hv⟩, hi⟩)
    · exact Or.inl hshort
    · exact Or.inr ⟨hh, ha, hv, (htest hh ha).mp hi⟩
  · rintro (hshort | ⟨hh, ha, hv, hi⟩)
    · exact Or.inl hshort
    · exact Or.inr ⟨⟨⟨hh, ha⟩, hv⟩, (htest hh ha).mpr hi⟩

end IteratedFunctions
