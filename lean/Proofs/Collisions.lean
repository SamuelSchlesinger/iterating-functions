/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Algebraic.MassProduction.SortingSemantics.Defs

/-!
# Adjacent collisions after sorting

Sorting complete records allows one pass to find either a checkpoint hit or a
repeated orbit state. Two distinct input records with the same key force an
adjacent equal-key pair in the sorted output.
-/

@[expose] public section

namespace IteratedFunctions

open Algebraic.MassProduction.Sorting.Semantics

universe u v
variable {α : Type u} {β : Type v} [LinearOrder β] {R : ℕ}

/-- Equal keys at distinct positions of a sorted sequence give adjacent equal keys. -/
theorem adjacent_of_equal_keys (keys : Fin R → β) (hs : Monotone keys)
    {i j : Fin R} (hij : i ≠ j) (heq : keys i = keys j) :
    ∃ (p : ℕ) (hp : p + 1 < R),
      keys ⟨p, by lia⟩ = keys ⟨p + 1, by assumption⟩ ∧
      keys ⟨p, by lia⟩ = keys i := by
  suffices hforward : ∀ i j : Fin R, i < j → keys i = keys j →
      ∃ (p : ℕ) (hp : p + 1 < R),
        keys ⟨p, by lia⟩ = keys ⟨p + 1, by assumption⟩ ∧
        keys ⟨p, by lia⟩ = keys i by
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hforward i j hlt heq
    · obtain ⟨p, hp, he, hi⟩ := hforward j i hlt heq.symm
      exact ⟨p, hp, he, hi.trans heq.symm⟩
  intro i j hij heq
  have hnext : i.val + 1 < R := by have := j.isLt; exact Nat.lt_of_le_of_lt hij this
  refine ⟨i.val, hnext, ?_, rfl⟩
  apply le_antisymm
  · exact hs (by change i.val ≤ i.val + 1; lia)
  · exact (hs (show (⟨i.val + 1, hnext⟩ : Fin R) ≤ j from hij)).trans_eq heq.symm

/-- A sorter preserves a collision between distinct complete records, and makes
some such collision adjacent. The output pair has the original collision key. -/
theorem adjacent_collision (input output : Fin R → α) (key : α → β)
    (hperm : SequencePermutes output input)
    (hs : SequenceIncreasing (key ∘ output))
    (i j : Fin R) (hne : input i ≠ input j) (heq : key (input i) = key (input j)) :
    ∃ (p : ℕ) (hp : p + 1 < R),
      key (output ⟨p, by lia⟩) = key (output ⟨p + 1, by assumption⟩) ∧
      key (output ⟨p, by lia⟩) = key (input i) := by
  have hrev : SequencePermutes input output := List.Perm.symm hperm
  obtain ⟨a, ha⟩ := hrev.rangeContained i
  obtain ⟨b, hb⟩ := hrev.rangeContained j
  have hab : a ≠ b := by
    intro h
    exact hne (ha.trans (h ▸ hb.symm))
  have hkeys : (key ∘ output) a = (key ∘ output) b := by
    dsimp only [Function.comp_apply]
    rw [← ha, ← hb, heq]
  have hmono : Monotone (key ∘ output) := by
    intro a b hab
    rcases hab.eq_or_lt with rfl | hab
    · exact le_rfl
    · exact hs a b hab
  obtain ⟨p, hp, he, hi⟩ := adjacent_of_equal_keys (key ∘ output) hmono hab hkeys
  exact ⟨p, hp, he, hi.trans (congrArg key ha.symm)⟩

/-- Even with repeated complete records, a collision between different records
forces an adjacent pair of different records having that same key. -/
theorem adjacent_distinct_of_equal_keys (records : Fin R → α) (key : α → β)
    (hs : Monotone (key ∘ records)) (i j : Fin R) (hij : i < j)
    (hne : records i ≠ records j) (heq : key (records i) = key (records j)) :
    ∃ (p : ℕ) (hp : p + 1 < R),
      records ⟨p, by lia⟩ ≠ records ⟨p + 1, hp⟩ ∧
      key (records ⟨p, by lia⟩) = key (records ⟨p + 1, hp⟩) ∧
      key (records ⟨p, by lia⟩) = key (records i) := by
  classical
  let P := fun q => ∃ hq : q < R,
    i.val < q ∧ q ≤ j.val ∧ records ⟨q, hq⟩ ≠ records i
  have hex : ∃ q, P q := ⟨j.val, j.isLt, hij, le_rfl, hne.symm⟩
  let q := Nat.find hex
  obtain ⟨hq, hiq, hqj, hdiff⟩ := Nat.find_spec hex
  have hprev : q - 1 < R := by change Nat.find hex - 1 < R; lia
  have hip : i.val ≤ q - 1 := by change i.val ≤ Nat.find hex - 1; lia
  have hqp : q - 1 + 1 = q := by change Nat.find hex - 1 + 1 = Nat.find hex; lia
  have hsame : records ⟨q - 1, hprev⟩ = records i := by
    by_contra h
    have hlt : i.val < q - 1 := by
      have hne : i.val ≠ q - 1 := by
        intro he
        exact h (congrArg records (Fin.ext he.symm))
      lia
    exact Nat.find_min hex (show q - 1 < Nat.find hex by dsimp only [q]; lia)
      ⟨hprev, hlt, by dsimp only [q]; lia, h⟩
  have hqkey : key (records ⟨q, hq⟩) = key (records i) := by
    apply le_antisymm
    · exact (hs (show (⟨q, hq⟩ : Fin R) ≤ j from hqj)).trans_eq heq.symm
    · exact hs (show i ≤ (⟨q, hq⟩ : Fin R) from hiq.le)
  refine ⟨q - 1, by lia, ?_, ?_, congrArg key hsame⟩
  · simpa only [hqp, hsame] using hdiff.symm
  · simpa only [hqp, hsame] using hqkey.symm

/-- The collision detector may safely reject identical adjacent records. -/
theorem adjacent_distinct_collision (input output : Fin R → α) (key : α → β)
    (hperm : SequencePermutes output input) (hs : SequenceIncreasing (key ∘ output))
    (i j : Fin R) (hne : input i ≠ input j) (heq : key (input i) = key (input j)) :
    ∃ (p : ℕ) (hp : p + 1 < R),
      output ⟨p, by lia⟩ ≠ output ⟨p + 1, hp⟩ ∧
      key (output ⟨p, by lia⟩) = key (output ⟨p + 1, hp⟩) ∧
      key (output ⟨p, by lia⟩) = key (input i) := by
  have hrev : SequencePermutes input output := List.Perm.symm hperm
  obtain ⟨a, ha⟩ := hrev.rangeContained i
  obtain ⟨b, hb⟩ := hrev.rangeContained j
  have hdiff : output a ≠ output b := by simpa only [← ha, ← hb] using hne
  have hkeys : key (output a) = key (output b) := by simpa only [← ha, ← hb] using heq
  have hmono : Monotone (key ∘ output) := by
    intro a b hab
    exact hab.eq_or_lt.elim (fun h => h ▸ le_rfl) (hs a b)
  have hab : a ≠ b := fun h => hdiff (h ▸ rfl)
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · obtain ⟨p, hp, hdiff, hk, hi⟩ :=
      adjacent_distinct_of_equal_keys output key hmono a b hlt hdiff hkeys
    exact ⟨p, hp, hdiff, hk, hi.trans (congrArg key ha.symm)⟩
  · obtain ⟨p, hp, hdiff, hk, hi⟩ :=
      adjacent_distinct_of_equal_keys output key hmono b a hlt hdiff.symm hkeys.symm
    exact ⟨p, hp, hdiff, hk, hi.trans ((congrArg key hb.symm).trans heq.symm)⟩

end IteratedFunctions
