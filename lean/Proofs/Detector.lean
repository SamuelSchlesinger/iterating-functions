/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Records

/-!
# Detecting a useful collision in one sorted array

Both checkpoint hits and repetitions are collisions between distinct complete
records with equal state keys. Padding and identical-record collisions are
excluded. A single sort and a linear selection scan suffice.
-/

@[expose] public section

namespace IteratedFunctions.Record

open Algebraic.MassProduction.Sorting
open Algebraic.MassProduction.Sorting.Semantics

variable {n w M R : ℕ}

/-- Row-major packing of complete records. -/
def pack (records : Fin R → Record n w) : Fin (R * width n w) → Bool :=
  fun bit => let p := (finProdFinEquiv (m := R) (n := width n w)).symm bit
    encode (records p.1) p.2

theorem flatRecords_pack (d : ℕ) (records : Fin (networkRecords d) → Record n w)
    (j : Fin (networkRecords d)) : flatRecords (pack records) j = encode (records j) := by
  funext bit
  simp [flatRecords, networkRecord, pack]

/-- Decode the records after sorting by padding flag and state. -/
noncomputable def sorted (d : ℕ) (records : Fin (networkRecords d) → Record n w) :
    Fin (networkRecords d) → Record n w :=
  fun j => decode (flatRecords
    (bitonicSortBits (keyFits (n := n) (w := w)) d true (pack records)) j)

theorem sorted_perm (d : ℕ) (records : Fin (networkRecords d) → Record n w) :
    SequencePermutes (sorted d records) records := by
  have h := (bitonicSortBits_recordsPermute
    (keyFits (n := n) (w := w)) d true (pack records)).map decode
  unfold sorted
  simpa only [Function.comp_def, flatRecords_pack, decode_encode] using h

theorem sorted_keys (d : ℕ) (records : Fin (networkRecords d) → Record n w) :
    SequenceIncreasing (key ∘ sorted d records) := by
  have h := bitonicSortBits_keysSorted (keyFits (n := n) (w := w)) d true (pack records)
  simpa only [FlatKeysSorted, SequenceSorted, ↓reduceIte, sorted, Function.comp_def,
    flat_key_decode] using h

/-- Two adjacent physical records. -/
def adjacentPair (records : Fin R → Record n w) (j : Fin (R - 1)) : Record n w × Record n w :=
  (records ⟨j.val, by have := j.isLt; lia⟩, records ⟨j.val + 1, by have := j.isLt; lia⟩)

/-- The complete adjacent-pair detector, with a total fallback value. -/
def detect (records : Fin R → Record n w) : Record n w × Record n w :=
  chooseRecord (fun j => collision (adjacentPair records j).1 (adjacentPair records j).2)
    (adjacentPair records) (pad, pad) (R - 1)

/-- The initial array contains a collision witnessing either kind of checkpoint coverage. -/
theorem initial_collision (f : State n → State n) (T K : ℕ) (checkpoints : Fin M → State n)
    (x : State n) (hR : M + (K + 1) ≤ R) (hK : K < 2 ^ w)
    (hcover : (∃ d ≤ K, ∃ h : Fin M, f^[d] x = checkpoints h) ∨
      ∃ i j, i < j ∧ j ≤ K ∧ f^[i] x = f^[j] x) :
    ∃ a b : Fin R,
      initial (w := w) f T K checkpoints x a ≠ initial (w := w) f T K checkpoints x b ∧
      (initial (w := w) f T K checkpoints x a).key = (initial (w := w) f T K checkpoints x b).key ∧
      (initial (w := w) f T K checkpoints x a).padding = false := by
  rcases hcover with ⟨d, hd, h, heq⟩ | ⟨i, j, hij, hj, heq⟩
  · refine ⟨⟨h.val, by have := h.isLt; lia⟩, ⟨M + d, by lia⟩, ?_, ?_, ?_⟩
    all_goals rw [initial_stored f T K checkpoints x hR h]
    · rw [initial_query f T K checkpoints x hR ⟨d, by lia⟩]
      intro hbad
      have := congrArg checkpoint hbad
      simp [stored, query] at this
    · rw [initial_query f T K checkpoints x hR ⟨d, by lia⟩]
      simp [key, stored, query, heq]
    · rfl
  · have hi : i ≤ K := by lia
    refine ⟨⟨M + i, by lia⟩, ⟨M + j, by lia⟩, ?_, ?_, ?_⟩
    all_goals rw [initial_query f T K checkpoints x hR ⟨i, by lia⟩]
    · rw [initial_query f T K checkpoints x hR ⟨j, by lia⟩]
      intro hbad
      have hidx := congrArg (fun r : Record n w => r.index.toNat) hbad
      simp only [query, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hi.trans_lt hK),
        Nat.mod_eq_of_lt (hj.trans_lt hK)] at hidx
      lia
    · rw [initial_query f T K checkpoints x hR ⟨j, by lia⟩]
      simp [key, query, heq]
    · rfl

/-- Sorting turns the known initial collision into a successful detector flag. -/
theorem sorted_has_collision (d : ℕ) (records : Fin (networkRecords d) → Record n w)
    (hex : ∃ a b, records a ≠ records b ∧ (records a).key = (records b).key ∧
      (records a).padding = false) :
    ∃ j : Fin (networkRecords d - 1),
      collision (adjacentPair (sorted d records) j).1
        (adjacentPair (sorted d records) j).2 = true := by
  obtain ⟨a, b, hne, heq, hpad⟩ := hex
  obtain ⟨p, hp, hdiff, hkey, horig⟩ := adjacent_distinct_collision records (sorted d records)
    key (sorted_perm d records) (sorted_keys d records) a b hne heq
  refine ⟨⟨p, by lia⟩, ?_⟩
  apply (collision_iff _ _).mpr
  obtain ⟨hpad', hstate⟩ := (key_eq_iff _ _).mp hkey
  have hfirst := (key_eq_iff _ _).mp horig
  exact ⟨hfirst.1.trans hpad, hpad'.symm.trans (hfirst.1.trans hpad), hstate, hdiff⟩

/-- The pair selected by the detector carries a correct reconstruction witness. -/
theorem detect_sorted_witness (f : State n → State n) (T K d : ℕ)
    (checkpoints : Fin M → State n) (x : State n)
    (hR : M + (K + 1) ≤ networkRecords d) (hK : K < 2 ^ w)
    (hcover : (∃ t ≤ K, ∃ h : Fin M, f^[t] x = checkpoints h) ∨
      ∃ i j, i < j ∧ j ≤ K ∧ f^[i] x = f^[j] x) :
    let pair := detect (sorted d (initial (w := w) f T K checkpoints x))
    Witness f T K checkpoints x pair.1 pair.2 := by
  let records := initial (R := networkRecords d) (w := w) f T K checkpoints x
  have hc := sorted_has_collision d records
    (initial_collision f T K checkpoints x hR hK hcover)
  obtain ⟨j, _, hj, hchosen⟩ := chooseRecord_spec
    (fun j => collision (adjacentPair (sorted d records) j).1
      (adjacentPair (sorted d records) j).2)
    (adjacentPair (sorted d records)) (pad, pad) (networkRecords d - 1)
    (by obtain ⟨j, hj⟩ := hc; exact ⟨j, j.isLt, hj⟩)
  change Witness f T K checkpoints x (detect (sorted d records)).1 (detect (sorted d records)).2
  change detect (sorted d records) = _ at hchosen
  rw [hchosen]
  apply collision_witness f T K checkpoints x _ _ ?_ ?_ hj
  · obtain ⟨source, heq⟩ := (sorted_perm d records).rangeContained
      ⟨j.val, by have := j.isLt; lia⟩
    change Valid f T K checkpoints x ((sorted d records) _)
    rw [heq]
    exact initial_cases f T K checkpoints x source
  · obtain ⟨source, heq⟩ := (sorted_perm d records).rangeContained
      ⟨j.val + 1, by have := j.isLt; lia⟩
    change Valid f T K checkpoints x ((sorted d records) _)
    rw [heq]
    exact initial_cases f T K checkpoints x source

end IteratedFunctions.Record
