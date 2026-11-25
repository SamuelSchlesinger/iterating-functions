/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! # Element distinctness in one rotation of a record list -/

@[expose] public section

namespace IteratedFunctions.DistinctnessRotation

variable {α : Type*} [DecidableEq α] {q : ℕ}

/-- Move the first record to the end and count it if it occurs nowhere else. -/
def step : List α × ZMod q → List α × ZMod q
  | ([], z) => ([], z)
  | (a :: xs, z) => (xs ++ [a], if a ∈ xs then z else z + 1)

theorem step_bijective : Function.Bijective (step (α := α) (q := q)) := by
  constructor
  · rintro ⟨xs, z⟩ ⟨ys, t⟩ eq
    cases xs with
    | nil =>
      cases ys with
      | nil => exact eq
      | cons b ys => simp [step] at eq
    | cons a xs =>
      cases ys with
      | nil => simp [step] at eq
      | cons b ys =>
        obtain ⟨rfl, rfl⟩ := List.append_singleton_inj.mp (congrArg Prod.fst eq)
        by_cases ha : a ∈ xs <;> simpa [step, ha] using eq
  · rintro ⟨xs, z⟩
    rcases xs.eq_nil_or_concat' with rfl | ⟨ys, a, rfl⟩
    · exact ⟨([], z), rfl⟩
    · refine ⟨(a :: ys, if a ∈ ys then z else z - 1), ?_⟩
      by_cases ha : a ∈ ys <;> simp [step, ha]

/-- Number of positions whose record occurs exactly once in the list. -/
def singletons (xs : List α) : ℕ := xs.countP fun a => xs.count a == 1

theorem singletons_eq_length (xs : List α) : singletons xs = xs.length ↔ xs.Nodup := by
  simp [singletons, List.countP_eq_length, List.nodup_iff_count_of_mem]

private theorem rotate_prefix (original todo seen : List α) (hp : (todo ++ seen).Perm original)
    (z : ZMod q) :
    step^[todo.length] (todo ++ seen, z) =
      (seen ++ todo, z + (todo.countP fun a => original.count a == 1 : ℕ)) := by
  induction todo generalizing seen z with
  | nil => simp
  | cons a todo ih =>
    have next : (todo ++ (seen ++ [a])).Perm original := by
      rw [← List.append_assoc]
      exact (List.perm_append_singleton a _).trans hp
    have count := hp.count_eq a
    simp only [List.cons_append, List.count_cons_self] at count
    rw [List.length_cons, Function.iterate_succ_apply, List.cons_append, step, List.append_assoc,
      ih _ next]
    by_cases ha : a ∈ todo ++ seen
    · have h : original.count a ≠ 1 := by
        have := List.count_pos_iff.mpr ha
        lia
      simp [ha, h]
    · have h : original.count a = 1 := by rw [← count, List.count_eq_zero_of_not_mem ha]
      simp [ha, h, add_assoc, add_comm]

/-- A complete lap restores the list and adds its singleton count to any initial counter. -/
theorem lap (xs : List α) (z : ZMod q) :
    step^[xs.length] (xs, z) = (xs, z + (singletons xs : ZMod q)) := by
  simpa [singletons] using rotate_prefix xs xs [] (by simp) z

/-- At length `2^h`, bit `h` of the counter after one lap decides distinctness. -/
theorem highBit_iff_nodup (xs : List α) (h : ℕ) (hlen : xs.length = 2 ^ h) :
    ((step^[2 ^ h] (xs, (0 : ZMod (2 ^ (h + 1))))).2.val).testBit h = true ↔ xs.Nodup := by
  have bound : singletons xs ≤ 2 ^ h := hlen ▸ List.countP_le_length
  have fits : singletons xs < 2 ^ (h + 1) :=
    bound.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self h))
  rw [← hlen, lap]
  simp only [zero_add, ZMod.val_natCast_of_lt fits, ← singletons_eq_length, hlen]
  rcases lt_or_eq_of_le bound with lt | eq
  · simp [Nat.testBit_lt_two_pow lt, lt.ne]
  · simp [eq]

/-- The least period is exactly twice the list length precisely for a distinct list. -/
theorem minimalPeriod_iff_nodup (xs : List α) (h : ℕ) (hlen : xs.length = 2 ^ h)
    (z : ZMod (2 ^ (h + 1))) :
    Function.minimalPeriod step (xs, z) = 2 ^ (h + 1) ↔ xs.Nodup := by
  have bound : singletons xs ≤ 2 ^ h := hlen ▸ List.countP_le_length
  have grow : 2 ^ h < 2 ^ (h + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self h)
  have one : Function.IsPeriodicPt step (2 ^ h) (xs, z) ↔ singletons xs = 0 := by
    change step^[2 ^ h] (xs, z) = (xs, z) ↔ _
    rw [← hlen, lap]
    simp [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt (bound.trans_lt grow)]
  have two : Function.IsPeriodicPt step (2 ^ (h + 1)) (xs, z) ↔ 2 ^ h ∣ singletons xs := by
    change step^[2 ^ (h + 1)] (xs, z) = (xs, z) ↔ _
    have laps := congrArg (fun t => step^[t] (xs, z))
      (show 2 ^ (h + 1) = xs.length + xs.length by rw [hlen, pow_succ, Nat.mul_two])
    rw [laps, Function.iterate_add_apply, lap, lap]
    simp only [Prod.mk.injEq, true_and, add_assoc, add_eq_left, ← Nat.cast_add,
      ZMod.natCast_eq_zero_iff]
    rw [← two_mul, pow_succ', Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)]
  rw [← singletons_eq_length, hlen]
  constructor
  · intro hp
    have returns := Function.isPeriodicPt_minimalPeriod step (xs, z)
    rw [hp] at returns
    have moves : ¬ Function.IsPeriodicPt step (2 ^ h) (xs, z) := by
      rw [Function.isPeriodicPt_iff_minimalPeriod_dvd, hp]
      exact Nat.not_dvd_of_pos_of_lt (Nat.two_pow_pos h) grow
    exact bound.antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (mt one.mpr moves)) (two.mp returns))
  · intro eq
    apply Function.minimalPeriod_eq_prime_pow
    · rw [one, eq]
      exact (Nat.two_pow_pos h).ne'
    · rw [two, eq]

end IteratedFunctions.DistinctnessRotation
