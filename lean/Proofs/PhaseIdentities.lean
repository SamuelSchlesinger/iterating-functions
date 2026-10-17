/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CycleLabels

/-!
# Canonical hitting times along trajectories

For a map on a finite linearly ordered type, `canonicalTime f x` is the first time at which the
trajectory of `x` visits the least state of its eventual cycle.  Off the cycles, one step lowers
it by one.  A power `f^[T] x` with `T` at least the transient depth determines it modulo the
cycle length, and nothing else.  These are the phase identities (P1) and (P2) of the black-box
section of the paper.
-/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} [Finite α] [LinearOrder α] (f : α → α)

/-- (P1) One step from a transient state lowers the canonical hitting time by one. -/
theorem canonicalTime_apply (x : α) (hx : x ∉ Function.periodicPts f) :
    canonicalTime f (f x) + 1 = canonicalTime f x := by
  have hc : canonicalCycle f (f x) = canonicalCycle f x := by
    simpa using canonicalCycle_iterate f x 1
  have hpos : 0 < canonicalTime f x := by
    rcases Nat.eq_zero_or_pos (canonicalTime f x) with h | h
    · have hs := canonicalTime_spec f x
      rw [h, Function.iterate_zero_apply] at hs
      exact absurd (hs ▸ canonicalCycle_periodic f x) hx
    · exact h
  have hle1 : canonicalTime f x ≤ canonicalTime f (f x) + 1 := by
    have h : f^[canonicalTime f (f x) + 1] x = canonicalCycle f x := by
      rw [Function.iterate_succ_apply, canonicalTime_spec, hc]
    exact Nat.find_min' (canonicalCycle_reachable f x) h
  have hle2 : canonicalTime f (f x) ≤ canonicalTime f x - 1 := by
    have h : f^[canonicalTime f x - 1] (f x) = canonicalCycle f (f x) := by
      rw [hc, ← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
      exact canonicalTime_spec f x
    exact Nat.find_min' (canonicalCycle_reachable f (f x)) h
  lia

/-- (P2) Past the transient, `f^[T] x` is the state `a` steps after the least cyclic state
exactly when `a` plus the canonical hitting time is congruent to `T` modulo the cycle length. -/
theorem iterate_eq_canonical_iff (x : α) {T : ℕ} (hT : transientDepth f x ≤ T) (a : ℕ) :
    f^[T] x = f^[a] (canonicalCycle f x) ↔
      a + canonicalTime f x ≡ T [MOD cycleLength f x] := by
  set κ := canonicalTime f x with hκ
  set ℓ := cycleLength f x with hℓdef
  set c := canonicalCycle f x with hcdef
  have hcκ : f^[κ] x = c := canonicalTime_spec f x
  have hcper : Function.minimalPeriod f c = ℓ := by
    have h := minimalPeriod_at_periodic_iterate f x (t := κ)
      (by rw [hcκ]; exact canonicalCycle_periodic f x)
    rwa [hcκ] at h
  have hℓ : 0 < ℓ := cycleLength_pos f x
  have hTper : Function.IsPeriodicPt f ℓ (f^[T] x) := by
    have h := (cycleLength_periodic f x).apply_iterate (T - transientDepth f x)
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hT] at h
  have hκle : κ ≤ ℓ * κ + T := (Nat.le_mul_of_pos_left κ hℓ).trans (Nat.le_add_right _ _)
  have hrep : f^[T] x = f^[ℓ * κ + T - κ] c := by
    rw [← hcκ, ← Function.iterate_add_apply, Nat.sub_add_cancel hκle,
      Function.iterate_add_apply]
    exact ((hTper.mul_const κ).eq).symm
  have hcp : Function.IsPeriodicPt f ℓ c := hcper ▸ Function.isPeriodicPt_minimalPeriod f c
  have hiff : ∀ i j : ℕ, f^[i] c = f^[j] c ↔ i ≡ j [MOD ℓ] := by
    intro i j
    rw [← hcp.iterate_mod_apply i, ← hcp.iterate_mod_apply j]
    constructor
    · intro he
      exact Function.iterate_injOn_Iio_minimalPeriod
        (show i % ℓ < Function.minimalPeriod f c by rw [hcper]; exact Nat.mod_lt _ hℓ)
        (show j % ℓ < Function.minimalPeriod f c by rw [hcper]; exact Nat.mod_lt _ hℓ) he
    · intro he
      exact congrArg (fun k => f^[k] c) he
  have hshift : ℓ * κ + T ≡ T [MOD ℓ] := by
    simp [Nat.ModEq, Nat.add_mod]
  rw [hrep, hiff]
  constructor
  · intro h
    have h' := h.add_right κ
    rw [Nat.sub_add_cancel hκle] at h'
    exact (h'.symm.trans hshift)
  · intro h
    apply Nat.ModEq.add_right_cancel' κ
    rw [Nat.sub_add_cancel hκle]
    exact (hshift.trans h.symm)

end IteratedFunctions
