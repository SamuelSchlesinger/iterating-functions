/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Checkpoints
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Reconstructing a fixed iterate from a short prefix

The checkpoint payload is shifted backwards by the length of the simulated prefix.
The online correction therefore only iterates forwards. In the other branch a
repeated pair reduces the exponent modulo its positive repeat interval.
-/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} {f : α → α} {x : α} {i j d K T : ℕ}

/-- A checkpoint at time `d` permits forward-only correction of the shifted payload. -/
theorem shifted_payload (hd : d ≤ K) (hT : K ≤ T) :
    f^[K - d] (f^[T - K] (f^[d] x)) = f^[T] x := by
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
  congr 1
  lia

/-- Any repeated pair gives a valid period, whether or not it is the first pair. -/
theorem periodic_of_repeat (hij : i ≤ j) (heq : f^[i] x = f^[j] x) :
    Function.IsPeriodicPt f (j - i) (f^[i] x) := by
  change f^[j - i] (f^[i] x) = f^[i] x
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij, heq]

/-- Reduce the part of the exponent following the start of a repeated interval. -/
theorem repeat_reconstruction (hij : i ≤ j) (heq : f^[i] x = f^[j] x)
    (hT : i ≤ T) :
    f^[i + (T - i) % (j - i)] x = f^[T] x := by
  have hp := periodic_of_repeat hij heq
  rw [Nat.add_comm i, Function.iterate_add_apply, hp.iterate_mod_apply,
    ← Function.iterate_add_apply, Nat.sub_add_cancel hT]

/-- The reduced position lies in the stored prefix. -/
theorem repeat_position_lt (hij : i < j) : i + (T - i) % (j - i) < j := by
  have := Nat.mod_lt (T - i) (Nat.sub_pos_of_lt hij)
  lia

/-- A finite invariant set admits sparse, exponent-dependent payloads with a short
forward correction, or a short repeated interval giving the same answer. -/
theorem fixed_power_reconstruction (S : Finset α) (hS : ∀ x ∈ S, f x ∈ S)
    {L : ℕ} (hL : 0 < L) (T : ℕ) :
    ∃ H : Finset α, H ⊆ S ∧ H.card * L ≤ S.card ∧
      ∃ payload : α → α, ∀ x ∈ S,
        T < 2 * L ∨
        (∃ d < 2 * L, f^[d] x ∈ H ∧
          f^[2 * L - d] (payload (f^[d] x)) = f^[T] x) ∨
        (∃ i j, i < j ∧ j < L ∧ f^[i] x = f^[j] x ∧
          i + (T - i) % (j - i) < L ∧
          f^[i + (T - i) % (j - i)] x = f^[T] x) := by
  obtain ⟨H, hHS, hsize, hcover⟩ := exists_checkpoints f S hS hL
  refine ⟨H, hHS, hsize, f^[T - 2 * L], ?_⟩
  intro x hx
  by_cases hT : T < 2 * L
  · exact Or.inl hT
  · rcases hcover x hx with ⟨i, j, hij, hj, heq⟩ | ⟨d, hd, hh⟩
    · refine Or.inr (Or.inr ⟨i, j, hij, hj, heq, ?_, ?_⟩)
      · exact (repeat_position_lt hij).trans hj
      · exact repeat_reconstruction hij.le heq (by lia)
    · exact Or.inr (Or.inl ⟨d, hd, hh, shifted_payload hd.le (by lia)⟩)

/-- The image after a fixed burn-in is forward invariant. -/
theorem mapsTo_range_iterate (f : α → α) (d : ℕ) :
    Set.MapsTo f (Set.range f^[d]) (Set.range f^[d]) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (Function.iterate_succ_apply f d x).symm.trans
    (Function.iterate_succ_apply' f d x)⟩

end IteratedFunctions
