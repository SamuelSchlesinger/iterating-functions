/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ControlledMaps
public import Proofs.AffinePayload
public import Proofs.VariableTime

/-!
# Fast-forwarding a small nonlinear controller with an affine payload

Affine transformations are closed under composition, even when they are
singular or do not commute. All the exponential dependence is confined to
the number of controller bits. The controller must be autonomous.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {q p : ℕ}

/-- Exact gate budget from affine evaluation and controller selection. -/
def affineControllerBudget (q p : ℕ) : ℕ :=
  2 + 2 ^ q * (p * (5 * (p + 1) + 1) + 6 * q + 4 * p + 1)

/-- Every fixed power has size exponential only in the autonomous controller width. -/
theorem affine_controller_power (g : State q → State q)
    (a : State q → (State p →ᵃ[Bool] State p)) (T : ℕ) :
    ∃ c : Circuit Boolean.signature (q + p) (q + p),
      c.Computes Boolean.interpretation ((controlledBits g (fun u => a u))^[T]) ∧
      c.size ≤ affineControllerBudget q p := by
  let family : Set (State p → State p) := Set.range fun a : State p →ᵃ[Bool] State p => ⇑a
  apply controlled_family_power g (fun u => a u) family
    (show id ∈ family from ⟨AffineMap.id Bool (State p), rfl⟩)
    (fun _ ⟨f, hf⟩ _ ⟨h, hh⟩ => ?_) (fun u => ⟨a u, rfl⟩)
    (p * (5 * (p + 1) + 1)) (fun _ ⟨f, hf⟩ => ?_) T
  · exact ⟨f.comp h, by simp only [← hf, ← hh]; rfl⟩
  · exact hf ▸ affine_payload_circuit f

/-- The exact budget is `O(2^q * (q + p^2 + 1))`, including zero-width cases. -/
theorem affineControllerBudget_le (q p : ℕ) :
    affineControllerBudget q p ≤ 32 * 2 ^ q * (q + p ^ 2 + 1) := by
  have hp : p ≤ p ^ 2 := by nlinarith
  have hb : p * (5 * (p + 1) + 1) + 6 * q + 4 * p + 1 ≤
      16 * (q + p ^ 2 + 1) := by nlinarith
  have hpow : 1 ≤ 2 ^ q := Nat.one_le_pow q 2 (by decide)
  have := Nat.mul_le_mul_left (2 ^ q) hb
  unfold affineControllerBudget
  nlinarith

/-- Polynomially many controller states give a polynomial gate bound in the
total width, uniformly over all fixed exponents. -/
theorem affine_controller_polynomial (g : State q → State q)
    (a : State q → (State p →ᵃ[Bool] State p)) (K d : ℕ)
    (hcontroller : 2 ^ q ≤ K * (q + p + 1) ^ d) (T : ℕ) :
    ∃ c : Circuit Boolean.signature (q + p) (q + p),
      c.Computes Boolean.interpretation ((controlledBits g (fun u => a u))^[T]) ∧
      c.size ≤ 32 * K * (q + p + 1) ^ (d + 2) := by
  obtain ⟨c, hc, hs⟩ := affine_controller_power g a T
  refine ⟨c, hc, hs.trans ((affineControllerBudget_le q p).trans ?_)⟩
  have hwidth : q + p ^ 2 + 1 ≤ (q + p + 1) ^ 2 := by
    nlinarith only [Nat.zero_le q, Nat.zero_le p,
      Nat.zero_le (q * p), Nat.zero_le (q * q)]
  calc
    32 * 2 ^ q * (q + p ^ 2 + 1) ≤
        32 * (K * (q + p + 1) ^ d) * (q + p + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 32 hcontroller) hwidth
    _ = 32 * K * (q + p + 1) ^ (d + 2) := by rw [pow_add]; ring

/-- An input time uses the same fixed-power bound at each conditional binary stage. -/
theorem affine_controller_variable_time (g : State q → State q)
    (a : State q → (State p →ᵃ[Bool] State p)) (m : ℕ) :
    ∃ c : Circuit Boolean.signature ((q + p) + m) (q + p),
      c.Computes Boolean.interpretation (fun x =>
        (controlledBits g (fun u => a u))^[binaryValue (fun j => x (Fin.natAdd (q + p) j))]
          (fun i => x (Fin.castAdd m i))) ∧
      c.size ≤ m * (affineControllerBudget q p + 4 * (q + p)) :=
  binary_powering_circuit _ _ m (affine_controller_power g a)

end IteratedFunctions
