/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.OrbitStructure

/-! # Cycle-spectrum reduction of fixed powers

Every fixed power of a map on a finite state type is determined by the
eventual cycle length of its argument: past the state-space cardinality,
an exponent may be reduced modulo the cycle length.  The cycle length is
recovered from the finite set of cycle lengths by a divisibility test, and
a permutation is inverted by the power one below the cycle length.
-/

@[expose] public section

namespace IteratedFunctions

universe u

section Finite

variable {α : Type u} [Finite α] (f : α → α)

/-- Past the transient, adding whole cycles does not change the state. -/
theorem iterate_add_cycleLength_mul (x : α) {a : ℕ} (ha : transientDepth f x ≤ a) (q : ℕ) :
    f^[a + cycleLength f x * q] x = f^[a] x := by
  have hp := (cycleLength_periodic f x).mul_const q
  calc f^[a + cycleLength f x * q] x
      = f^[a - transientDepth f x]
          (f^[cycleLength f x * q] (f^[transientDepth f x] x)) := by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        congr 1
        lia
    _ = f^[a - transientDepth f x] (f^[transientDepth f x] x) := by rw [hp.eq]
    _ = f^[a] x := by
        rw [← Function.iterate_add_apply]
        congr 1
        lia

end Finite

section Fintype

variable {α : Type u} [Fintype α] (f : α → α)

theorem cycleLength_le_card (x : α) : cycleLength f x ≤ Fintype.card α :=
  (Nat.le_add_left _ _).trans (depth_add_cycleLength_le_card f x)

/-- The spectrum reduction: every exponent at least the cardinality `N` can be
replaced by `N + (T - N) mod ℓ(x)`. -/
theorem iterate_eq_card_add_mod (x : α) {T : ℕ} (hT : Fintype.card α ≤ T) :
    f^[T] x = f^[Fintype.card α + (T - Fintype.card α) % cycleLength f x] x := by
  have hd := (transientDepth_lt_card f x).le
  have h := iterate_add_cycleLength_mul f x
    (a := Fintype.card α + (T - Fintype.card α) % cycleLength f x) (by lia)
    ((T - Fintype.card α) / cycleLength f x)
  rw [← h]
  congr 1
  have := Nat.mod_add_div (T - Fintype.card α) (cycleLength f x)
  lia

/-- The reduced exponent is below `2N`, so `n + 1` time bits suffice when `N = 2^n`. -/
theorem card_add_mod_lt (x : α) (T : ℕ) :
    Fintype.card α + T % cycleLength f x < 2 * Fintype.card α := by
  have := Nat.mod_lt T (cycleLength_pos f x)
  have := cycleLength_le_card f x
  lia

/-- After `N` steps every state lies on its cycle, whose minimal period is `ℓ(x)`. -/
theorem minimalPeriod_iterate_card (x : α) :
    Function.minimalPeriod f (f^[Fintype.card α] x) = cycleLength f x := by
  have hd := (transientDepth_lt_card f x).le
  have h : f^[Fintype.card α] x =
      f^[Fintype.card α - transientDepth f x] (f^[transientDepth f x] x) := by
    rw [← Function.iterate_add_apply]
    congr 1
    lia
  rw [h, Function.minimalPeriod_apply_iterate (transientDepth_spec f x)]
  rfl

/-- The cycle-length test for maps: `F^(N+ℓ)(x) = F^N(x)` exactly when `ℓ(x)` divides `ℓ`. -/
theorem cycle_test_iff (x : α) (ℓ : ℕ) :
    f^[Fintype.card α + ℓ] x = f^[Fintype.card α] x ↔ cycleLength f x ∣ ℓ := by
  rw [show Fintype.card α + ℓ = ℓ + Fintype.card α by lia, Function.iterate_add_apply,
    ← minimalPeriod_iterate_card f x, ← Function.isPeriodicPt_iff_minimalPeriod_dvd]
  rfl

/-- The distinct cycle lengths of `f`. -/
noncomputable def cycleSpectrum : Finset ℕ :=
  Finset.univ.image (cycleLength f)

theorem cycleLength_mem_cycleSpectrum (x : α) : cycleLength f x ∈ cycleSpectrum f :=
  Finset.mem_image_of_mem _ (Finset.mem_univ x)

theorem pos_of_mem_cycleSpectrum {ℓ : ℕ} (hℓ : ℓ ∈ cycleSpectrum f) : 0 < ℓ := by
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hℓ
  exact cycleLength_pos f y

/-- The spectrum test: among any set of positive candidates containing `ℓ(x)`,
the cycle length is the least one passing the divisibility test. -/
theorem spectrum_test (S : Finset ℕ) (x : α) (hS : cycleLength f x ∈ S)
    (hpos : ∀ ℓ ∈ S, 0 < ℓ) :
    IsLeast {ℓ | ℓ ∈ S ∧ f^[Fintype.card α + ℓ] x = f^[Fintype.card α] x}
      (cycleLength f x) :=
  ⟨⟨hS, (cycle_test_iff f x _).mpr dvd_rfl⟩,
    fun ℓ ⟨hℓ, he⟩ => Nat.le_of_dvd (hpos ℓ hℓ) ((cycle_test_iff f x ℓ).mp he)⟩

theorem cycleSpectrum_test (x : α) :
    IsLeast {ℓ | ℓ ∈ cycleSpectrum f ∧ f^[Fintype.card α + ℓ] x = f^[Fintype.card α] x}
      (cycleLength f x) :=
  spectrum_test f _ x (cycleLength_mem_cycleSpectrum f x)
    (fun _ h => pos_of_mem_cycleSpectrum f h)

end Fintype

/-! ## Permutations -/

section Perm

variable {α : Type u} [Finite α] (f : α → α)

theorem transientDepth_eq_zero_of_injective (hf : Function.Injective f) (x : α) :
    transientDepth f x = 0 :=
  (transientDepth_eq_zero_iff f x).mpr (hf.mem_periodicPts x)

theorem cycleLength_eq_minimalPeriod_of_injective (hf : Function.Injective f) (x : α) :
    cycleLength f x = Function.minimalPeriod f x := by
  simp [cycleLength, transientDepth_eq_zero_of_injective f hf]

/-- For an injective map, `F^ℓ(x) = x` exactly when `ℓ(x)` divides `ℓ`. -/
theorem injective_cycle_test_iff (hf : Function.Injective f) (x : α) (ℓ : ℕ) :
    f^[ℓ] x = x ↔ cycleLength f x ∣ ℓ := by
  rw [cycleLength_eq_minimalPeriod_of_injective f hf,
    ← Function.isPeriodicPt_iff_minimalPeriod_dvd]
  rfl

/-- The spectrum test for permutations, without the shift by `N`. -/
theorem injective_spectrum_test (hf : Function.Injective f) (S : Finset ℕ) (x : α)
    (hS : cycleLength f x ∈ S) (hpos : ∀ ℓ ∈ S, 0 < ℓ) :
    IsLeast {ℓ | ℓ ∈ S ∧ f^[ℓ] x = x} (cycleLength f x) :=
  ⟨⟨hS, (injective_cycle_test_iff f hf x _).mpr dvd_rfl⟩,
    fun ℓ ⟨hℓ, he⟩ =>
      Nat.le_of_dvd (hpos ℓ hℓ) ((injective_cycle_test_iff f hf x ℓ).mp he)⟩

/-- A permutation is inverted by the power one below the cycle length of the argument. -/
theorem perm_symm_eq_iterate (σ : Equiv.Perm α) (x : α) :
    σ.symm x = (⇑σ)^[cycleLength σ x - 1] x := by
  have hpos := cycleLength_pos σ x
  have h : (⇑σ)^[cycleLength σ x] x = x :=
    (injective_cycle_test_iff σ σ.injective x _).mpr dvd_rfl
  apply σ.injective
  rw [Equiv.apply_symm_apply, ← Function.iterate_succ_apply' (⇑σ),
    Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne'), h]

end Perm

end IteratedFunctions
