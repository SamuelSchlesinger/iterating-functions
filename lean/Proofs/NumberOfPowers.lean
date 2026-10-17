/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.OrbitStructure
public import Proofs.Reconstruction
public import Proofs.CircuitCounting
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat

/-!
# The exact number of distinct powers of a finite map

For `f : α → α` on a finite type, let `μ` be the longest transient depth and `λ` the least
common multiple of the cycle lengths.  Two powers `f^[a]` and `f^[b]` with `a < b` agree
exactly when `μ ≤ a` and `λ ∣ b - a`, so `f` has exactly `μ + λ` distinct powers.  A family of
powers larger than the ordered-syntax budget then contains a power without small circuits.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

universe u

section Pointwise

variable {α : Type u} [Finite α] (f : α → α)

/-- Past the transient, every state has the cycle length of its eventual cycle as exact period. -/
theorem minimalPeriod_iterate_eq_cycleLength (x : α) {a : ℕ} (ha : transientDepth f x ≤ a) :
    Function.minimalPeriod f (f^[a] x) = cycleLength f x := by
  have h := Function.minimalPeriod_apply_iterate (transientDepth_spec f x)
    (a - transientDepth f x)
  rwa [← Function.iterate_add_apply, Nat.sub_add_cancel ha] at h

/-- Pointwise form: two times give the same state iff the first is past the transient and
their difference is a multiple of the cycle length. -/
theorem iterate_apply_eq_iff (x : α) {a b : ℕ} (hab : a < b) :
    f^[a] x = f^[b] x ↔ transientDepth f x ≤ a ∧ cycleLength f x ∣ b - a := by
  constructor
  · intro he
    have hper := periodic_of_repeat hab.le he
    have ha := (periodic_iterate_iff f x a).mp
      (Function.mk_mem_periodicPts (by lia : 0 < b - a) hper)
    refine ⟨ha, ?_⟩
    rw [← minimalPeriod_iterate_eq_cycleLength f x ha]
    exact hper.minimalPeriod_dvd
  · rintro ⟨ha, hd⟩
    have hp : Function.IsPeriodicPt f (b - a) (f^[a] x) := by
      rw [Function.isPeriodicPt_iff_minimalPeriod_dvd,
        minimalPeriod_iterate_eq_cycleLength f x ha]
      exact hd
    calc
      f^[a] x = f^[b - a] (f^[a] x) := hp.eq.symm
      _ = f^[b] x := by rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le]

end Pointwise

variable {α : Type u} [Fintype α] (f : α → α)

/-- The longest transient depth `μ(f)` over all states. -/
noncomputable def maxTransientDepth : ℕ := Finset.univ.sup (transientDepth f)

/-- The least common multiple `λ(f)` of all cycle lengths. -/
noncomputable def cyclePeriod : ℕ := Finset.univ.lcm (cycleLength f)

theorem cyclePeriod_pos : 0 < cyclePeriod f := by
  apply Nat.pos_of_ne_zero
  intro h
  obtain ⟨x, _, hx⟩ := Finset.lcm_eq_zero_iff.mp h
  exact (cycleLength_pos f x).ne' hx

/-- Two powers `f^[a]` and `f^[b]` with `a < b` coincide iff `μ ≤ a` and `λ ∣ b - a`. -/
theorem iterate_eq_iterate_iff {a b : ℕ} (hab : a < b) :
    f^[a] = f^[b] ↔ maxTransientDepth f ≤ a ∧ cyclePeriod f ∣ b - a := by
  rw [funext_iff]
  simp only [iterate_apply_eq_iff f _ hab, maxTransientDepth, cyclePeriod,
    Finset.sup_le_iff, Finset.lcm_dvd_iff, Finset.mem_univ, true_implies]
  exact forall_and

/-- Every power past `μ` reduces to one of the first `μ + λ` powers. -/
theorem iterate_eq_reduced {T : ℕ} (hT : maxTransientDepth f ≤ T) :
    f^[T] = f^[maxTransientDepth f + (T - maxTransientDepth f) % cyclePeriod f] := by
  set μ := maxTransientDepth f
  set p := cyclePeriod f
  have hdiv := Nat.div_add_mod (T - μ) p
  have hle : μ + (T - μ) % p ≤ T := by
    have := Nat.mod_le (T - μ) p
    lia
  rcases hle.lt_or_eq with hlt | heq
  · refine ((iterate_eq_iterate_iff f hlt).mpr ⟨by lia, ?_⟩).symm
    exact ⟨(T - μ) / p, by lia⟩
  · rw [heq]

/-- The powers `f^[0], …, f^[μ + λ - 1]` are pairwise distinct. -/
theorem iterate_injective_below :
    Function.Injective
      (fun i : Fin (maxTransientDepth f + cyclePeriod f) => f^[i.val]) := by
  intro i j h
  by_contra hne
  have key (i j : Fin (maxTransientDepth f + cyclePeriod f)) (hij : i.val < j.val)
      (h : f^[i.val] = f^[j.val]) : False := by
    obtain ⟨hμ, hd⟩ := (iterate_eq_iterate_iff f hij).mp h
    have := Nat.le_of_dvd (by lia) hd
    have := j.isLt
    lia
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hij | hji
  · exact key i j hij h
  · exact key j i hji h.symm

/-- **The number of powers.**  A map on a finite type has exactly `μ + λ` distinct powers. -/
theorem card_range_iterate :
    Nat.card (Set.range fun T : ℕ => f^[T]) = maxTransientDepth f + cyclePeriod f := by
  have hrange : Set.range (fun T : ℕ => f^[T]) =
      Set.range (fun i : Fin (maxTransientDepth f + cyclePeriod f) => f^[i.val]) := by
    ext g
    constructor
    · rintro ⟨T, rfl⟩
      by_cases hT : T < maxTransientDepth f + cyclePeriod f
      · exact ⟨⟨T, hT⟩, rfl⟩
      · have hm := Nat.mod_lt (T - maxTransientDepth f) (cyclePeriod_pos f)
        exact ⟨⟨_, by lia⟩, (iterate_eq_reduced f (by lia)).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, rfl⟩
  rw [hrange, Nat.card_range_of_injective (iterate_injective_below f)]
  simp

/-- **Counting step.**  If the ordered-syntax budget for `q` gates is smaller than the number
of distinct powers, some power below `μ + λ` has no circuit with at most `q` gates. -/
theorem exists_hard_power_of_budget_lt {n : ℕ} (g : State n → State n) (q : ℕ)
    (large : Boolean.signature.orderedBudget n n q <
      maxTransientDepth g + cyclePeriod g) :
    ∃ T < maxTransientDepth g + cyclePeriod g,
      ∀ out : Circuit Boolean.signature n n,
        out.Computes Boolean.interpretation g^[T] → q < out.size := by
  classical
  let family := Finset.univ.image
    (fun i : Fin (maxTransientDepth g + cyclePeriod g) => g^[i.val])
  have hcard : family.card = maxTransientDepth g + cyclePeriod g := by
    rw [Finset.card_image_of_injective _ (iterate_injective_below g)]
    simp
  obtain ⟨target, ht, hh⟩ := Circuit.exists_hard_in_family (G := q)
    Boolean.interpretation family (by rw [hcard]; exact large)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  refine ⟨i.val, i.isLt, fun out hcomp => ?_⟩
  by_contra hn
  exact hh out (by lia) hcomp

/-- An explicit exponent form of the counting step, via `boolean_orderedBudget_le_pow`. -/
theorem exists_hard_power {n : ℕ} (g : State n → State n) (q h : ℕ)
    (hw : n + q + 1 ≤ 2 ^ h)
    (large : 2 ^ (3 * q + h * (2 * q + n + 1)) <
      maxTransientDepth g + cyclePeriod g) :
    ∃ T < maxTransientDepth g + cyclePeriod g,
      ∀ out : Circuit Boolean.signature n n,
        out.Computes Boolean.interpretation g^[T] → q < out.size :=
  exists_hard_power_of_budget_lt g q
    ((boolean_orderedBudget_le_pow n n q h hw).trans_lt large)

end IteratedFunctions
