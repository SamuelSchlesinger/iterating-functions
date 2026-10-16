/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.FixedPower

/-!
# Encoded state spaces and image-sensitive iteration

The state type can inhabit any universe. The circuit still operates on a
specified Boolean encoding, and the transition circuit must realize that
encoding on the invariant set. This preserves the Boolean cost model.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

universe u
variable {α : Type u} {n : ℕ}

theorem iterate_encoded (f : α → α) (S : Finset α) (e : α → State n)
    (c : Circuit Boolean.signature n n) (hS : ∀ x ∈ S, f x ∈ S)
    (hstep : ∀ x ∈ S, c.eval Boolean.interpretation (e x) = e (f x))
    {x : α} (hx : x ∈ S) (T : ℕ) :
    (c.eval Boolean.interpretation)^[T] (e x) = e (f^[T] x) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    apply hstep
    have hm : ∀ t, f^[t] x ∈ S := by
      intro t
      induction t with
      | zero => exact hx
      | succ t ih => simpa only [Function.iterate_succ_apply'] using hS _ ih
    exact hm T

/-- Arbitrary-universe state spaces, with all computation charged on their bit encoding. -/
theorem fixed_power_encoded (f : α → α) (S : Finset α) (e : α → State n)
    (he : Set.InjOn e S) (c : Circuit Boolean.signature n n)
    (hS : ∀ x ∈ S, f x ∈ S)
    (hstep : ∀ x ∈ S, c.eval Boolean.interpretation (e x) = e (f x))
    (T L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n n,
      (∀ x ∈ S, out.eval Boolean.interpretation (e x) = e (f^[T] x)) ∧
      out.size ≤ 40000 * powerBudget n c.size S.card L := by
  classical
  have himage : ∀ y ∈ S.image e, c.eval Boolean.interpretation y ∈ S.image e := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [hstep x hx]
    exact Finset.mem_image.mpr ⟨f x, hS x hx, rfl⟩
  obtain ⟨out, hout, hsize⟩ := fixed_power_on n c (S.image e) T L himage hL hLN
  refine ⟨out, fun x hx => ?_, ?_⟩
  · rw [hout (Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
    exact iterate_encoded f S e c hS hstep hx T
  · simpa only [Finset.card_image_of_injOn he] using hsize

/-- After a separately computed burn-in, the storage term counts only its image. -/
theorem image_sensitive (c burn : Circuit Boolean.signature n n) (d T L : ℕ)
    (hburn : burn.Computes Boolean.interpretation (c.eval Boolean.interpretation)^[d])
    (hdT : d ≤ T) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n n,
      out.Computes Boolean.interpretation (c.eval Boolean.interpretation)^[T] ∧
      out.size ≤ burn.size + 40000 * powerBudget n c.size
        (Finset.univ.image (c.eval Boolean.interpretation)^[d]).card L := by
  classical
  let f := c.eval Boolean.interpretation
  let S := Finset.univ.image f^[d]
  have hS : ∀ y ∈ S, f y ∈ S := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨f x, Finset.mem_univ _, ?_⟩
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  obtain ⟨tail, htail, hsize⟩ := fixed_power_on n c S (T - d) L hS hL hLN
  refine ⟨tail.comp burn, fun x => ?_, ?_⟩
  · rw [Circuit.eval_comp, hburn x]
    rw [htail (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩),
      ← Function.iterate_add_apply, Nat.sub_add_cancel hdT]
  · rw [Circuit.size_comp]
    exact Nat.add_le_add_left hsize burn.size

end IteratedFunctions
