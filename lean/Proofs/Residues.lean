/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Reconstruction
public import Proofs.Words
public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

/-!
# Moving a residue into a short repeated interval

Start at `T % p` and add `p` while below the beginning of the interval.
At most `K` additions suffice when that beginning is at most `K`.
This replaces division in the online circuit by a bounded sequence of additions.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

/-- One bounded correction of a residue. -/
def liftResidue (lower period r : ℕ) : ℕ := if r < lower then r + period else r

/-- Repeated correction preserves the residue and never passes the interval. -/
theorem liftResidue_invariant (lower period r t : ℕ) (hp : 0 < period) (hr : r < period) :
    let v := (liftResidue lower period)^[t] r
    (lower ≤ v ∨ t ≤ v) ∧ v < lower + period ∧ v % period = r := by
  induction t with
  | zero =>
    change (lower ≤ r ∨ 0 ≤ r) ∧ r < lower + period ∧ r % period = r
    exact ⟨Or.inr (Nat.zero_le _), by lia, Nat.mod_eq_of_lt hr⟩
  | succ t ih =>
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply']
    rw [liftResidue]
    split <;> rename_i h
    · refine ⟨?_, by lia, ?_⟩
      · rcases ih.1 with hlow | ht
        · exact (not_lt_of_ge hlow h).elim
        · exact Or.inr (by lia)
      · simpa using ih.2.2
    · exact ⟨Or.inl (by lia), ih.2⟩

/-- Enough corrections place the residue in the desired interval. -/
theorem liftResidue_spec (lower period T K : ℕ) (hp : 0 < period) (hK : lower ≤ K) :
    let v := (liftResidue lower period)^[K] (T % period)
    lower ≤ v ∧ v < lower + period ∧ v % period = T % period := by
  have h := liftResidue_invariant lower period (T % period) K hp (Nat.mod_lt _ hp)
  refine ⟨?_, h.2⟩
  exact h.1.elim id (hK.trans ·)

/-- Equal residues after a repeated pair determine the same orbit state. -/
theorem iterate_eq_of_repeat_modEq {α : Type*} {f : α → α} {x : α} {i j r T : ℕ}
    (hij : i ≤ j) (heq : f^[i] x = f^[j] x) (hr : i ≤ r) (hT : i ≤ T)
    (hmod : r % (j - i) = T % (j - i)) : f^[r] x = f^[T] x := by
  have hp := periodic_of_repeat hij heq
  have hsub : (r - i) % (j - i) = (T - i) % (j - i) :=
    Nat.ModEq.add_right_cancel' i (by
      simpa only [Nat.ModEq, Nat.sub_add_cancel hr, Nat.sub_add_cancel hT] using hmod)
  calc
    f^[r] x = f^[r - i] (f^[i] x) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hr]
    _ = f^[(r - i) % (j - i)] (f^[i] x) := (hp.iterate_mod_apply _).symm
    _ = f^[(T - i) % (j - i)] (f^[i] x) := by rw [hsub]
    _ = f^[T] x := by rw [hp.iterate_mod_apply, ← Function.iterate_add_apply,
      Nat.sub_add_cancel hT]

/-- The bounded-addition implementation of the short-orbit branch is correct. -/
theorem liftResidue_reconstructs {α : Type*} {f : α → α} {x : α} {i j T K : ℕ}
    (hij : i < j) (heq : f^[i] x = f^[j] x) (hK : i ≤ K) (hT : i ≤ T) :
    let r := (liftResidue i (j - i))^[K] (T % (j - i))
    i ≤ r ∧ r < j ∧ f^[r] x = f^[T] x := by
  obtain ⟨hlo, hhi, hmod⟩ := liftResidue_spec i (j - i) T K (by lia) hK
  exact ⟨hlo, by lia, iterate_eq_of_repeat_modEq hij.le heq hlo hT hmod⟩

/-- The word operation used by the actual circuit. -/
def liftWord {w : ℕ} (lower period r : BitVec w) : BitVec w :=
  if r.ult lower then r + period else r

/-- The word correction agrees with natural-number correction when the interval fits. -/
theorem liftWord_toNat {w : ℕ} (lower period r : BitVec w)
    (hfit : lower.toNat + period.toNat ≤ 2 ^ w) :
    (liftWord lower period r).toNat = liftResidue lower.toNat period.toNat r.toNat := by
  unfold liftWord liftResidue
  by_cases hr : r.toNat < lower.toNat
  · simp only [BitVec.ult, hr, decide_true, ↓reduceIte, BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by lia)
  · simp only [BitVec.ult, hr, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem liftWord_iterate_toNat {w : ℕ} (lower period r : BitVec w)
    (hfit : lower.toNat + period.toNat ≤ 2 ^ w) (K : ℕ) :
    ((liftWord lower period)^[K] r).toNat =
      (liftResidue lower.toNat period.toNat)^[K] r.toNat := by
  induction K with
  | zero => rfl
  | succ K ih => rw [Function.iterate_succ_apply', liftWord_toNat _ _ _ hfit, ih,
      Function.iterate_succ_apply']

/-- The only exponent-dependent online data is a table of bounded residues. -/
def residueWord {w : ℕ} (T K : ℕ) (period : BitVec w) : BitVec w :=
  word (selectBits period (fun j : Fin (K + 1) =>
    fun i : Fin w => (BitVec.ofNat w (T % j.val)).getLsbD i.val))

theorem residueWord_toNat {w T K : ℕ} (period : BitVec w)
    (hK : K < 2 ^ w) (hp : 0 < period.toNat) (hpK : period.toNat ≤ K) :
    (residueWord T K period).toNat = T % period.toNat := by
  let j : Fin (K + 1) := ⟨period.toNat, by lia⟩
  have he : BitVec.ofNat w j.val = period := by simp [j]
  have hs := selectBits_eq (show K + 1 ≤ 2 ^ w by lia)
    (fun j : Fin (K + 1) => fun i : Fin w => (BitVec.ofNat w (T % j.val)).getLsbD i.val) j
  rw [he] at hs
  rw [residueWord, hs, word_bits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt ((Nat.mod_lt _ hp).trans_le (hpK.trans hK.le))

/-- Exact online index for the repeated-pair branch. -/
def repeatWordIndex {w : ℕ} (T K : ℕ) (lo hi : BitVec w) : BitVec w :=
  (liftWord lo (hi - lo))^[K] (residueWord T K (hi - lo))

/-- The index produced by the word algorithm lies in the repeated interval and
selects the required fixed iterate. -/
theorem repeatWordIndex_spec {α : Type*} {f : α → α} {x : α} {w T K : ℕ}
    (lo hi : BitVec w) (hlt : lo.toNat < hi.toNat) (hhi : hi.toNat ≤ K)
    (hK : K < 2 ^ w) (hT : K ≤ T)
    (heq : f^[lo.toNat] x = f^[hi.toNat] x) :
    let r := (repeatWordIndex T K lo hi).toNat
    lo.toNat ≤ r ∧ r < hi.toNat ∧ f^[r] x = f^[T] x := by
  have hp : (hi - lo).toNat = hi.toNat - lo.toNat := BitVec.toNat_sub_of_le hlt.le
  have hfit : lo.toNat + (hi - lo).toNat ≤ 2 ^ w := by rw [hp]; have := hi.isLt; lia
  rw [repeatWordIndex, liftWord_iterate_toNat _ _ _ hfit,
    residueWord_toNat _ hK (by rw [hp]; lia) (by rw [hp]; lia), hp]
  exact liftResidue_reconstructs hlt heq (by lia) (by lia)

/-- One word correction has a quadratic gate bound. -/
theorem synthesis_liftWord {n w : ℕ} (s : Set ((Fin n → Bool) → Bool))
    (lower period r : (Fin n → Bool) → BitVec w)
    (hl : ∀ i : Fin w, (fun x => (lower x).getLsbD i.val) ∈ s)
    (hp : ∀ i : Fin w, (fun x => (period x).getLsbD i.val) ∈ s)
    (hr : ∀ i : Fin w, (fun x => (r x).getLsbD i.val) ∈ s) :
    Synthesis Boolean.interpretation s (wordWires fun x => liftWord (lower x) (period x) (r x))
      (50 * (w + 1) ^ 2) := by
  have hsum := synthesis_add s r period hr hp
  have hcmp := synthesis_ult s r lower hr hl
  have hmux := synthesis_word_mux
    (s ∪ (wordWires (fun x => r x + period x) ∪ {fun x => (r x).ult (lower x)}))
    (fun x => r x + period x) r (fun x => (r x).ult (lower x))
    (Or.inr (Or.inr rfl)) (fun i => Or.inr (Or.inl ⟨i, rfl⟩)) (fun i => Or.inl (hr i))
  have h := (hsum.union hcmp).trans hmux
  exact h.mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)

/-- Iterate word corrections, sharing all intermediate words. -/
theorem synthesis_liftWord_iterate {n w : ℕ} (s : Set ((Fin n → Bool) → Bool))
    (lower period init : (Fin n → Bool) → BitVec w)
    (hl : ∀ i : Fin w, (fun x => (lower x).getLsbD i.val) ∈ s)
    (hp : ∀ i : Fin w, (fun x => (period x).getLsbD i.val) ∈ s)
    (hinit : ∀ i : Fin w, (fun x => (init x).getLsbD i.val) ∈ s) (K : ℕ) :
    Synthesis Boolean.interpretation s
      (wordWires fun x => (liftWord (lower x) (period x))^[K] (init x))
      (K * (50 * (w + 1) ^ 2)) := by
  let q := fun t => wordWires fun x => (liftWord (lower x) (period x))^[t] (init x)
  have hs := Synthesis.steps (I := Boolean.interpretation) (s := s) q
    (50 * (w + 1) ^ 2) K (by rintro _ ⟨i, rfl⟩; exact hinit i) (fun t _ => ?_)
  · exact hs.mono Set.Subset.rfl (Synthesis.mem_stages q K) le_rfl
  · simpa only [q, Function.iterate_succ_apply'] using
      synthesis_liftWord (s ∪ Synthesis.stages q t) lower period
        (fun x => (liftWord (lower x) (period x))^[t] (init x))
        (fun i => Or.inl (hl i)) (fun i => Or.inl (hp i))
        (fun i => Or.inr (Synthesis.mem_stages q t ⟨i, rfl⟩))

/-- A residue table uses only its word width and entry count, regardless of `T`. -/
theorem synthesis_residueWord {n w : ℕ} (s : Set ((Fin n → Bool) → Bool))
    (T K : ℕ) (period : (Fin n → Bool) → BitVec w)
    (hp : ∀ i : Fin w, (fun x => (period x).getLsbD i.val) ∈ s)
    (hconst : ∀ b : Bool, (fun _ : Fin n → Bool => b) ∈ s) :
    Synthesis Boolean.interpretation s (wordWires fun x => residueWord T K (period x))
      (w * ((K + 1) * (2 * w + 3) + 1)) := by
  have h := synthesis_selectBits s period
    (fun j : Fin (K + 1) => fun _ => fun i : Fin w =>
      (BitVec.ofNat w (T % j.val)).getLsbD i.val) hp (fun _ _ => hconst _)
  simpa only [wordWires, residueWord, word_bit] using h

/-- The complete repeated-pair index circuit has no dependence on the bit length of `T`. -/
theorem synthesis_repeatWordIndex {n w : ℕ} (s : Set ((Fin n → Bool) → Bool))
    (T K : ℕ) (lo hi : (Fin n → Bool) → BitVec w)
    (hlo : ∀ i : Fin w, (fun x => (lo x).getLsbD i.val) ∈ s)
    (hhi : ∀ i : Fin w, (fun x => (hi x).getLsbD i.val) ∈ s)
    (hconst : ∀ b : Bool, (fun _ : Fin n → Bool => b) ∈ s) :
    Synthesis Boolean.interpretation s (wordWires fun x => repeatWordIndex T K (lo x) (hi x))
      (100 * (K + 1) * (w + 1) ^ 2) := by
  let p := fun x => hi x - lo x
  let r := fun x => residueWord T K (p x)
  have hp := synthesis_sub s hi lo hhi hlo
  have hr := synthesis_residueWord (s ∪ wordWires p) T K p
    (fun i => Or.inr ⟨i, rfl⟩) (fun b => Or.inl (hconst b))
  have hout := synthesis_liftWord_iterate (s ∪ (wordWires p ∪ wordWires r)) lo p r
    (fun i => Or.inl (hlo i)) (fun i => Or.inr (Or.inl ⟨i, rfl⟩))
    (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) K
  have h := (hp.comp hr).trans hout
  apply h.mono Set.Subset.rfl Set.Subset.rfl
  nlinarith [Nat.zero_le (K * w ^ 2), Nat.zero_le (K * w)]

end IteratedFunctions
