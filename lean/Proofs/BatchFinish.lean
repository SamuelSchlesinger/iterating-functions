/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.FixedPower

/-! # Finishing one trajectory after a shared dictionary query -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits Algebraic.MassProduction.Sorting

variable {n w a R : ℕ}

theorem chooseRecord_no_flags {α : Type*} (flags : Fin R → Bool) (records : Fin R → α)
    (fallback : α) (h : ∀ j, flags j = false) (t : ℕ) :
    chooseRecord flags records fallback t = fallback := by
  induction t with
  | zero => rfl
  | succ t ih => simp [chooseRecord, h, ih]

def hitRecord (index : ℕ) (payload : State n) : Fin (1 + (w + n)) → Bool :=
  Fin.append (fun _ : Fin 1 => true)
    (Fin.append (fun bit : Fin w => (BitVec.ofNat w index).getLsbD bit.val) payload)

def chosenHit (K : ℕ) (flags : Fin (K + 1) → Bool)
    (payloads : Fin (K + 1) → State n) : Fin (1 + (w + n)) → Bool :=
  chooseRecord flags (fun j => hitRecord j.val (payloads j)) (fun _ => false) (K + 1)

def hitIndex (record : Fin (1 + (w + n)) → Bool) : BitVec w :=
  word fun bit => record (Fin.natAdd 1 (Fin.castAdd n bit))

def hitPayload (record : Fin (1 + (w + n)) → Bool) : State n :=
  fun bit => record (Fin.natAdd 1 (Fin.natAdd w bit))

@[simp] theorem hitIndex_hitRecord (j : ℕ) (p : State n) :
    hitIndex (hitRecord (w := w) j p) = BitVec.ofNat w j := by
  simpa only [hitIndex, hitRecord, Fin.append_right, Fin.append_left] using
    word_bits (BitVec.ofNat w j)

@[simp] theorem hitRecord_flag (j : ℕ) (p : State n) :
    hitRecord (w := w) j p 0 = true := by
  have hz : (0 : Fin (1 + (w + n))) = Fin.castAdd (w + n) (0 : Fin 1) := by ext; simp
  rw [hz, hitRecord, Fin.append_left]

@[simp] theorem hitPayload_hitRecord (j : ℕ) (p : State n) :
    hitPayload (hitRecord (w := w) j p) = p := by
  funext bit
  simp [hitPayload, hitRecord]

theorem chosenHit_flag_iff (K : ℕ) (flags : Fin (K + 1) → Bool)
    (payloads : Fin (K + 1) → State n) :
    chosenHit (w := w) K flags payloads 0 = true ↔ ∃ j, flags j = true := by
  constructor
  · intro h
    by_contra hh
    have hf : ∀ j, flags j = false := fun j => Bool.eq_false_iff.mpr (fun hj => hh ⟨j, hj⟩)
    simp [chosenHit, chooseRecord_no_flags _ _ _ hf] at h
  · rintro ⟨j, hj⟩
    obtain ⟨i, _, _, hi⟩ := chooseRecord_spec flags (fun j => hitRecord (w := w) j.val (payloads j))
      (fun _ => false) (K + 1) ⟨j, j.isLt, hj⟩
    change chosenHit (w := w) K flags payloads = _ at hi
    rw [hi, hitRecord_flag]

def finishHit (f : State n → State n) (K : ℕ)
    (flags : Fin (K + 1) → Bool) (payloads : Fin (K + 1) → State n)
    (fallback : State n) : State n :=
  let selected := chosenHit (w := w) K flags payloads
  if selected 0 then hitValue f K (hitIndex selected) (hitPayload selected) else fallback

theorem finishHit_correct (f : State n → State n) (T K : ℕ) (x : State n)
    (flags : Fin (K + 1) → Bool) (payloads : Fin (K + 1) → State n) (fallback : State n)
    (hK : K < 2 ^ w) (hT : K ≤ T)
    (hyes : ∀ j, flags j = true → payloads j = f^[T - K] (f^[j.val] x))
    (hno : (¬ ∃ j, flags j = true) → fallback = f^[T] x) :
    finishHit (w := w) f K flags payloads fallback = f^[T] x := by
  unfold finishHit
  dsimp only
  by_cases hh : ∃ j, flags j = true
  · rw [ite_eq_left ((chosenHit_flag_iff K flags payloads).mpr hh)]
    obtain ⟨j, _, hj, he⟩ := chooseRecord_spec flags
      (fun j => hitRecord (w := w) j.val (payloads j))
      (fun _ => false) (K + 1) (by obtain ⟨j, hj⟩ := hh; exact ⟨j, j.isLt, hj⟩)
    change chosenHit (w := w) K flags payloads = _ at he
    rw [he, hitIndex_hitRecord, hitPayload_hitRecord, hyes j hj]
    exact hitValue_spec f T K j.val x (by have := j.isLt; lia) hK hT
  · rw [ite_eq_right (fun h => hh ((chosenHit_flag_iff K flags payloads).mp h))]
    exact hno hh

theorem synthesis_finishHit (c : Circuit Boolean.signature n n)
    (s : Set (State a → Bool)) (K : ℕ)
    (flags : State a → Fin (K + 1) → Bool)
    (payloads : State a → Fin (K + 1) → State n) (fallback : State a → State n)
    (hf : ∀ j, (fun x => flags x j) ∈ s)
    (hp : ∀ j bit, (fun x => payloads x j bit) ∈ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s)
    {C : ℕ} (hfall : Synthesis Boolean.interpretation s (wires fallback) C) :
    Synthesis Boolean.interpretation s
      (wires fun x => finishHit (w := w) (c.eval Boolean.interpretation)
        K (flags x) (payloads x) (fallback x))
      ((K + 1) * (4 * (1 + (w + n))) + K * c.size +
        200 * (K + 1) * (n + w + 1) ^ 2 + C + 4 * n) := by
  let chosen := fun x => chosenHit (w := w) K (flags x) (payloads x)
  have hsel := synthesis_chooseRecord s flags
    (fun x j => hitRecord (w := w) j.val (payloads x j)) (fun _ _ => false) hf
    (fun j bit => ?_) (fun _ => hc false)
  · let src := s ∪ wires chosen
    have hi : ∀ bit : Fin w, (fun x => (hitIndex (chosen x)).getLsbD bit.val) ∈ src := by
      intro bit
      simp only [hitIndex, word_bit]
      exact Or.inr ⟨_, rfl⟩
    have hpay : wires (fun x => hitPayload (chosen x)) ⊆ src := by
      rintro _ ⟨bit, rfl⟩
      exact Or.inr ⟨_, rfl⟩
    have hh := synthesis_hitValue src c K (fun x => hitIndex (chosen x))
      (fun x => hitPayload (chosen x)) hi hpay (fun b => Or.inl (hc b))
    have hfall' : Synthesis Boolean.interpretation src (wires fallback) C :=
      hfall.mono Set.subset_union_left Set.Subset.rfl le_rfl
    have hout := synthesis_ite hh hfall' (Synthesis.of_mem (s := src) (Or.inr ⟨0, rfl⟩))
    have h := hsel.trans hout
    apply h.mono Set.Subset.rfl Set.Subset.rfl
    lia
  · induction bit using Fin.addCases with
    | left bit => simpa only [hitRecord, Fin.append_left] using hc true
    | right bit =>
      induction bit using Fin.addCases with
      | left bit =>
          simpa only [hitRecord, Fin.append_right, Fin.append_left] using
            (hc ((BitVec.ofNat w j.val).getLsbD bit.val))
      | right bit => simpa [hitRecord] using hp j bit

/-- A circuit sufficient on trajectories that repeat in the short prefix. -/
theorem repetition_fallback (c : Circuit Boolean.signature n n) (T L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) (hT : 2 * L ≤ T) :
    ∃ out : Circuit Boolean.signature n n,
      (∀ x, Repeats (c.eval Boolean.interpretation) x L →
        out.eval Boolean.interpretation x = (c.eval Boolean.interpretation)^[T] x) ∧
      out.size ≤ 40000 * (L * c.size + (n + 1) ^ 3 * (L + 1)) := by
  let K := 2 * L
  let d := Nat.clog 2 (K + 1)
  let cp : Fin 0 → State n := Fin.elim0
  have hcap : 0 + (K + 1) ≤ networkRecords d := by
    simpa only [Nat.zero_add, networkRecords_eq_two_pow] using
      Nat.le_pow_clog (by decide : 1 < 2) (K + 1)
  have hd : d ≤ n + 2 := by
    apply Nat.clog_le_of_le_pow
    simp only [Nat.pow_succ]
    dsimp [K]
    have := Nat.one_le_two_pow (n := n)
    lia
  have hpow : 2 ^ d ≤ 2 * (K + 1) := by
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (show 1 < K + 1 by dsimp [K]; lia)
    have hdpos : 0 < d := Nat.clog_pos (by decide) (by dsimp [K]; lia)
    rw [show 2 ^ d = 2 ^ (d - 1) * 2 by
      rw [← Nat.pow_succ, show (d - 1).succ = d by lia]]
    change 2 ^ (d - 1) < K + 1 at hp
    lia
  have hfit : K < 2 ^ (n + 2) := by
    dsimp [K]
    simp only [Nat.pow_succ]
    have := Nat.one_le_two_pow (n := n)
    lia
  obtain ⟨out, hout, hs⟩ := exists_fixedOutput (w := n + 2) c T K d cp
  refine ⟨out, ?_, ?_⟩
  · intro x hx
    rw [hout]
    apply reconstruct_spec _ T K cp x _ _ hfit hT
    apply Record.detect_sorted_witness _ T K d cp x hcap hfit
    obtain ⟨i, j, hij, hj, he⟩ := hx
    exact Or.inr ⟨i, j, hij, by dsimp [K]; lia, he⟩
  · have hc := construction_cost n c.size 0 L d hL hd (by simpa [K] using hpow)
    exact hs.trans (by simpa [K] using hc)

end IteratedFunctions
