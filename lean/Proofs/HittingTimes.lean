/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CycleLabels

/-! # Exact phase and first-hitting-time identities -/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} [Finite α] (f : α → α)

theorem iterate_eq_iff_modEq_after (x : α) {a b : ℕ}
    (ha : transientDepth f x ≤ a) (hb : transientDepth f x ≤ b) :
    f^[a] x = f^[b] x ↔ Nat.ModEq (cycleLength f x) a b := by
  let μ := transientDepth f x
  let ell := cycleLength f x
  have hp := cycleLength_periodic f x
  have ha' : f^[a] x = f^[(a - μ) % ell] (f^[μ] x) := by
    rw [hp.iterate_mod_apply, ← Function.iterate_add_apply, Nat.sub_add_cancel ha]
  have hb' : f^[b] x = f^[(b - μ) % ell] (f^[μ] x) := by
    rw [hp.iterate_mod_apply, ← Function.iterate_add_apply, Nat.sub_add_cancel hb]
  rw [ha', hb']
  have hi := Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (f := f) (x := f^[μ] x)
    (m := (a - μ) % ell) (n := (b - μ) % ell)
    (Nat.mod_lt _ (cycleLength_pos f x)) (Nat.mod_lt _ (cycleLength_pos f x))
  rw [hi]
  constructor
  · intro h
    have hm : Nat.ModEq ell (a - μ) (b - μ) := h
    simpa only [μ, Nat.sub_add_cancel ha, Nat.sub_add_cancel hb] using hm.add_right μ
  · intro h
    exact h.sub ha hb Nat.ModEq.rfl

variable [LinearOrder α]

theorem depth_le_canonicalTime (x : α) : transientDepth f x ≤ canonicalTime f x := by
  apply (periodic_iterate_iff f x _).mp
  rw [canonicalTime_spec]
  exact canonicalCycle_periodic f x

theorem phase_cancel (x : α) :
    Nat.ModEq (cycleLength f x) (phase f x + canonicalTime f x) 0 := by
  unfold Nat.ModEq phase
  calc
    _ = (cycleLength f x - canonicalTime f x % cycleLength f x +
        canonicalTime f x % cycleLength f x) % cycleLength f x := by
      simp only [Nat.add_mod, Nat.mod_mod]
    _ = _ := by rw [Nat.sub_add_cancel (Nat.mod_lt _ (cycleLength_pos f x)).le]; simp

/-- The phase convention agrees with forward iteration after the transient. -/
theorem phase_spec (x : α) {t : ℕ} (ht : transientDepth f x ≤ t) :
    f^[t] x = f^[(phase f x + t) % cycleLength f x] (canonicalCycle f x) := by
  rw [← canonicalTime_spec f x, ← Function.iterate_add_apply]
  apply (iterate_eq_iff_modEq_after f x ht (by have := depth_le_canonicalTime f x; lia)).mpr
  have hm : Nat.ModEq (cycleLength f x) ((phase f x + t) % cycleLength f x)
      (phase f x + t) := by simp [Nat.ModEq]
  have hc := (phase_cancel f x).add_right t
  have hc' : Nat.ModEq (cycleLength f x)
      ((phase f x + t) + canonicalTime f x) t := by
    convert hc using 1 <;> ac_rfl
  exact ((hm.add_right _).trans hc').symm

/-- Any visit to the canonical representative determines the same phase. -/
theorem phase_of_hit (x : α) {t : ℕ} (ht : f^[t] x = canonicalCycle f x) :
    phase f x = (cycleLength f x - t % cycleLength f x) % cycleLength f x := by
  have hd : transientDepth f x ≤ t := (periodic_iterate_iff f x t).mp
    (ht ▸ canonicalCycle_periodic f x)
  have hm := (iterate_eq_iff_modEq_after f x hd (depth_le_canonicalTime f x)).mp
    (ht.trans (canonicalTime_spec f x).symm)
  unfold phase
  rw [hm]

theorem phase_shift (x : α) (t : ℕ) :
    phase f (f^[t] x) = (phase f x + t) % cycleLength f x := by
  let y := f^[t] x
  let a := canonicalTime f x
  let b := canonicalTime f y
  let ell := cycleLength f x
  have hb : f^[b + t] x = canonicalCycle f x := by
    rw [Function.iterate_add_apply, canonicalTime_spec, canonicalCycle_iterate]
  have hd : transientDepth f x ≤ b + t := (periodic_iterate_iff f x _).mp
    (hb ▸ canonicalCycle_periodic f x)
  have hm : Nat.ModEq ell (b + t) a :=
    (iterate_eq_iff_modEq_after f x hd (depth_le_canonicalTime f x)).mp
      (hb.trans (canonicalTime_spec f x).symm)
  have hx := phase_cancel f x
  have hy := phase_cancel f y
  rw [cycleLength_iterate] at hy
  have hboth : Nat.ModEq ell (phase f y + (b + t)) ((phase f x + t) + (b + t)) := by
    have hr := hm.add_left (phase f x)
    have hxt : Nat.ModEq ell (phase f x + (b + t)) 0 := hr.trans hx
    have hc : Nat.ModEq ell ((phase f x + t) + b) 0 := by
      convert hxt using 1
      ac_rfl
    have hc' := hy.trans hc.symm
    have hc'' := hc'.add_right t
    convert hc'' using 1 <;> ac_rfl
  have he := Nat.ModEq.add_right_cancel' (b + t) hboth
  have hlt : phase f y < ell := by simpa only [y, cycleLength_iterate] using phase_lt f y
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hlt] using he

/-- The nonnegative residue needed after first entering the cycle. -/
noncomputable def cyclicDistance (x y : α) : ℕ :=
  (phase f y + cycleLength f x -
    (phase f x + transientDepth f x) % cycleLength f x) % cycleLength f x

/-- Exact first hitting time for a cyclic target on the same eventual cycle. -/
theorem cyclic_first_hit (x y : α) (hy : y ∈ Function.periodicPts f)
    (hc : canonicalCycle f x = canonicalCycle f y) :
    let t := transientDepth f x + cyclicDistance f x y
    f^[t] x = y ∧ ∀ j < t, f^[j] x ≠ y := by
  obtain ⟨a, ha⟩ := (cyclic_reachable_iff f x y hy).mpr hc
  have hel : cycleLength f y = cycleLength f x := by
    rw [← ha, cycleLength_iterate]
  let ell := cycleLength f x
  let z := (phase f x + transientDepth f x) % ell
  let d := cyclicDistance f x y
  have hell : 0 < ell := cycleLength_pos f x
  have hz : z < ell := Nat.mod_lt _ hell
  have hphase : phase f y < ell := by simpa only [hel] using phase_lt f y
  have hd : d < ell := Nat.mod_lt _ hell
  have hsum : Nat.ModEq ell (z + d) (phase f y) := by
    change (z + (phase f y + ell - z) % ell) % ell = phase f y % ell
    rw [Nat.add_mod_mod, Nat.add_sub_of_le (show z ≤ phase f y + ell by lia), Nat.add_mod_right]
  have hstart : Nat.ModEq ell (phase f x + transientDepth f x) z := by simp [Nat.ModEq, z]
  have hend : Nat.ModEq ell (phase f x + (transientDepth f x + d)) (phase f y) := by
    simpa only [Nat.add_assoc] using (hstart.add_right d).trans hsum
  have hyrepr : y = f^[phase f y] (canonicalCycle f x) := by
    have h := phase_spec f y (t := 0) (by rw [(transientDepth_eq_zero_iff f y).mpr hy])
    simpa only [Nat.add_zero, Nat.mod_eq_of_lt (phase_lt f y), Function.iterate_zero_apply,
      ← hc] using h
  dsimp only
  constructor
  · rw [phase_spec f x (by lia), hend, Nat.mod_eq_of_lt hphase, ← hyrepr]
  · intro j hj he
    have hjμ : transientDepth f x ≤ j := (periodic_iterate_iff f x j).mp (he ▸ hy)
    have hpj : phase f y = (phase f x + j) % ell := by
      rw [← he, phase_shift]
    have hjmod : Nat.ModEq ell (phase f x + j) (phase f y) := by
      simp only [Nat.ModEq, hpj, Nat.mod_mod]
    have hh := hend.trans hjmod.symm
    have hc1 := Nat.ModEq.add_left_cancel' (phase f x) hh
    have hc2 : Nat.ModEq ell d (j - transientDepth f x) := by
      apply Nat.ModEq.add_left_cancel' (transientDepth f x)
      simpa only [Nat.add_sub_of_le hjμ] using hc1
    have hdle : d ≤ j - transientDepth f x := by
      change d % ell = (j - transientDepth f x) % ell at hc2
      rw [Nat.mod_eq_of_lt hd] at hc2
      exact hc2 ▸ Nat.mod_le _ _
    dsimp only [d] at hdle
    lia

end IteratedFunctions
