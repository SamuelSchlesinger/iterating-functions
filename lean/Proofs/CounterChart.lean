/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CounterIntervals
public import Proofs.CounterRemainders
public import Proofs.LabelEncoding

/-!
# Sparse orbit coordinates from interval labels

Each interval stores its cycle representative, cycle length, and the phase of
its first state. One modular addition encodes its other states. Decoding tests
the phase distance from each interval start. This proves a chart without an
enumeration of payload states or an assumed constant-time table primitive.
-/

@[expose] public section

namespace IteratedFunctions

attribute [local instance] counterChartBitVecFintype

local instance counterChartWordOrder (n : ℕ) : LinearOrder (BitVec n) :=
  LinearOrder.lift' BitVec.toNat BitVec.toNat_injective

variable {n R w : ℕ}

/-- Two spare bits hold cycle lengths and sums even for a cycle of length `2^n`. -/
abbrev chartWidth (n : ℕ) := n + 2

theorem cycleLength_le_words (f : BitVec n → BitVec n) (x : BitVec n) :
    cycleLength f x ≤ 2 ^ n := by
  have h := depth_add_cycleLength_le_card f x
  have hc : Fintype.card (BitVec n) = 2 ^ n :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  rw [hc] at h
  lia

theorem chart_ofNat_toNat {a : ℕ} (ha : a ≤ 2 ^ n) :
    (BitVec.ofNat (chartWidth n) a).toNat = a := by
  apply Nat.mod_eq_of_lt
  simp only [chartWidth, Nat.pow_succ]
  have := Nat.two_pow_pos n
  lia

@[simp] theorem chart_setWidth_toNat (x : BitVec n) :
    (x.setWidth (chartWidth n)).toNat = x.toNat := by
  simpa only [BitVec.ofNat_toNat] using chart_ofNat_toNat x.isLt.le

/-- Reuse the already charged modular-adder circuit on two reduced residues. -/
theorem addResidue_toNat (d a b : BitVec w)
    (ha : a.toNat < d.toNat) (hb : b.toNat < d.toNat) :
    (ModulusCounter.addResidue d a b).toNat = (a.toNat + b.toNat) % d.toNat := by
  have hd : 0 < d.toNat := by lia
  rw [ModulusCounter.addResidue_spec d a b b.toNat
    (fun _ => (Nat.mod_eq_of_lt hb).symm)]
  simp only [ModulusCounter.advance, hd, ha, and_self, ite_true, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt ((Nat.mod_lt _ hd).trans d.isLt)

/-- Canonical coordinates of a cyclic word. -/
noncomputable def wordCycleLabel (f : BitVec n → BitVec n) (x : BitVec n) :
    State (n + (chartWidth n + chartWidth n)) :=
  labelBits (fun i => (canonicalCycle f x).getLsbD i.val)
    (BitVec.ofNat (chartWidth n) (cycleLength f x))
    (BitVec.ofNat (chartWidth n) (phase f x))

namespace CounterIntervalChart

variable {f : BitVec n → BitVec n} (chart : CounterIntervalChart f R)

def first (j : Fin R) : BitVec n := BitVec.ofNat n (chart.start j)

noncomputable def period (j : Fin R) : BitVec (chartWidth n) :=
  BitVec.ofNat (chartWidth n) (cycleLength f (chart.first j))

noncomputable def initialPhase (j : Fin R) : BitVec (chartWidth n) :=
  BitVec.ofNat (chartWidth n) (phase f (chart.first j))

def length (j : Fin R) : BitVec (chartWidth n) :=
  BitVec.ofNat (chartWidth n) (chart.stop j - chart.start j)

@[simp] theorem period_toNat (j : Fin R) :
    (chart.period j).toNat = cycleLength f (chart.first j) :=
  chart_ofNat_toNat (cycleLength_le_words f _)

@[simp] theorem initialPhase_toNat (j : Fin R) :
    (chart.initialPhase j).toNat = phase f (chart.first j) :=
  chart_ofNat_toNat ((phase_lt f _).le.trans (cycleLength_le_words f _))

@[simp] theorem length_toNat (j : Fin R) :
    (chart.length j).toNat = chart.stop j - chart.start j :=
  chart_ofNat_toNat ((Nat.sub_le _ _).trans (chart.stop_le j))

def contains (j : Fin R) (x : BitVec n) : Bool :=
  !(x.setWidth (chartWidth n)).ult (BitVec.ofNat (chartWidth n) (chart.start j)) &&
    (x.setWidth (chartWidth n)).ult (BitVec.ofNat (chartWidth n) (chart.stop j))

@[simp] theorem contains_iff (j : Fin R) (x : BitVec n) :
    chart.contains j x = true ↔ chart.start j ≤ x.toNat ∧ x.toNat < chart.stop j := by
  have hx := chart_setWidth_toNat x
  simp only [contains, Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, hx,
    chart_ofNat_toNat (chart.start_lt j).le, chart_ofNat_toNat (chart.stop_le j),
    decide_eq_false_iff_not, not_lt, decide_eq_true_eq]

def offset (j : Fin R) (x : BitVec n) : BitVec (chartWidth n) :=
  x.setWidth (chartWidth n) - BitVec.ofNat (chartWidth n) (chart.start j)

theorem offset_toNat (j : Fin R) (x : BitVec n) (hx : chart.start j ≤ x.toNat) :
    (chart.offset j x).toNat = x.toNat - chart.start j := by
  have hw := chart_setWidth_toNat x
  have hs := chart_ofNat_toNat (chart.start_lt j).le
  unfold offset
  rw [BitVec.toNat_sub_of_le (by change _ ≤ (x.setWidth _).toNat; rw [hs, hw]; exact hx), hw, hs]

noncomputable def encodedRow (j : Fin R) (x : BitVec n) :
    State (n + (chartWidth n + chartWidth n)) :=
  labelBits (fun i => (canonicalCycle f (chart.first j)).getLsbD i.val) (chart.period j)
    (ModulusCounter.addResidue (chart.period j) (chart.initialPhase j) (chart.offset j x))

theorem encodedRow_spec (hf : Function.Injective f) (j : Fin R) (x : BitVec n)
    (hx : chart.contains j x = true) : chart.encodedRow j x = wordCycleLabel f x := by
  obtain ⟨hlo, hhi⟩ := (chart.contains_iff j x).mp hx
  have hpath := chart.point_eq j x hlo hhi
  have hd : x.toNat - chart.start j < cycleLength f (chart.first j) :=
    (show x.toNat - chart.start j < chart.stop j - chart.start j by lia).trans_le
      (chart.length_le_period hf j)
  have hp : (ModulusCounter.addResidue (chart.period j) (chart.initialPhase j)
      (chart.offset j x)).toNat = phase f x := by
    rw [addResidue_toNat]
    · rw [initialPhase_toNat, period_toNat, chart.offset_toNat j x hlo, ← phase_shift]
      exact congrArg (phase f) hpath
    · simpa using phase_lt f (chart.first j)
    · simpa only [period_toNat, chart.offset_toNat j x hlo] using hd
  have hc : canonicalCycle f (chart.first j) = canonicalCycle f x := by
    rw [← hpath, canonicalCycle_iterate]
    rfl
  have hl : cycleLength f (chart.first j) = cycleLength f x := by
    rw [← hpath, cycleLength_iterate]
    rfl
  have he : ModulusCounter.addResidue (chart.period j) (chart.initialPhase j)
      (chart.offset j x) = BitVec.ofNat (chartWidth n) (phase f x) := by
    apply BitVec.eq_of_toNat_eq
    rw [hp, chart_ofNat_toNat ((phase_lt f x).le.trans (cycleLength_le_words f x))]
  unfold encodedRow wordCycleLabel
  rw [he, hc]
  simp only [period, hl]

/-- Encode by selecting any interval containing the input. -/
noncomputable def encode (x : BitVec n) : State (n + (chartWidth n + chartWidth n)) :=
  chooseRecord (fun j => chart.contains j x) (fun j => chart.encodedRow j x) (fun _ => false) R

theorem encode_spec (hf : Function.Injective f) (x : BitVec n) :
    chart.encode x = wordCycleLabel f x := by
  obtain ⟨j, hlo, hhi⟩ := chart.covers x
  obtain ⟨k, _, hk, hout⟩ := chooseRecord_spec (fun j => chart.contains j x)
    (fun j => chart.encodedRow j x) (fun _ => false) R
    ⟨j, j.isLt, (chart.contains_iff j x).mpr ⟨hlo, hhi⟩⟩
  exact hout.trans (chart.encodedRow_spec hf k x hk)

end CounterIntervalChart

end IteratedFunctions
