/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module

public import Proofs.Reconstruction
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Semantic correctness of the distinguished-point algorithm

This module checks the six-step procedure in the proof of the
distinguished-point theorem of the manuscript (`thm:distinguished`): scan,
lookup, correction, period, residue and cycle walk, and output.  The period
walk uses its own register, so the checkpoint answer of the correction step
survives until the output.

The set `H` of distinguished points is abstract.  Its only property used here
is the hitting hypothesis: every trajectory prefix `x, f x, …, f^[K] x` of
pairwise distinct states meets `H`.  The payload table and the residue table
are hypotheses on arbitrary functions `z` and `R`, required only on the keys
`H` and on the indices `1 ≤ λ ≤ K`, as in the manuscript.

This is **semantic correctness only**.  The hashed construction of `H`, the
Bellare–Rompel existence argument, the gate counts, the circuit width, and the
reversible and pebbling results are not formalized here.
-/

@[expose] public section

namespace IteratedFunctions

universe u v
variable {α : Type u} (f : α → α)

/-- Apply stages `0, …, k-1` in order.  Each stage may depend on its index,
which the manuscript hardwires into the straight-line program. -/
def runStages {β : Type v} (step : ℕ → β → β) : ℕ → β → β
  | 0, b => b
  | k + 1, b => step k (runStages step k b)

@[simp] theorem runStages_zero {β : Type v} (step : ℕ → β → β) (b : β) :
    runStages step 0 b = b := rfl

@[simp] theorem runStages_succ {β : Type v} (step : ℕ → β → β) (k : ℕ) (b : β) :
    runStages step (k + 1) b = step k (runStages step k b) := rfl

/-! ## Step 1: scan -/

/-- The scan configuration `(u, φ, d, c)` of the manuscript. -/
structure ScanState (α : Type u) where
  u : α
  found : Bool
  d : ℕ
  c : α

section Scan

variable (H : α → Prop) [DecidablePred H]

/-- Scan stage `i`: record the first distinguished point, then advance `u`
unless `i = K`. -/
def scanStep (K i : ℕ) (σ : ScanState α) : ScanState α where
  u := if i < K then f σ.u else σ.u
  found := σ.found || decide (H σ.u)
  d := if σ.found = false ∧ H σ.u then i else σ.d
  c := if σ.found = false ∧ H σ.u then σ.u else σ.c

/-- Stages `i = 0, 1, …, K` of the scan, from `(x, 0, 0, x)`. -/
def scan (K : ℕ) (x : α) : ScanState α :=
  runStages (scanStep f H K) (K + 1) ⟨x, false, 0, x⟩

theorem scan_invariant (K : ℕ) (x : α) :
    ∀ k ≤ K + 1,
      (runStages (scanStep f H K) k ⟨x, false, 0, x⟩).u = f^[min k K] x ∧
      ((runStages (scanStep f H K) k ⟨x, false, 0, x⟩).found = true ↔
        ∃ i < k, H (f^[i] x)) ∧
      ((runStages (scanStep f H K) k ⟨x, false, 0, x⟩).found = true →
        (runStages (scanStep f H K) k ⟨x, false, 0, x⟩).d < k ∧
        H (f^[(runStages (scanStep f H K) k ⟨x, false, 0, x⟩).d] x) ∧
        (∀ i < (runStages (scanStep f H K) k ⟨x, false, 0, x⟩).d, ¬ H (f^[i] x)) ∧
        (runStages (scanStep f H K) k ⟨x, false, 0, x⟩).c =
          f^[(runStages (scanStep f H K) k ⟨x, false, 0, x⟩).d] x) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨hu, hiff, hfd⟩ := ih (by lia)
    rw [runStages_succ]
    generalize hσ : runStages (scanStep f H K) k ⟨x, false, 0, x⟩ = σ at hu hiff hfd
    have hmin : min k K = k := by lia
    rw [hmin] at hu
    refine ⟨?_, ?_, ?_⟩
    · simp only [scanStep]
      by_cases hkK : k < K
      · rw [ite_eq_left hkK, hu, ← Function.iterate_succ_apply' f k x]
        congr 1
        lia
      · rw [ite_eq_right hkK, hu]
        congr 1
        lia
    · simp only [scanStep, Bool.or_eq_true, decide_eq_true_eq, hiff, hu]
      constructor
      · rintro (⟨i, hi, hHi⟩ | hHk)
        · exact ⟨i, by lia, hHi⟩
        · exact ⟨k, by lia, hHk⟩
      · rintro ⟨i, hi, hHi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact Or.inl ⟨i, hi, hHi⟩
        · exact Or.inr hHi
    · intro hfound
      simp only [scanStep]
      by_cases hσt : σ.found = true
      · obtain ⟨hd, hHd, hfirst, hc⟩ := hfd hσt
        have hnot : ¬ (σ.found = false ∧ H σ.u) := by simp [hσt]
        rw [ite_eq_right hnot, ite_eq_right hnot]
        exact ⟨by lia, hHd, hfirst, hc⟩
      · have hσf : σ.found = false := by simpa using hσt
        have hHu : H σ.u := by
          simpa [scanStep, hσf] using hfound
        have hyes : σ.found = false ∧ H σ.u := ⟨hσf, hHu⟩
        rw [ite_eq_left hyes, ite_eq_left hyes]
        have hnone : ¬ ∃ i < k, H (f^[i] x) := by
          rw [← hiff, hσf]
          simp
        refine ⟨by lia, hu ▸ hHu, ?_, hu⟩
        intro i hi hHi
        exact hnone ⟨i, hi, hHi⟩

/-- The scan ends at `x_K` and returns the first distinguished point of the
prefix `x_0, …, x_K`, if there is one. -/
theorem scan_spec (K : ℕ) (x : α) :
    (scan f H K x).u = f^[K] x ∧
    ((scan f H K x).found = true ↔ ∃ i ≤ K, H (f^[i] x)) ∧
    ((scan f H K x).found = true →
      (scan f H K x).d ≤ K ∧ H (f^[(scan f H K x).d] x) ∧
      (∀ i < (scan f H K x).d, ¬ H (f^[i] x)) ∧
      (scan f H K x).c = f^[(scan f H K x).d] x) := by
  unfold scan
  obtain ⟨hu, hiff, hfd⟩ := scan_invariant f H K x (K + 1) le_rfl
  rw [show min (K + 1) K = K by lia] at hu
  refine ⟨hu, ?_, ?_⟩
  · rw [hiff]
    exact ⟨fun ⟨i, hi, h⟩ => ⟨i, by lia, h⟩, fun ⟨i, hi, h⟩ => ⟨i, by lia, h⟩⟩
  · intro hfound
    obtain ⟨hd, hHd, hfirst, hc⟩ := hfd hfound
    exact ⟨by lia, hHd, hfirst, hc⟩

end Scan

/-! ## Step 3: correction -/

/-- Correction stage `i`: apply `f` exactly when `i ≥ d`. -/
def correctionStep (d i : ℕ) (v : α) : α := if d ≤ i then f v else v

theorem correction_run (d k : ℕ) (v : α) :
    runStages (correctionStep f d) k v = f^[k - d] v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [runStages_succ, ih, correctionStep]
    by_cases hd : d ≤ k
    · rw [ite_eq_left hd, ← Function.iterate_succ_apply' f (k - d) v]
      congr 1
      lia
    · rw [ite_eq_right hd]
      congr 1
      lia

/-! ## Step 4: period, in a separate register -/

/-- The period configuration: the walking register `w`, a found flag, and the
recorded period, initially the dummy value `1`. -/
structure PeriodState (α : Type u) where
  w : α
  found : Bool
  period : ℕ

section Period

variable [DecidableEq α]

/-- Period stage `i`, which is stage `j = i + 1` of the manuscript: advance `w`
and record `j` the first time `w` returns to `y`. -/
def periodStep (y : α) (i : ℕ) (σ : PeriodState α) : PeriodState α where
  w := f σ.w
  found := σ.found || decide (f σ.w = y)
  period := if σ.found = false ∧ f σ.w = y then i + 1 else σ.period

/-- Stages `j = 1, …, K` of the period walk from `y`. -/
def periodWalk (K : ℕ) (y : α) : PeriodState α :=
  runStages (periodStep f y) K ⟨y, false, 1⟩

theorem periodWalk_invariant (y : α) (k : ℕ) :
    (runStages (periodStep f y) k ⟨y, false, 1⟩).w = f^[k] y ∧
    ((runStages (periodStep f y) k ⟨y, false, 1⟩).found = true ↔
      ∃ j, 1 ≤ j ∧ j ≤ k ∧ f^[j] y = y) ∧
    ((runStages (periodStep f y) k ⟨y, false, 1⟩).found = true →
      1 ≤ (runStages (periodStep f y) k ⟨y, false, 1⟩).period ∧
      (runStages (periodStep f y) k ⟨y, false, 1⟩).period ≤ k ∧
      f^[(runStages (periodStep f y) k ⟨y, false, 1⟩).period] y = y ∧
      ∀ j, 1 ≤ j → j < (runStages (periodStep f y) k ⟨y, false, 1⟩).period →
        f^[j] y ≠ y) := by
  induction k with
  | zero =>
    refine ⟨rfl, ?_, ?_⟩
    · simp only [runStages_zero, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro j h1 h0
      lia
    · simp
  | succ k ih =>
    obtain ⟨hw, hiff, hfd⟩ := ih
    rw [runStages_succ]
    generalize hσ : runStages (periodStep f y) k ⟨y, false, 1⟩ = σ at hw hiff hfd
    have hstep : f σ.w = f^[k + 1] y := by
      rw [hw, Function.iterate_succ_apply']
    refine ⟨hstep, ?_, ?_⟩
    · simp only [periodStep, Bool.or_eq_true, decide_eq_true_eq, hiff, hstep]
      constructor
      · rintro (⟨j, h1, hj, he⟩ | he)
        · exact ⟨j, h1, by lia, he⟩
        · exact ⟨k + 1, by lia, le_rfl, he⟩
      · rintro ⟨j, h1, hj, he⟩
        rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
        · exact Or.inl ⟨j, h1, by lia, he⟩
        · have : j = k + 1 := by lia
          subst this
          exact Or.inr he
    · intro hfound
      simp only [periodStep]
      by_cases hσt : σ.found = true
      · obtain ⟨h1, hle, he, hmin⟩ := hfd hσt
        have hnot : ¬ (σ.found = false ∧ f σ.w = y) := by simp [hσt]
        rw [ite_eq_right hnot]
        exact ⟨h1, by lia, he, hmin⟩
      · have hσf : σ.found = false := by simpa using hσt
        have hret : f σ.w = y := by
          simpa [periodStep, hσf] using hfound
        have hyes : σ.found = false ∧ f σ.w = y := ⟨hσf, hret⟩
        rw [ite_eq_left hyes]
        have hnone : ¬ ∃ j, 1 ≤ j ∧ j ≤ k ∧ f^[j] y = y := by
          rw [← hiff, hσf]
          simp
        refine ⟨by lia, le_rfl, hstep ▸ hret, ?_⟩
        intro j h1 hj he
        exact hnone ⟨j, h1, by lia, he⟩

/-- If `y` returns to itself within `K` steps, the period walk returns the least
return time `λ`, with `1 ≤ λ ≤ K`. -/
theorem periodWalk_spec (K : ℕ) (y : α) (h : ∃ p, 1 ≤ p ∧ p ≤ K ∧ f^[p] y = y) :
    1 ≤ (periodWalk f K y).period ∧ (periodWalk f K y).period ≤ K ∧
    Function.IsPeriodicPt f (periodWalk f K y).period y ∧
    ∀ j, 1 ≤ j → j < (periodWalk f K y).period → f^[j] y ≠ y := by
  obtain ⟨_, hiff, hfd⟩ := periodWalk_invariant f y K
  exact hfd (hiff.mpr h)

end Period

/-! ## Step 5: cycle walk -/

/-- Cycle-walk stage `i`: apply `f` exactly when `i < r`. -/
def walkStep (r i : ℕ) (v : α) : α := if i < r then f v else v

theorem walk_run (r k : ℕ) (v : α) :
    runStages (walkStep f r) k v = f^[min r k] v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [runStages_succ, ih, walkStep]
    by_cases hk : k < r
    · rw [ite_eq_left hk, ← Function.iterate_succ_apply' f (min r k) v]
      congr 1
      lia
    · rw [ite_eq_right hk]
      congr 1
      lia

/-! ## The whole procedure -/

section Algorithm

variable (H : α → Prop) [DecidablePred H] [DecidableEq α]

/-- The distinguished-point procedure for `F^T` with walk length `K`, payload
table `z` and residue table `R`.  For `T < K` it unrolls `T` steps.  Otherwise
it runs the scan, looks up `z` at the first distinguished point `c`, corrects
forward, finds the period of `x_K` in a separate register, walks
`R λ` steps from `x_K`, and selects the checkpoint answer if a distinguished
point was found. -/
def distinguishedPower (K T : ℕ) (z : α → α) (R : ℕ → ℕ) (x : α) : α :=
  if T < K then f^[T] x
  else
    let σ := scan f H K x
    let v := runStages (correctionStep f σ.d) K (z σ.c)
    let w := periodWalk f K σ.u
    let v' := runStages (walkStep f (R w.period)) K σ.u
    if σ.found then v else v'

/-- **Semantic correctness of the distinguished-point algorithm.**  If every
prefix of `K + 1` pairwise distinct states meets `H`, the payloads are
`z h = f^[T-K] h` on `H`, and the residues are `R λ = (T-K) % λ` for
`1 ≤ λ ≤ K`, then the procedure returns `f^[T] x` on every input.  Nothing
about circuit size, the hash family, or how `H` is found is claimed. -/
theorem distinguishedPower_correct (K T : ℕ) (z : α → α) (R : ℕ → ℕ)
    (hhit : ∀ y : α, (∀ i ≤ K, ∀ j ≤ K, f^[i] y = f^[j] y → i = j) →
      ∃ i ≤ K, H (f^[i] y))
    (hz : ∀ h, H h → z h = f^[T - K] h)
    (hR : ∀ l, 1 ≤ l → l ≤ K → R l = (T - K) % l)
    (x : α) :
    distinguishedPower f H K T z R x = f^[T] x := by
  unfold distinguishedPower
  split_ifs with hTK
  · rfl
  push Not at hTK
  obtain ⟨hu, hiff, hfd⟩ := scan_spec f H K x
  simp only
  cases hfound : (scan f H K x).found with
  | true =>
    -- Checkpoint branch: forward correction of the shifted payload.
    obtain ⟨hd, hHd, -, hc⟩ := hfd hfound
    simp only [ite_true]
    rw [correction_run, hc, hz _ (hc ▸ hHd)]
    exact shifted_payload hd hTK
  | false =>
    -- Repetition branch: the prefix repeats, so `x_K` lies on a short cycle.
    simp only [Bool.false_eq_true, ite_false]
    have hnohit : ¬ ∃ i ≤ K, H (f^[i] x) := by
      rw [← hiff, hfound]
      simp
    have hrep : ∃ i j, i < j ∧ j ≤ K ∧ f^[i] x = f^[j] x := by
      by_contra hno
      apply hnohit
      apply hhit x
      intro i hi j hj he
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hij | hji
      · exact hno ⟨i, j, hij, hj, he⟩
      · exact hno ⟨j, i, hji, hi, he.symm⟩
    obtain ⟨i, j, hij, hjK, he⟩ := hrep
    have hperK : Function.IsPeriodicPt f (j - i) (f^[K] x) := by
      have hp := (periodic_of_repeat hij.le he).apply_iterate (K - i)
      rwa [← Function.iterate_add_apply, Nat.sub_add_cancel (by lia : i ≤ K)] at hp
    obtain ⟨hl1, hlK, hlper, -⟩ :=
      periodWalk_spec f K (scan f H K x).u ⟨j - i, by lia, by lia, hu ▸ hperK⟩
    set l := (periodWalk f K (scan f H K x).u).period
    have hr : R l = (T - K) % l := hR l hl1 hlK
    have hrK : min (R l) K = (T - K) % l := by
      have := Nat.mod_lt (T - K) (by lia : 0 < l)
      rw [hr]
      lia
    rw [walk_run, hrK, hlper.iterate_mod_apply, hu, ← Function.iterate_add_apply,
      Nat.sub_add_cancel hTK]

end Algorithm

end IteratedFunctions
