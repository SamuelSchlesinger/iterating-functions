/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Optimization
public import Proofs.FiniteOrbit
public import Proofs.LowerBound

/-!
# In-place multi-head machines

An in-place machine has one tape whose cells are exactly the `n` input cells, a finite tape
alphabet `Γ`, `h` heads, and a finite control `Q`.  This module defines its configurations
`(w, p, q)` with `w : Fin n → Γ`, `p : Fin h → Fin n` and `q : Q`, its one-step map, and the
finite set of configurations reachable from the initial configurations `ι(x)`, `x : Fin n → Bool`.

It checks the configuration count `|Γ|^n * n^h * |Q|`, the two bounds on the number of
reachable configurations used in the paper (all configurations; `2^n * (t+1)` under a halting
time bound), the bound `2^n * τ` for a machine that returns to an initial configuration every
`τ` steps, and the stabilization of a run after as many steps as there are configurations.
The circuit bounds apply `fixed_power_encoded` to the forward-invariant reachable set, given a
Boolean encoding of configurations, a circuit for the step map on that encoding, and a circuit
for the initial encoding.  The step circuit is a hypothesis: the locality construction from the
transition table is not checked here.  Finally, a machine whose rounds of `τ` steps realize the
modulus counter transfers the counting lower bound to its `τ*T`-th power.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

namespace InPlace

universe u v

/-- A head move. Moves past either end of the tape leave the head in place. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq

/-- Apply a clamped move to a head position. -/
def Move.apply {n : ℕ} : Move → Fin n → Fin n
  | .left, p => if hp : 0 < p.val then ⟨p.val - 1, by omega⟩ else p
  | .stay, p => p
  | .right, p => if hp : p.val + 1 < n then ⟨p.val + 1, hp⟩ else p

/-- An in-place machine with `h` heads. The transition reads the state, the symbols under the
heads, and for each head whether it is on the first and on the last cell. It returns the new
state, a symbol to write under each head, and a move for each head. -/
structure Machine (Q : Type u) (Γ : Type v) (h : ℕ) where
  δ : Q → (Fin h → Γ) → (Fin h → Bool) → (Fin h → Bool) → Q × (Fin h → Γ) × (Fin h → Move)
  start : Q
  halting : Q → Prop
  /-- The inclusion of the input alphabet `{0,1}` into `Γ`. -/
  embed : Bool → Γ

/-- Configurations: tape contents, head positions, and control state. -/
abbrev Config (Q : Type u) (Γ : Type v) (n h : ℕ) := (Fin n → Γ) × (Fin h → Fin n) × Q

variable {Q : Type u} {Γ : Type v} {n h : ℕ}

/-- Write under the heads in order of increasing index, so the largest index wins. -/
def writeHeads (w : Fin n → Γ) (p : Fin h → Fin n) (σ : Fin h → Γ) : Fin n → Γ :=
  Fin.foldl h (fun w j => Function.update w (p j) (σ j)) w

/-- A cell under no head is unchanged. -/
theorem writeHeads_of_forall_ne (w : Fin n → Γ) (p : Fin h → Fin n) (σ : Fin h → Γ) (i : Fin n)
    (hi : ∀ j, p j ≠ i) : writeHeads w p σ i = w i := by
  induction h with
  | zero => rfl
  | succ h ih =>
    unfold writeHeads at ih ⊢
    rw [Fin.foldl_succ_last, Function.update_of_ne (hi _).symm]
    exact ih (fun j => p j.castSucc) (fun j => σ j.castSucc) (fun j => hi _)

/-- Rewriting the symbols read leaves the tape unchanged. -/
theorem writeHeads_read (w : Fin n → Γ) (p : Fin h → Fin n) :
    writeHeads w p (fun j => w (p j)) = w := by
  induction h with
  | zero => rfl
  | succ h ih =>
    unfold writeHeads at ih ⊢
    rw [Fin.foldl_succ_last]
    rw [ih (fun j => p j.castSucc)]
    exact Function.update_eq_self _ _

/-- The one-step map of an in-place machine. -/
def Machine.step (M : Machine Q Γ h) (z : Config Q Γ n h) : Config Q Γ n h :=
  let out := M.δ z.2.2 (fun j => z.1 (z.2.1 j)) (fun j => decide ((z.2.1 j).val = 0))
    (fun j => decide ((z.2.1 j).val + 1 = n))
  (writeHeads z.1 z.2.1 out.2.1, fun j => (out.2.2 j).apply (z.2.1 j), out.1)

/-- The initial configuration: the input on the tape, every head on the first cell. -/
def Machine.init [NeZero n] (M : Machine Q Γ h) (x : Fin n → Bool) : Config Q Γ n h :=
  (fun i => M.embed (x i), fun _ => 0, M.start)

/-- Halting states are absorbing: they write the symbols read, do not move, and keep the
state. -/
def Machine.HaltingAbsorbing (M : Machine Q Γ h) : Prop :=
  ∀ q, M.halting q → ∀ r a b, M.δ q r a b = (q, r, fun _ => Move.stay)

theorem Machine.step_of_halting {M : Machine Q Γ h} (hM : M.HaltingAbsorbing)
    (z : Config Q Γ n h) (hz : M.halting z.2.2) : M.step z = z := by
  obtain ⟨w, p, q⟩ := z
  simp only [Machine.step, hM q hz, writeHeads_read, Move.apply]

/-- The number of configurations, which is the number of valid encodings. -/
theorem card_config [Fintype Q] [Fintype Γ] :
    Fintype.card (Config Q Γ n h) = Fintype.card Γ ^ n * n ^ h * Fintype.card Q := by
  simp only [Config, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.mul_assoc]

section Reach

variable [Fintype Q] [Fintype Γ] [NeZero n]

open Classical in
/-- The configurations reachable from some initial configuration. -/
noncomputable def reach (M : Machine Q Γ h) (n : ℕ) [NeZero n] : Finset (Config Q Γ n h) :=
  Finset.univ.filter fun z => ∃ x t, M.step^[t] (M.init x) = z

variable (M : Machine Q Γ h)

theorem mem_reach {z : Config Q Γ n h} :
    z ∈ reach M n ↔ ∃ x t, M.step^[t] (M.init x) = z := by
  unfold reach
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem init_mem_reach (x : Fin n → Bool) : M.init x ∈ reach M n :=
  (mem_reach M).mpr ⟨x, 0, rfl⟩

theorem iterate_mem_reach (x : Fin n → Bool) (t : ℕ) : M.step^[t] (M.init x) ∈ reach M n :=
  (mem_reach M).mpr ⟨x, t, rfl⟩

/-- The reachable set is forward invariant. -/
theorem step_mem_reach {z : Config Q Γ n h} (hz : z ∈ reach M n) : M.step z ∈ reach M n := by
  obtain ⟨x, t, rfl⟩ := (mem_reach M).mp hz
  refine (mem_reach M).mpr ⟨x, t + 1, ?_⟩
  rw [Function.iterate_succ_apply']

/-- Every configuration is counted in the configuration bound. -/
theorem reach_card_le_configs :
    (reach M n).card ≤ Fintype.card Γ ^ n * n ^ h * Fintype.card Q :=
  card_config (Q := Q) (Γ := Γ) (n := n) (h := h) ▸ Finset.card_le_univ _

/-- Reachable configurations are covered by the first `B` steps from every input. -/
theorem reach_card_le_of_cover (B : ℕ)
    (hcover : ∀ (x : Fin n → Bool) (t : ℕ),
      ∃ y, ∃ j < B, M.step^[t] (M.init x) = M.step^[j] (M.init y)) :
    (reach M n).card ≤ 2 ^ n * B := by
  classical
  have hsub : reach M n ⊆ (Finset.univ ×ˢ Finset.range B).image
      (fun xj : (Fin n → Bool) × ℕ => M.step^[xj.2] (M.init xj.1)) := by
    intro z hz
    obtain ⟨x, t, rfl⟩ := (mem_reach M).mp hz
    obtain ⟨y, j, hj, he⟩ := hcover x t
    exact Finset.mem_image.mpr ⟨(y, j), by simp [hj], he.symm⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp

/-- Under a halting-time bound `t`, at most `2^n * (t+1)` configurations are reachable. -/
theorem reach_card_le_time (hM : M.HaltingAbsorbing) (t : ℕ)
    (ht : ∀ x : Fin n → Bool, ∃ s ≤ t, M.halting (M.step^[s] (M.init x)).2.2) :
    (reach M n).card ≤ 2 ^ n * (t + 1) := by
  refine reach_card_le_of_cover M (t + 1) fun x r => ?_
  obtain ⟨s, hs, hh⟩ := ht x
  by_cases hrs : r ≤ s
  · exact ⟨x, r, by lia, rfl⟩
  · refine ⟨x, s, by lia, ?_⟩
    have hfix := Function.iterate_fixed (M.step_of_halting hM _ hh) (r - s)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by lia)] at hfix
    exact hfix

omit [Fintype Q] [Fintype Γ] in
/-- Running `τ*m` steps of a machine with rounds of length `τ` runs `m` rounds. -/
theorem iterate_rounds (τ : ℕ) (P : (Fin n → Bool) → Fin n → Bool)
    (hround : ∀ x, M.step^[τ] (M.init x) = M.init (P x)) (x : Fin n → Bool) (m : ℕ) :
    M.step^[τ * m] (M.init x) = M.init (P^[m] x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.mul_succ, Nat.add_comm, Function.iterate_add_apply, ih, hround,
      Function.iterate_succ_apply']

/-- A machine that returns to an initial configuration every `τ` steps reaches at most
`2^n * τ` configurations. -/
theorem reach_card_le_round (τ : ℕ) (hτ : 0 < τ) (P : (Fin n → Bool) → Fin n → Bool)
    (hround : ∀ x, M.step^[τ] (M.init x) = M.init (P x)) :
    (reach M n).card ≤ 2 ^ n * τ := by
  refine reach_card_le_of_cover M τ fun x t => ⟨P^[t / τ] x, t % τ, Nat.mod_lt _ hτ, ?_⟩
  conv_lhs => rw [← Nat.div_add_mod t τ, Nat.add_comm, Function.iterate_add_apply,
    iterate_rounds M τ P hround]

end Reach

/-- A run stabilizes after as many steps as there are configurations: the configuration then
halts exactly when the run ever halts, and it is then the halting configuration. -/
theorem iterate_card_halting [Fintype Q] [Fintype Γ] (M : Machine Q Γ h)
    (hM : M.HaltingAbsorbing) (z : Config Q Γ n h) :
    (M.halting (M.step^[Fintype.card (Config Q Γ n h)] z).2.2 ↔
        ∃ t, M.halting (M.step^[t] z).2.2) ∧
      ∀ t, M.halting (M.step^[t] z).2.2 →
        M.step^[Fintype.card (Config Q Γ n h)] z = M.step^[t] z := by
  classical
  let H : Config Q Γ n h → Prop := fun z => M.halting z.2.2
  have ha : absorb M.step H = M.step := by
    funext y
    unfold absorb
    split_ifs with hy
    · exact (M.step_of_halting hM y hy).symm
    · rfl
  refine ⟨?_, fun t ht => ?_⟩
  · have := absorb_eventual_iff M.step H z
    rwa [ha] at this
  · obtain ⟨t₀, _, hp, hfirst, he⟩ := absorb_first_visit M.step H z ⟨t, ht⟩
    rw [ha] at he
    rw [he]
    have ht₀ : t₀ ≤ t := by
      by_contra hc
      exact hfirst t (by lia) ht
    have hfix := Function.iterate_fixed (M.step_of_halting hM _ hp) (t - t₀)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel ht₀] at hfix
    exact hfix.symm

/-- The integer budget is monotone in the storage count. -/
theorem powerBudget_mono {w s M M' L : ℕ} (hM : M ≤ M') :
    powerBudget w s M L ≤ powerBudget w s M' L := by
  unfold powerBudget
  have : M / L ≤ M' / L := Nat.div_le_div_right hM
  gcongr

/-- The real budget is monotone in the storage count. -/
theorem optimizedBudget_mono {w s M M' : ℕ} (hM : M ≤ M') :
    optimizedBudget w s M ≤ optimizedBudget w s M' := by
  unfold optimizedBudget
  gcongr

section Circuits

variable [Fintype Q] [Fintype Γ] [NeZero n] {w : ℕ} (M : Machine Q Γ h)

/-- The reachable set fits in the encoding width. -/
theorem reach_card_le_two_pow (e : Config Q Γ n h → State w) (he : Set.InjOn e (reach M n)) :
    (reach M n).card ≤ 2 ^ w := by
  classical
  rw [← Finset.card_image_of_injOn he]
  simpa using Finset.card_le_univ ((reach M n).image e)

/-- Every fixed power on the initial configurations, with any upper bound `R` on the number of
reachable configurations in the storage term. The initial-encoding circuit `ι` is charged. -/
theorem inplace_fixed_power (e : Config Q Γ n h → State w) (he : Set.InjOn e (reach M n))
    (c : Circuit Boolean.signature w w)
    (hstep : ∀ z ∈ reach M n, c.eval Boolean.interpretation (e z) = e (M.step z))
    (ι : Circuit Boolean.signature n w)
    (hι : ∀ x, ι.eval Boolean.interpretation x = e (M.init x))
    (R : ℕ) (hR : (reach M n).card ≤ R) (T L : ℕ) (hL : 0 < L) (hLw : L ≤ 2 ^ w) :
    ∃ out : Circuit Boolean.signature n w,
      (∀ x, out.eval Boolean.interpretation x = e (M.step^[T] (M.init x))) ∧
      out.size ≤ ι.size + 40000 * powerBudget w c.size R L := by
  obtain ⟨d, hd, hs⟩ := fixed_power_encoded M.step (reach M n) e he c
    (fun z hz => step_mem_reach M hz) hstep T L hL hLw
  refine ⟨d.comp ι, fun x => ?_, ?_⟩
  · rw [Circuit.eval_comp, hι, hd _ (init_mem_reach M x)]
  · rw [Circuit.size_comp]
    have := powerBudget_mono (w := w) (s := c.size) (L := L) hR
    lia

/-- The square-root form, with any upper bound `R` on the number of reachable configurations. -/
theorem inplace_fixed_power_optimized (e : Config Q Γ n h → State w)
    (he : Set.InjOn e (reach M n)) (c : Circuit Boolean.signature w w)
    (hstep : ∀ z ∈ reach M n, c.eval Boolean.interpretation (e z) = e (M.step z))
    (ι : Circuit Boolean.signature n w)
    (hι : ∀ x, ι.eval Boolean.interpretation x = e (M.init x))
    (R : ℕ) (hR : (reach M n).card ≤ R) (T : ℕ) :
    ∃ out : Circuit Boolean.signature n w,
      (∀ x, out.eval Boolean.interpretation x = e (M.step^[T] (M.init x))) ∧
      (out.size : ℝ) ≤ ι.size + 120000 * optimizedBudget w c.size R := by
  obtain ⟨L, hL, hLw, hopt⟩ := powerBudget_optimized w c.size (reach M n).card
    (reach_card_le_two_pow M e he)
  obtain ⟨out, hout, hs⟩ := inplace_fixed_power M e he c hstep ι hι _ le_rfl T L hL hLw
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ ι.size + 40000 * (powerBudget w c.size (reach M n).card L : ℝ) := by
    exact_mod_cast hs
  have hm := optimizedBudget_mono (w := w) (s := c.size) hR
  linarith

/-- The alphabet bound: the storage term is the number of configurations. -/
theorem inplace_configs_optimized (e : Config Q Γ n h → State w)
    (he : Set.InjOn e (reach M n)) (c : Circuit Boolean.signature w w)
    (hstep : ∀ z ∈ reach M n, c.eval Boolean.interpretation (e z) = e (M.step z))
    (ι : Circuit Boolean.signature n w)
    (hι : ∀ x, ι.eval Boolean.interpretation x = e (M.init x)) (T : ℕ) :
    ∃ out : Circuit Boolean.signature n w,
      (∀ x, out.eval Boolean.interpretation x = e (M.step^[T] (M.init x))) ∧
      (out.size : ℝ) ≤ ι.size + 120000 *
        optimizedBudget w c.size (Fintype.card Γ ^ n * n ^ h * Fintype.card Q) :=
  inplace_fixed_power_optimized M e he c hstep ι hι _ (reach_card_le_configs M) T

/-- The time bound: under absorbing halting states and a halting time `t`, the storage term is
`2^n * (t+1)`. -/
theorem inplace_time_optimized (hM : M.HaltingAbsorbing) (t : ℕ)
    (ht : ∀ x : Fin n → Bool, ∃ s ≤ t, M.halting (M.step^[s] (M.init x)).2.2)
    (e : Config Q Γ n h → State w)
    (he : Set.InjOn e (reach M n)) (c : Circuit Boolean.signature w w)
    (hstep : ∀ z ∈ reach M n, c.eval Boolean.interpretation (e z) = e (M.step z))
    (ι : Circuit Boolean.signature n w)
    (hι : ∀ x, ι.eval Boolean.interpretation x = e (M.init x)) (T : ℕ) :
    ∃ out : Circuit Boolean.signature n w,
      (∀ x, out.eval Boolean.interpretation x = e (M.step^[T] (M.init x))) ∧
      (out.size : ℝ) ≤ ι.size + 120000 * optimizedBudget w c.size (2 ^ n * (t + 1)) :=
  inplace_fixed_power_optimized M e he c hstep ι hι _ (reach_card_le_time M hM t ht) T

/-- Halting, the halting state, and the final configuration of a machine that need not halt:
one circuit returns the encoding of the configuration after `|Γ|^n * n^h * |Q|` steps. It is a
halting configuration exactly when the run halts, and it is then the final configuration. -/
theorem inplace_halting (hM : M.HaltingAbsorbing) (e : Config Q Γ n h → State w)
    (he : Set.InjOn e (reach M n)) (c : Circuit Boolean.signature w w)
    (hstep : ∀ z ∈ reach M n, c.eval Boolean.interpretation (e z) = e (M.step z))
    (ι : Circuit Boolean.signature n w)
    (hι : ∀ x, ι.eval Boolean.interpretation x = e (M.init x)) :
    ∃ (out : Circuit Boolean.signature n w) (final : (Fin n → Bool) → Config Q Γ n h),
      (∀ x, out.eval Boolean.interpretation x = e (final x) ∧
        (M.halting (final x).2.2 ↔ ∃ t, M.halting (M.step^[t] (M.init x)).2.2) ∧
        ∀ t, M.halting (M.step^[t] (M.init x)).2.2 → final x = M.step^[t] (M.init x)) ∧
      (out.size : ℝ) ≤ ι.size + 120000 *
        optimizedBudget w c.size (Fintype.card Γ ^ n * n ^ h * Fintype.card Q) := by
  obtain ⟨out, hout, hs⟩ := inplace_configs_optimized M e he c hstep ι hι
    (Fintype.card (Config Q Γ n h))
  exact ⟨out, fun x => M.step^[Fintype.card (Config Q Γ n h)] (M.init x),
    fun x => ⟨hout x, iterate_card_halting M hM (M.init x)⟩, hs⟩

end Circuits

section Sharpness

variable {k w : ℕ} [NeZero (k + k)] (M : Machine Q Γ h)

/-- A machine whose rounds of `τ` steps apply the modulus counter, and whose encoding exposes the
input word of an initial configuration as a projection, inherits the counting lower bound:
some power `τ*T` has no circuit of at most `lowerBudget k` gates. -/
theorem round_lower_bound (hk : 64 ≤ k) (τ : ℕ)
    (hround : ∀ x, M.step^[τ] (M.init x) = M.init (ModulusCounter.power (k := k) 1 x))
    (e : Config Q Γ (k + k) h → State w) (tape : Fin (k + k) → Fin w)
    (htape : ∀ x, e (M.init x) ∘ tape = x) :
    ∃ T < ModulusCounter.period k,
      ∀ out : Circuit Boolean.signature (k + k) w,
        (∀ x, out.eval Boolean.interpretation x = e (M.step^[τ * T] (M.init x))) →
          lowerBudget k < out.size := by
  obtain ⟨T, hT, hh⟩ := exists_hard_counter_power k hk
  refine ⟨T, hT, fun out hout => ?_⟩
  have hc : ((Circuit.wiring Boolean.signature tape).comp out).Computes Boolean.interpretation
      (ModulusCounter.power (k := k) T) := by
    intro x
    rw [Circuit.eval_comp, hout, iterate_rounds M τ _ hround, Circuit.eval_wiring, htape,
      ModulusCounter.iterate_power]
  simpa using hh _ hc

/-- Both sides for a round machine: the counting lower bound for some power, and the
reachable-set upper bound `2^(2k) * τ` for every power, given an encoded step circuit. -/
theorem round_bounds [Fintype Q] [Fintype Γ] (hk : 64 ≤ k) (τ : ℕ) (hτ : 0 < τ)
    (hround : ∀ x, M.step^[τ] (M.init x) = M.init (ModulusCounter.power (k := k) 1 x))
    (e : Config Q Γ (k + k) h → State w) (he : Set.InjOn e (reach M (k + k)))
    (tape : Fin (k + k) → Fin w) (htape : ∀ x, e (M.init x) ∘ tape = x)
    (c : Circuit Boolean.signature w w)
    (hstep : ∀ z ∈ reach M (k + k), c.eval Boolean.interpretation (e z) = e (M.step z))
    (ι : Circuit Boolean.signature (k + k) w)
    (hι : ∀ x, ι.eval Boolean.interpretation x = e (M.init x)) :
    (∃ T < ModulusCounter.period k,
      ∀ out : Circuit Boolean.signature (k + k) w,
        (∀ x, out.eval Boolean.interpretation x = e (M.step^[τ * T] (M.init x))) →
          lowerBudget k < out.size) ∧
    ∀ T, ∃ out : Circuit Boolean.signature (k + k) w,
      (∀ x, out.eval Boolean.interpretation x = e (M.step^[T] (M.init x))) ∧
      (out.size : ℝ) ≤ ι.size + 120000 * optimizedBudget w c.size (2 ^ (k + k) * τ) :=
  ⟨round_lower_bound M hk τ hround e tape htape, fun T =>
    inplace_fixed_power_optimized M e he c hstep ι hι _
      (reach_card_le_round M τ hτ _ hround) T⟩

end Sharpness

end InPlace

end IteratedFunctions
