/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ModulusCounter
public import Proofs.CircuitCounting
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.FinEnum

/-!
# A permutation with one prime cycle per hash class

This module checks the combinatorial skeleton of the near-counting-ceiling permutation.
States of `State (m + K)` are pairs `(r, b)` of an `m`-bit class and a `K`-bit position.
Given a cycle length `ℓ r < 2^K` for each class, the permutation advances `b` modulo `ℓ r`
when `b < ℓ r` and fixes every other state.

* `PrimeCycles.iterate_step` and `PrimeCycles.power_apply_mod`: the `T`-th power adds `T`
  modulo `ℓ r`, so it depends on `T` only through the table `r ↦ T mod ℓ r`.
* `PrimeCycles.iterate_eq_iterate_iff`: when the nontrivial lengths are pairwise coprime, two
  powers agree exactly when the exponents agree modulo `order ℓ`, the product of the
  nontrivial lengths.  Hence `order ℓ` is the order (`iterate_eq_id_iff`) and the number of
  distinct powers (`card_range_iterate`).
* `classPrime`: the hash-class construction.  The candidates of class `r` are
  `2^(K-1) + (r xor f z) * 2^g + z` for `z < 2^g`, with `K = m + g + 1`; the class length is
  the candidate prime with least `z`, or `1`.  Different classes get different primes.
* `near_landau_lower_bound`: with these lengths and any mixing function `f`, the permutation
  is bijective, and if the ordered-syntax exponent for `q` gates is below
  `(K - 1) * #{r | ℓ r > 1}`, some power below the order needs more than `q` gates.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

namespace PrimeCycles

open ModulusCounter (advance advance_add advance_lt advance_zero)

variable {m K : ℕ}

/-- The `m`-bit class word. -/
def classWord (x : State (m + K)) : BitVec m := word fun i => x (Fin.castAdd K i)

/-- The `K`-bit position word. -/
def posWord (x : State (m + K)) : BitVec K := word fun i => x (Fin.natAdd m i)

/-- Pack a class and a position. -/
def pack (r : BitVec m) (b : BitVec K) : State (m + K) :=
  Fin.append (fun i : Fin m => r.getLsbD i.val) (fun i : Fin K => b.getLsbD i.val)

@[simp] theorem classWord_pack (r : BitVec m) (b : BitVec K) : classWord (pack r b) = r := by
  simp only [classWord, pack, Fin.append_left, word_bits]

@[simp] theorem posWord_pack (r : BitVec m) (b : BitVec K) : posWord (pack r b) = b := by
  simp only [posWord, pack, Fin.append_right, word_bits]

@[simp] theorem pack_words (x : State (m + K)) : pack (classWord x) (posWord x) = x := by
  funext bit
  induction bit using Fin.addCases <;> simp [pack, classWord, posWord]

/-- The `T`-th power, written directly: advance the position by `T` modulo `ℓ r` on the
cycle `b < ℓ r`, and fix every other state (in particular every state with `ℓ r ≤ 1`). -/
def power (ℓ : BitVec m → ℕ) (T : ℕ) (x : State (m + K)) : State (m + K) :=
  pack (classWord x) (BitVec.ofNat K (advance (ℓ (classWord x)) (posWord x).toNat T))

/-- The permutation itself. -/
def step (ℓ : BitVec m → ℕ) : State (m + K) → State (m + K) := power ℓ 1

variable (ℓ : BitVec m → ℕ)

@[simp] theorem power_zero : power (K := K) ℓ 0 = id := by
  funext x
  simp [power]

theorem power_add (hℓ : ∀ r, ℓ r < 2 ^ K) (S T : ℕ) (x : State (m + K)) :
    power ℓ T (power ℓ S x) = power ℓ (S + T) x := by
  simp only [power, classWord_pack, posWord_pack, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (advance_lt (hℓ _) (BitVec.isLt _)), advance_add]

/-- **Powers.**  The `T`-th iterate of the step is `power ℓ T`. -/
theorem iterate_step (hℓ : ∀ r, ℓ r < 2 ^ K) (T : ℕ) :
    (step (K := K) ℓ)^[T] = power ℓ T := by
  funext x
  induction T with
  | zero => simp
  | succ T ih => rw [Function.iterate_succ_apply', ih, step, power_add ℓ hℓ]

theorem advance_mod (a b T : ℕ) : advance a b (T % a) = advance a b T := by
  unfold advance
  split_ifs with h
  · rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  · rfl

/-- **The power formula.**  `F^T (r, b)` depends on `T` only through `T mod ℓ r`:
it is `(r, (b + (T mod ℓ r)) mod ℓ r)` on the cycle and `(r, b)` elsewhere. -/
theorem power_apply_mod (T : ℕ) (r : BitVec m) (b : BitVec K) :
    power ℓ T (pack r b) =
      pack r (BitVec.ofNat K
        (if 0 < ℓ r ∧ b.toNat < ℓ r then (b.toNat + T % ℓ r) % ℓ r else b.toNat)) := by
  simp only [power, classWord_pack, posWord_pack, ← advance_mod (ℓ r) _ T]
  rfl

/-- Every positive length divides this common multiple, so its power is the identity. -/
theorem power_prod_eq_id :
    power (K := K) ℓ (∏ r ∈ Finset.univ.filter (fun r => 0 < ℓ r), ℓ r) = id := by
  funext x
  simp only [power, id]
  unfold advance
  split_ifs with h
  · have hd : ℓ (classWord x) ∣ ∏ r ∈ Finset.univ.filter (fun r => 0 < ℓ r), ℓ r :=
      Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩)
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt h.2]
    simp
  · simp

theorem step_bijective (hℓ : ∀ r, ℓ r < 2 ^ K) : Function.Bijective (step (K := K) ℓ) := by
  set P := ∏ r ∈ Finset.univ.filter (fun r => 0 < ℓ r), ℓ r
  have hP : 0 < P := Finset.prod_pos fun r hr => (Finset.mem_filter.mp hr).2
  have hid := power_prod_eq_id (K := K) ℓ
  have h1 (x : State (m + K)) : power ℓ (P - 1) (step ℓ x) = x := by
    rw [step, power_add ℓ hℓ, Nat.add_sub_cancel' hP, hid]; rfl
  have h2 (x : State (m + K)) : step ℓ (power ℓ (P - 1) x) = x := by
    rw [step, power_add ℓ hℓ, Nat.sub_add_cancel hP, hid]; rfl
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

/-- Two powers agree exactly when the exponents agree modulo every nontrivial length. -/
theorem power_eq_power_iff (hℓ : ∀ r, ℓ r < 2 ^ K) (S T : ℕ) :
    power (K := K) ℓ S = power ℓ T ↔ ∀ r, 1 < ℓ r → S ≡ T [MOD ℓ r] := by
  constructor
  · intro he r hr
    have hx := congrArg (fun F => (posWord (F (pack r (BitVec.ofNat K 0)))).toNat) he
    have hS := (Nat.mod_lt S (by lia : 0 < ℓ r)).trans (hℓ r)
    have hT := (Nat.mod_lt T (by lia : 0 < ℓ r)).trans (hℓ r)
    simpa [Nat.ModEq, power, advance, show 0 < ℓ r by lia, Nat.mod_eq_of_lt hS,
      Nat.mod_eq_of_lt hT] using hx
  · intro h
    funext x
    simp only [power]
    congr 2
    unfold advance
    split_ifs with ha
    · by_cases h1 : 1 < ℓ (classWord x)
      · exact (h _ h1).add_left _
      · have : ℓ (classWord x) = 1 := by lia
        rw [this, Nat.mod_one, Nat.mod_one]
    · rfl

/-- The nontrivial classes. -/
noncomputable def active : Finset (BitVec m) := Finset.univ.filter fun r => 1 < ℓ r

/-- The order: the product of the nontrivial cycle lengths. -/
noncomputable def order : ℕ := ∏ r ∈ active ℓ, ℓ r

theorem order_pos : 0 < order ℓ :=
  Finset.prod_pos fun r hr => by
    have := (Finset.mem_filter.mp hr).2
    lia

theorem dvd_order {r : BitVec m} (hr : 1 < ℓ r) : ℓ r ∣ order ℓ :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)

/-- A product of pairwise coprime divisors divides. -/
theorem prod_dvd_of_pairwise_coprime {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hc : (s : Set ι).Pairwise fun i j => (f i).Coprime (f j)) {d : ℕ}
    (hd : ∀ i ∈ s, f i ∣ d) : ∏ i ∈ s, f i ∣ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · exact Nat.coprime_prod_right_iff.mpr fun j hj =>
        hc (by simp) (by simp [hj]) (by rintro rfl; exact hi hj)
    · exact hd i (by simp)
    · exact ih (hc.mono (by simp)) fun j hj => hd j (by simp [hj])

/-- Pairwise coprimality of the nontrivial lengths. -/
def LengthsCoprime : Prop := ((active ℓ : Finset (BitVec m)) : Set (BitVec m)).Pairwise
  fun r s => (ℓ r).Coprime (ℓ s)

variable {ℓ}

theorem modEq_order_iff (hc : LengthsCoprime ℓ) (S T : ℕ) :
    S ≡ T [MOD order ℓ] ↔ ∀ r, 1 < ℓ r → S ≡ T [MOD ℓ r] := by
  constructor
  · exact fun h r hr => Nat.ModEq.of_dvd (dvd_order ℓ hr) h
  · intro h
    rcases le_total S T with hST | hST
    · rw [Nat.modEq_iff_dvd' hST]
      exact prod_dvd_of_pairwise_coprime _ _ hc fun r hr =>
        (Nat.modEq_iff_dvd' hST).mp (h r (Finset.mem_filter.mp hr).2)
    · refine Nat.ModEq.symm ?_
      rw [Nat.modEq_iff_dvd' hST]
      exact prod_dvd_of_pairwise_coprime _ _ hc fun r hr =>
        (Nat.modEq_iff_dvd' hST).mp (h r (Finset.mem_filter.mp hr).2).symm

/-- **Powers and residues.**  With pairwise coprime lengths, `F^S = F^T` exactly when
`S ≡ T` modulo the product of the nontrivial lengths. -/
theorem iterate_eq_iterate_iff (hℓ : ∀ r, ℓ r < 2 ^ K) (hc : LengthsCoprime ℓ) (S T : ℕ) :
    (step (K := K) ℓ)^[S] = (step ℓ)^[T] ↔ S ≡ T [MOD order ℓ] := by
  rw [iterate_step ℓ hℓ, iterate_step ℓ hℓ, power_eq_power_iff ℓ hℓ, modEq_order_iff hc]

/-- **The order.**  `F^T` is the identity exactly when the product divides `T`. -/
theorem iterate_eq_id_iff (hℓ : ∀ r, ℓ r < 2 ^ K) (hc : LengthsCoprime ℓ) (T : ℕ) :
    (step (K := K) ℓ)^[T] = id ↔ order ℓ ∣ T := by
  have h := iterate_eq_iterate_iff (K := K) hℓ hc T 0
  rw [Function.iterate_zero] at h
  rw [h, Nat.modEq_zero_iff_dvd]

/-- Distinct residues modulo the order give distinct powers. -/
theorem iterate_injective (hℓ : ∀ r, ℓ r < 2 ^ K) (hc : LengthsCoprime ℓ) :
    Function.Injective fun T : Fin (order ℓ) => (step (K := K) ℓ)^[T.val] := by
  intro S T h
  have hm := (iterate_eq_iterate_iff hℓ hc S.val T.val).mp h
  exact Fin.ext (by
    unfold Nat.ModEq at hm
    rwa [Nat.mod_eq_of_lt S.isLt, Nat.mod_eq_of_lt T.isLt] at hm)

/-- **The number of distinct powers** is the product of the nontrivial lengths. -/
theorem card_range_iterate (hℓ : ∀ r, ℓ r < 2 ^ K) (hc : LengthsCoprime ℓ) :
    Nat.card (Set.range fun T : ℕ => (step (K := K) ℓ)^[T]) = order ℓ := by
  have hrange : Set.range (fun T : ℕ => (step (K := K) ℓ)^[T]) =
      Set.range (fun T : Fin (order ℓ) => (step (K := K) ℓ)^[T.val]) := by
    ext G
    constructor
    · rintro ⟨T, rfl⟩
      refine ⟨⟨T % order ℓ, Nat.mod_lt _ (order_pos ℓ)⟩, ?_⟩
      exact (iterate_eq_iterate_iff hℓ hc _ _).mpr (Nat.mod_modEq _ _)
    · rintro ⟨T, rfl⟩
      exact ⟨T.val, rfl⟩
  rw [hrange, Nat.card_range_of_injective (iterate_injective hℓ hc)]
  simp

/-- The order is at least `L ^ c` when the `c` nontrivial lengths are at least `L`. -/
theorem pow_card_le_order {L : ℕ} (hL : ∀ r, 1 < ℓ r → L ≤ ℓ r) :
    L ^ (active ℓ).card ≤ order ℓ :=
  Finset.pow_card_le_prod _ _ _ fun r hr => hL r (Finset.mem_filter.mp hr).2

/-- **Counting step.**  If the ordered-syntax budget for `q` gates is below the order, some
power below the order has no circuit with at most `q` gates. -/
theorem exists_hard_power_of_budget_lt (hℓ : ∀ r, ℓ r < 2 ^ K) (hc : LengthsCoprime ℓ) (q : ℕ)
    (large : Boolean.signature.orderedBudget (m + K) (m + K) q < order ℓ) :
    ∃ T < order ℓ, ∀ out : Circuit Boolean.signature (m + K) (m + K),
      out.Computes Boolean.interpretation (step (K := K) ℓ)^[T] → q < out.size := by
  classical
  let family := Finset.univ.image fun T : Fin (order ℓ) => (step (K := K) ℓ)^[T.val]
  have hcard : family.card = order ℓ := by
    rw [Finset.card_image_of_injective _ (iterate_injective hℓ hc)]
    simp
  obtain ⟨target, ht, hh⟩ := Circuit.exists_hard_in_family (G := q)
    Boolean.interpretation family (by rw [hcard]; exact large)
  obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp ht
  refine ⟨T.val, T.isLt, fun out hcomp => ?_⟩
  by_contra hn
  exact hh out (by lia) hcomp

/-! ### The hash classes -/

/-- The `z`-th candidate of class `r`: `2^(m+g) + (r xor f z) * 2^g + z`. -/
def candidate (g : ℕ) (f : ℕ → ℕ) (r : BitVec m) (z : ℕ) : ℕ :=
  2 ^ (m + g) + (r.toNat ^^^ f z) * 2 ^ g + z

/-- The class length: the prime candidate with least `z < 2^g`, or `1` if there is none. -/
noncomputable def classPrime (m g : ℕ) (f : ℕ → ℕ) (r : BitVec m) : ℕ := by
  classical
  exact if h : ∃ z, z < 2 ^ g ∧ (candidate g f r z).Prime then
    candidate g f r (Nat.find h) else 1

theorem candidate_mod {g : ℕ} (f : ℕ → ℕ) (r : BitVec m) {z : ℕ} (hz : z < 2 ^ g) :
    candidate g f r z % 2 ^ g = z := by
  unfold candidate
  rw [pow_add, Nat.add_mod, Nat.add_mod (2 ^ m * 2 ^ g), Nat.mul_mod_left, Nat.mul_mod_left,
    Nat.mod_eq_of_lt hz]
  simp [Nat.mod_eq_of_lt hz]

theorem candidate_bounds {g : ℕ} {f : ℕ → ℕ} (hf : ∀ z, f z < 2 ^ m) (r : BitVec m)
    {z : ℕ} (hz : z < 2 ^ g) :
    2 ^ (m + g) ≤ candidate g f r z ∧ candidate g f r z < 2 ^ (m + g + 1) := by
  have hx : r.toNat ^^^ f z < 2 ^ m := Nat.xor_lt_two_pow r.isLt (hf z)
  unfold candidate
  generalize r.toNat ^^^ f z = x at hx ⊢
  have : (x + 1) * 2 ^ g ≤ 2 ^ m * 2 ^ g := Nat.mul_le_mul_right _ hx
  rw [pow_succ, pow_add]
  constructor <;> nlinarith

/-- Different classes have disjoint candidate sets. -/
theorem candidate_injective {g : ℕ} (f : ℕ → ℕ) {r s : BitVec m} {y z : ℕ}
    (hy : y < 2 ^ g) (hz : z < 2 ^ g) (h : candidate g f r y = candidate g f s z) : r = s := by
  have hyz : y = z := by
    rw [← candidate_mod f r hy, ← candidate_mod f s hz, h]
  subst hyz
  unfold candidate at h
  have hm : (r.toNat ^^^ f y) * 2 ^ g = (s.toNat ^^^ f y) * 2 ^ g := by lia
  have hx := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos g) hm
  have := congrArg (· ^^^ f y) hx
  simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
  exact BitVec.eq_of_toNat_eq this

theorem classPrime_spec {g : ℕ} (f : ℕ → ℕ) (r : BitVec m) :
    classPrime m g f r = 1 ∨
      ∃ z < 2 ^ g, classPrime m g f r = candidate g f r z ∧ (classPrime m g f r).Prime := by
  classical
  unfold classPrime
  split_ifs with h
  · right
    have hs := Nat.find_spec h
    exact ⟨_, hs.1, rfl, hs.2⟩
  · left; rfl

theorem classPrime_bounds {g : ℕ} {f : ℕ → ℕ} (hf : ∀ z, f z < 2 ^ m) (r : BitVec m) :
    classPrime m g f r < 2 ^ (m + g + 1) ∧
      (1 < classPrime m g f r → 2 ^ (m + g) ≤ classPrime m g f r ∧ (classPrime m g f r).Prime) := by
  rcases classPrime_spec (g := g) f r with h | ⟨z, hz, he, hp⟩
  · rw [h]
    exact ⟨Nat.one_lt_two_pow (by lia), by lia⟩
  · rw [he] at hp ⊢
    have hb := candidate_bounds hf r hz
    exact ⟨hb.2, fun _ => ⟨hb.1, hp⟩⟩

/-- **Distinct primes.**  The nontrivial class lengths are distinct primes, hence pairwise
coprime. -/
theorem classPrime_coprime (g : ℕ) (f : ℕ → ℕ) :
    LengthsCoprime (classPrime m g f) := by
  intro r hr s hs hrs
  have hr' := (Finset.mem_filter.mp hr).2
  have hs' := (Finset.mem_filter.mp hs).2
  rcases classPrime_spec (g := g) f r with h | ⟨y, hy, hey, hpr⟩
  · lia
  rcases classPrime_spec (g := g) f s with h | ⟨z, hz, hez, hps⟩
  · lia
  rw [Nat.coprime_primes hpr hps]
  intro he
  rw [hey, hez] at he
  exact hrs (candidate_injective f hy hz he)

/-- **Lower bound for the hash-class permutation.**  For any mixing function `f` with values
below `2^m`, put `K = m + g + 1` and let `ℓ r` be the least-index prime candidate of class
`r`.  The step is a bijection of `State (m + K)`, its powers below `order` are distinct,
`order ≥ 2^((K-1) c)` where `c` is the number of classes containing a prime, and if the
explicit ordered-syntax exponent for `q` gates is below `(K - 1) c`, some power `F^T` with
`T < order` has no Boolean circuit with at most `q` gates. -/
theorem near_landau_lower_bound (m g : ℕ) (f : ℕ → ℕ) (hf : ∀ z, f z < 2 ^ m) (q h : ℕ)
    (hw : m + (m + g + 1) + q + 1 ≤ 2 ^ h)
    (large : 3 * q + h * (2 * q + (m + (m + g + 1)) + 1) <
      (m + g) * (active (classPrime m g f)).card) :
    Function.Bijective (step (K := m + g + 1) (classPrime m g f)) ∧
      2 ^ ((m + g) * (active (classPrime m g f)).card) ≤ order (classPrime m g f) ∧
      ∃ T < order (classPrime m g f),
        ∀ out : Circuit Boolean.signature (m + (m + g + 1)) (m + (m + g + 1)),
          out.Computes Boolean.interpretation (step (K := m + g + 1) (classPrime m g f))^[T] →
            q < out.size := by
  have hℓ : ∀ r, classPrime m g f r < 2 ^ (m + g + 1) := fun r => (classPrime_bounds hf r).1
  have hord : 2 ^ ((m + g) * (active (classPrime m g f)).card) ≤ order (classPrime m g f) := by
    rw [pow_mul]
    exact pow_card_le_order fun r hr => ((classPrime_bounds hf r).2 hr).1
  refine ⟨step_bijective _ hℓ, hord, exists_hard_power_of_budget_lt hℓ (classPrime_coprime g f)
    q ?_⟩
  exact (boolean_orderedBudget_le_pow _ _ q h hw).trans_lt
    ((Nat.pow_lt_pow_right (by decide) large).trans_le hord)

end PrimeCycles

end IteratedFunctions
