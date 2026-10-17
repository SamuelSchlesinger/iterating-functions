/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CounterRemainders
public import Proofs.BatchLookup
public import Proofs.LowerBound

/-! # Batched powers of the modulus counter

All `r` members share one dictionary `a ↦ T mod a` over the positive `k`-bit
moduli. Each member then needs only the linear residue addition. Conversely,
one block of a batched circuit already computes the single power, and when the
power is not the identity every block needs its own output gate.
-/

@[expose] public section

namespace IteratedFunctions.ModulusCounter

open Cslib.Circuits

variable {k r : ℕ}

@[simp] theorem divNat_finProdFinEquiv {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).divNat = a :=
  congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (a, b))

@[simp] theorem modNat_finProdFinEquiv {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).modNat = b :=
  congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (a, b))

/-- Block `member` of a batched state. -/
def block (x : State (r * (k + k))) (member : Fin r) : State (k + k) :=
  fun bit => x (finProdFinEquiv (member, bit))

/-- The batched map `B_{P,T,r}`: the power applied independently to every block. -/
def batchPower (T : ℕ) (x : State (r * (k + k))) : State (r * (k + k)) :=
  fun i => power T (block x (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

@[simp] theorem batchPower_apply (T : ℕ) (x : State (r * (k + k))) (member : Fin r)
    (bit : Fin (k + k)) :
    batchPower T x (finProdFinEquiv (member, bit)) = power T (block x member) bit := by
  simp [batchPower]

@[simp] theorem block_batchPower (T : ℕ) (x : State (r * (k + k))) (member : Fin r) :
    block (batchPower T x) member = power T (block x member) := by
  funext bit
  simp [block]

/-- The batched power is the power of the batched update. -/
theorem iterate_batchPower (T : ℕ) :
    (batchPower (r := r) (k := k) 1)^[T] = batchPower T := by
  funext x
  induction T with
  | zero =>
    funext i
    obtain ⟨⟨member, bit⟩, rfl⟩ := finProdFinEquiv.surjective i
    simp [block]
  | succ T ih =>
    rw [Function.iterate_succ_apply', ih]
    funext i
    obtain ⟨⟨member, bit⟩, rfl⟩ := finProdFinEquiv.surjective i
    rw [batchPower_apply, batchPower_apply, block_batchPower, power_add]

/-- The left half of every state is preserved. -/
theorem power_left (T : ℕ) (y : State (k + k)) (i : Fin k) :
    power T y (Fin.castAdd k i) = y (Fin.castAdd k i) := by
  simp [power, pack, leftWord]

/-- States with modulus zero are fixed. -/
theorem power_pack_zero (T : ℕ) (b : BitVec k) : power T (pack 0 b) = pack 0 b := by
  simp [power, advance]

theorem pack_zero_zero : pack (0 : BitVec k) 0 = fun _ => false := by
  funext bit
  induction bit using Fin.addCases <;> simp only [pack, Fin.append_left, Fin.append_right] <;>
    exact BitVec.getLsbD_zero

/-- Dictionary keys: the positive moduli `1, ..., 2^k - 1`. -/
def residueKeys (k : ℕ) (j : Fin (2 ^ k - 1)) (bit : Fin k) : Bool :=
  (BitVec.ofNat k (j.val + 1)).getLsbD bit.val

/-- Dictionary payloads: `T mod a` for the key `a`. -/
def residueValues (k T : ℕ) (j : Fin (2 ^ k - 1)) (bit : Fin k) : Bool :=
  (BitVec.ofNat k (T % (j.val + 1))).getLsbD bit.val

theorem residueKeys_injective (k : ℕ) : Function.Injective (residueKeys k) := by
  intro i j h
  have hw : BitVec.ofNat k (i.val + 1) = BitVec.ofNat k (j.val + 1) :=
    BitVec.eq_of_getLsbD_eq fun b hb => congrFun h ⟨b, hb⟩
  have hn := congrArg BitVec.toNat hw
  have hi : i.val + 1 < 2 ^ k := by have := i.isLt; lia
  have hj : j.val + 1 < 2 ^ k := by have := j.isLt; lia
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hn
  exact Fin.ext (by lia)

theorem clog_le_of_le (hr : r ≤ 2 ^ (k + k)) : Nat.clog 2 (2 ^ k + r) ≤ 2 * k + 1 := by
  apply Nat.clog_le_of_le_pow
  have h1 : 2 ^ k ≤ 2 ^ (k + k) := Nat.pow_le_pow_right (by decide) (by lia)
  rw [show 2 * k + 1 = (k + k) + 1 by lia, pow_succ]
  lia

/-- The batched counter power, using one shared residue dictionary. -/
theorem batched_counter_power (T r : ℕ) (hr : r ≤ 2 ^ (k + k)) :
    ∃ out : Circuit Boolean.signature (r * (k + k)) (r * (k + k)),
      out.Computes Boolean.interpretation (batchPower T) ∧
        out.size ≤ 40000 * (k + 1) ^ 3 * (2 ^ k + r) := by
  classical
  let queries : State (r * (k + k)) → Fin (r * k) → Bool := fun x i =>
    x (finProdFinEquiv ((finProdFinEquiv.symm i).1, Fin.castAdd k (finProdFinEquiv.symm i).2))
  obtain ⟨lookup, hm, hv, -, hlookup⟩ :=
    SharedLookup.fixed_dictionary (Q := r) (residueKeys k) (residueValues k T)
      (residueKeys_injective k)
  have hdict := Synthesis.circuit (I := Boolean.interpretation) (s := inputs (r * (k + k)))
    lookup queries (fun i => ⟨_, rfl⟩)
  let s1 := inputs (r * (k + k)) ∪
    Set.range fun j x => lookup.eval Boolean.interpretation (queries x) j
  let a := fun (member : Fin r) (x : State (r * (k + k))) => leftWord (block x member)
  let b := fun (member : Fin r) (x : State (r * (k + k))) => rightWord (block x member)
  let rem := fun (member : Fin r) (x : State (r * (k + k))) => word fun bit : Fin k =>
    lookup.eval Boolean.interpretation (queries x) (finProdFinEquiv (member, Fin.natAdd 1 bit))
  have ha (member : Fin r) : wordWires (a member) ⊆ s1 := by
    rintro _ ⟨i, rfl⟩
    left
    refine ⟨finProdFinEquiv (member, Fin.castAdd k i), ?_⟩
    funext x
    simp [a, leftWord, block]
  have hb (member : Fin r) : wordWires (b member) ⊆ s1 := by
    rintro _ ⟨i, rfl⟩
    left
    refine ⟨finProdFinEquiv (member, Fin.natAdd k i), ?_⟩
    funext x
    simp [b, rightWord, block]
  have hrem (member : Fin r) : wordWires (rem member) ⊆ s1 := by
    rintro _ ⟨i, rfl⟩
    right
    exact ⟨finProdFinEquiv (member, Fin.natAdd 1 i), by funext x; simp [rem]⟩
  have hadd (member : Fin r) := synthesis_addResidue s1 (a member) (b member) (rem member)
    (ha member) (hb member) (hrem member)
  have hfam := Synthesis.iUnion (fun member => wordWires fun x =>
      addResidue (a member x) (b member x) (rem member x)) (fun _ => 100 * (k + 1)) hadd
  have hspec (member : Fin r) (x : State (r * (k + k))) :
      addResidue (a member x) (b member x) (rem member x) =
        BitVec.ofNat k (advance (a member x).toNat (b member x).toNat T) := by
    apply addResidue_spec
    intro hpos
    let j : Fin (2 ^ k - 1) := ⟨(a member x).toNat - 1, by have := (a member x).isLt; lia⟩
    have hq : (fun bit => queries x (finProdFinEquiv (member, bit))) =
        fun bit => (a member x).getLsbD bit.val := by
      funext bit
      simp [queries, a, leftWord, block]
    have hkey : residueKeys k j = fun bit => queries x (finProdFinEquiv (member, bit)) := by
      rw [hq]
      funext bit
      simp only [residueKeys, j, Nat.sub_add_cancel hpos, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
    have hrw : rem member x = BitVec.ofNat k (T % (a member x).toNat) := by
      have hbits (bit : Fin k) := hv (queries x) member j hkey bit
      simp only [rem, hbits]
      simp only [residueValues, j, Nat.sub_add_cancel hpos, word_bits]
    rw [hrw, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ((Nat.mod_lt _ hpos).trans (a member x).isLt)]
  have h := (Synthesis.of_subset (I := Boolean.interpretation) (s := inputs (r * (k + k)))
    (t := inputs (r * (k + k))) Set.Subset.rfl).union (hdict.comp hfam)
  have hout : Set.range (fun i x => batchPower (k := k) T x i) ⊆
      inputs (r * (k + k)) ∪ ((Set.range fun j x =>
        lookup.eval Boolean.interpretation (queries x) j) ∪
        ⋃ member, wordWires fun x => addResidue (a member x) (b member x) (rem member x)) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨⟨member, bit⟩, rfl⟩ := finProdFinEquiv.surjective i
    induction bit using Fin.addCases with
    | left i =>
      left
      refine ⟨finProdFinEquiv (member, Fin.castAdd k i), ?_⟩
      funext x
      simp only [batchPower_apply, power_left, block]
    | right i =>
      right; right
      refine Set.mem_iUnion.mpr ⟨member, i, ?_⟩
      funext x
      simp only [hspec, batchPower_apply, power, pack, Fin.append_right, a, b]
  obtain ⟨out, ho, hsize⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  refine ⟨out, fun x => funext fun i => congrFun (ho x) i, hsize.trans ?_⟩
  -- Gate count.
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.zero_add] at hlookup ⊢
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hM : 2 ^ k - 1 + r + 1 = 2 ^ k + r := by lia
  rw [hM] at hlookup
  have hc := clog_le_of_le hr
  have hw : (Nat.clog 2 (2 ^ k + r) + k + (1 + k) + 3) ^ 3 ≤ 125 * (k + 1) ^ 3 := by
    have h5 : Nat.clog 2 (2 ^ k + r) + k + (1 + k) + 3 ≤ 5 * (k + 1) := by lia
    have := Nat.pow_le_pow_left h5 3
    nlinarith
  have hl := hlookup.trans (Nat.mul_le_mul_left (256 * (2 ^ k + r)) hw)
  have hk : k + 1 ≤ (k + 1) ^ 3 := by
    simpa using Nat.pow_le_pow_right (show 1 ≤ k + 1 by lia) (show 1 ≤ 3 by lia)
  have hr' := Nat.mul_le_mul_left (100 * r) hk
  nlinarith [Nat.zero_le (2 ^ k * (k + 1) ^ 3), Nat.zero_le (r * (k + 1) ^ 3)]

/-- One block of a batched circuit computes the single power, with no extra gate:
feed the same state to every block. -/
theorem power_of_batched (T : ℕ) (member : Fin r)
    (c : Circuit Boolean.signature (r * (k + k)) (r * (k + k)))
    (hc : c.Computes Boolean.interpretation (batchPower T)) :
    ∃ out : Circuit Boolean.signature (k + k) (k + k),
      out.Computes Boolean.interpretation (power T) ∧ out.size ≤ c.size := by
  let init : State (k + k) → State (r * (k + k)) := fun y i => y (finProdFinEquiv.symm i).2
  have h := Synthesis.circuit (I := Boolean.interpretation) (s := inputs (k + k)) c init
    (fun i => ⟨_, rfl⟩)
  have hout : Set.range (fun bit y => power (k := k) T y bit) ⊆
      Set.range fun j y => c.eval Boolean.interpretation (init y) j := by
    rintro _ ⟨bit, rfl⟩
    refine ⟨finProdFinEquiv (member, bit), ?_⟩
    funext y
    change c.eval Boolean.interpretation (init y) _ = power T y bit
    rw [hc, batchPower_apply]
    congr 1
    funext b
    simp [block, init]
  obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, fun y => funext fun i => congrFun (ho y) i, hs⟩

/-- If the power is not the identity, every block needs its own output gate. -/
theorem batch_size_ge_of_ne_id (T : ℕ) (hT : power (k := k) T ≠ id)
    (c : Circuit Boolean.signature (r * (k + k)) (r * (k + k)))
    (hc : c.Computes Boolean.interpretation (batchPower T)) : r ≤ c.size := by
  classical
  -- A right-half output bit that `power T` changes somewhere.
  have hex : ∃ y : State (k + k), ∃ bit, power T y bit ≠ y bit := by
    by_contra hn
    push Not at hn
    exact hT (funext fun y => funext fun bit => hn y bit)
  obtain ⟨y, bit, hy⟩ := hex
  have hright : ∃ j : Fin k, bit = Fin.natAdd k j := by
    induction bit using Fin.addCases with
    | left i => exact absurd (power_left T y i) hy
    | right j => exact ⟨j, rfl⟩
  obtain ⟨j, rfl⟩ := hright
  let g : State (k + k) → Bool := fun z => power T z (Fin.natAdd k j)
  let e : BitVec k := BitVec.twoPow k j.val
  have he (i : Fin k) : e.getLsbD i.val = decide (i = j) := by
    simp only [e, BitVec.getLsbD_twoPow]
    by_cases h : i = j
    · simp [h]
    · simp [h, Fin.val_ne_of_ne (Ne.symm h)]
  have hge : g (pack 0 e) = true := by
    change power T (pack 0 e) (Fin.natAdd k j) = true
    rw [power_pack_zero]
    simp only [pack, Fin.append_right, he, decide_true]
  have hgz : g (fun _ => false) = false := by
    change power T (fun _ => false) (Fin.natAdd k j) = false
    rw [← pack_zero_zero, power_pack_zero]
    simp only [pack, Fin.append_right]
    exact BitVec.getLsbD_zero
  -- The input with block `member` equal to `pack 0 e` and all other bits zero.
  let xe : Fin r → State (r * (k + k)) := fun member i =>
    if (finProdFinEquiv.symm i).1 = member then pack 0 e (finProdFinEquiv.symm i).2 else false
  have hxe_same (member : Fin r) : block (xe member) member = pack 0 e := by
    funext b
    simp [xe, block]
  have hxe_other {member other : Fin r} (h : other ≠ member) :
      block (xe member) other = fun _ => false := by
    funext b
    simp [xe, block, h]
  let o : Fin r → Fin (r * (k + k)) := fun member => finProdFinEquiv (member, Fin.natAdd k j)
  have heval (member : Fin r) (x : State (r * (k + k))) :
      c.program.trace Boolean.interpretation x (c.outputs (o member)) = g (block x member) := by
    change c.eval Boolean.interpretation x (o member) = _
    rw [hc, batchPower_apply]
  have hgate (member : Fin r) : ∃ γ, c.outputs (o member) = Wire.gate γ := by
    cases hw : c.outputs (o member) with
    | gate γ => exact ⟨γ, rfl⟩
    | input i =>
      exfalso
      have hi (x : State (r * (k + k))) : x i = g (block x member) := by
        rw [← heval member x, hw, Program.trace_input]
      -- The input wire must be bit `j` of the right half of block `member`.
      have h1 := hi (xe member)
      rw [hxe_same, hge] at h1
      have hi_eq : i = o member := by
        obtain ⟨⟨m', q⟩, rfl⟩ := finProdFinEquiv.surjective i
        simp only [xe, Equiv.symm_apply_apply] at h1
        split_ifs at h1 with hm
        subst hm
        induction q using Fin.addCases with
        | left q => simp [pack] at h1
        | right q =>
          simp only [pack, Fin.append_right, he, decide_eq_true_eq] at h1
          rw [h1]
      -- Then the output is the identity on that bit, contradicting the choice of `y`.
      let xy : State (r * (k + k)) := fun i => y (finProdFinEquiv.symm i).2
      have h2 := hi xy
      have hb : block xy member = y := by funext b; simp [xy, block]
      rw [hb, hi_eq] at h2
      exact hy (by simpa [xy, o, g] using h2.symm)
  choose γ hγ using hgate
  have hinj : Function.Injective γ := by
    intro m m' hmm
    by_contra hne
    have h1 := heval m (xe m)
    have h2 := heval m' (xe m)
    rw [hγ m, hmm, ← hγ m'] at h1
    rw [h1, hxe_same, hxe_other (Ne.symm hne), hge, hgz] at h2
    exact Bool.false_ne_true h2.symm
  simpa using Fintype.card_le_of_injective γ hinj

/-- Both lower bounds: a batched circuit is at least as large as any circuit
for the single power, and, unless the power is the identity, at least `r`. -/
theorem batch_lower_bounds (T : ℕ) (hr : 0 < r)
    (c : Circuit Boolean.signature (r * (k + k)) (r * (k + k)))
    (hc : c.Computes Boolean.interpretation (batchPower T)) :
    (∃ out : Circuit Boolean.signature (k + k) (k + k),
      out.Computes Boolean.interpretation (power T) ∧ out.size ≤ c.size) ∧
    (power (k := k) T ≠ id → r ≤ c.size) :=
  ⟨power_of_batched T ⟨0, hr⟩ c hc, fun h => batch_size_ge_of_ne_id T h c hc⟩

/-- For the hard exponents of `exists_hard_counter_power`, the batched cost lies
between `max (lowerBudget k + 1) r` and `40000*(k+1)^3*(2^k+r)`, for every
`1 ≤ r ≤ 2^(2k)`. -/
theorem batched_hard_counter_power (k : ℕ) (hk : 64 ≤ k) :
    ∃ T < period k, ∀ r, 0 < r → r ≤ 2 ^ (k + k) →
      (∃ out : Circuit Boolean.signature (r * (k + k)) (r * (k + k)),
        out.Computes Boolean.interpretation (batchPower T) ∧
          out.size ≤ 40000 * (k + 1) ^ 3 * (2 ^ k + r)) ∧
      ∀ c : Circuit Boolean.signature (r * (k + k)) (r * (k + k)),
        c.Computes Boolean.interpretation (batchPower T) →
          lowerBudget k < c.size ∧ r ≤ c.size := by
  obtain ⟨T, hT, hh⟩ := exists_hard_counter_power k hk
  refine ⟨T, hT, fun r hr hrN => ⟨batched_counter_power T r hrN, fun c hc => ?_⟩⟩
  obtain ⟨out, ho, hs⟩ := power_of_batched T ⟨0, hr⟩ c hc
  refine ⟨(hh out ho).trans_le hs, batch_size_ge_of_ne_id T ?_ c hc⟩
  intro hid
  have h0 := hh (Circuit.id Boolean.signature (k + k)) (fun x => by rw [hid]; rfl)
  simp at h0

end IteratedFunctions.ModulusCounter
