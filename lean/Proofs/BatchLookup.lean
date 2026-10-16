/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Sorting
public import Proofs.RecordCircuits
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchOrCircuit
public import Complexitylib.Algebraic.Basis.DeMorgan.NativeCost
public import Complexitylib.Algebraic.Basis.DeMorgan.CSLib

/-! # Shared batched lookup

The Circuit library supplies the two-sort routing semantics, including absent
keys and repeated requests. We replace its sorters by the shared-comparison
circuits to retain a cubic width/depth factor, and charge native Boolean gates.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits Algebraic
open Algebraic.MassProduction Algebraic.MassProduction.Sorting
open Algebraic.MassProduction.RoutingMetadata
open Algebraic.MassProduction.CanonicalMetadataRouting
open Algebraic.MassProduction.Nonuniform

namespace SharedLookup

def native {n m : ℕ} (c : Circuit DeMorgan.signature n m) : Circuit Boolean.signature n m :=
  DeMorgan.toBoolean.compile (DeMorgan.withSharedConstants c)

theorem native_eval {n m : ℕ} (c : Circuit DeMorgan.signature n m) (x : Fin n → Bool) :
    (native c).eval Boolean.interpretation x = c.eval DeMorgan.interpretation x := by
  rw [native, Realization.compile_eval, DeMorgan.withSharedConstants_eval]

theorem native_size {n m : ℕ} (c : Circuit DeMorgan.signature n m) :
    (native c).size ≤ c.cost DeMorgan.standardCost + 2 := by
  exact (DeMorgan.toBoolean_size_le _).trans_eq (DeMorgan.withSharedConstants_size c)

noncomputable def sortBy {k r : ℕ} (order : Equiv.Perm (Fin r)) (hk : k ≤ r) (d : ℕ) :=
  ((SharedSorting.sort hk d true).mapInputs (recordBitEquiv d r order)).mapOutputs
    (recordBitEquiv d r order.symm)

theorem sortBy_eval {k r : ℕ} (order : Equiv.Perm (Fin r)) (hk : k ≤ r) (d : ℕ)
    (x : Fin (networkBits d r) → Bool) :
    (sortBy order hk d).eval Boolean.interpretation x = bitonicSortByBits order hk d true x := by
  rw [sortBy, Circuit.eval_mapOutputs, Circuit.eval_mapInputs, SharedSorting.sort_eval]
  rfl

theorem sortBy_size {k r : ℕ} (order : Equiv.Perm (Fin r)) (hk : k ≤ r) (d : ℕ) :
    (sortBy order hk d).size ≤ 18 * d ^ 2 * 2 ^ d * (r + 1) := by
  simpa only [sortBy, Circuit.size_mapOutputs, Circuit.size_mapInputs] using
    SharedSorting.sort_size hk d true

noncomputable def canonical (d k m v : ℕ) :=
  (sortBy (metadataOrderBitOrder k m v) (metadataOrderKeyFits k m v) d).comp
    (native (CanonicalRouting.complementRoutingTagsCircuit d k (m + v)))

theorem canonical_eval (d k m v : ℕ)
    (x : Fin (networkBits d (recordWidth k m v)) → Bool) :
    (canonical d k m v).eval Boolean.interpretation x = canonicalSortBits d k m v x := by
  rw [canonical, Circuit.eval_comp, sortBy_eval, native_eval,
    CanonicalRouting.complementRoutingTagsCircuit_eval]
  rfl

noncomputable def router (d k m v : ℕ) :=
  (canonical d k m v).comp ((native (Broadcast.recordsCircuit d k m v)).comp
    (SharedSorting.sort (Routing.keyAndTagFitsRecord k (m + v)) d true))

theorem router_eval (d k m v : ℕ)
    (x : Fin (networkBits d (recordWidth k m v)) → Bool) :
    (router d k m v).eval Boolean.interpretation x =
      (Broadcast.routingCircuit d k m v).eval DeMorgan.interpretation x := by
  simp only [router, Circuit.eval_comp, canonical_eval, native_eval, SharedSorting.sort_eval,
    Broadcast.routingCircuit, Broadcast.sortedCircuit, canonicalSortCircuit_eval,
    bitonicSortCircuit_eval]

theorem router_size (d k m v : ℕ) :
    (router d k m v).size ≤
      36 * d ^ 2 * 2 ^ d * (recordWidth k m v + 1) +
        2 ^ d * (v * (6 * k + 4)) + 2 ^ d * recordWidth k m v + 4 := by
  have h1 := SharedSorting.sort_size (Routing.keyAndTagFitsRecord k (m + v)) d true
  have h2 := (native_size (Broadcast.recordsCircuit d k m v)).trans
    (Nat.add_le_add_right Broadcast.recordsCircuit_cost_le 2)
  have h3 := (native_size (CanonicalRouting.complementRoutingTagsCircuit d k (m + v))).trans
    (Nat.add_le_add_right CanonicalRouting.complementRoutingTagsCircuit_cost_le 2)
  have h4 := sortBy_size (metadataOrderBitOrder k m v) (metadataOrderKeyFits k m v) d
  simp only [router, canonical, Circuit.size_comp]
  rw [networkRecords_eq_two_pow] at h2
  simp only [networkBits, networkRecords_eq_two_pow] at h3
  change _ ≤ 18 * d ^ 2 * 2 ^ d * (recordWidth k m v + 1) at h1
  change _ ≤ 2 ^ d * recordWidth k m v + 2 at h3
  exact (Nat.add_le_add (Nat.add_le_add h1 h2) (Nat.add_le_add h3 h4)).trans_eq (by ring)

/-- Cubic overhead, with linear dependence on the padded record count. -/
theorem router_size_cubic (d k v : ℕ) :
    (router d k (d + 1) v).size ≤ 64 * 2 ^ d * (d + k + v + 3) ^ 3 + 4 := by
  let W := d + k + v + 3
  have hW : 1 ≤ W := by dsimp [W]; lia
  have hd : d ≤ W := by dsimp [W]; lia
  have hk : k ≤ W := by dsimp [W]; lia
  have hv : v ≤ W := by dsimp [W]; lia
  have hw : recordWidth k (d + 1) v + 1 = W := by
    unfold recordWidth Routing.recordWidth W
    lia
  have h1 : 36 * d ^ 2 * 2 ^ d * (recordWidth k (d + 1) v + 1) ≤
      36 * 2 ^ d * W ^ 3 := by
    have hdsq : d ^ 2 ≤ W ^ 2 := by gcongr
    have hprod := Nat.mul_le_mul_right (36 * 2 ^ d * W) hdsq
    rw [hw]
    nlinarith
  have h2 : v * (6 * k + 4) ≤ 10 * W ^ 2 := by nlinarith
  have h3 : W ^ 2 ≤ W ^ 3 := Nat.pow_le_pow_right hW (by decide)
  have h4 : W ≤ W ^ 3 := by simpa using Nat.pow_le_pow_right hW (by decide : 1 ≤ 3)
  have hs := router_size d k (d + 1) v
  have h5 := Nat.mul_le_mul_left (2 ^ d)
    (show recordWidth k (d + 1) v ≤ W ^ 3 by lia)
  change _ ≤ 64 * 2 ^ d * W ^ 3 + 4
  nlinarith [Nat.mul_le_mul_left (2 ^ d) h2,
    Nat.mul_le_mul_left (10 * 2 ^ d) h3,
    Nat.mul_le_mul_left (2 ^ d) h4]

noncomputable def circuit {inputs sources requests padding depth keyWidth valueWidth : ℕ}
    (keys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (values : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (queries : Fin requests → Fin keyWidth → DeMorgan.Wiring inputs)
    (hR : sources + requests + padding = networkRecords depth) :=
  ((router depth keyWidth (depth + 1) valueWidth).comp
    (native (DeMorgan.Wiring.circuit (BatchOr.layoutWiring keys values queries hR)))).mapOutputs
      (BatchOr.outputIndex hR)

theorem circuit_eval_iff {inputs sources requests padding depth keyWidth valueWidth : ℕ}
    (keys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (values : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (queries : Fin requests → Fin keyWidth → DeMorgan.Wiring inputs)
    (hR : sources + requests + padding = networkRecords depth)
    (x : Fin inputs → Bool) (q : Fin requests) (bit : Fin valueWidth) :
    (circuit keys values queries hR).eval Boolean.interpretation x
        (finProdFinEquiv (q, bit)) = true ↔
      ∃ source, (fun i => (keys source i).eval x) = (fun i => (queries q i).eval x) ∧
        (values source bit).eval x = true := by
  have he : (circuit keys values queries hR).eval Boolean.interpretation x =
      (BatchOr.circuit keys values queries hR).eval DeMorgan.interpretation x := by
    simp only [circuit, BatchOr.circuit, Circuit.eval_mapOutputs, Circuit.eval_comp,
      router_eval, native_eval]
  rw [he]
  exact BatchOr.circuit_eval_iff keys values queries hR x q bit

theorem circuit_size {inputs sources requests padding depth keyWidth valueWidth : ℕ}
    (keys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (values : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (queries : Fin requests → Fin keyWidth → DeMorgan.Wiring inputs)
    (hR : sources + requests + padding = networkRecords depth) :
    (circuit keys values queries hR).size ≤
      64 * 2 ^ depth * (depth + keyWidth + valueWidth + 3) ^ 3 + 6 := by
  have hinit := native_size (DeMorgan.Wiring.circuit (BatchOr.layoutWiring keys values queries hR))
  simp only [DeMorgan.Wiring.circuit_cost, Nat.zero_add] at hinit
  have hs := router_size_cubic depth keyWidth valueWidth
  simp only [circuit, Circuit.size_mapOutputs, Circuit.size_comp]
  lia

/-- Batched OR with arbitrary keys and missing entries; all outputs retain query order. -/
theorem exists_batch_or {inputs sources requests keyWidth valueWidth : ℕ}
    (keys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (values : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (queries : Fin requests → Fin keyWidth → DeMorgan.Wiring inputs) :
    ∃ out : Circuit Boolean.signature inputs (requests * valueWidth),
      (∀ x q bit, out.eval Boolean.interpretation x (finProdFinEquiv (q, bit)) = true ↔
        ∃ source, (fun i => (keys source i).eval x) = (fun i => (queries q i).eval x) ∧
          (values source bit).eval x = true) ∧
      out.size ≤ 256 * (sources + requests + 1) *
        (Nat.clog 2 (sources + requests + 1) + keyWidth + valueWidth + 3) ^ 3 := by
  let R := sources + requests + 1
  let d := Nat.clog 2 R
  have hR : sources + requests ≤ 2 ^ d := by
    have := Nat.le_pow_clog (by decide : 1 < 2) R
    dsimp [R, d] at *
    lia
  let padding := 2 ^ d - (sources + requests)
  have he : sources + requests + padding = networkRecords d := by
    rw [networkRecords_eq_two_pow]
    dsimp [padding]
    lia
  refine ⟨circuit keys values queries he, circuit_eval_iff keys values queries he, ?_⟩
  have hs := circuit_size keys values queries he
  have hpow : 2 ^ d ≤ 2 * R := by
    by_cases hd : d = 0
    · rw [hd]
      dsimp [R]
      lia
    · have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
        (show 1 < R by
          by_contra hr
          have : R = 1 := by dsimp [R] at *; lia
          simp [d, this] at hd)
      have hsucc : 2 ^ d = 2 ^ (d - 1) * 2 := by
        rw [← Nat.pow_succ, show (d - 1).succ = d by lia]
      rw [hsucc]
      change 2 ^ (d - 1) < R at hp
      lia
  let W := d + keyWidth + valueWidth + 3
  have hw : 1 ≤ W ^ 3 := by
    have : 0 < W ^ 3 := by dsimp [W]; positivity
    lia
  have hrec : 1 ≤ R := by dsimp [R]; lia
  have hmul := Nat.mul_le_mul_right (64 * W ^ 3) hpow
  change _ ≤ 256 * R * W ^ 3
  change _ ≤ 64 * 2 ^ d * W ^ 3 + 6 at hs
  nlinarith [Nat.mul_le_mul hrec hw]

/-- Fixed dictionaries are batched ORs with unique source keys. A leading true
payload bit gives the match flag, so absent queries have a zero record. -/
theorem fixed_dictionary {M Q k v : ℕ}
    (keys : Fin M → Fin k → Bool) (values : Fin M → Fin v → Bool)
    (hkeys : Function.Injective keys) :
    ∃ out : Circuit Boolean.signature (Q * k) (Q * (1 + v)),
      (∀ x q, out.eval Boolean.interpretation x (finProdFinEquiv (q, 0)) = true ↔
        ∃ source, keys source = fun bit => x (finProdFinEquiv (q, bit))) ∧
      (∀ x q source, keys source = (fun bit => x (finProdFinEquiv (q, bit))) →
        ∀ bit, out.eval Boolean.interpretation x
          (finProdFinEquiv (q, Fin.natAdd 1 bit)) = values source bit) ∧
      (∀ x q, (¬ ∃ source, keys source = fun bit => x (finProdFinEquiv (q, bit))) →
        ∀ bit, out.eval Boolean.interpretation x (finProdFinEquiv (q, bit)) = false) ∧
      out.size ≤ 256 * (M + Q + 1) *
        (Nat.clog 2 (M + Q + 1) + k + (1 + v) + 3) ^ 3 := by
  let keyW : Fin M → Fin k → DeMorgan.Wiring (Q * k) :=
    fun source bit => DeMorgan.Wiring.constant (keys source bit)
  let valW : Fin M → Fin (1 + v) → DeMorgan.Wiring (Q * k) :=
    fun source bit => DeMorgan.Wiring.constant
    (Fin.append (fun _ : Fin 1 => true) (values source) bit)
  let queryW : Fin Q → Fin k → DeMorgan.Wiring (Q * k) :=
    fun q bit => DeMorgan.Wiring.input (finProdFinEquiv (q, bit))
  obtain ⟨out, he, hs⟩ := exists_batch_or keyW valW queryW
  refine ⟨out, ?_, ?_, ?_, hs⟩
  · intro x q
    have hz : (Fin.castAdd v (0 : Fin 1) : Fin (1 + v)) = 0 := by ext; simp
    have h := he x q (Fin.castAdd v (0 : Fin 1))
    simp only [keyW, valW, queryW, DeMorgan.Wiring.eval_constant,
      DeMorgan.Wiring.eval_input, Fin.append_left, and_true] at h
    rwa [hz] at h
  · intro x q source hsource bit
    apply Bool.eq_iff_iff.mpr
    rw [he]
    simp only [keyW, valW, queryW, DeMorgan.Wiring.eval_constant,
      DeMorgan.Wiring.eval_input, Fin.append_right]
    constructor
    · rintro ⟨s, hmatch, hv⟩
      have : s = source := hkeys (hmatch.trans hsource.symm)
      simpa [this] using hv
    · intro hv
      exact ⟨source, hsource, hv⟩
  · intro x q hnone bit
    apply Bool.eq_false_iff.mpr
    intro htrue
    obtain ⟨source, hm, _⟩ := (he x q bit).mp htrue
    exact hnone ⟨source, hm⟩

end SharedLookup

end IteratedFunctions
