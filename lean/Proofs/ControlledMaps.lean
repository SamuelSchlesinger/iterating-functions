/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.VariableTime
public import Proofs.Selection

/-!
# Autonomous controllers and bounded-cost payload maps

The controller evolves independently of the payload. For each initial
controller, iteration composes only payload maps. The semantic result works
in arbitrary universes; the Boolean circuit selects among all controller
values and charges every candidate payload circuit and every selector bit.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
open scoped BigOperators

universe u v
variable {α : Type u} {β : Type v}

/-- An autonomous controller chooses the transformation of a payload. -/
def controlledMap (g : α → α) (a : α → β → β) (x : α × β) : α × β :=
  (g x.1, a x.1 x.2)

/-- The composite payload map selected by an initial controller and fixed time. -/
def controlledPayload (g : α → α) (a : α → β → β) : ℕ → α → β → β
  | 0, _ => id
  | T + 1, u => a (g^[T] u) ∘ controlledPayload g a T u

theorem controlledMap_iterate (g : α → α) (a : α → β → β)
    (T : ℕ) (u : α) (v : β) :
    (controlledMap g a)^[T] (u, v) = (g^[T] u, controlledPayload g a T u v) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    rfl

/-- Composition closure suffices semantically, without any finite-state hypothesis. -/
theorem controlledPayload_mem (g : α → α) (a : α → β → β)
    (family : Set (β → β)) (hid : id ∈ family)
    (hcomp : ∀ f ∈ family, ∀ h ∈ family, f ∘ h ∈ family)
    (ha : ∀ u, a u ∈ family) (T : ℕ) (u : α) :
    controlledPayload g a T u ∈ family := by
  induction T with
  | zero => exact hid
  | succ T ih => exact hcomp _ (ha _) _ ih

variable {q p : ℕ}

/-- Flat Boolean encoding of controller followed by payload. -/
def controlledBits (g : State q → State q) (a : State q → State p → State p)
    (x : State (q + p)) : State (q + p) :=
  Fin.append (g (fun i => x (Fin.castAdd p i)))
    (a (fun i => x (Fin.castAdd p i)) (fun i => x (Fin.natAdd q i)))

@[simp] theorem controlledBits_append (g : State q → State q)
    (a : State q → State p → State p) (u : State q) (v : State p) :
    controlledBits g a (Fin.append u v) = Fin.append (g u) (a u v) := by
  simp [controlledBits]

theorem controlledBits_iterate (g : State q → State q)
    (a : State q → State p → State p) (T : ℕ) (x : State (q + p)) :
    (controlledBits g a)^[T] x =
      controlledBits (g^[T]) (controlledPayload g a T) x := by
  induction T with
  | zero => simp [controlledBits, controlledPayload, Fin.append_castAdd_natAdd]
  | succ T ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [controlledBits, Fin.append_left, Fin.append_right, controlledPayload,
      Function.comp_apply, Function.iterate_succ_apply']

/-- Selecting among small payload circuits has overhead linear in controller and
output width per controller value. No circuit for `g` is assumed or needed. -/
theorem controlled_circuit (g : State q → State q) (a : State q → State p → State p)
    (K : ℕ) (ha : ∀ u, ∃ c : Circuit Boolean.signature p p,
      c.Computes Boolean.interpretation (a u) ∧ c.size ≤ K) :
    ∃ c : Circuit Boolean.signature (q + p) (q + p),
      c.Computes Boolean.interpretation (controlledBits g a) ∧
      c.size ≤ 2 + 2 ^ q * (K + 6 * q + 4 * p + 1) := by
  classical
  let e : Fin (2 ^ q) ≃ State q :=
    (Fintype.equivFinOfCardEq (by simp [State])).symm
  let u := fun x : State (q + p) => fun i => x (Fin.castAdd p i)
  let v := fun x : State (q + p) => fun i => x (Fin.natAdd q i)
  let flags := fun j x => decide (u x = e j)
  let records := fun j x => Fin.append (g (e j)) (a (e j) (v x))
  let constants : Set (State (q + p) → Bool) := {fun _ => false, fun _ => true}
  let src := inputs (q + p) ∪ constants
  have hc (b : Bool) : (fun _ : State (q + p) => b) ∈ src := by
    cases b <;> simp [src, constants]
  have hconst : Synthesis Boolean.interpretation (inputs (q + p)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have hflag (j : Fin (2 ^ q)) :
      Synthesis Boolean.interpretation src {flags j} (2 * q + 1) := by
    have h := synthesis_word_eq_const src (fun x => word (u x))
      (fun i => by simpa [u] using (show (fun x : State (q + p) => x (Fin.castAdd p i))
        ∈ src from Or.inl ⟨_, rfl⟩)) (word (e j))
    have he (x : State (q + p)) : word (u x) = word (e j) ↔ u x = e j := by
      constructor
      · intro hh
        funext i
        simpa only [word_bit] using congrArg (fun w : BitVec q => w.getLsbD i.val) hh
      · exact congrArg word
    simpa only [he] using h
  have hrecord (j : Fin (2 ^ q)) :
      Synthesis Boolean.interpretation src (wires (records j)) K := by
    obtain ⟨c, hc', hs⟩ := ha (e j)
    have h := Synthesis.circuit (I := Boolean.interpretation) (s := src) c v
      (fun i => Or.inl ⟨_, rfl⟩)
    have heval : c.eval Boolean.interpretation = a (e j) := funext hc'
    rw [heval] at h
    have hav : wires (records j) ⊆ src ∪ wires (fun x => a (e j) (v x)) := by
      rintro _ ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i =>
        apply Or.inl
        simpa only [records, Fin.append_left] using hc (g (e j) i)
      | right i =>
        apply Or.inr
        exact ⟨i, by simp only [records, Fin.append_right]⟩
    exact (h.trans (Synthesis.of_subset hav)).mono Set.Subset.rfl Set.Subset.rfl
      (by simpa using hs)
  have hall := Synthesis.iUnion (fun j => {flags j} ∪ wires (records j))
    (fun _ => (2 * q + 1) + K) (fun j => (hflag j).union (hrecord j))
  let all := ⋃ j, {flags j} ∪ wires (records j)
  have hselect := synthesis_chooseRecord (src ∪ all)
    (fun x j => flags j x) (fun x j => records j x) (fun _ _ => false)
    (fun j => Or.inr (Set.mem_iUnion.mpr ⟨j, Or.inl rfl⟩))
    (fun j bit => Or.inr (Set.mem_iUnion.mpr ⟨j, Or.inr ⟨bit, rfl⟩⟩))
    (fun _ => Or.inl (hc false))
  have he (x : State (q + p)) :
      chooseRecord (fun j => flags j x) (fun j => records j x) (fun _ => false) (2 ^ q) =
        controlledBits g a x := by
    obtain ⟨j, _, hj, hout⟩ := chooseRecord_spec (fun j => flags j x)
      (fun j => records j x) (fun _ => false) (2 ^ q)
      ⟨e.symm (u x), (e.symm (u x)).isLt, by simp [flags]⟩
    have hj' : u x = e j := of_decide_eq_true hj
    rw [hout]
    change Fin.append (g (e j)) (a (e j) (v x)) = Fin.append (g (u x)) (a (u x) (v x))
    rw [hj']
  simp only [he] at hselect
  obtain ⟨c, hc', hs⟩ := (hconst.trans (hall.trans hselect)).exists_circuit_outputs
  refine ⟨c, hc', hs.trans ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- A composition-closed payload family with a uniform gate bound can be powered
at a cost exponential only in the controller width. -/
theorem controlled_family_power (g : State q → State q)
    (a : State q → State p → State p) (family : Set (State p → State p))
    (hid : id ∈ family)
    (hcomp : ∀ f ∈ family, ∀ h ∈ family, f ∘ h ∈ family)
    (ha : ∀ u, a u ∈ family) (K : ℕ)
    (hK : ∀ f ∈ family, ∃ c : Circuit Boolean.signature p p,
      c.Computes Boolean.interpretation f ∧ c.size ≤ K) (T : ℕ) :
    ∃ c : Circuit Boolean.signature (q + p) (q + p),
      c.Computes Boolean.interpretation ((controlledBits g a)^[T]) ∧
      c.size ≤ 2 + 2 ^ q * (K + 6 * q + 4 * p + 1) := by
  obtain ⟨c, hc, hs⟩ := controlled_circuit (g^[T]) (controlledPayload g a T) K
    (fun u => hK _ (controlledPayload_mem g a family hid hcomp ha T u))
  exact ⟨c, fun x => (hc x).trans (controlledBits_iterate g a T x).symm, hs⟩

/-- The same closed family supports a live exponent by conditional binary powers. -/
theorem controlled_family_variable_time (g : State q → State q)
    (a : State q → State p → State p) (family : Set (State p → State p))
    (hid : id ∈ family)
    (hcomp : ∀ f ∈ family, ∀ h ∈ family, f ∘ h ∈ family)
    (ha : ∀ u, a u ∈ family) (K : ℕ)
    (hK : ∀ f ∈ family, ∃ c : Circuit Boolean.signature p p,
      c.Computes Boolean.interpretation f ∧ c.size ≤ K) (m : ℕ) :
    ∃ c : Circuit Boolean.signature ((q + p) + m) (q + p),
      c.Computes Boolean.interpretation (fun x =>
        (controlledBits g a)^[binaryValue (fun j => x (Fin.natAdd (q + p) j))]
          (fun i => x (Fin.castAdd m i))) ∧
      c.size ≤ m * (2 + 2 ^ q * (K + 6 * q + 4 * p + 1) + 4 * (q + p)) :=
  binary_powering_circuit _ _ m (controlled_family_power g a family hid hcomp ha K hK)

end IteratedFunctions
