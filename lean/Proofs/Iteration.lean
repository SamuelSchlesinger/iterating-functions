/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Synthesis
public import Complexitylib.Algebraic.Iteration
public import Mathlib.Logic.Function.Iterate

/-!
# Iteration and retained orbit prefixes

The circuit iteration is the construction from the user's circuit library,
on CSLib's circuit type. Its semantics agree with Mathlib's function iteration.
The retained-prefix bound counts each transition once, sharing all states
with subsequent sorting and selection circuits.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

universe u v
variable {α : Type u}

/-- The circuit library and Mathlib use extensionally equal notions of iteration. -/
theorem iterateFunction_eq (f : α → α) (t : ℕ) : Circuit.iterateFunction f t = f^[t] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x
    simp only [Circuit.iterateFunction, ih, Function.iterate_succ_apply']

variable {σ : Signature.{v}} {U : Type u} {n m : ℕ}

/-- Exact evaluation and size of the direct unrolling, over any signature and carrier. -/
theorem unroll_spec (c : Circuit σ m m) (I : Interpretation σ U) (T : ℕ) :
    (c.iterate T).Computes I (c.eval I)^[T] ∧ (c.iterate T).size = T * c.size := by
  refine ⟨fun x => ?_, Circuit.size_iterate c T⟩
  rw [Circuit.eval_iterate, iterateFunction_eq]

/-- Retain an entire orbit prefix with only one circuit copy per transition. -/
theorem synthesis_orbit (I : Interpretation σ U) (c : Circuit σ m m)
    (s : Set ((Fin n → U) → U)) (init : (Fin n → U) → Fin m → U)
    (hinit : ∀ bit, (fun x => init x bit) ∈ s) (t : ℕ) :
    Synthesis I s
      (Synthesis.stages (fun j => Set.range fun bit x => (c.eval I)^[j] (init x) bit) t)
      (t * c.size) := by
  let q := fun j => Set.range fun bit x => (c.eval I)^[j] (init x) bit
  refine Synthesis.steps q c.size t ?_ ?_
  · rintro _ ⟨bit, rfl⟩
    exact hinit bit
  · intro j _
    have hs := Synthesis.circuit (I := I) (s := s ∪ Synthesis.stages q j) c
      (fun x => (c.eval I)^[j] (init x))
      (fun bit => Or.inr (Synthesis.mem_stages q j ⟨bit, rfl⟩))
    simpa only [q, Function.iterate_succ_apply'] using hs

end IteratedFunctions
