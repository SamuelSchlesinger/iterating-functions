/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Synthesis
public import Cslib.Computability.Circuit.Composition
public import Mathlib.Order.PiLex
public import Mathlib.Data.Bool.Basic

/-!
# Shared circuit constructions

These lemmas use CSLib's simultaneous synthesis relation. In particular, a
comparison result can feed every bit of a conditional swap without being rebuilt.
-/

@[expose] public section

namespace Cslib.Circuits.Synthesis

universe u v
variable {σ : Signature.{v}} {U : Type u} {n k m : ℕ}
variable {I : Interpretation σ U} {s : Set ((Fin n → U) → U)}

/-- Apply an existing multioutput circuit to functions already available as wires. -/
theorem circuit (c : Circuit σ k m) (args : (Fin n → U) → Fin k → U)
    (hargs : ∀ i, (fun x => args x i) ∈ s) :
    Synthesis I s (Set.range fun j x => c.eval I (args x) j) c.size := by
  classical
  intro g p hp
  choose wires hw using fun i => mem_available.mp (hp (hargs i))
  refine ⟨g + c.size, p.append wires c.program, le_rfl, ?_, ?_⟩
  · intro f hf
    obtain ⟨w, hw'⟩ := mem_available.mp hf
    exact mem_available.mpr ⟨w.castAdd c.size, fun x =>
      (Program.trace_append_castAdd p wires I x c.program w).trans (hw' x)⟩
  · rintro _ ⟨j, rfl⟩
    refine mem_available.mpr ⟨Program.appendedWire wires (c.outputs j), fun x => ?_⟩
    rw [Program.trace_append_appendedWire]
    change c.eval I (fun i => p.trace I x (wires i)) j = _
    simp only [hw]

/-- The values retained through stage `t` of a straight-line construction. -/
def stages (q : ℕ → Set ((Fin n → U) → U)) (t : ℕ) : Set ((Fin n → U) → U) :=
  ⋃ j ∈ Finset.range (t + 1), q j

@[simp] theorem stages_zero (q : ℕ → Set ((Fin n → U) → U)) : stages q 0 = q 0 := by
  simp [stages]

theorem stages_succ (q : ℕ → Set ((Fin n → U) → U)) (t : ℕ) :
    stages q (t + 1) = stages q t ∪ q (t + 1) := by
  simp [stages, Finset.range_add_one, Set.union_comm]

theorem mem_stages (q : ℕ → Set ((Fin n → U) → U)) (t : ℕ) : q t ⊆ stages q t := by
  intro f hf
  exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by lia), hf⟩⟩

/-- A bounded sequence of constructions adds the costs and retains every stage. -/
theorem steps (q : ℕ → Set ((Fin n → U) → U)) (C t : ℕ) (hzero : q 0 ⊆ s)
    (hstep : ∀ j < t, Synthesis I (s ∪ stages q j) (q (j + 1)) C) :
    Synthesis I s (stages q t) (t * C) := by
  induction t with
  | zero => simpa using of_subset hzero
  | succ t ih =>
    have h := (ih (fun j hj => hstep j (by lia))).comp (hstep t (by lia))
    simpa only [stages_succ, Nat.succ_mul] using h

variable {s : Set ((Fin n → Bool) → Bool)}
variable {f g a b : (Fin n → Bool) → Bool}

/-- A Boolean equality test using five De Morgan gates. -/
theorem bool_eq (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis Boolean.interpretation s {fun x => decide (f x = g x)} 5 := by
  have h := ((of_mem hf).and (of_mem hg)).or
    ((of_mem hf).not.and (of_mem hg).not)
  convert h using 1
  congr 1
  funext x
  cases f x <;> cases g x <;> rfl

/-- One shared control bit selects one output bit in four gates. -/
theorem mux (hf : f ∈ s) (ha : a ∈ s) (hb : b ∈ s) :
    Synthesis Boolean.interpretation s {fun x => if f x then a x else b x} 4 := by
  have h := ((of_mem hf).and (of_mem ha)).or ((of_mem hf).not.and (of_mem hb))
  convert h using 1
  congr 1
  funext x
  cases f x <;> simp

end Cslib.Circuits.Synthesis

namespace IteratedFunctions

open Cslib.Circuits

/-- Lexicographic comparison, from the first coordinate to the last. -/
def lexLess : {w : ℕ} → (Fin w → Bool) → (Fin w → Bool) → Bool
  | 0, _, _ => false
  | w + 1, a, b => (!a 0 && b 0) ||
      (decide (a 0 = b 0) && lexLess (fun i : Fin w => a i.succ) (fun i => b i.succ))

/-- The recursive comparison agrees with the lexicographic order used by the sorter. -/
theorem lexLess_eq_true_iff {w : ℕ} (a b : Fin w → Bool) :
    lexLess a b = true ↔ toLex a < toLex b := by
  induction w with
  | zero =>
    change false = true ↔ ∃ i : Fin 0, _
    simp
  | succ w ih =>
    change _ ↔ ∃ i : Fin (w + 1), (∀ j < i, a j = b j) ∧ a i < b i
    rw [lexLess]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, ih]
    constructor
    · rintro (⟨ha, hb⟩ | ⟨hab, i, hbefore, hlt⟩)
      · exact ⟨0, fun j hj => (Fin.not_lt_zero j hj).elim, by simp [ha, hb]⟩
      · refine ⟨i.succ, ?_, hlt⟩
        intro j hj
        induction j using Fin.cases with
        | zero => exact hab
        | succ j => exact hbefore j (Fin.succ_lt_succ_iff.mp hj)
    · rintro ⟨i, hbefore, hlt⟩
      induction i using Fin.cases with
      | zero => exact Or.inl (Bool.lt_iff.mp hlt)
      | succ i => exact Or.inr ⟨hbefore 0 (Fin.succ_pos i), i,
          fun j hj => hbefore j.succ (Fin.succ_lt_succ_iff.mpr hj), hlt⟩

/-- Compare two available words with a gate budget linear in their width. -/
theorem synthesis_lexLess {n w : ℕ} (s : Set ((Fin n → Bool) → Bool))
    (a b : (Fin n → Bool) → Fin w → Bool)
    (ha : ∀ i, (fun x => a x i) ∈ s) (hb : ∀ i, (fun x => b x i) ∈ s) :
    Synthesis Boolean.interpretation s {fun x => lexLess (a x) (b x)} (9 * w + 1) := by
  induction w with
  | zero => exact Synthesis.const false
  | succ w ih =>
    have tail := ih (fun x i => a x i.succ) (fun x i => b x i.succ)
      (fun i => ha i.succ) (fun i => hb i.succ)
    have eq := Synthesis.bool_eq (ha 0) (hb 0)
    have lt := (Synthesis.of_mem (ha 0)).not.and (Synthesis.of_mem (hb 0))
    have out := lt.or (eq.and tail)
    convert out using 1
    · rfl
    · lia

end IteratedFunctions
