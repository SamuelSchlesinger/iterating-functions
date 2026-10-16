/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Statement
public import Proofs.Words
public import Proofs.Sorting
public import Proofs.Collisions
public import Proofs.Selection

/-!
# Records for the fixed-power construction

The key consists of a padding flag and a state. Payload fields distinguish
checkpoint records from prefix records, and store either a shifted state or a
prefix index. Padding is explicit and excluded by the collision predicate.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits Algebraic.MassProduction.Sorting

variable {n w : ℕ}

/-- A complete record carried through the sorting network. -/
@[ext] structure Record (n w : ℕ) where
  padding : Bool
  state : State n
  checkpoint : Bool
  index : BitVec w
  payload : State n
  deriving DecidableEq

namespace Record

/-- Key and metadata widths, with every payload bit charged. -/
def width (n w : ℕ) : ℕ := (n + 1) + (w + n + 1)

def key (r : Record n w) : Lex (Fin (n + 1) → Bool) := toLex (Fin.cons r.padding r.state)

def encode (r : Record n w) : Fin (width n w) → Bool :=
  Fin.append (Fin.cons r.padding r.state)
    (Fin.cons r.checkpoint (Fin.append (fun i => r.index.getLsbD i.val) r.payload))

def decode (bits : Fin (width n w) → Bool) : Record n w where
  padding := bits (Fin.castAdd (w + n + 1) 0)
  state i := bits (Fin.castAdd (w + n + 1) i.succ)
  checkpoint := bits (Fin.natAdd (n + 1) 0)
  index := word (fun i => bits (Fin.natAdd (n + 1) (Fin.castAdd n i).succ))
  payload i := bits (Fin.natAdd (n + 1) (Fin.natAdd w i).succ)

@[simp] theorem decode_encode (r : Record n w) : decode (encode r) = r := by
  ext <;> simp [decode, encode, Fin.cons]

@[simp] theorem encode_decode (bits : Fin (width n w) → Bool) : encode (decode bits) = bits := by
  funext i
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.cases with
    | zero => simp [encode, decode]
    | succ i => simp [encode, decode]
  | right i =>
    induction i using Fin.cases with
    | zero => simp [encode, decode]
    | succ i =>
      induction i using Fin.addCases with
      | left i => simp [encode, decode]
      | right i => simp [encode, decode]

theorem encode_injective : Function.Injective (encode : Record n w → Fin (width n w) → Bool) :=
  Function.LeftInverse.injective decode_encode

theorem keyFits : n + 1 ≤ width n w := by unfold width; lia

theorem flat_key_encode (r : Record n w) : flatRecordKey (keyFits (n := n) (w := w)) (encode r) =
    r.key := by
  apply congrArg toLex
  funext i
  change encode r (Fin.castLE keyFits i) = r.key i
  exact Fin.append_left _ _ i

theorem flat_key_decode (bits : Fin (width n w) → Bool) :
    flatRecordKey (keyFits (n := n) (w := w)) bits = (decode bits).key := by
  rw [← flat_key_encode, encode_decode]

theorem key_eq_iff (a b : Record n w) :
    a.key = b.key ↔ a.padding = b.padding ∧ a.state = b.state := by
  constructor
  · intro h
    refine ⟨congrFun h 0, ?_⟩
    funext i
    exact congrFun h i.succ
  · rintro ⟨hpad, hstate⟩
    simp [key, hpad, hstate]

def query (state : State n) (index : ℕ) : Record n w :=
  ⟨false, state, false, BitVec.ofNat w index, fun _ => false⟩

def stored (state payload : State n) : Record n w :=
  ⟨false, state, true, 0, payload⟩

def pad : Record n w := ⟨true, fun _ => false, false, 0, fun _ => false⟩

/-- Reject padding and identical complete records. Any remaining equal-key pair
gives a checkpoint hit or a genuine repeated pair. -/
def collision (a b : Record n w) : Bool :=
  !a.padding && !b.padding && decide (a.state = b.state) && decide (a ≠ b)

theorem collision_iff (a b : Record n w) :
    collision a b = true ↔ a.padding = false ∧ b.padding = false ∧
      a.state = b.state ∧ a ≠ b := by
  simp [collision, and_assoc]

variable {M R : ℕ}

/-- Hardwired checkpoints, followed by the short orbit prefix, followed by padding. -/
def initial (f : State n → State n) (T K : ℕ) (checkpoints : Fin M → State n)
    (x : State n) (j : Fin R) : Record n w :=
  if h : j.val < M then stored (checkpoints ⟨j.val, h⟩) (f^[T - K] (checkpoints ⟨j.val, h⟩))
  else if _h : j.val - M ≤ K then query (f^[j.val - M] x) (j.val - M)
  else pad

theorem initial_stored (f : State n → State n) (T K : ℕ) (checkpoints : Fin M → State n)
    (x : State n) (hR : M + (K + 1) ≤ R) (j : Fin M) :
    initial (R := R) (w := w) f T K checkpoints x ⟨j.val, by have := j.isLt; lia⟩ =
      stored (checkpoints j) (f^[T - K] (checkpoints j)) := by
  simp [initial, j.isLt]

theorem initial_query (f : State n → State n) (T K : ℕ) (checkpoints : Fin M → State n)
    (x : State n) (hR : M + (K + 1) ≤ R) (j : Fin (K + 1)) :
    initial (R := R) (w := w) f T K checkpoints x ⟨M + j.val, by have := j.isLt; lia⟩ =
      query (f^[j.val] x) j.val := by
  simp [initial, Nat.not_lt.mpr (Nat.le_add_right M j.val),
    Nat.le_of_lt_succ j.isLt]

/-- Every nonpadding record retains its exact source description. -/
theorem initial_cases (f : State n → State n) (T K : ℕ) (checkpoints : Fin M → State n)
    (x : State n) (j : Fin R) :
    initial (w := w) f T K checkpoints x j = pad ∨
      (∃ h : Fin M, initial (w := w) f T K checkpoints x j =
        stored (checkpoints h) (f^[T - K] (checkpoints h))) ∨
      ∃ d ≤ K, initial (w := w) f T K checkpoints x j = query (f^[d] x) d := by
  unfold initial
  split_ifs with h1 h2
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, h2, rfl⟩)
  · exact Or.inl rfl

/-- A nonpadding record is either a checkpoint or one specific orbit-prefix state. -/
def Valid (f : State n → State n) (T K : ℕ) (checkpoints : Fin M → State n)
    (x : State n) (r : Record n w) : Prop :=
  r = pad ∨ (∃ h : Fin M, r = stored (checkpoints h) (f^[T - K] (checkpoints h))) ∨
    ∃ d ≤ K, r = query (f^[d] x) d

/-- The complete mathematical information certified by a detected collision. -/
inductive Witness (f : State n → State n) (T K : ℕ) (checkpoints : Fin M → State n)
    (x : State n) : Record n w → Record n w → Prop
  | hitLeft (h : Fin M) (d : ℕ) (hd : d ≤ K) (heq : f^[d] x = checkpoints h) :
      Witness f T K checkpoints x
        (stored (checkpoints h) (f^[T - K] (checkpoints h))) (query (f^[d] x) d)
  | hitRight (h : Fin M) (d : ℕ) (hd : d ≤ K) (heq : f^[d] x = checkpoints h) :
      Witness f T K checkpoints x (query (f^[d] x) d)
        (stored (checkpoints h) (f^[T - K] (checkpoints h)))
  | repeated (i j : ℕ) (hi : i ≤ K) (hj : j ≤ K) (hne : i ≠ j)
      (heq : f^[i] x = f^[j] x) :
      Witness f T K checkpoints x (query (f^[i] x) i) (query (f^[j] x) j)

/-- A collision of valid records supplies a correct witness, without requiring
a unique record for each state. -/
theorem collision_witness (f : State n → State n) (T K : ℕ) (checkpoints : Fin M → State n)
    (x : State n) (a b : Record n w)
    (ha : Valid f T K checkpoints x a) (hb : Valid f T K checkpoints x b)
    (hc : collision a b = true) : Witness f T K checkpoints x a b := by
  obtain ⟨hpa, hpb, hstate, hne⟩ := (collision_iff a b).mp hc
  rcases ha with rfl | ⟨h, rfl⟩ | ⟨i, hi, rfl⟩
  · simp [pad] at hpa
  · rcases hb with rfl | ⟨h', rfl⟩ | ⟨j, hj, rfl⟩
    · simp [pad] at hpb
    · have he : checkpoints h = checkpoints h' := hstate
      exact (hne (by rw [he])).elim
    · exact Witness.hitLeft h j hj hstate.symm
  · rcases hb with rfl | ⟨h', rfl⟩ | ⟨j, hj, rfl⟩
    · simp [pad] at hpb
    · exact Witness.hitRight h' i hi hstate
    · exact Witness.repeated i j hi hj (by intro h; subst j; exact hne rfl) hstate

end Record
end IteratedFunctions
