/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Detector
public import Proofs.Residues
public import Proofs.Iteration

/-!
# Reconstruction from a detected pair

Checkpoint payloads are advanced by the missing prefix distance. Repeated
prefix states select an equivalent short index using the fixed residue table.
All branches are total, including inputs that are not valid detector outputs.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n w R : ℕ}

theorem selectBits_toNat {k : ℕ} (index : BitVec k) (values : Fin R → Fin w → Bool)
    (hR : R ≤ 2 ^ k) (hi : index.toNat < R) :
    selectBits index values = values ⟨index.toNat, hi⟩ := by
  simpa using selectBits_eq hR values ⟨index.toNat, hi⟩

def hitValue (f : State n → State n) (K : ℕ) (index : BitVec w) (payload : State n) :
    State n :=
  selectBits (BitVec.ofNat w K - index) (fun j : Fin (K + 1) => f^[j.val] payload)

def repeatedValue (f : State n → State n) (T K : ℕ) (x : State n) (lo hi : BitVec w) :
    State n :=
  selectBits (repeatWordIndex T K lo hi) (fun j : Fin (K + 1) => f^[j.val] x)

def reconstruct (f : State n → State n) (T K : ℕ) (x : State n)
    (a b : Record n w) : State n :=
  if a.checkpoint then hitValue f K b.index a.payload
  else if b.checkpoint then hitValue f K a.index b.payload
  else if a.index.ult b.index then repeatedValue f T K x a.index b.index
  else repeatedValue f T K x b.index a.index

theorem hitValue_spec (f : State n → State n) (T K d : ℕ) (x : State n)
    (hd : d ≤ K) (hK : K < 2 ^ w) (hT : K ≤ T) :
    hitValue f K (BitVec.ofNat w d) (f^[T - K] (f^[d] x)) = f^[T] x := by
  have he : (BitVec.ofNat w K - BitVec.ofNat w d).toNat = K - d := by
    rw [BitVec.toNat_sub_of_le]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hK,
        Nat.mod_eq_of_lt (hd.trans_lt hK)]
    · change (BitVec.ofNat w d).toNat ≤ (BitVec.ofNat w K).toNat
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hK,
        Nat.mod_eq_of_lt (hd.trans_lt hK)] using hd
  rw [hitValue, selectBits_toNat _ _ (by lia) (by rw [he]; lia)]
  simpa only [he] using shifted_payload (f := f) (x := x) hd hT

theorem repeatedValue_spec (f : State n → State n) (T K i j : ℕ) (x : State n)
    (hij : i < j) (hj : j ≤ K) (hK : K < 2 ^ w) (hT : K ≤ T)
    (heq : f^[i] x = f^[j] x) :
    repeatedValue f T K x (BitVec.ofNat w i) (BitVec.ofNat w j) = f^[T] x := by
  have hiw : (BitVec.ofNat w i).toNat = i := Nat.mod_eq_of_lt (by lia)
  have hjw : (BitVec.ofNat w j).toNat = j := Nat.mod_eq_of_lt (by lia)
  have hs := repeatWordIndex_spec (f := f) (x := x)
    (BitVec.ofNat w i) (BitVec.ofNat w j) (by rwa [hiw, hjw]) (by rwa [hjw]) hK hT
    (by rwa [hiw, hjw])
  rw [repeatedValue, selectBits_toNat _ _ (by lia) (by have := hs.2.1; rw [hjw] at this; lia)]
  exact hs.2.2

theorem reconstruct_spec {M : ℕ} (f : State n → State n) (T K : ℕ)
    (checkpoints : Fin M → State n) (x : State n) (a b : Record n w)
    (hK : K < 2 ^ w) (hT : K ≤ T) (h : Record.Witness f T K checkpoints x a b) :
    reconstruct f T K x a b = f^[T] x := by
  cases h with
  | hitLeft h d hd heq =>
    simpa only [reconstruct, Record.stored, Record.query, ↓reduceIte, ← heq] using
      hitValue_spec f T K d x hd hK hT
  | hitRight h d hd heq =>
    simpa only [reconstruct, Record.stored, Record.query, Bool.false_eq_true,
      ↓reduceIte, ← heq] using hitValue_spec f T K d x hd hK hT
  | repeated i j hi hj hne heq =>
    simp only [reconstruct, Record.query, Bool.false_eq_true, ↓reduceIte,
      BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hi.trans_lt hK),
      Nat.mod_eq_of_lt (hj.trans_lt hK), decide_eq_true_eq]
    split_ifs with hij
    · exact repeatedValue_spec f T K i j x hij hj hK hT heq
    · exact repeatedValue_spec f T K j i x (by lia) hi hK hT heq.symm

end IteratedFunctions
