/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ForestRecordQueries

/-! # Boolean implementation of a compressed-forest query -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n a K : ℕ}

/-- After shared lookup, two record scans and one further prefix finish the query. -/
theorem synthesis_forest_query (c : Circuit Boolean.signature n n)
    (s : Set (State a → Bool)) (x y : State a → State n)
    (marks : State a → Fin (K + 2) → Bool)
    (markRecords : State a → Fin (K + 2) → State (forestRecordWidth n))
    (flags : State a → Fin (K + 1) → Bool)
    (records : State a → Fin (K + 1) → State (forestRecordWidth n))
    (hy : wires y ⊆ s) (hz : (fun _ => false) ∈ s)
    (hp : orbitPrefixWires (c.eval Boolean.interpretation) x K ⊆ s)
    (hd : wordWires (fun z => depthWord (c.eval Boolean.interpretation) (y z)) ⊆ s)
    (hm : dictionaryWires marks markRecords ⊆ s)
    (hk : dictionaryWires flags records ⊆ s) :
    Synthesis Boolean.interpretation s
      {fun z => forestQueryResult (c.eval Boolean.interpretation) K (x z) (y z)
        (marks z) (markRecords z) (flags z) (records z)}
      (K * c.size + 1000 * (K + 1) * (n + 3)) := by
  let f := c.eval Boolean.interpretation
  let W := forestRecordWidth n
  have hmF (j) : (fun z => marks z j) ∈ s := hm (Or.inl ⟨j, rfl⟩)
  have hmR (j) : wires (fun z => markRecords z j) ⊆ s :=
    fun _ h => hm (Or.inr (Set.mem_iUnion.mpr ⟨j, h⟩))
  have hkF (j) : (fun z => flags z j) ∈ s := hk (Or.inl ⟨j, rfl⟩)
  have hkR (j) : wires (fun z => records z j) ⊆ s :=
    fun _ h => hk (Or.inr (Set.mem_iUnion.mpr ⟨j, h⟩))
  let eligible := fun z => forestEligible f (y z) (flags z) (records z)
  have he := Synthesis.family (I := Boolean.interpretation) (s := s)
    (fun j z => eligible z j) (fun _ => 5 * (n + 3) + 4) (fun j => by
      simpa only [eligible, forestEligible, Nat.zero_add, Nat.add_assoc] using
        (Synthesis.of_mem (hkF j)).and ((synthesis_ult s
        (fun z => forestRecordDepth (records z j)) (fun z => depthWord f (y z))
        (fun bit => (forestRecord_fields s _ (hkR j)).2.1 ⟨bit, rfl⟩)
        (fun bit => hd ⟨bit, rfl⟩)).not))
  let s1 := s ∪ Set.range (fun j z => eligible z j)
  have old1 : s ⊆ s1 := fun _ h => Or.inl h
  have avE (j) : (fun z => eligible z j) ∈ s1 := Or.inr ⟨j, rfl⟩
  let hit := fun z => forestHitRecord (marks z) (markRecords z)
  let key := fun z => forestKeyRecord f (y z) (flags z) (records z)
  let foundH := fun z => forestHitFound (marks z)
  let foundK := fun z => forestKeyFound f (y z) (flags z) (records z)
  have hh := synthesis_chooseRecord (w := W) s1
    (fun z (j : Fin (K + 1)) => marks z j.castSucc)
    (fun z j => markRecords z j.castSucc) (fun _ _ => false)
    (fun j => old1 (hmF j.castSucc))
    (fun j bit => old1 (hmR j.castSucc ⟨bit, rfl⟩)) (fun _ => old1 hz)
  have hkey := synthesis_chooseRecord (w := W) s1 eligible records (fun _ _ => false)
    avE (fun j bit => old1 (hkR j ⟨bit, rfl⟩)) (fun _ => old1 hz)
  have hfoundH := synthesis_any_flags s1 (fun z (j : Fin (K + 1)) => marks z j.castSucc)
    (fun j => old1 (hmF j.castSucc))
  have hfoundK := synthesis_any_flags s1 eligible avE
  have hselect := ((hh.union hkey).union hfoundH).union hfoundK
  let s2 := s1 ∪ (wires hit ∪ wires key ∪ {foundH} ∪ {foundK})
  have old2 : s1 ⊆ s2 := fun _ h => Or.inl h
  have avHit : wires hit ⊆ s2 := fun _ h => Or.inr (Or.inl (Or.inl (Or.inl h)))
  have avKey : wires key ⊆ s2 := fun _ h => Or.inr (Or.inl (Or.inl (Or.inr h)))
  have avFoundH : foundH ∈ s2 := Or.inr (Or.inl (Or.inr rfl))
  have avFoundK : foundK ∈ s2 := Or.inr (Or.inr rfl)
  let anchor := fun z => forestAnchorRecord f (y z) (marks z) (markRecords z) (flags z) (records z)
  let foundA := fun z => forestAnchorFound f (y z) (marks z) (flags z) (records z)
  have ha := synthesis_record_mux s2 (fun z => marks z (Fin.last (K + 1)))
    (fun z => markRecords z (Fin.last (K + 1))) key
    (old2 (old1 (hmF _))) (fun _ h => old2 (old1 (hmR _ h))) avKey
  have hfoundA := (Synthesis.of_mem (I := Boolean.interpretation)
    (old2 (old1 (hmF (Fin.last (K + 1)))))).or (Synthesis.of_mem avFoundK)
  let s3 := s2 ∪ (wires anchor ∪ {foundA})
  have old3 : s2 ⊆ s3 := fun _ h => Or.inl h
  have avA : wires anchor ⊆ s3 := fun _ h => Or.inr (Or.inl h)
  have avFoundA : foundA ∈ s3 := Or.inr (Or.inr rfl)
  let anchorState := fun z => forestRecordState (anchor z)
  have hprefix := synthesis_prefix c s3 anchorState (forestRecord_fields s3 anchor avA).1 K
  let s4 := s3 ∪ orbitPrefixWires f anchorState K
  have old4 : s3 ⊆ s4 := fun _ h => Or.inl h
  have avY : wires y ⊆ s4 := fun _ h => old4 (old3 (old2 (old1 (hy h))))
  have hshort := synthesis_prefix_hit s4 (fun z (j : Fin (K + 1)) => f^[j.val] (x z)) y
    (fun j _ h => old4 (old3 (old2 (old1 (hp (Set.mem_iUnion.mpr ⟨j, h⟩)))))) avY
  have hverify := synthesis_prefix_hit s4
    (fun z (j : Fin (K + 1)) => f^[j.val] (anchorState z)) y
    (fun j _ h => Or.inr (Set.mem_iUnion.mpr ⟨j, h⟩)) avY
  have fieldsH := forestRecord_fields s4 hit (fun _ h => old4 (old3 (avHit h)))
  have fieldsA := forestRecord_fields s4 anchor (fun _ h => old4 (avA h))
  have hlow := synthesis_ult s4 (fun z => forestRecordLow (hit z))
    (fun z => forestRecordLow (anchor z))
    (fun bit => fieldsH.2.2.1 ⟨bit, rfl⟩) (fun bit => fieldsA.2.2.1 ⟨bit, rfl⟩)
  have hhigh := synthesis_ult s4 (fun z => forestRecordHigh (anchor z))
    (fun z => forestRecordLow (hit z))
    (fun bit => fieldsA.2.2.2 ⟨bit, rfl⟩) (fun bit => fieldsH.2.2.1 ⟨bit, rfl⟩)
  have hinterval := hlow.not.and hhigh.not
  let short := fun z => forestPrefixTest f K (x z) (y z)
  let verify := fun z => forestPrefixTest f K (anchorState z) (y z)
  let interval := fun z => forestIntervalTest (hit z) (anchor z)
  let s5 := s4 ∪ ({short} ∪ {verify} ∪ {interval})
  have old5 : s4 ⊆ s5 := fun _ h => Or.inl h
  have avShort : short ∈ s5 := Or.inr (Or.inl (Or.inl rfl))
  have avVerify : verify ∈ s5 := Or.inr (Or.inl (Or.inr rfl))
  have avInterval : interval ∈ s5 := Or.inr (Or.inr rfl)
  have hfinish := (Synthesis.of_mem (I := Boolean.interpretation) avShort).or
    ((((Synthesis.of_mem (old5 (old4 (old3 avFoundH)))).and
      (Synthesis.of_mem (old5 (old4 avFoundA)))).and (Synthesis.of_mem avVerify)).and
        (Synthesis.of_mem avInterval))
  have hfull := he.trans (hselect.trans ((ha.union hfoundA).trans
    (hprefix.trans (((hshort.union hverify).union hinterval).trans hfinish))))
  apply hfull.mono Set.Subset.rfl Set.Subset.rfl
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  dsimp only [W, forestRecordWidth]
  nlinarith [Nat.zero_le (K * n)]

end IteratedFunctions
