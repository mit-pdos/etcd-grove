/-
**`bootGo`'s values are what the membership package's construction computes** (claim #34, stage 2,
2026-11-25; `notes/bootstrap-proof-plan.md` §7.2, §7.4): `bootGo.sha1` is Perennial's
`crypto.sha1.sha1`, `bootGo.memberID` is `membership.memberIDOf`, `bootGo.memberOf` is
`membership.memberOfURLs`, `bootGo.memMap` is the `memOfList` of the initial cluster's entries, and,
for the ids `MemberIDs()` answers (`membership.idsSorted`), `bootGo.ps` is those ids and `bootGo.cid`
is `membership.clusterIdOf` of them. Pure; a defs module (`bootstrapNewClusterNoWAL`'s proof uses it).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootValues
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.BuildLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bootGo

open go_etcd_io.etcd.server.v3.etcdserver.api

/-- `bootGo.sha1` is Perennial's `crypto.sha1.sha1` (the same text). -/
theorem sha1_eq (m : List w8) : sha1 m = crypto.sha1.sha1 m := rfl

/-- Little-endian combination of a reversed list is the big-endian fold. -/
theorem combine_reverse (l : List w8) :
    LittleEndian.combine l.reverse = l.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    rw [List.reverse_append, List.foldl_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.foldl_cons, List.foldl_nil]
    rw [LittleEndian.combine_unfold, ih]
    omega

/-- `be64` is `beToU64` of the first eight bytes. -/
theorem be64_eq (l : List w8) : be64 l = beToU64 (l.take 8) := by
  unfold be64 beToU64
  rw [leToU64_unseal]
  unfold leToU64Def
  rw [combine_reverse]

/-- `bytes64` is `u64Be`. -/
theorem bytes64_eq (x : w64) : bytes64 x = u64Be x := by
  unfold bytes64 u64Be
  rw [u64Le_unseal]
  unfold u64LeDef
  simp only [LittleEndian.split, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.range, List.range.loop, List.map_cons, List.map_nil,
    Nat.div_div_eq_div_mul]
  rfl

/-- Go's string order: `strLe` is `membership.strLeB`. -/
theorem strLe_eq (x y : GoString) : strLe x y = membership.strLeB x y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => simp [strLe, membership.strLeB, go.GoStringLe]
    | cons b bs =>
      simp only [strLe, membership.strLeB, go.GoStringLe, go.GoStringLt]
      symm; apply decide_eq_true; right; exact List.Lex.nil
  | cons a as ih =>
    cases y with
    | nil =>
      simp only [strLe, membership.strLeB, go.GoStringLe, go.GoStringLt]
      symm; apply decide_eq_false
      rintro (h | h)
      · cases h
      · cases h
    | cons b bs =>
      unfold strLe
      rw [ih bs]
      simp only [membership.strLeB, go.GoStringLe, go.GoStringLt]
      by_cases hab : a.toNat < b.toNat
      · simp only [hab, ↓reduceIte]
        symm; apply decide_eq_true; right
        exact List.Lex.rel (by simp only [uint.Z]; omega)
      · by_cases hba : b.toNat < a.toNat
        · simp only [hab, hba, ↓reduceIte]
          symm; apply decide_eq_false
          rintro (h | h)
          · cases h; omega
          · cases h with
            | cons h => omega
            | rel h => simp only [uint.Z] at h; omega
        · have hab' : a = b := BitVec.eq_of_toNat_eq (by omega)
          subst hab'
          simp only [hab, ↓reduceIte, List.cons.injEq, true_and]
          apply decide_eq_decide.2
          constructor
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr (List.Lex.cons h)
          · rintro (h | h)
            · exact Or.inl h
            · cases h with
              | cons h => exact Or.inr h
              | rel h => simp only [uint.Z] at h; omega

/-- `bootGo.memberID` is `membership.memberIDOf`. -/
theorem memberID_eq (us : List GoString) (token : GoString) :
    memberID us token = membership.memberIDOf us token := by
  unfold memberID membership.memberIDOf
  have : strLe = membership.strLeB := funext fun x => funext fun y => strLe_eq x y
  rw [this, be64_eq, sha1_eq]

/-- `bootGo.memberOf` is `membership.memberOfURLs`. -/
theorem memberOf_eq [GooseExts] (U : BootURLs) (token name : GoString) :
    memberOf U token name = membership.memberOfURLs name (U.initURLs name) token := by
  unfold memberOf membership.memberOfURLs
  rw [memberID_eq]
  rfl

/-- The initial cluster's entries' members. -/
noncomputable abbrev entries [GooseExts] (U : BootURLs) (token : GoString) : List apply.MemberM :=
  U.initMap.domList.map (fun k => membership.memberOfURLs k (U.initURLs k) token)

theorem members_perm [GooseExts] (U : BootURLs) (token : GoString) :
    (members U token).Perm (entries U token) := by
  unfold members entries
  refine (List.mergeSort_perm _ _).trans ?_
  rw [List.map_congr_left (fun k _ => memberOf_eq U token k)]

theorem entries_ids_nodup [GooseExts] (U : BootURLs) (token : GoString)
    (h : initMapOk U token) : ((entries U token).map (·.id)).Nodup := by
  have := h.1
  unfold entries
  rw [List.map_map]
  simpa [Function.comp_def, memberOf_eq] using this

/-- **`bootGo.memMap` is the `memOfList` of the entries.** -/
theorem memMap_eq [GooseExts] (U : BootURLs) (token : GoString) (h : initMapOk U token) :
    memMap U token = membership.memOfList (entries U token) := by
  have hnd := entries_ids_nodup U token h
  unfold memMap
  exact membership.memOfList_perm _ _ (members_perm U token)
    (((members_perm U token).map _).nodup_iff.2 hnd)

/-- **`bootGo.ps` is `MemberIDs()`' answer.** -/
theorem ps_eq [GooseExts] (U : BootURLs) (token : GoString) (h : initMapOk U token)
    (ids : List w64) (hids : membership.idsSorted (membership.memOfList (entries U token)) ids) :
    ps U token = ids := by
  obtain ⟨hnd, hmem, hsorted⟩ := hids
  have hndE := entries_ids_nodup U token h
  have hpe : (ps U token).Perm ((entries U token).map (·.id)) := (members_perm U token).map _
  have hndp : (ps U token).Nodup := hpe.nodup_iff.2 hndE
  have hperm : (ps U token).Perm ids := by
    refine (List.perm_ext_iff_of_nodup hndp hnd).2 (fun k => ?_)
    rw [hpe.mem_iff, hmem k, membership.memOfList_isSome _ hndE k]
  apply List.Perm.eq_of_pairwise (le := fun a b : w64 => a.toNat ≤ b.toNat)
  · intro a b _ _ hab hba
    exact BitVec.eq_of_toNat_eq (by omega)
  · unfold ps members
    rw [List.pairwise_map]
    exact List.Pairwise.imp (fun h => by simpa using h)
      (List.pairwise_mergeSort (le := fun a b : apply.MemberM => decide (a.id.toNat ≤ b.id.toNat))
        (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _)
  · exact hsorted.imp (fun h => Nat.le_of_lt h)
  · exact hperm

/-- **`bootGo.cid` is `genID()`'s.** -/
theorem cid_eq [GooseExts] (U : BootURLs) (token : GoString) (h : initMapOk U token)
    (ids : List w64) (hids : membership.idsSorted (membership.memOfList (entries U token)) ids) :
    cid U token = membership.clusterIdOf ids := by
  unfold cid membership.clusterIdOf
  have hb : bytes64 = u64Be := funext bytes64_eq
  rw [ps_eq U token h ids hids, be64_eq, sha1_eq, hb]

end bootGo
end EtcdGrove
end Perennial
