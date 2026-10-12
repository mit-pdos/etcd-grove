/-
Proof of `Spec/.../mvcc/watcherSetByKey__add.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherSetByKey__add
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherSet__add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watcherSetByKey.add.wp_proof
    (hAdd : mvcc.watcherSet.add.spec (GF := GF) (hG := hG)) :
    mvcc.watcherSetByKey.add.spec (GF := GF) (hG := hG) := by
  intro km KM W wa r fcs
  wp_start as ⟨Hkm, #Hfix, %Hpre⟩
  obtain ⟨Hwa, Hend⟩ := Hpre
  iunfold mvcc.ownKeyMap at Hkm
  icases Hkm with ⟨Hkm, %Hdom, Hsets⟩
  iunfold mvcc.watcherFixed at Hfix
  icases Hfix with ⟨%Hnn, %ks, %es, #Hk, #Hks, #He, #Hes, #Hs, #Hi, #Hf⟩
  wp_auto
  wp_apply wp_bytes_to_string ks r.key DFrac.discard $$ [$Hks] as -
  wp_apply wp_map_lookup1 $$ Hkm as Hkm
  -- the members' other keys keep their sets
  have Hother : ∀ k, k ≠ r.key → mvcc.keyMembers (<[wa := r]> W) k = mvcc.keyMembers W k :=
    fun k hne => mvcc.keyMembers_insert_ne W wa r k Hwa (fun h => hne h.2.symm)
  have Hdom' : ∀ k, (KM !! k).isSome = true ∨ k = r.key ↔
      ∃ w r', (<[wa := r]> W) !! w = some r' ∧ r'.end? = none ∧ r'.key = k := by
    intro k
    rw [Hdom k]
    constructor
    · rintro (⟨w, r', hw, he, hk⟩ | rfl)
      · refine ⟨w, r', ?_, he, hk⟩
        rw [GMap.lookup_insert_ne _ _ (fun h => by subst h; rw [Hwa] at hw; cases hw)]
        exact hw
      · exact ⟨wa, r, GMap.lookup_insert _ _ _, Hend, rfl⟩
    · rintro ⟨w, r', hw, he, hk⟩
      by_cases hww : w = wa
      · subst hww; rw [GMap.lookup_insert] at hw; cases hw; exact Or.inr hk.symm
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hww)] at hw
        exact Or.inl ⟨w, r', hw, he, hk⟩
  cases hk : KM !! r.key with
  | none =>
    simp only [Option.getD_none]
    wp_auto
    rw [go.make1_underlying, go.is_underlying (t := watcherSet.ty)]
    wp_apply (wp_map_make1 (K := Loc) (V := Unit)) as %mn Hmn
    wp_apply wp_bytes_to_string ks r.key DFrac.discard $$ [$Hks] as -
    wp_apply wp_mapInsert $$ Hkm as Hkm
    (try wp_auto)
    ihave Hmn : mvcc.ownWatcherSet mn ∅ $$ [Hmn]
    · iunfold mvcc.ownWatcherSet; iexact Hmn
    wp_apply hAdd $$ [$Hmn] as Hmn
    · ipureintro; rfl
    iapply HΦ
    iexists (<[r.key := mn]> KM)
    iunfold mvcc.ownKeyMap
    iframe Hkm
    isplitl []
    · ipureintro
      intro k
      rw [← Hdom' k]
      by_cases hkk : k = r.key
      · subst hkk; simp
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkk)]; simp [hkk]
    iapply (BigSepM.bigSepM_insert hk).2
    isplitl [Hmn]
    · rw [mvcc.keyMembers_insert_eq W wa r Hwa Hend]
      have Hemp : mvcc.keyMembers W r.key = ∅ := by
        rw [mvcc.keyMembers_empty_iff, ← Hdom r.key, hk]; simp
      rw [Hemp]
      iexact Hmn
    iapply (BigSepM.bigSepM_mono (fun {k v} hkv => ?_)) $$ Hsets
    have hne : k ≠ r.key := by rintro rfl; exact absurd (hkv.symm.trans hk) (by simp)
    rw [Hother k hne]
  | some m0 =>
    simp only [Option.getD_some]
    icases (BigSepM.bigSepM_lookup_acc_impl (m := KM) hk) $$ Hsets with ⟨Hset, Hsets⟩
    iunfold mvcc.ownWatcherSet at Hset
    ihave %Hm0 := ownMap_not_nil _ _ _ $$ Hset
    rw [decide_eq_false Hm0]
    wp_auto
    (try wp_auto)
    ihave Hset : mvcc.ownWatcherSet m0 (mvcc.keyMembers W r.key) $$ [Hset]
    · iunfold mvcc.ownWatcherSet; iexact Hset
    wp_apply hAdd $$ [$Hset] as Hset
    · ipureintro
      rw [mvcc.keyMembers, mvcc.membersBy_lookup, Hwa]
    iapply HΦ
    iexists KM
    iunfold mvcc.ownKeyMap
    iframe Hkm
    isplitl []
    · ipureintro
      intro k
      rw [← Hdom' k]
      by_cases hkk : k = r.key
      · subst hkk; simp [hk]
      · simp [hkk]
    iapply Hsets
    · imodintro
      iintro %k %v %_ %hne Hv
      rw [Hother k hne]
      iexact Hv
    rw [mvcc.keyMembers_insert_eq W wa r Hwa Hend]
    iexact Hset

end proof

end EtcdGrove
end Perennial
