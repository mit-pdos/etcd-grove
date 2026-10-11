/-
Proof of `Spec/store__Restore.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.store__Restore
public import Spec.k8s_io.utils.third_party.forked.golang.btree.New
public import Spec.go_etcd_io.etcd.cache.v3.kvItemLess
public import Spec.go_etcd_io.etcd.cache.v3.newKVItem
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__ReplaceOrInsert
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__RebaseHistory
public import Spec.go_etcd_io.etcd.cache.v3.newClonedSnapshot
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__Append

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 k8s_io.utils.third_party.forked.golang

/-! ## `restoreMap` -/

theorem Restore_restoreMap_take_succ (kvs : KvMap) (i : Nat) (e : KvEntry)
    (h : kvs[i]? = some e) :
    restoreMap (kvs.take (i + 1)) = btInsert kvLess e (restoreMap (kvs.take i)) := by
  unfold restoreMap
  rw [List.take_add_one, h, Option.toList_some, List.foldl_append]
  rfl

theorem Restore_foldl_sorted (kvs : KvMap) (m : KvMap) (hm : m.Pairwise kvLess) :
    (kvs.foldl (fun m e => btInsert kvLess e m) m).Pairwise kvLess := by
  induction kvs generalizing m with
  | nil => exact hm
  | cons e es ih => exact ih _ (btInsert_sorted kvLess_swo hm)

theorem Restore_restoreMap_sorted (kvs : KvMap) : (restoreMap kvs).Pairwise kvLess :=
  Restore_foldl_sorted kvs [] List.Pairwise.nil

theorem Restore_foldl_mem (kvs : KvMap) (m : KvMap) (x : KvEntry)
    (h : x ∈ kvs.foldl (fun m e => btInsert kvLess e m) m) : x ∈ kvs ∨ x ∈ m := by
  induction kvs generalizing m with
  | nil => exact Or.inr h
  | cons e es ih =>
    rcases ih _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases btInsert_mem h with rfl | h
      · exact Or.inl List.mem_cons_self
      · exact Or.inr h

theorem Restore_restoreMap_mem (kvs : KvMap) (x : KvEntry) (h : x ∈ restoreMap kvs) : x ∈ kvs := by
  rcases Restore_foldl_mem kvs [] x h with h | h
  · exact h
  · exact absurd h List.not_mem_nil

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem store.Restore.wp_proof
    (wp_btree_New : btree.New.spec (GF := GF) (hG := hG))
    (wp_kvItemLess : kvItemLess.spec (GF := GF) (hG := hG))
    (wp_newKVItem : newKVItem.spec (GF := GF) (hG := hG))
    (wp_ReplaceOrInsert : btree.BTree.ReplaceOrInsert.spec (GF := GF) (hG := hG))
    (wp_RebaseHistory : ringBuffer.RebaseHistory.spec (GF := GF) (hG := hG))
    (wp_newClonedSnapshot : newClonedSnapshot.spec (GF := GF) (hG := hG))
    (wp_Append : ringBuffer.Append.spec (GF := GF) (hG := hG)) :
    store.Restore.spec (GF := GF) (hG := hG) := by
  have wp_btree_New : btree.New.modelSpec (GF := GF) (hG := hG) := btree.New.modelSpec_of wp_btree_New
  have wp_ReplaceOrInsert : btree.BTree.ReplaceOrInsert.modelSpec (GF := GF) (hG := hG) := btree.BTree.ReplaceOrInsert.modelSpec_of wp_ReplaceOrInsert
  intro s γ cap E R P kvsSl kvs dq rev
  wp_start as ⟨#His, #Hguard, Hkvs, #HkvsAt, HP0, %Hdom, #HE, #HRr⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isStoreWriter
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlocked, HP⟩
  unfold storeLockInv
  iNamed HP
  unfold isStore
  iNamed His
  unfold storeLockRest
  icases Hrest with ⟨Hgt, Hsnap, %Hsynced⟩
  -- the dominance: no revision the store can be at is above `rev`
  icases keep_pure (Hdom st.latestRev) $$ [$HP0 $HR] with ⟨⟨HP0, -⟩, %Hrev⟩
  -- borrow the latest tree
  imod storeTree_borrow s γ st.latest $$ [$Htree $Hgt] with ⟨Htr, Hgt⟩
  ihave Hless : btLessSpec (functions kvItemLess []) (kvItemIs (hG := hG)) kvLess $$ []
  · unfold btLessSpec
    iintro %a %b %va %vb
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply wp_kvItemLess a b va vb $$ [Hpre] HΦ'
    iframe
    iPkgInit
  wp_auto
  unfold storeLatestTree
  icases Htr with ⟨%t0, Ht0, -, -⟩
  wp_apply wp_btree_New kvItemPtrT deg (functions kvItemLess []) (kvItemIs (hG := hG)) kvLess
    $$ [Hless] as %t Ht
  · iframe; ipureintro; exact ⟨Hdeg, kvLess_swo⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hkvs
  simp only [List.length_map] at Hlen
  ihave HI : iprop(∃ (j : w64) (kvp : Loc),
      "i" ∷ i_ptr ↦ j ∗ "kv" ∷ kv_ptr ↦ kvp ∗
      "Ht" ∷ ownBTree kvItemPtrT t (kvItemIs (hG := hG)) kvLess
        (restoreMap (kvs.take (sint.nat j))) (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z kvsSl.len⌝) $$ [i kv Ht]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · obtain ⟨e, He⟩ : ∃ e, kvs[sint.nat j]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    rw [ite_eq_left (by omega)]
    wp_apply wp_load_slice_index kvsSl (sint.Z j) (kvs.map Prod.snd) dq e.2 Hj.1 $$ [Hkvs] as Hkvs
    · iframe; ipureintro; simp [He]
    iunfold kvsAt at HkvsAt
    ihave #HkvAt : kvAt (hG := hG) e $$ []
    · iapply HkvsAt; ipureintro; exact List.mem_of_getElem? He
    wp_apply wp_newKVItem e $$ [$HkvAt] as %p #Hp
    wp_apply wp_ReplaceOrInsert kvItemPtrT t (kvItemIs (hG := hG)) kvLess
      (restoreMap (kvs.take (sint.nat j))) p e $$ [Ht] as %old %ok ⟨Ht, -⟩
    · iframe; isplitr
      · ipureintro; exact kvLess_swo
      iexact Hp
    wp_for_post
    iframe
    iexists j + W64 1, e.2
    simp only [named]
    rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word,
      Restore_restoreMap_take_succ kvs _ e He]
    iframe
    ipureintro; word
  · have Hjl : sint.nat j = kvs.length := by word
    rw [Hjl, List.take_length]
    wp_apply wp_RebaseHistory $$ [$Hhist] as Hhist
    ihave #HkvsR : kvsAt (hG := hG) (restoreMap kvs) $$ []
    · iunfold kvsAt at HkvsAt
      iunfold kvsAt
      imodintro
      iintro %x %Hx
      iapply HkvsAt
      ipureintro; exact Restore_restoreMap_mem kvs x Hx
    wp_apply wp_newClonedSnapshot rev t (restoreMap kvs) $$ [$Ht $HkvsR] as %p ⟨Ht, #Hp⟩
    · ipureintro; exact Restore_restoreMap_sorted kvs
    ihave #Hpc : snapCert E p (rev, restoreMap kvs) $$ []
    · iunfold snapCert; isplitl []
      · iexact Hp
      · iexact HE
    wp_apply wp_Append $$ [$Hhist $Hpc] as Hhist
    · ipureintro; intro last h; simp at h
    wp_apply sync.Cond.wp_Broadcast $$ [$Hcond]
    have Hcap' := Hinv.cap_pos
    have Hra : ringAppend cap ([] : List (w64 × KvMap)) (rev, restoreMap kvs) =
        [(rev, restoreMap kvs)] := by
      simp [ringAppend, Hcap']
    rw [Hra]
    have Hinv' : StoreInv cap (restoreState rev kvs) := by
      have h0 := Hinv.rev_nonneg
      constructor
      · exact Hcap'
      · exact Hinv.cap_le
      · show 0 ≤ sint.Z rev; omega
      · exact Restore_restoreMap_sorted kvs
      · show 1 ≤ cap; omega
      · simp [restoreState, RevSorted]
      · intro h hh; simp [restoreState] at hh; subst hh; simp [restoreState]
      · intro h hh; simp [restoreState] at hh; subst hh; exact Restore_restoreMap_sorted kvs
    have Hrev0 : 0 ≤ sint.Z rev := by have := Hinv.rev_nonneg; omega
    imod ghostVar_update (restoreState rev kvs) γ.state st $$ Hst with Hst
    imod mono_nat_own_update (sint.nat rev) (by word) $$ Hrev
      with ⟨Hrev, #Hlb⟩
    imod mono_nat_own_update (sint.nat rev + 1) (by
        have := storeSnapKey_le cap st Hinv
        have : sint.nat st.latestRev ≤ sint.nat rev := by word
        omega) $$ Hsnap with ⟨Hsnap, #Hslb⟩
    imod storeTree_return s γ (restoreMap kvs) $$ [$Htree $Hgt Ht0 Ht] with Hgt
    · unfold storeLatestTree
      iexists t
      iframe
      iexact HkvsR
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlocked Hst Hrev HlatestRev Hhist Hgt Hsnap]
    · iexists restoreState rev kvs
      rw [storeSnapKey_restore rev kvs Hrev0]
      simp only [named, restoreState]
      iframe
      iframe HRr
      isplitr
      · ipureintro; exact restoreState_synced rev kvs
      ipureintro; exact Hinv'
    iapply HΦ
    iframe Hkvs HP0
    isplitr
    · unfold storeRevLb; iexact Hlb
    unfold storeSnapLb
    iexact Hslb

end proof

end EtcdGrove
end Perennial
