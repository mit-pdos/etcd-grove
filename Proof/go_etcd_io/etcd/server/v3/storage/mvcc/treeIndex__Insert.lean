/-
Proof of `Spec/.../mvcc/treeIndex__Insert.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Insert
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__ReplaceOrInsert
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

theorem mvcc.treeIndex.Insert.wp_proof
    (wp_ROI : btree.BTree.ReplaceOrInsert.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Insert.spec (GF := GF) (hG := hG) := by
  have wp_ROI : btree.BTree.ReplaceOrInsert.modelSpec (GF := GF) (hG := hG) :=
    btree.BTree.ReplaceOrInsert.modelSpec_of wp_ROI
  intro ti γ ilog pend ki k gs m q
  wp_start as ⟨#Hti, Hw, Hcu, %Hn, #Hkey, Hki, %Hm⟩
  obtain ⟨Hm, Hne⟩ := Hm
  iunfold mvcc.isTreeIndex at Hti
  iNamed Hti
  iunfold mvcc.idxWriter at Hw
  icases Hw with ⟨Hauth, #Hwlb, %Hwwf, Hlauth⟩
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  ihave #Hitem : mvcc.kiItemIs (GF := GF) ki (ki, k) $$ []
  · iunfold mvcc.kiItemIs
    isplitl []
    · ipureintro; rfl
    iexact Hkey
  -- `ti.Lock()`: the promoted method, through the guard
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Lock")]
  wp_call
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.idxLockInv t γ 1)) $$ Hlc1 HP with HP
  iunfold mvcc.idxLockInv at HP
  icases HP with ⟨%ilog', %pend', %L, %cmax, HP⟩
  iNamedSuffix HP "L"
  ihave %Hcle := mvcc.crevUB_lb γ q (-1) cmax (by decide) HLL.2 $$ Hcu HcrevL
  have HLLn : mvcc.IdxCRep (-1) (mvcc.evsOf (ilog' ++ [pend'])) (mvcc.idxOfEntries L) := by
    have h := HLL.1; rwa [show cmax = -1 by have := HLL.2; omega] at h
  -- the lock's events are the writer's
  ihave %Hpre := mono_list_auth_lb_valid γ.hist 1 _ _ $$ Hauth HhistL
  ihave %Hcnt := monoNatLbOwn_valid γ.nev 1 _ _ $$ HnevL Hwlb
  have hevs := mvcc.writer_events ilog ilog' pend pend' Hpre.2 Hcnt.2
  iunfold mvcc.ownTree at HtreeL
  icases HtreeL with ⟨%Hsorted, Ht, Hkis⟩
  -- the key is in the tree, with the index `m`
  have Hidx := mvcc.idxGet_entries L Hsorted k
  rw [mvcc.IdxCRep.get_neg (ilog' ++ [pend']) HwfL.logB HLLn k, hevs] at Hidx
  obtain ⟨z, hf⟩ : ∃ z, L.find? (fun z => decide (z.2.1 = k)) = some z := by
    cases hf : L.find? (fun z => decide (z.2.1 = k)) with
    | none =>
      rw [hf, Option.map_none] at Hidx
      exact absurd (Hm.trans ((mvcc.idxGet_indexOf_eq_none_iff _ k).1 Hidx)) Hne
    | some z => exact ⟨z, rfl⟩
  rw [hf, Option.map_some] at Hidx
  obtain ⟨i, hi, hk⟩ := mvcc.find?_entry_getElem? L k z hf
  have hz : z.2.2 = m := by
    have := (mvcc.indexOf_rep (mvcc.evsOf (ilog ++ [pend]))).2 k
    rw [Hidx, Option.getD_some] at this
    rw [this, Hm]
  have Hfind := mvcc.btFind_items L Hsorted ki k
  rw [hf, Option.map_some] at Hfind
  (try wp_auto)
  -- `ti.tree.ReplaceOrInsert(ki)`
  wp_apply (wp_ROI mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess _ ki (ki, k))
    $$ [$Ht $Hitem] as %old %ok ⟨Ht, Hres⟩
  · ipureintro; exact mvcc.kiItemLess_swo
  rw [Hfind]
  icases Hres with ⟨%Hok, #Hitemw⟩
  iunfold mvcc.kiItemIs at Hitemw
  icases Hitemw with ⟨%Hold, #Hkold⟩
  simp only at Hold
  subst Hold
  (try wp_auto)
  -- the replaced key index leaves the tree, `ki` takes its place
  icases BigSepL.bigSepL_lookup_acc (Φ := fun _ z => mvcc.ownEntry (GF := GF) z 1) hi |>.1 $$ Hkis
    with ⟨Hz, Hback⟩
  iunfold mvcc.ownEntry at Hz
  icases Hz with ⟨%Hzn, %gs', Hzki⟩
  have hset : btInsert mvcc.entryLess (ki, k, m) L = L.set i (ki, k, m) :=
    mvcc.btInsert_set_entry L ((mvcc.itemsOfEntries_sorted_iff L).1 Hsorted) i z (ki, k, m) hi hk.symm
  have hidx : mvcc.idxOfEntries (L.set i (ki, k, m)) = mvcc.idxOfEntries L := by
    rw [mvcc.idxOfEntries_set]
    have h1 : ((ki, k, m) : mvcc.IdxEntry).2.1 = z.2.1 := hk.symm
    have h2 : ((ki, k, m) : mvcc.IdxEntry).2.2 = z.2.2 := hz.symm
    rw [h1, h2]
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hi
    have : (mvcc.idxOfEntries L)[i]'(by unfold mvcc.idxOfEntries; rw [List.length_map]; exact hlt) =
        (z.2.1, z.2.2) := by
      unfold mvcc.idxOfEntries; rw [List.getElem_map, hget]
    rw [← this, List.set_getElem_self]
  -- the deferred `ti.Unlock()`
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Unlock")]
  wp_call
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HnevL Ht Hback Hki]
  · inext
    iunfold mvcc.idxLockInv
    iexists ilog', pend', btInsert mvcc.entryLess (ki, k, m) L, cmax
    simp only [named]
    iframe HnevL
    isplitl []
    · iexact HhistL
    isplitl [Ht Hback Hki]
    · iunfold mvcc.ownTree
      rw [mvcc.itemsOfEntries_btInsert]
      isplitl []
      · ipureintro; exact btInsert_sorted mvcc.kiItemLess_swo Hsorted
      iframe Ht
      rw [hset]
      iapply Hback
      iunfold mvcc.ownEntry
      isplitl []
      · ipureintro; exact Hn
      iexists gs
      iexact Hki
    isplitl []
    · iexact HcrevL
    isplitl []
    · iexact HclL
    ipureintro
    refine ⟨?_, HwfL⟩
    rw [hset, hidx]
    exact HLL
  (try wp_auto)
  iapply HΦ
  iframe Hcu
  isplitl [Hauth Hlauth]
  · iunfold mvcc.idxWriter
    iframe Hauth Hlauth
    isplitl []
    · iexact Hwlb
    ipureintro; exact Hwwf
  iexists z.1, gs'
  isplitl []
  · ipureintro; exact Hzn
  isplitl []
  · rw [← hk]; iexact Hkold
  rw [← hz]
  iexact Hzki

end proof

end EtcdGrove
end Perennial
