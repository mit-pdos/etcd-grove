/-
Proof of `Spec/.../mvcc/treeIndex__Tombstone.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Tombstone
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__tombstone
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Get
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

theorem mvcc.treeIndex.Tombstone.wp_proof
    (wp_Get : btree.BTree.Get.spec (GF := GF) (hG := hG))
    (hTomb : mvcc.keyIndex.tombstone.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Tombstone.spec (GF := GF) (hG := hG) := by
  have wp_Get : btree.BTree.Get.modelSpec (GF := GF) (hG := hG) := btree.BTree.Get.modelSpec_of wp_Get
  intro ti γ ilog pend key k rev
  wp_start as ⟨#Hti, Hw, #Hkey, %Hpre⟩
  obtain ⟨Hrev, Hilog, Hpend, Hwf'⟩ := Hpre
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨⟨%e, #Herr⟩, -, -, -, -, -, -, -, -⟩
  iunfold mvcc.isTreeIndex at Hti
  iNamed Hti
  iunfold mvcc.idxWriter at Hw
  icases Hw with ⟨Hauth, #Hwlb, %Hwwf⟩
  obtain ⟨Hwf, Hlen, Hplen, Hcs⟩ := Hwwf
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  -- `keyi := &keyIndex{key: key}`
  iStructNamedPrefix «$r0» "K"
  ipersist Kkey
  ihave #Hitem : mvcc.kiItemIs (GF := GF) «$r0_ptr» («$r0_ptr», k) $$ []
  · iunfold mvcc.kiItemIs
    isplitl []
    · ipureintro; rfl
    iunfold mvcc.kiKey
    iexists key
    iframe #
  -- `ti.Lock()`
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Lock")]
  wp_call
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.idxLockInv t γ 1)) $$ Hlc1 HP with HP
  iunfold mvcc.idxLockInv at HP
  icases HP with ⟨%ilog', %pend', %L, HP⟩
  iNamedSuffix HP "L"
  ihave %Hpre := mono_list_auth_lb_valid γ.hist 1 _ _ $$ Hauth HhistL
  ihave %Hcnt := monoNatLbOwn_valid γ.nev 1 _ _ $$ HnevL Hwlb
  have hevs : mvcc.evsOf (ilog' ++ [pend']) = mvcc.evsOf (ilog ++ [pend]) := by
    have := mvcc.evsOfHist_prefix_eq _ _ Hpre.2
      (by rw [mvcc.evsOfHist_histShape, mvcc.evsOfHist_histShape]; exact Hcnt.2)
    rw [mvcc.evsOfHist_histShape, mvcc.evsOfHist_histShape] at this
    exact this
  rw [hevs] at HLL
  iunfold mvcc.ownTree at HtreeL
  icases HtreeL with ⟨%Hsorted, Ht, Hkis⟩
  wp_apply (wp_Get mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess _ _ «$r0_ptr» («$r0_ptr», k))
    $$ [$Ht $Hitem] as %item %ok ⟨Ht, Hres⟩
  · ipureintro; exact mvcc.kiItemLess_swo
  have Hfind := mvcc.btFind_items L Hsorted «$r0_ptr» k
  have Hidx := mvcc.idxGet_entries L Hsorted k
  have hrevm : rev.Main' = W64 ilog.length := congrArg mvcc.Rev.main Hrev
  have hrevs : rev.Sub' = W64 pend.length := congrArg mvcc.Rev.sub Hrev
  have hwf'' : mvcc.IdxWf ilog (pend ++ [.del k]) := ⟨Hwf', Hlen, by simp; omega, Hcs⟩
  have hidxnew : mvcc.indexOf (mvcc.evsOf (ilog ++ [pend ++ [.del k]])) =
      mvcc.idxTombstone (mvcc.idxOfEntries L) k ⟨W64 ilog.length, W64 pend.length⟩ := by
    rw [mvcc.evsOf_append_change, mvcc.indexOf_append_ev, ← HLL, mvcc.evOfChange_del]; rfl
  have hcount : (mvcc.evsOf (ilog ++ [pend ++ [.del k]])).length =
      (mvcc.evsOf (ilog ++ [pend])).length + 1 := by
    rw [mvcc.evsOf_append_change, List.length_append, List.length_singleton]
  have hlast : mvcc.kiLastEmpty (mvcc.kiOfKey (mvcc.evsOf (ilog ++ [pend])) k) = false :=
    mvcc.kiLastEmpty_false_of_del ilog pend k Hwf Hwf' Hlen Hilog Hplen Hcs
  -- the key has an index (its last generation is not empty)
  obtain ⟨z, hf, hwz⟩ : ∃ z, L.find? (fun z => decide (z.2.1 = k)) = some z ∧
      btFind mvcc.kiItemLess («$r0_ptr», k) (mvcc.itemsOfEntries L) = some (z.1, z.2.1) := by
    cases hf : L.find? (fun z => decide (z.2.1 = k)) with
    | none =>
      exfalso
      rw [hf] at Hidx
      have := (mvcc.indexOf_rep (mvcc.evsOf (ilog ++ [pend]))).2 k
      rw [← HLL, Hidx] at this
      simp only [Option.map_none, Option.getD_none] at this
      rw [← this] at hlast
      exact absurd hlast (by rw [mvcc.kiLastEmpty_kiEmpty]; decide)
    | some z => exact ⟨z, rfl, by rw [Hfind, hf]; rfl⟩
  rw [hwz]
  icases Hres with ⟨%Hok, #Hitemw⟩
  subst Hok
  iunfold mvcc.kiItemIs at Hitemw
  icases Hitemw with ⟨%Hiw, #HzKey⟩
  rw [hf] at Hidx
  simp only [Option.map_some] at Hidx
  obtain ⟨i, hi, hk⟩ := mvcc.find?_entry_getElem? L k z hf
  have hz : z.2.2 = mvcc.kiOfKey (mvcc.evsOf (ilog ++ [pend])) k := by
    have := (mvcc.indexOf_rep (mvcc.evsOf (ilog ++ [pend]))).2 k
    rw [← HLL, Hidx] at this
    exact this
  rw [← hz] at hlast
  have hne := mvcc.kiIsEmpty_false_of_head (mvcc.indexOf_head' _ (z.2.1, z.2.2)
    (by rw [← HLL]; unfold mvcc.idxOfEntries; exact List.mem_map_of_mem (List.mem_of_getElem? hi)))
  -- the ghost steps
  imod monoListAuthOwn_update_app [mvcc.HistItem.ev (mvcc.evOfChange ilog.length pend.length (.del k))]
    $$ Hauth with ⟨Hauth, #Hlb'⟩
  imod mono_nat_own_update ((mvcc.evsOf (ilog ++ [pend])).length + 1) (by rw [hevs]; omega)
    $$ HnevL with ⟨HnevL, #Hnlb'⟩
  (try wp_auto)
  -- `ki.tombstone(ti.lg, rev.Main, rev.Sub)` on the key's index, borrowed from the tree
  icases BigSepL.bigSepL_lookup_acc (Φ := fun _ z => mvcc.ownEntry (GF := GF) z 1) hi |>.1 $$ Hkis
    with ⟨Hz, Hback⟩
  iunfold mvcc.ownEntry at Hz
  icases Hz with ⟨%Hzn, %gs, Hki⟩
  simp only at Hiw
  rw [Hiw]
  have Hlt : mvcc.Rev.lt z.2.2.modified ⟨rev.Main', rev.Sub'⟩ := by
    rw [hrevm, hrevs, hz, mvcc.kiOfKey_eq_kiFold]
    exact mvcc.kiFold_modified_lt k _ _ _ (mvcc.Rev.lt_zero_of_pos _ _ Hilog (by omega))
      (mvcc.evsOf_rev_lt ilog pend (by omega) Hplen)
  wp_apply (hTomb z.1 gs z.2.2 z.2.1 lg rev.Main' rev.Sub' _) $$ [$HzKey $Hki $Herr] as %err Hpost
  · ipureintro; exact ⟨Hlgnn, hne.2⟩
  rw [hne.1, hlast]
  simp only [Hlt, Bool.false_eq_true, ↓reduceIte]
  icases Hpost with ⟨%Herr', %gs', Hki⟩
  subst Herr'
  (try wp_auto)
  -- the deferred `ti.Unlock()`
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Unlock")]
  wp_call
  (try wp_auto)
  have hset : mvcc.itemsOfEntries (L.set i (z.1, z.2.1, mvcc.kiTombstone z.2.2 ⟨W64 ilog.length, W64 pend.length⟩)) =
      mvcc.itemsOfEntries L := mvcc.itemsOfEntries_set L i z _ hi rfl rfl
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HnevL Ht Hback Hki]
  · inext
    iunfold mvcc.idxLockInv
    iexists ilog, pend ++ [.del k],
      L.set i (z.1, z.2.1, mvcc.kiTombstone z.2.2 ⟨W64 ilog.length, W64 pend.length⟩)
    simp only [named]
    rw [← mvcc.histShape_ev, hcount]
    iframe HnevL
    isplitl []
    · iexact Hlb'
    isplitl [Ht Hback Hki]
    · iunfold mvcc.ownTree
      rw [hset]
      isplitl []
      · ipureintro; exact Hsorted
      iframe Ht
      iapply Hback
      iunfold mvcc.ownEntry
      isplitl []
      · ipureintro; exact Hzn
      iexists gs'
      rw [← hrevm, ← hrevs]
      iexact Hki
    ipureintro
    refine ⟨?_, hwf''⟩
    rw [hidxnew, ← mvcc.btInsert_idx_set L Hsorted i z (List.getElem?_eq_some_iff.1 hi), hk]
    simp only [mvcc.idxTombstone, Hidx, hlast, Bool.false_eq_true, ↓reduceIte]
  (try wp_auto)
  iapply HΦ
  iunfold mvcc.idxWriter
  rw [← mvcc.histShape_ev, hcount]
  iframe Hauth
  isplitl []
  · iexact Hnlb'
  ipureintro; exact hwf''

end proof

end EtcdGrove
end Perennial
