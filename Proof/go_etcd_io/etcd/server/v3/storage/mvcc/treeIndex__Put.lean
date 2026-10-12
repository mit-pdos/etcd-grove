/-
Proof of `Spec/.../mvcc/treeIndex__Put.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Put
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__put
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Get
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

/-- The writer's history and the lock's agree on the events (the lock's is a prefix with at
least as many events). -/
theorem writer_events (ilog ilog' : mvcc.Log) (pend pend' : List mvcc.Change)
    (hpre : mvcc.histShape ilog' pend' <+: mvcc.histShape ilog pend)
    (hcnt : (mvcc.evsOf (ilog ++ [pend])).length ≤ (mvcc.evsOf (ilog' ++ [pend'])).length) :
    mvcc.evsOf (ilog' ++ [pend']) = mvcc.evsOf (ilog ++ [pend]) := by
  have := mvcc.evsOfHist_prefix_eq _ _ hpre (by rw [mvcc.evsOfHist_histShape, mvcc.evsOfHist_histShape]; exact hcnt)
  rw [mvcc.evsOfHist_histShape, mvcc.evsOfHist_histShape] at this
  exact this

theorem mvcc.treeIndex.Put.wp_proof
    (wp_Get : btree.BTree.Get.spec (GF := GF) (hG := hG))
    (wp_ROI : btree.BTree.ReplaceOrInsert.spec (GF := GF) (hG := hG))
    (hPut : mvcc.keyIndex.put.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Put.spec (GF := GF) (hG := hG) := by
  have wp_Get : btree.BTree.Get.modelSpec (GF := GF) (hG := hG) := btree.BTree.Get.modelSpec_of wp_Get
  have wp_ROI : btree.BTree.ReplaceOrInsert.modelSpec (GF := GF) (hG := hG) :=
    btree.BTree.ReplaceOrInsert.modelSpec_of wp_ROI
  intro ti γ ilog pend key k rev v l
  wp_start as ⟨#Hti, Hw, #Hkey, %Hpre⟩
  obtain ⟨Hrev, Hilog, Hpend, Hwf'⟩ := Hpre
  iunfold mvcc.isTreeIndex at Hti
  iNamed Hti
  iunfold mvcc.idxWriter at Hw
  icases Hw with ⟨Hauth, #Hwlb, %Hwwf, Hlauth⟩
  obtain ⟨Hwf, Hlen, Hplen, Hcs⟩ := Hwwf
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  -- `keyi := &keyIndex{key: key}`
  ihave %Hn := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamedPrefix «$r0» "K"
  ipersist Kkey
  ihave #Hitem : mvcc.kiItemIs (GF := GF) «$r0_ptr» («$r0_ptr», k) $$ []
  · iunfold mvcc.kiItemIs
    isplitl []
    · ipureintro; rfl
    iunfold mvcc.kiKey
    iexists key
    iframe #
  -- `ti.Lock()`: the promoted method, through the guard
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.idxLockInv t γ 1)) $$ Hlc1 HP with HP
  iunfold mvcc.idxLockInv at HP
  icases HP with ⟨%ilog', %pend', %L, HP⟩
  iNamedSuffix HP "L"
  -- the lock's events are the writer's
  ihave %Hpre := mono_list_auth_lb_valid γ.hist 1 _ _ $$ Hauth HhistL
  ihave %Hcnt := monoNatLbOwn_valid γ.nev 1 _ _ $$ HnevL Hwlb
  have hevs := writer_events ilog ilog' pend pend' Hpre.2 Hcnt.2
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
  have hev : mvcc.evOfChange ilog.length pend.length (.put k v l) =
      { rev := ⟨W64 ilog.length, W64 pend.length⟩, key := k, tomb := false } := rfl
  have hwf'' : mvcc.IdxWf ilog (pend ++ [.put k v l]) :=
    ⟨Hwf', Hlen, by simp; omega, Hcs⟩
  have hidxnew : mvcc.indexOf (mvcc.evsOf (ilog ++ [pend ++ [.put k v l]])) =
      mvcc.idxPut (mvcc.idxOfEntries L) k ⟨W64 ilog.length, W64 pend.length⟩ := by
    rw [mvcc.evsOf_append_change, mvcc.indexOf_append_ev, ← HLL, hev]; rfl
  have hcount : (mvcc.evsOf (ilog ++ [pend ++ [.put k v l]])).length =
      (mvcc.evsOf (ilog ++ [pend])).length + 1 := by
    rw [mvcc.evsOf_append_change, List.length_append, List.length_singleton]
  -- the ghost steps: the event is put, the count grows
  imod monoListAuthOwn_update_app [mvcc.HistItem.ev (mvcc.evOfChange ilog.length pend.length (.put k v l))]
    $$ Hauth with ⟨Hauth, #Hlb'⟩
  imod mono_nat_own_update ((mvcc.evsOf (ilog ++ [pend])).length + 1) (by rw [hevs]; omega)
    $$ HnevL with ⟨HnevL, #Hnlb'⟩
  generalize btFind mvcc.kiItemLess («$r0_ptr», k) (mvcc.itemsOfEntries L) = f at Hfind ⊢
  cases f with
  | none =>
    icases Hres with % ⟨Hok, Hitem0⟩
    subst Hok Hitem0
    have hf : L.find? (fun z => decide (z.2.1 = k)) = none := by
      cases hf : L.find? (fun z => decide (z.2.1 = k)) with
      | none => rfl
      | some z => rw [hf] at Hfind; simp at Hfind
    rw [hf] at Hidx
    simp only [Option.map_none] at Hidx
    (try wp_auto)
    -- `keyi.put(ti.lg, rev.Main, rev.Sub)` on the fresh key index
    ihave Hki : mvcc.ownKi (GF := GF) «$r0_ptr» slice.nil mvcc.KeyIndex.fresh (DFrac.own 1)
        $$ [Kmodified Kgenerations]
    · iunfold mvcc.ownKi
      iframe Kgenerations
      isplitl [Kmodified]
      · rw [show mvcc.revVal mvcc.KeyIndex.fresh.modified = (zeroValDef : Revision) from rfl]
        iexact Kmodified
      iunfold mvcc.ownGens
      iexists []
      isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      simp only [mvcc.KeyIndex.fresh, mvcc.ownGensL]
      itrivial
    have Hlt : mvcc.Rev.lt mvcc.Rev.zero ⟨rev.Main', rev.Sub'⟩ := by
      rw [hrevm, hrevs]; exact mvcc.Rev.lt_zero_of_pos _ _ Hilog (by omega)
    wp_apply (hPut «$r0_ptr» slice.nil mvcc.KeyIndex.fresh lg rev.Main' rev.Sub') $$ [$Hki]
      as %r Hr
    · ipureintro; exact ⟨Hlgnn, Hlt⟩
    icases Hr with ⟨%Hr, %gs', Hki⟩
    subst Hr
    (try wp_auto)
    -- `ti.tree.ReplaceOrInsert(keyi)`
    wp_apply (wp_ROI mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess _ «$r0_ptr» («$r0_ptr», k))
      $$ [$Ht $Hitem] as %old %ok2 ⟨Ht, -⟩
    · ipureintro; exact mvcc.kiItemLess_swo
    (try wp_auto)
    -- the deferred `ti.Unlock()`
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HnevL Ht Hkis Hki]
    · inext
      iunfold mvcc.idxLockInv
      iexists ilog, pend ++ [.put k v l],
        btInsert mvcc.entryLess («$r0_ptr», k, mvcc.kiPut mvcc.KeyIndex.fresh ⟨W64 ilog.length, W64 pend.length⟩) L
      simp only [named]
      rw [← mvcc.histShape_ev, hcount]
      iframe HnevL
      isplitl []
      · iexact Hlb'
      isplitl [Ht Hkis Hki]
      · iunfold mvcc.ownTree
        rw [mvcc.itemsOfEntries_btInsert]
        isplitl []
        · ipureintro; exact btInsert_sorted mvcc.kiItemLess_swo Hsorted
        iframe Ht
        iapply mvcc.bigSepL_ownEntry_insert
        iframe Hkis
        iunfold mvcc.ownEntry
        isplitl []
        · ipureintro; exact Hn
        iexists gs'
        rw [← hrevm, ← hrevs]
        iexact Hki
      ipureintro
      refine ⟨?_, hwf''⟩
      rw [mvcc.idxOfEntries_btInsert, hidxnew]
      simp only [mvcc.idxPut, Hidx]
    (try wp_auto)
    iapply HΦ
    iunfold mvcc.idxWriter
    rw [← mvcc.histShape_ev, hcount]
    iframe Hauth Hlauth
    isplitl []
    · iexact Hnlb'
    ipureintro; exact hwf''
  | some w =>
    icases Hres with ⟨%Hok, #Hitemw⟩
    subst Hok
    iunfold mvcc.kiItemIs at Hitemw
    icases Hitemw with ⟨%Hiw, -⟩
    obtain ⟨z, hf, hwz⟩ : ∃ z, L.find? (fun z => decide (z.2.1 = k)) = some z ∧ w = (z.1, z.2.1) := by
      cases hf : L.find? (fun z => decide (z.2.1 = k)) with
      | none => rw [hf] at Hfind; simp at Hfind
      | some z => rw [hf] at Hfind; simp only [Option.map_some, Option.some.injEq] at Hfind; exact ⟨z, rfl, Hfind⟩
    subst hwz
    rw [hf] at Hidx
    simp only [Option.map_some] at Hidx
    obtain ⟨i, hi, hk⟩ := mvcc.find?_entry_getElem? L k z hf
    have hz : z.2.2 = mvcc.kiOfKey (mvcc.evsOf (ilog ++ [pend])) k := by
      have := (mvcc.indexOf_rep (mvcc.evsOf (ilog ++ [pend]))).2 k
      rw [← HLL, Hidx] at this
      exact this
    (try wp_auto)
    -- `okeyi.put(ti.lg, rev.Main, rev.Sub)` on the key's index, borrowed from the tree
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
    wp_apply (hPut z.1 gs z.2.2 lg rev.Main' rev.Sub') $$ [$Hki] as %r Hr
    · ipureintro; exact ⟨Hlgnn, Hlt⟩
    icases Hr with ⟨%Hr, %gs', Hki⟩
    subst Hr
    (try wp_auto)
    -- the deferred `ti.Unlock()`
    (try wp_auto)
    have hset : mvcc.itemsOfEntries (L.set i (z.1, z.2.1, mvcc.kiPut z.2.2 ⟨W64 ilog.length, W64 pend.length⟩)) =
        mvcc.itemsOfEntries L := mvcc.itemsOfEntries_set L i z _ hi rfl rfl
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HnevL Ht Hback Hki]
    · inext
      iunfold mvcc.idxLockInv
      iexists ilog, pend ++ [.put k v l],
        L.set i (z.1, z.2.1, mvcc.kiPut z.2.2 ⟨W64 ilog.length, W64 pend.length⟩)
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
      simp only [mvcc.idxPut, Hidx]
    (try wp_auto)
    iapply HΦ
    iunfold mvcc.idxWriter
    rw [← mvcc.histShape_ev, hcount]
    iframe Hauth Hlauth
    isplitl []
    · iexact Hnlb'
    ipureintro; exact hwf''

end proof

end EtcdGrove
end Perennial
