/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Write
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchFrac
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewWatchableLemmas

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

theorem mvcc.newWatchableStore.wp_proof
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hNewStore : mvcc.NewStore.spec (GF := GF) (hG := hG))
    (hNewWG : mvcc.newWatcherGroup.spec (GF := GF) (hG := hG))
    (hsplit : adt.ownIvt_split.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.watchableStore.Write.spec (GF := GF) (hG := hG))
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG)) :
    mvcc.newWatchableStore.spec (GF := GF) (hG := hG) := by
  intro lg b le cfg kb γb γl P f rd0 γi γok γtag Hcfg0 Hrb0
  wp_start as ⟨Hbk, Hbv, Hncmp, Hrg, Hwt1, Hwt2, Hrts, Hlrd, #Hlessor, Hro, Hifresh, Hok0⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  wp_join iprop(∃ lg' : Loc, lg_ptr ↦ lg') with [lg] as ⟨%lg', lg⟩
  · wp_apply hNop as %l %Hl
    isplitr
    · ipureintro; rfl
    iexists l; iexact lg
  wp_apply (hNewStore _ _ _ _ _ _ _ _ f _ true γi γok Hcfg0 Hrb0)
    $$ [$Hbk $Hbv $Hncmp $Hrg $Hwt1 $Hwt2 $Hrts $Hlrd $Hlessor $Hro $Hifresh $Hok0] as %st
    ⟨%γs, ⟨%hγb, %hγl, %hγk, %hγw, %hγi, %hγok⟩, #Hst, ⟨%rd1, Hro⟩, Hok, #HhookP, Hviews, Hreaders, Htoks, #Hcert, HlogQ, Hsclose, Hfw,
      Hwsd, Hfrag, Hright⟩
  -- the watchable store never compacts its store (compaction is out of its model): the right's
  -- half of the revision's authority given up, the readers those of a never-compacted store (the
  -- closer, with the scheduler's stop token, goes to the caller: D19m (C))
  imod mvcc.crevFrozen_alloc γs ⊤ $$ Hright with #Hfrz
  ihave Hreaders := mvcc.storeReaders_of st γs _ $$ [$Hfrz $Hreaders]
  wp_apply chan.wp_make2 (V := Unit) $$ [] as %vc %γv ⟨#Hvc, %Hvcap, Hvown⟩
  · ipureintro; decide
  wp_apply hNewWG as %gu Hgu
  wp_apply hNewWG as %gs Hgs
  wp_apply chan.wp_make1 (V := Unit) as %stc %γstc ⟨#Hstc, %Hstcap, Hstown⟩
  iStructNamed «$r0»
  icases Hviews with ⟨%rv0, %wv0, HRV, -, HWV, -⟩
  ipersist store
  ipersist victimc
  ipersist stopc
  ihave #Hst' := Hst
  iunfold mvcc.isStore at Hst'
  iNamed Hst'
  wp_alloc rv as Hrv
  (try wp_auto)
  wp_alloc wv as Hwv
  (try wp_auto)
  ihave #Hlessor1 := Hlessor
  iunfold mvcc.isLessor at Hlessor1
  icases Hlessor1 with ⟨%lp, %Hli, -, -, -, -, #HSetRD⟩
  subst Hli
  -- the read view, read-only for good
  iStructNamed Hrv
  ipersist kv
  ipersist HRV
  -- the ghost state
  imod ghost_map_alloc_empty (K := Loc) (V := mvcc.WatcherNames) (GF := GF) with ⟨%γm, Hmeta⟩
  imod mono_list_own_alloc (GF := GF) ([[], []] : mvcc.Log) with ⟨%γwl, Hwl, -⟩
  ihave ⟨Hwl1, Hwl2⟩ : iprop(monoListAuthOwn (GF := GF) γwl (1 : Qp).half ([[], []] : mvcc.Log) ∗
      monoListAuthOwn γwl (1 : Qp).half ([[], []] : mvcc.Log)) $$ [Hwl]
  · iapply (mvcc.monoList_halves γwl ([[], []] : mvcc.Log)).1 $$ Hwl
  imod ghostVar_alloc (GF := GF) mvcc.wsInit with ⟨%γwst, Hwst⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γt, Hta⟩
  imod ownTokAuth_add (2 ^ 63 - 3) γt 0 $$ Hta with ⟨Hta, Htw⟩
  imod mono_nat_own_alloc (GF := GF) mvcc.wsInit.Lmu.length with ⟨%γrel, Hrel, -⟩
  let γ : mvcc.WsNames := ⟨γs, γm, γwl, γwst, γt, γrel, γtag⟩
  ihave Hwt : mvcc.watchBudget γ 1 (∅ : GMap Loc mvcc.WatcherNames) $$ [Hta]
  · iunfold mvcc.watchBudget
    iexists 0 + (2 ^ 63 - 3)
    iframe Hta
    ipureintro; rw [GMap.map_size_empty]; omega
  ihave Hsy := Hgs $$ %(mvcc.syncedAddr «$r0_ptr») synced
  ihave Hun := Hgu $$ %(mvcc.unsyncedAddr «$r0_ptr») unsynced
  -- the outer quarter of the committed log's authority, `s.mu`'s (unit W-K)
  ihave HlogQ : mvcc.logQ γs [[], []] $$ [HlogQ]
  · have h : (if true = true then mvcc.logQ (GF := GF) γs [[], []] else iprop(True)) =
        mvcc.logQ γs [[], []] := by simp
    rw [← h]; iexact HlogQ
  -- the inner store's fields: the watchable store's share (D22 receiver epochs, S3)
  ihave Hwsf : mvcc.wsFields «$r0_ptr» γ 1 $$ [Hfw Hwsd]
  · iunfold mvcc.wsFields; iexists st; iframe store Hfw; iunfold mvcc.wsDep at Hwsd; iexact Hwsd
  ihave Hbody : mvcc.watchStoreInv «$r0_ptr» γ 1 $$ [Hwst Hwl1 Hsy Hun victims Hmeta Hwt HlogQ Hrel Hwsf]
  · iunfold mvcc.watchStoreInv
    iexists mvcc.wsInit
    isplitl [Hwst Hwl1 Hsy Hun victims Hmeta Hwt HlogQ]
    rotate_left
    · iframe Hrel Hwsf; ipureintro; exact ⟨mvcc.wsInit_settled, fun w γw h => by simp [mvcc.wsInit, GMap.lookup_empty] at h,
        fun w st h => by simp [mvcc.wsInit, GMap.lookup_empty] at h⟩
    iunfold mvcc.watchStoreBody
    simp only [named, mvcc.wsInit]
    iframe Hwst Hsy Hun victims Hmeta Hwt
    isplitl [Hwl1 HlogQ]
    · iunfold mvcc.wlogQ; iframe Hwl1; iexact HlogQ
    isplitr
    · iexact Hcert
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · ipureintro; rfl
    isplitr
    · rw [List.zip_nil_left]; iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    ipureintro; exact mvcc.wsInit_ok
  haveI := mvcc.watchStoreInv_fractional hsplit «$r0_ptr» γ
  imod sync.init_RWMutex (mvcc.watchStoreInv «$r0_ptr» γ) (mvcc.wsMuAddr «$r0_ptr») $$ Hbody mu with Hmus
  icases sync.ownRWMutex_slots_guard _ _ $$ Hmus with ⟨Hmus, #Hmug⟩
  -- the channels
  imod start_bag (V := Unit) (fun _ => iprop(True)) _ vc γv trivial $$ Hvc Hvown with #Hvcb
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γstc stc $$ Hstc Hstown with Hstop
  ihave #Hstop0 := ownBroadcastChan_Unknown _ _ _ _ $$ Hstop
  ihave #Hws : mvcc.isWatchableStore «$r0_ptr» st γ $$ []
  · iunfold mvcc.isWatchableStore
    iexists vc, stc, rv, γv
    simp only [named]
    iframe store Hst HRV kv Hmug victimc Hvcb stopc
    isplitr
    · iunfold mvcc.isStopChan
      iexists γstc; iexact Hstop0
    ipureintro; exact hγw
  ipersist s
  (try wp_auto)
  wp_apply HSetRD $$ [Hro] as Hro
  · rw [hγl]; iexact Hro
  (try wp_auto)
  iapply HΦ
  iexists st, γ
  isplitr
  · ipureintro; exact ⟨hγb, hγl, hγk, hγi, hγok, rfl⟩
  isplitr
  · iexact Hws
  isplitl [Hro]
  · iexists _; rw [← hγl]; iframe Hro
    -- the deleter: `s.Write(traceutil.TODO())`, as a `lease.TxnDelete`
    iunfold mvcc.rdIs
    isplitr
    · ipureintro; intro h; injection h with _ _ h3; cases h3
    iintro !> %L %Pw %Pre %Q %fw %Φ' !> ⟨Hrd, Hwt, Hww, %Hlen, Hh, Hpre, #Hfw⟩ HΦ'
    ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
    · iPkgInit
    ihave #Hmpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
    · iPkgInit
    wp_auto
    wp_apply hTODO as %tr ⟨%Htrnn, Htr⟩
    wp_apply (hWrite «$r0_ptr» st γ tr L Pw Pre Q fw true)
      $$ [$Hrd $Hwt $Hww $Hh $Hpre $Htr] as %tw ⟨Htw, HQ, Hh'⟩
    · iframe #
      ipureintro; exact ⟨Hlen, Htrnn⟩
    iapply HΦ'
    iframe Htw HQ Hh'
  iframe HhookP Hsclose wg Hfrag
  isplitr [Hmus Hreaders Hstop Htw Hok]
  · iunfold mvcc.watchWriter
    iframe Hcert Hwl2
    have hb : mvcc.wBudget [[], []] = 2 ^ 63 - 5 := by unfold mvcc.wBudget; rfl
    rw [hb]; iexact Htoks
  isplitl [Htw]
  · iunfold mvcc.watchToks; iexact Htw
  isplitl [Hok]
  · iexact Hok
  isplitr [Hstop]
  · iapply mvcc.watchReaders_of «$r0_ptr» st γ
    iframe Hreaders Hmus
  iexists stc
  iframe stopc
  iunfold mvcc.stopCloser
  iexists γstc; iexact Hstop

end proof

end EtcdGrove
end Perennial
