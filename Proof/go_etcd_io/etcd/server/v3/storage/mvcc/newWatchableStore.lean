/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup
public import Spec.go_uber_org.zap.NewNop
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
    (hsplit : adt.ownIvt_split.spec (GF := GF) (hG := hG)) :
    mvcc.newWatchableStore.spec (GF := GF) (hG := hG) := by
  intro lg b le cfg γb γl P f
  wp_start as ⟨Hbk, Hbv, #Hlessor⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  wp_join iprop(∃ lg' : Loc, lg_ptr ↦ lg') with [lg] as ⟨%lg', lg⟩
  · wp_apply hNop as %l %Hl
    isplitr
    · ipureintro; rfl
    iexists l; iexact lg
  wp_apply hNewStore $$ [$Hbk $Hbv $Hlessor] as %st ⟨%γs, ⟨%hγb, %hγl⟩, #Hst, #HhookP, Hviews,
    Hreaders, Htoks, #Hcert, Hsclose⟩
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
  icases Hlessor1 with ⟨%li, %Hli, -, -, -, #HSetRD⟩
  subst Hli
  -- the read view, read-only for good
  iStructNamed Hrv
  ipersist kv
  ipersist HRV
  -- the ghost state
  imod ghost_map_alloc_empty (K := Loc) (V := mvcc.WatcherNames) (GF := GF) with ⟨%γm, Hmeta⟩
  imod ghostVar_alloc (GF := GF) ([[], []] : mvcc.Log) with ⟨%γwl, Hwl⟩
  icases (mvcc.ghostVar_halves_nw γwl _).1 $$ Hwl with ⟨Hwl1, Hwl2⟩
  imod ghostVar_alloc (GF := GF) mvcc.wsInit with ⟨%γwst, Hwst⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γt, Hta⟩
  imod ownTokAuth_add (2 ^ 63 - 3) γt 0 $$ Hta with ⟨Hta, Htw⟩
  let γ : mvcc.WsNames := ⟨γs, γm, γwl, γwst, γt⟩
  ihave Hwt : mvcc.watchBudget γ 1 (∅ : GMap Loc mvcc.WatcherNames) $$ [Hta]
  · iunfold mvcc.watchBudget
    iexists 0 + (2 ^ 63 - 3)
    iframe Hta
    ipureintro; rw [GMap.map_size_empty]; omega
  ihave Hsy := Hgs $$ %(mvcc.syncedAddr «$r0_ptr») synced
  ihave Hun := Hgu $$ %(mvcc.unsyncedAddr «$r0_ptr») unsynced
  ihave Hbody : mvcc.watchStoreInv «$r0_ptr» γ 1 $$ [Hwst Hwl1 Hsy Hun victims Hmeta Hwt]
  · iunfold mvcc.watchStoreInv
    iexists mvcc.wsInit
    iunfold mvcc.watchStoreBody
    simp only [named, mvcc.wsInit]
    iframe Hwst Hsy Hun victims Hmeta Hwt
    isplitl [Hwl1]
    · iexact Hwl1
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
  icases mvcc.guard_of_slots_nw _ _ $$ Hmus with ⟨Hmus, #Hmug⟩
  -- the channels
  imod start_bag (V := Unit) (fun _ => iprop(True)) _ vc γv trivial $$ Hvc Hvown with #Hvcb
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γstc stc $$ Hstc Hstown with Hstop
  ihave #Hstop0 := ownBroadcastChan_Unknown _ _ _ _ $$ Hstop
  (try wp_auto)
  wp_apply HSetRD
  (try wp_auto)
  iapply HΦ
  iexists st, γ
  isplitr
  · ipureintro; exact ⟨hγb, hγl⟩
  isplitr
  · iunfold mvcc.isWatchableStore
    iexists vc, stc, rv, γv
    simp only [named]
    iframe store Hst HRV kv Hmug victimc Hvcb stopc
    iunfold mvcc.isStopChan
    iexists γstc; iexact Hstop0
  iframe HhookP Hsclose wg
  isplitr [Hmus Hreaders Hstop Htw]
  · iunfold mvcc.watchWriter
    iframe Hcert Hwl2
    have hb : mvcc.wBudget [[], []] = 2 ^ 63 - 5 := by unfold mvcc.wBudget; rfl
    rw [hb]; iexact Htoks
  isplitl [Htw]
  · iunfold mvcc.watchToks; iexact Htw
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
