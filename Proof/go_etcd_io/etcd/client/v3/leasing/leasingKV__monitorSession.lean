/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__monitorSession.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__monitorSession
public import Spec.go_etcd_io.etcd.client.v3.concurrency.NewSession
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Done
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingSessionLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.monitorSession.wp_proof
    (hNS : EtcdGrove.concurrency.NewSession.spec (GF := GF) (hG := hG))
    (hDone : EtcdGrove.concurrency.Session.Done.spec (GF := GF) (hG := hG)) :
    leasingKV.monitorSession.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx
  wp_start as ⟨#Hlkv, Hmon⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, #Hclf, #Hkvf, #Hpfxf, #Hctxf,
    #Hcancelf, #Hoslf, #HKV, #HDo, #HTxn, #HLC, #Hlctx, #Hlcc, #Hcache, #Hwg, #Hwginv, %Hbound⟩
  ihave #Hctx' : iprop(context.isContextDef lctx lcs) $$ [Hlctx]
  · iexact Hlctx
  unfold context.isContextDef
  iNamed Hctx'
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency $$ []
  · iPkgInit
  unfold lkvCache isLeaseCache
  icases Hcache with ⟨#Hguard, #Hcl⟩
  iunfold isLeasingClient at HLC
  icases HLC with ⟨-, -, -, %cctx, %gs, %pctx, %pcs, #Hscl, #Hopts, %Hpctx, #Hpc, #Hpcc⟩
  wp_auto
  ipersist lkv
  ihave HI : iprop("Hmon" ∷ sessionMonitor lkv γ) $$ [Hmon]
  · iexact Hmon
  wp_for HI
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  wp_apply HErrU as %err0 Herr0
  cases err0 with
  | ok e =>
    (try wp_auto)
    simp only [goose_wp_simp_extra, Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
  (try wp_auto)
  simp only [goose_wp_simp_extra, ↓reduceIte]
  iunfold sessionMonitor at Hmon
  icases Hmon with ⟨%s, %sc, %γch, %closed, Hs, #Hso, Hsc, Hbc⟩
  wp_auto
  wp_join (Q := fun v => iprop(structFieldRef leasingKV go!"session" lkv ↦{DFrac.own (1 : Qp).half} s ∗
      (⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝))) with [Hs]
  · iframe Hs
    ileft; ipureintro; first | rfl | trivial
  · unfold sessionOk
    simp only [Hif, ↓reduceIte]
    icases Hso with ⟨%γs, %scl, %sid, #Hsess, -⟩
    wp_apply hDone s γs scl sid $$ [$Hcpkg $Hsess] as %dch #Hdch
    wp_apply +noauto HDone as %ch1 %γ1 #Hdone1
    (try wp_auto)
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iunfold concurrency.sessionDoneChan at Hdch
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γs.done
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdch
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hdch
      iintro -
      (try wp_auto)
      iframe Hs
      ileft; ipureintro; first | rfl | trivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.isContextDone_is_chan $$ Hdone1
      iapply context.isContextDone_receive _ _ _ _ $$ Hdone1
      iintro -
      (try wp_auto)
      iframe Hs
      iright; ipureintro; first | rfl | trivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  iintro ⟨Hs, (%Hv | %Hv)⟩
  rotate_left
  · subst Hv
    (try wp_auto)
    wp_for_post
    iapply HΦ
    itrivial
  subst Hv
  (try wp_auto)
  -- the first critical section: a fresh `sessionc` if it was closed, a fresh entries map
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  icases leaseCacheInv_open_w $$ HP with ⟨%st, Hown, HX, Hinst, Hready, #Hfacts, %Hwf, Hclose⟩
  icases leasingX_monitor_open lkv γ st s sc $$ [$HX $Hs $Hsc] with ⟨Hs, Hsc, Hback⟩
  wp_join iprop(∃ (sc' : GoChan) (γch' : ChanNames),
      structFieldRef leasingKV go!"sessionc" lkv ↦ sc' ∗
      ownBroadcastChan sc' γch' (sessionReadyQ γ) .Pending ∗ □ sessioncOk γ sc')
    at next with [Hsc Hbc] as ⟨%sc', %γch', Hsc, Hpend, #Hsco'⟩
  · (try wp_auto)
    cases closed
    · -- `sessionc` still open: the default
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases pending_unknown _ _ _ $$ Hbc with ⟨Hbc, #Hbcu⟩
      wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
          iprop(ownBroadcastChan sc γch (sessionReadyQ γ) .Pending ∗
            structFieldRef leasingKV go!"sessionc" lkv ↦ sc) $$ [] [Hbc Hsc] []
      · iapply BigSepL2.bigSepL2_singleton.2
        iintro ⟨Hbc, Hsc⟩
        simp only [chan.nonblockingAltClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γch
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownBroadcastChan_is_chan $$ Hbcu
        iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ _ $$ Hbc
        isplit
        · itrivial
        · iintro Hbc
          iframe
      · iframe
      · iintro ⟨Hbc, Hsc⟩ -
        (try wp_auto)
        wp_join_done
        iexists sc, γch
        iframe
        unfold sessioncOk
        iexists γch
        iexact Hbcu
    · -- `sessionc` closed: a fresh one
      simp only [↓reduceIte]
      ihave #Hbc' := Hbc
      wp_apply_core chan.wp_select_nonblocking_alt [iprop(False)]
          iprop(structFieldRef leasingKV go!"sessionc" lkv ↦ sc) $$ [] [Hsc] []
      · iapply BigSepL2.bigSepL2_singleton.2
        iintro Hsc
        simp only [chan.nonblockingAltClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γch
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownBroadcastChan_is_chan $$ Hbc'
        iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ _ $$ Hbc'
        isplit
        · iintro -
          (try wp_auto)
          wp_apply +noauto chan.wp_make1 (V := Unit) as %ch %γc ⟨#Hch, %_, Hoc⟩
          imod alloc_broadcast_chan (E := ⊤) (sessionReadyQ γ) γc ch $$ Hch Hoc with Hpend
          icases pending_unknown _ _ _ $$ Hpend with ⟨Hpend, #Hpu⟩
          (try wp_auto)
          wp_join_done
          iexists ch, γc
          iframe
          unfold sessioncOk
          iexists γc
          iexact Hpu
        · itrivial
      · iframe
      · iintro Hsc HF
        iexfalso
        iapply BigSepL.bigSepL_singleton.1 $$ HF
  icases lcOwn_reset _ st $$ Hown with ⟨Hent, Hreset⟩
  wp_apply +noauto wp_map_make1 (K := GoString) (V := Loc) as %m Hm
  ihave %Hmnn := ownMap_not_nil m _ _ $$ Hm
  (try wp_auto)
  imod Hreset $$ %m Hent Hm with Hown
  imod mono_nat_own_update 1 (readyN_le st) $$ Hready with ⟨Hready, #Hlcr⟩
  imod Hback $$ %s %sc' %(st.reset m) %(Nat.le_refl _) Hso Hsco' Hs Hsc with ⟨HX, Hs, Hsc, -, -⟩
  ihave #Hfacts' := lcFacts_reset pfx st m $$ Hfacts
  ihave Hready : monoNatAuthOwn γ.lc.ready 1 (st.reset m).readyN $$ [Hready]
  · rw [reset_readyN st m Hmnn]; iexact Hready
  ihave Hinst : monoListAuthOwn γ.lc.inst 1 (st.reset m).installed $$ [Hinst]
  · rw [show (st.reset m).installed = st.installed from rfl]; iexact Hinst
  imod Hclose $$ %_ %(reset_wf Hwf m) Hfacts' Hinst Hready Hown HX with HP
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
  wp_apply hNS cl cctx osl gs pctx pcs $$ [$Hcpkg $Hscl $Hopts $Hpc $Hpcc] as %s' %err1 Hns
  · ipureintro; exact Hpctx
  icases Hns with (%Hns | ⟨%Hns, %γs, %sid, #Hsess, -⟩)
  · -- no session: try again
    obtain ⟨rfl, Hne⟩ := Hns
    obtain ⟨e1, rfl⟩ : ∃ e, err1 = GoInterface.ok e := by
      cases err1 with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    (try wp_auto)
    wp_for_post
    iframe
    iunfold sessionMonitor
    iexists s, sc', γch', false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    iframe #
  obtain ⟨rfl, Hsnn⟩ := Hns
  (try wp_auto)
  -- the second critical section: set the session, close `sessionc`
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  icases leaseCacheInv_open_w $$ HP with ⟨%st2, Hown, HX, Hinst, Hready, #Hfacts2, %Hwf2, Hclose⟩
  icases leasingX_monitor_open lkv γ st2 s sc' $$ [$HX $Hs $Hsc] with ⟨Hs, Hsc, Hback⟩
  (try wp_auto)
  ihave #Hso' : sessionOk γ s' $$ []
  · unfold sessionOk
    simp only [Hsnn, ↓reduceIte]
    iexists γs, cl, sid
    iframe #
    unfold leaseCacheReady
    iexact Hlcr
  have hn : sessN s' = 1 := by simp [sessN, Hsnn]
  have hle : sessN s ≤ sessN s' := by rw [hn]; unfold sessN; split <;> omega
  imod Hback $$ %s' %sc' %st2 %hle Hso' Hsco' Hs Hsc with ⟨HX, Hs, Hsc, -, #Hsr⟩
  ihave #HQ : sessionReadyQ γ $$ []
  · unfold sessionReadyQ sessionReady leaseCacheReady
    rw [hn] at *
    iframe #
  wp_apply wp_broadcast_chan_close sc' γch' (sessionReadyQ γ) $$ [$Hpend $HQ] as Hdone
  imod Hclose $$ %st2 %Hwf2 Hfacts2 Hinst Hready Hown HX with HP
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
  wp_for_post
  iframe
  iunfold sessionMonitor
  iexists s', sc', γch', true
  simp only [↓reduceIte]
  iframe
  iframe #

end proof

end leasing
end EtcdGrove
end Perennial
