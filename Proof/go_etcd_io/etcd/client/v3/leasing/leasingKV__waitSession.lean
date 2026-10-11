/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__waitSession.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__waitSession
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- **The `sessionc` field** under the cache's lock (any fraction): its value `sc`, a broadcast
channel announcing `sessionReadyQ` (`sessioncOk`), and the way back. -/
theorem leasingX_sessionc (lkv : Loc) (γ : LeasingNames) (st : LeaseCacheSt) (q : Qp) :
    leasingX (GF := GF) lkv γ st q ⊢ ∃ sc : GoChan,
      structFieldRef leasingKV go!"sessionc" lkv ↦{DFrac.own q.half} sc ∗ □ sessioncOk γ sc ∗
      (structFieldRef leasingKV go!"sessionc" lkv ↦{DFrac.own q.half} sc -∗ leasingX lkv γ st q) := by
  unfold leasingX leasingXBody
  iintro ⟨%x, Hs, Hsc, Hl, %Hlast, Hn, #Hso, #Hsco⟩
  iexists x.2.1
  iframe Hsc
  iframe #
  iintro Hsc
  iexists x
  iframe
  iframe #
  ipureintro; exact Hlast

theorem leasingKV.waitSession.wp_proof : leasingKV.waitSession.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs
  wp_start as ⟨#Hlkv, Hrd, #Hctx⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, #Hclf, #Hkvf, #Hpfxf, #Hctxf,
    #Hcancelf, #Hoslf, -, -, -, -, #Hlctx, -, -, -, -, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold lkvReader leaseCacheReader
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  icases leaseCacheInv_open $$ HP with ⟨%st, Hown, HX, Hinst, #Hfacts, %Hwf, Hclose⟩
  icases leasingX_sessionc lkv γ st _ $$ HX with ⟨%sc, Hsc, #Hsco, HXback⟩
  (try wp_auto)
  ihave HX := HXback $$ Hsc
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hown HX Hinst] as Hrd
  · inext
    iapply Hclose $$ Hown HX Hinst
  (try wp_auto)
  ihave #Hl2 := Hlctx
  iNamedSuffix Hl2 "L"
  ihave #Hc2 := Hctx
  iNamedSuffix Hc2 "C"
  wp_apply +noauto HDoneL as %ch1 %γ1 #Hdone1
  (try wp_auto)
  wp_apply +noauto HDoneC as %ch2 %γ2 #Hdone2
  (try wp_auto)
  iunfold sessioncOk at Hsco
  icases Hsco with ⟨%γsc, #Hsc⟩
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γsc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hsc
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hsc
    iintro ⟨#HQ, -⟩
    (try wp_auto)
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; rfl
    iexact HQ
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ Hdone1
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone1
    iintro ⟨#HPD, #HCC⟩
    (try wp_auto)
    ihave #HErrD := HErrL $$ %Broadcast.Done
    wp_apply HErrD $$ [$HCC] as %cerr %Hcerr
    iapply HΦ
    iframe
    ileft; ipureintro; exact Hcerr
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch2, γ2
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ Hdone2
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone2
    iintro ⟨#HPD, #HCC⟩
    (try wp_auto)
    ihave #HErrD := HErrC $$ %Broadcast.Done
    wp_apply HErrD $$ [$HCC] as %cerr %Hcerr
    iapply HΦ
    iframe
    ileft; ipureintro; exact Hcerr
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end leasing
end EtcdGrove
end Perennial
