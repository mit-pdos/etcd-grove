/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__unicastResponse.lean` (the watch slice's
unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__unicastResponse

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
theorem watchGRPCStream.unicastResponse.wp_proof :
    watchGRPCStream.unicastResponse.spec (GF := GF) (hG := hG) := by
  intro V wgs wr watchID m M dq1 dq2 Pf Sf
  wp_start as ⟨Hsub, Hmap, Hcap⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 $$ [$Hmap] as Hmap
  (try wp_auto)
  cases hM : M !! watchID with
  | none =>
    simp only []
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro; rfl
  | some ws =>
    simp only []
    (try wp_auto)
    icases Hcap with ⟨%HPws, Hcap⟩
    iunfold sendCap1 at Hcap
    icases Hcap with ⟨#Hws, Hprod, Hel⟩
    generalize Pf ws = P at HPws ⊢
    generalize Sf ws = sent
    subst HPws
    ihave #Hws' := Hws
    iunfold wsIs at Hws'
    icases Hws' with ⟨-, -, #Hrecvc, #Hdonec, -, #Hspsc, #Hdn, -⟩
    simp only [Option.isSome_some, decide_true, Bool.not_true, Option.getD_some]
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, P.recvc,
        P.γr.chanName, wr
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · ihave #H := Hspsc
        unfold isSspsc
        icases H with ⟨$, -⟩
      iapply sspsc_send_au P.γr P.recvc _ _ sent wr _ $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [Hprod Hel]
      · iframe
      inext
      iintro Hprod
      (try wp_auto)
      iapply HΦ
      iframe
      ileft
      isplitr
      · ipureintro; rfl
      iunfold sendDone
      iexact Hprod
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, P.donec, P.γdn
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdn
      iapply broadcast_chan_receive $$ Hdn
      iintro ⟨#HdnD, -⟩
      (try wp_auto)
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; rfl
      iunfold sendFail
      iframe Hprod Hel HdnD
    iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end EtcdGrove
end Perennial
