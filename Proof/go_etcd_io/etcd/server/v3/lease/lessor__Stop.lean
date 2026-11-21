/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Stop.lean` (prove-ps2-lease, 2026-11-21; an
axiom since R2b-3c part 2, 2026-11-04). `Stop` is `close(le.stopC); <-le.doneC`: the close with
`stopC`'s close token (a close-once channel, `wp_once_close`; prove-ps2-renew), the receive on
`doneC` as a broadcast channel's (both in `lessorStopTok`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Stop
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.Stop.wp_proof : lease.lessor.Stop.spec (GF := GF) (hG := hG) := by
  intro lp
  wp_start as Htok
  iunfold lessorStopTok at Htok
  icases Htok with ⟨%c, %d, %γt, %γd, #Hc, #Hd, #Hstop, Ht, #Hdone⟩
  (try wp_auto)
  wp_apply (wp_once_close c γt) $$ [$Hstop $Ht]
  (try wp_auto)
  wp_apply chan.wp_receive (V := Unit) d γd $$ [] as -
  · iapply ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
  iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
  iintro -
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
