/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Stop.lean`. Lean-first (no Rocq
counterpart). (The lessor-noax stage, 2026-11-18) translated with its body and proved; until then
the trust boundary (names-only), as was `lessorStopTok`.

`Stop` is `close(le.stopC); <-le.doneC`: the close with the right of `lessorStopTok`, the receive on
the broadcast channel `doneC` (it returns once the expiry loop has closed it; until then it blocks,
which partial correctness allows).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Stop

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
  wp_start as Ht
  iunfold lessorStopTok at Ht
  icases Ht with ⟨%sc, %dn, %γs, %γd, #Hsc, Hs, #Hdn, #Hd⟩
  ihave #Hdch := ownBroadcastChan_is_chan _ _ _ _ $$ Hd
  ihave #Htt : □ (True : IProp GF) $$ []
  · imodintro; itrivial
  wp_auto
  wp_apply wp_broadcast_chan_close sc γs iprop(True) $$ [$Hs $Htt] as -
  (try wp_auto)
  wp_bind (App (Val (chan.receive (go.GoType.StructType []))) (Val #dn))
  iapply (chan.wp_receive (V := Unit) dn γd) $$ Hdch
  iintro -
  iapply broadcast_chan_receive $$ Hd
  iintro -
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
