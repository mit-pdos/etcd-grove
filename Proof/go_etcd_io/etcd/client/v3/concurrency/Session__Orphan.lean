/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Session__Orphan.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Orphan

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Session.Orphan.wp_proof : Session.Orphan.spec (GF := GF) (hG := hG) := by
  intro s γ client id
  wp_start as #Hs
  ihave #Hs' := Hs
  unfold isSession
  icases Hs' with ⟨%ops, %o, %octx, %ocs, %ctx, %cs, %cancel, %donec, #HC, #HO, #HI, #Hx, #Hcn,
    #HD, #Hops, %Ho, #Hoctx, #Hctx, #Hcancel, #Hdone, #Hlease⟩
  wp_auto
  unfold cancelSpec
  wp_apply Hcancel
  · imodintro; itrivial
  unfold sessionDoneChan
  ihave #Hch := ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
  wp_bind (App (Val (chan.receive (go.GoType.StructType []))) _)
  iapply chan.wp_receive (V := Unit) donec γ.done $$ Hch
  iintro _
  iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
  iintro ⟨-, #Hd⟩
  wp_auto
  iapply HΦ
  unfold sessionDone
  iexists donec
  iframe #

end proof

end concurrency
end EtcdGrove
end Perennial
