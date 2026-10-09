/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Session__Lease.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Lease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Session.Lease.wp_proof : Session.Lease.spec (GF := GF) (hG := hG) := by
  intro s γ client id
  wp_start as #Hs
  unfold isSession
  icases Hs with ⟨%ops, %o, %octx, %ocs, %ctx, %cs, %cancel, %donec, #HC, #HO, #HI, #Hx, #Hcn,
    #HD, #Hops, %Ho, #Hoctx, #Hctx, #Hcancel, #Hdone, #Hlease⟩
  wp_auto
  iapply HΦ
  itrivial

end proof

end concurrency
end EtcdGrove
end Perennial
