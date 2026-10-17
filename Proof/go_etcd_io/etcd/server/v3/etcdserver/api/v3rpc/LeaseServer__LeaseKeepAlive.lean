/-
Proof of the spec of the same name (etcd-io/etcd#21960: the handler runs its loop itself), and
of its relation to the spec the handler had before the PR (`spec_old`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__LeaseKeepAlive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__leaseKeepAlive

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.LeaseServer.LeaseKeepAlive.wp_proof
    (hLoop : v3rpc.LeaseServer.leaseKeepAlive.spec (GF := GF) (hG := hG)) :
    v3rpc.LeaseServer.LeaseKeepAlive.spec (GF := GF) (hG := hG) := by
  intro p S st γs Up Dn ci cd Lq Lr
  wp_start as ⟨#Hls, #Hstream, #Hspec, Hrt, Hst, %Hlen, HR⟩
  wp_auto
  wp_apply hLoop $$ [Hrt Hst HR] as %err Hdone
  · iframe; iframe #; ipureintro; exact Hlen
  iapply HΦ
  iexact Hdone

/-- **The PR's change is compatible**: the handler's new spec implies the one it had (its
postcondition only adds the stream's tokens). Its callers (grpc's generated handler) are
unaffected. -/
theorem v3rpc.LeaseServer.LeaseKeepAlive.spec_implies_old
    (h : v3rpc.LeaseServer.LeaseKeepAlive.spec (GF := GF) (hG := hG)) :
    v3rpc.LeaseServer.LeaseKeepAlive.spec_old (GF := GF) (hG := hG) := by
  intro p S st γs Up Dn ci cd Lq Lr
  iintro %Φ Hpre HΦ
  iapply h p S st γs Up Dn ci cd Lq Lr $$ Hpre
  iintro !> %err -
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
