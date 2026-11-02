/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LeaseGrant.lean`. Lean-first (no
Rocq counterpart); the lease-grant plan's D4 (2026-11-02): not proved (Draft). Its callees: the id
generator's `Next`, `requireAuthInfo`, `raftRequest` (whose apply of a grant needs the plan's D3:
the grant admitted by the request path and the apply thread).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseGrant
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__requireAuthInfo
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Generator__Next

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.LeaseGrant.wp_proof
    (hNext : idutil.Generator.Next.spec (GF := GF) (hG := hG))
    (hAuth : EtcdServer.requireAuthInfo.spec (GF := GF) (hG := hG))
    (hRR : EtcdServer.raftRequest.spec (GF := GF) (hG := hG)) :
    EtcdServer.LeaseGrant.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
