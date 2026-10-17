/-
Proof of the spec of the same name (pr-verify etcd#21621). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.connStatsHandler__HandleRPC

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.connStatsHandler.HandleRPC.wp_proof :
    v3rpc.connStatsHandler.HandleRPC.spec (GF := GF) (hG := hG) := by
  intro h ctx s
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
