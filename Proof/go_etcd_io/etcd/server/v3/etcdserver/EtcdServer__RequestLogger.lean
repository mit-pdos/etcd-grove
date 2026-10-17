/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__RequestLogger.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RequestLogger

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.RequestLogger.wp_proof : EtcdServer.RequestLogger.spec (GF := GF) (hG := hG) := by
  intro s rl
  wp_start as #Hrl
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
