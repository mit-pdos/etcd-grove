/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Term.lean`. Lean-first (no Rocq
counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Term
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getTerm

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.Term.wp_proof (hGT : EtcdServer.getTerm.spec (GF := GF) (hG := hG)) :
    EtcdServer.Term.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as #Hl
  wp_auto
  wp_apply hGT s $$ [] as %t -
  · iframe #
  try wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
