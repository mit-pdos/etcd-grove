/-
Proof of the spec of the same name (PR etcd#22259). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.clientIPFromContext
public import Spec.go_etcd_io.etcd.server.v3.auth.ClientIPFromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.clientIPFromContext.wp_proof
    (h_ClientIPFromContext : auth.ClientIPFromContext.spec (GF := GF) (hG := hG)) :
    v3rpc.clientIPFromContext.spec (GF := GF) (hG := hG) := by
  intro ctx o
  wp_start as #Hctx
  ihave #Hauth : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  wp_auto
  wp_apply (h_ClientIPFromContext ctx o) $$ [$Hauth $Hctx]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
