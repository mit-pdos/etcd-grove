/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/clientIPFromContext.lean` (PR etcd#22259).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.clientIPFromContext
public import Spec.go_etcd_io.etcd.server.v3.auth.ClientIPFromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.clientIPFromContext.wp_proof
    (h_ClientIPFromContext : auth.ClientIPFromContext.spec (GF := GF) (hG := hG)) :
    auth.clientIPFromContext.spec (GF := GF) (hG := hG) := by
  intro ctx o
  wp_start as #Hctx
  wp_auto
  wp_apply (h_ClientIPFromContext ctx o) $$ [$Hctx]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
