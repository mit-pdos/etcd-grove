/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/bucket__String.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__String
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__Name

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage go_etcd_io.etcd.server.v3.storage.schema

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.bucket.String.wp_proof (hName : schema.bucket.Name.spec (GF := GF) (hG := hG)) :
    schema.bucket.String.spec (GF := GF) (hG := hG) := by
  intro b s dq
  wp_start as Hs
  wp_auto
  wp_method_call
  wp_auto
  wp_apply hName
  wp_apply wp_bytes_to_string $$ [$Hs] as Hs
  iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial
