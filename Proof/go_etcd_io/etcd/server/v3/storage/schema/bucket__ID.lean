/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/bucket__ID.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__ID

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

theorem schema.bucket.ID.wp_proof :
    schema.bucket.ID.spec (GF := GF) (hG := hG) := by
  intro b
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
