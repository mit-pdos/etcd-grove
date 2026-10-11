/-
`schema.UnsafeCreateMetaBucket(tx)`: the trust boundary (names-only). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.schema

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `UnsafeCreateMetaBucket(tx)` (`tx.UnsafeCreateBucket(Meta)` on a batch transaction the
caller holds locked) returns: creating the `Meta` bucket does not touch the `Key` bucket. -/
abbrev schema.UnsafeCreateMetaBucket.spec : Prop :=
  ∀ (tx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (Val (@! schema.UnsafeCreateMetaBucket)) (Val #tx))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
