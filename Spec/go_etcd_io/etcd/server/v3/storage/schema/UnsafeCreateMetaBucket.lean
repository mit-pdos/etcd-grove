/-
`schema.UnsafeCreateMetaBucket(tx)` (`cindex.go`). Lean-first (no Rocq counterpart).
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

/-- `UnsafeCreateMetaBucket(tx)` calls `tx.UnsafeCreateBucket(Meta)`: under the contract of
`tx`'s `UnsafeCreateBucket` on the `Meta` bucket (from the caller's `P` to its `Q`: the batch
transaction's lock tokens, `batchTxInitSpec`'s triple in mvcc's `NewStore`), it makes `Q`
(2026-10-13: the triple was on any bucket, keeping `P`; the backend's bridge needs the bucket's
value, and counts the creations). -/
abbrev schema.UnsafeCreateMetaBucket.spec : Prop :=
  ∀ (tx : GoInterfaceOk) (P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ P ∗
      □ (∀ b : GoInterface,
        {{ P ∗ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ b }} (App (Val #(methods tx.ty go!"UnsafeCreateBucket" tx.v)) (Val #b))
        {{ RET #(); Q }}) }}
    (App (Val (@! schema.UnsafeCreateMetaBucket)) (Val #(GoInterface.ok tx)))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
