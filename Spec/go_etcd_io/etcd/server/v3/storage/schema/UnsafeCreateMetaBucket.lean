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
`tx`'s `UnsafeCreateBucket` (any bucket, keeping the caller's `P`: the batch transaction's lock
token, `batchTxSpec`'s triple in mvcc's `NewStore`), it keeps `P`. -/
abbrev schema.UnsafeCreateMetaBucket.spec : Prop :=
  ∀ (tx : GoInterfaceOk) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ P ∗
      □ (∀ b : GoInterface,
        {{ P }} (App (Val #(methods tx.ty go!"UnsafeCreateBucket" tx.v)) (Val #b)) {{ RET #(); P }}) }}
    (App (Val (@! schema.UnsafeCreateMetaBucket)) (Val #(GoInterface.ok tx)))
  {{ RET #(); P }}

end spec

end EtcdGrove
end Perennial
