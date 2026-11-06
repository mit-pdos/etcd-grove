/-
`schema.UnsafeCreateLeaseBucket(tx)` (`schema/lease.go:27`). Lean-first (no Rocq counterpart); the
lease-expiry plan's S1 (2026-11-04), for `lessor.initAndRecover`.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `UnsafeCreateLeaseBucket(tx)` calls `tx.UnsafeCreateBucket(Lease)`: under the contract of
`tx`'s `UnsafeCreateBucket` on the `Lease` bucket (from the caller's `P` to its `Q`: the batch
transaction's lock tokens in `lessor.initAndRecover`), it makes `Q`. -/
abbrev schema.UnsafeCreateLeaseBucket.spec : Prop :=
  ∀ (tx : GoInterfaceOk) (P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ P ∗
      □ (∀ b : GoInterface,
        {{ P ∗ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ b }} (App (Val #(methods tx.ty go!"UnsafeCreateBucket" tx.v)) (Val #b))
        {{ RET #(); Q }}) }}
    (App (Val (@! schema.UnsafeCreateLeaseBucket)) (Val #(GoInterface.ok tx)))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
