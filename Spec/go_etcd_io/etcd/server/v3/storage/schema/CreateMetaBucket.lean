/-
## `schema.CreateMetaBucket(tx)`: assumed (names only)

**Users.** Bootstrap (`etcdserver/bootstrap.go:266`: `schema.CreateMetaBucket(be.BatchTx())`, 2e).
Snippet: `examples/specreq/schema/schema.go` (`ReqCreateBuckets`).

**Assumed** (translated names only; `cindex.go:30-35`): `tx.LockOutsideApply()`, `UnsafeCreateBucket(Meta)`,
`tx.Unlock()` (deferred). Stated over the write section's triples (`wrSect`) and the contract.

**Changes.** New. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schema

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **Creates `Meta` in a write section** of `tx`. -/
def CreateMetaBucket.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (P : IProp GF) (Q : View → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txWr tx S R ∗ ⌜S.canCreate .metaB⌝ ∗
      wrSect tx go!"LockOutsideApply" P R (fun _ => True) Q ∗ P }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.CreateMetaBucket)) (Val #tx))
  {{ RET #(); ∃ V : View, Q (V.create .metaB) }}

end spec
end Schema
end EtcdGrove
end Perennial
