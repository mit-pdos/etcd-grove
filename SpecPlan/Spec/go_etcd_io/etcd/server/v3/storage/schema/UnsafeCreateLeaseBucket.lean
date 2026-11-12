/-
## `schema.UnsafeCreateLeaseBucket(tx)`

**Users.** `lessor.initAndRecover` (`lease/lessor.go:812`: the batch transaction, `LockOutsideApply`).
Snippet: `examples/specreq/schema/schema.go` (`ReqLeaseRecover`).

**Proof sketch.** `tx.UnsafeCreateBucket(Lease)` (`txWr`).

**Changes.** From `specs-ref`'s `UnsafeCreateLeaseBucket.lean`: over the contract.
**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

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

/-- **Creates `Lease`** (if absent; its records unchanged). -/
def UnsafeCreateLeaseBucket.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txWr tx S R ∗ R V ∗ ⌜S.canCreate .lease⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateLeaseBucket)) (Val #tx))
  {{ RET #(); R (V.create .lease) }}

end spec
end Schema
end EtcdGrove
end Perennial
