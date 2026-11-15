/-
## `schema.UnsafeDeleteLease(tx, lpb)`: assumed (names only)

**Users.** `lessor.Revoke` (`lease/lessor.go:359`: `&leasepb.Lease{ID}`, inside the range deleter's
write transaction, which holds the batch lock). Snippet: `examples/specreq/schema/schema.go` (`ReqLeasePutDelete`).

**Assumed** (`lease.go:59-61`): `tx.UnsafeDelete(Lease, leaseIDToBytes(lpb.ID))` (`txWr`).

**Changes.** From `specs-ref`'s `UnsafeDeleteLease.lean`: over the contract. **Margin.** None.
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

/-- **Deletes the record of `lpb.ID`.** -/
def UnsafeDeleteLease.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData) (lpb : Loc)
    (dq : DFrac) (v : go_etcd_io.etcd.server.v3.lease.leasepb.Lease),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txWr tx S R ∗ R V ∗ ⌜S.whole .lease ∧ V .lease = some m⌝ ∗ lpb ↦{dq} v }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeDeleteLease)) (Val #tx)) (Val #lpb))
  {{ RET #(); lpb ↦{dq} v ∗ R (V.del .lease (beU64 v.ID')) }}

end spec
end Schema
end EtcdGrove
end Perennial
