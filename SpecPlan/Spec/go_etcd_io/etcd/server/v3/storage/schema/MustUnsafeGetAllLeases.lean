/-
## `schema.MustUnsafeGetAllLeases(tx)`: assumed (names only)

**Users.** `lessor.initAndRecover` (`lease/lessor.go:813`, after `UnsafeCreateLeaseBucket`, the batch
lock held). Snippet: `examples/specreq/schema/schema.go` (`ReqLeaseRecover`).

**Assumed** (`lease.go:31-46`): `tx.UnsafeForEach(Lease, f)` (`txRd`: every entry once, in some order),
`f` (each entry once) unmarshals each value, inside the call, into a fresh `leasepb.Lease` (`Proto.Unmarshal.spec`: each value is a
record's encoding, `leaseBktIs`, so no error and no panic; `Unmarshal` copies the lent bytes) and
appends its pointer. On the batch transaction the order is the ids' (big-endian keys); the spec says
only "each once" (no caller needs the order). The messages are plain structs afterwards
(`leaseMsg_to_struct`).

**Changes.** From `specs-ref`'s `MustUnsafeGetAllLeases.lean` (over the real backend's locked
state): over the contract and the bucket's encoding of the lease table `L`.

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

/-- **The lease records**, one fresh `*leasepb.Lease` each, each once (in some order). -/
def MustUnsafeGetAllLeases.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData)
    (L : w64 → Option LeaseRec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txRd tx S R ∗ R V ∗ ⌜S.whole .lease ∧ V .lease = some m ∧ leaseBktIs m L⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeGetAllLeases)) (Val #tx))
  {{ (sl : GoSlice), RET #sl; R V ∗ ∃ (l : List LeaseRec) (ps : List Loc),
      ⌜(l.map (·.1)).Nodup ∧ ∀ r, r ∈ l ↔ L r.1 = some r⌝ ∗
      sl ↦* ps ∗ [∗list] p; r ∈ ps; l, leaseAt p r }}

end spec
end Schema
end EtcdGrove
end Perennial
