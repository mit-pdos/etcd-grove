/-
## `schema.MustUnsafePutLease(tx, lpb)`: assumed (names only)

**Users.** `Lease.persistTo` (`lease/lease.go:60`: `Grant`, `Checkpoint`, under `LockInsideApply`).
Snippet: `examples/specreq/schema/schema.go` (`ReqLeasePutDelete`).

**Assumed** (`lease.go:49-57`): the key `leaseIDToBytes(lpb.ID)` (`beU64`), `proto.Marshal(lpb)`
(three `int64` fields: never an error; `leaseMsg_of_struct`), `tx.UnsafePut(Lease, key, val)`
(`txWr`).

**Changes.** From `specs-ref`'s `MustUnsafePutLease.lean`: over the contract; the record's value is
any encoding of its fields (`leaseEnc`), so `leaseBktIs` moves to the table updated at the id.

**Margin.** None.
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

/-- **Stores the record** under its id's bytes. -/
def MustUnsafePutLease.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData) (lpb : Loc)
    (dq : DFrac) (v : go_etcd_io.etcd.server.v3.lease.leasepb.Lease),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txWr tx S R ∗ R V ∗ ⌜S.whole .lease ∧ V .lease = some m⌝ ∗ lpb ↦{dq} v }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.MustUnsafePutLease)) (Val #tx)) (Val #lpb))
  {{ RET #(); lpb ↦{dq} v ∗ ∃ bs : GoString,
      ⌜leaseEnc (v.ID', v.TTL', v.RemainingTTL') bs⌝ ∗ R (V.put .lease (beU64 v.ID') bs) }}

end spec
end Schema
end EtcdGrove
end Perennial
