/-
## `schema.MustUnsafePutLease(tx, lpb)`: assumed (names only)

**Users.** `Lease.persistTo` (`lease/lease.go:57-60`: a fresh local `leasepb.Lease{ID, TTL,
RemainingTTL}`, under `LockInsideApply`; its owner turns it into a message with
`leaseMsg_of_struct`). Snippet: `examples/specreq/schema/schema.go` (`ReqLeaseRecover`).

**Assumed** (`lease.go:49-57`): the key `leaseIDToBytes(lpb.ID)` (`beU64`), `proto.Marshal(lpb)`
(three `int64` fields: never an error; it writes the message's `sizeCache`, inside `msgAt`),
`tx.UnsafePut(Lease, key, val)` (`txWr`: an 8-byte key and a value of at most 33 bytes, within
bbolt's limits).

**Changes.** From `specs-ref`'s `MustUnsafePutLease.lean`: over the contract and `Proto.msgAt`
(round 1, F9: the struct points-to was claimed unchanged by `Marshal`'s write); the record's value is
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
    (dq : DFrac) (c : Proto.Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txWr tx S R ∗ R V ∗ ⌜S.whole .lease ∧ V .lease = some m⌝ ∗
      Proto.msgAt go_etcd_io.etcd.server.v3.lease.leasepb.Lease.ty lpb dq c }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.MustUnsafePutLease)) (Val #tx)) (Val #lpb))
  {{ RET #(); Proto.msgAt go_etcd_io.etcd.server.v3.lease.leasepb.Lease.ty lpb dq c ∗
      ∃ bs : GoString, ⌜leaseEnc (leaseModel c) bs⌝ ∗ R (V.put .lease (beU64 (leaseModel c).1) bs) }}

end spec
end Schema
end EtcdGrove
end Perennial
