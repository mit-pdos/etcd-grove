/-
## `(*lessor).Revoke(id)` (`lessor.go:326`)

**Users.** The applier's `LeaseRevoke` (`apply/backend.go:95`, 3a; reached from a client's revoke
and from the leader's revocation of an expired lease, 2d's `revokeExpiredLeases`), on the apply
thread. Snippet `lessor.go` (`ReqRevokeDeletes`).

**Proof sketch.** `le.mu.Lock()`; `leaseMap[id]` absent: unlock, `ErrLeaseNotFound`, the state and
`P` unchanged (`rd` not called). Present (`e`): the `defer close(l.revokec)` (the live object's close
right, from `le.mu`'s invariant; closed once: the object leaves the map below, and only a live
object is ever revoked); unlock. `le.rd` (the writer's half of the field: `ls.rd`, not `nil`) is
called: `rdOk`'s first triple, `P` to `D td [] n ls`. `l.Keys()` (`Lease.Keys.spec` at `lessorAt γ
n ls`, the writer's: the keys `ls.keys e.obj`), sorted (`sort.StringSlice.Sort`: by `keyLt`, the
keys distinct). For each key, `[]byte(key)` (a fresh slice), `td.DeleteRange(kb, nil)` (`rdOk`'s
second triple: the writer's token lent and given back at `n'`, `ls'`). `le.mu.Lock()` (the current
state is `ls'`, `lessorState` pins it); `delete(leaseMap, id)`; `le.b.BatchTx()` and 4b's
`UnsafeDeleteLease` under the transaction's lock (`rdOk`'s `beTxHeld ls.be`, lent by `D`), moving
`beLeases` to `bkt` without `id`; the history appended with `ls'.remove id` (`n' + 1`). `td.End()`
(`rdOk`'s last triple: `Q ks n' ls'`) under `le.mu`; unlock; the metric; `close(l.revokec)` (Renew's
waiters on the object see the lease gone: the close carries `lessorAt γ (n'+1) _`).

**Changes** (from `specs-ref`'s `lessor__Revoke.lean`): over the lessor's state and a contract of
the range deleter stated in the lessor's terms (`rdOk`, TaDa: the deleter's effects on the caller's
state are the caller's `D`, `Q`), in place of the owner's live list, the item map, the revokers,
mvcc's deleter (`rdIs`, `rdOwn`) and the KV writer's log. The lessor no longer says what the deletes
do to the store: that is the deleter's contract (mvcc's: its delete detaches the key, `GetLease`,
`Detach`), which the applier combines.

**Premise** `ls.rd ≠ func.nil`: without a range deleter `Revoke` returns `nil` leaving the lease
live with its `revokec` closed, and a second `Revoke` panics
(`nonissues/etcd-lease-revoke-twice-no-range-deleter.md`); etcd sets it at `NewStore`.

**Margin.** The keys come from the lease object's item set, not from the store: the caller's
invariant makes them the keys whose record names the lease (`req/..._storage_mvcc.md`, "from 3c").
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **Revoke lease `id`** (the writer): `ErrLeaseNotFound` for a lease not live, nothing done; else
its keys `ks` (sorted) deleted through the range deleter, one `DeleteRange` each, then the lease
removed from memory and from the bucket, and the deletion transaction ended. -/
def lessor.Revoke.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (n : Nat) (ls : LessorState) (id : w64) (P : IProp GF)
    (D : GoInterface → List Key → Nat → LessorState → IProp GF)
    (Q : List Key → Nat → LessorState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorState γ n ls ∗ ⌜ls.rd ≠ func.nil⌝ ∗ rdOk γ ls.rd n ls P D Q ∗ P }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Revoke")) (Val #id))
  {{ (err : GoInterface), RET #err;
      (⌜ls.leases (sint.Z id) = none⌝ ∗ errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗
        lessorState γ n ls ∗ P) ∨
      (⌜err = interface.nil⌝ ∗ ∃ (e : LeaseEnt) (ks : List Key) (n' : Nat) (ls' : LessorState),
        ⌜ls.leases (sint.Z id) = some e ∧ ks.Pairwise keyLt ∧ ∀ k, k ∈ ks ↔ ls.keys e.obj k⌝ ∗
        Q ks n' ls' ∗ lessorState γ (n' + 1) (ls'.remove (sint.Z id))) }}

end spec
end Lease
end EtcdGrove
end Perennial
