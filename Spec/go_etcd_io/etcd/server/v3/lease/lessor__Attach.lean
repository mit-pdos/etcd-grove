/-
## `(*lessor).Attach(id, items)` (`lessor.go:555`)

**Users.** mvcc (3e), on the apply thread through the `Lessor` interface: `put` with a lease
(`kvstore_txn.go:285`: one item; `panic("unexpected error from lease Attach")` on an error, so mvcc
needs the lease live: the put's lease check, `txn.checkLease`, at the same state), `restore`
(`kvstore.go:398`, error logged). Snippet `lessor.go` (`ReqAttachDetach`).

**Proof sketch.** `le.mu.Lock()` (current state `ls`); `leaseMap[id]` absent: `ErrLeaseNotFound`,
unlock. Present (`e`): `l.mu.Lock()` (the object's lock: its item set at `ls.keys e.obj`); for each
item, `itemSet[it]`, `itemMap[it] = id`; the history appended with `ls.attach id ks` (`n + 1`) and
the object's set updated, `l.mu.Unlock()`; unlock. The items slice is only read.

**Changes** (from `specs-ref`'s `lessor__Attach.lean`, `leaseOwn γl L I` with `insertAll` and the
premise that the items are on no other lease): over the lessor's state; **the premise dropped**:
the code attaches whatever it is given (an item on another lease is re-pointed in `itemMap` and
stays in the other lease's set: `LessorState.attach` says so); mvcc's caller detaches first.
**Margin.** None.
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

/-- **Attach keys to lease `id`** (the writer): `ErrLeaseNotFound` for a lease not live, nothing
changed; else `nil`, the keys attached (`LessorState.attach`). -/
def lessor.Attach.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (n : Nat) (ls : LessorState) (id : w64) (sl : GoSlice)
    (its : List go_etcd_io.etcd.server.v3.lease.LeaseItem) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorState γ n ls ∗ sl ↦*{dq} its }}
    (App (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Attach")) (Val #id)) (Val #sl))
  {{ (err : GoInterface), RET #err; sl ↦*{dq} its ∗
      ((⌜ls.leases (sint.Z id) = none⌝ ∗ errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗
        lessorState γ n ls) ∨
       (⌜ls.leases (sint.Z id) ≠ none ∧ err = interface.nil⌝ ∗
        lessorState γ (n + 1) (ls.attach (sint.Z id) (its.map (·.Key'))))) }}

end spec
end Lease
end EtcdGrove
end Perennial
