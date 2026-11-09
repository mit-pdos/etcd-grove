/-
## `(*lessor).Lookup(id)` (`lessor.go:458`)

**Users.** Readers on any goroutine: the request path (2c: `LeaseRenew`'s fast path
`v3_server.go:512`, `checkLeaseRenew` `:592`, `checkLeaseTimeToLive` `:624`, `leaseTimeToLive`
`:645`, after `waitAppliedIndex`); and the writer: txn's `checkLease` (`txn/put.go:83`, 3b) and the
auth applier's `checkLeasePuts` (`apply/auth.go:199`, 3a), on the apply thread. Snippets `lessor.go`
(`ReqGrantLookup`, `ReqReaderLowerBound`).

**Proof sketch.** `le.mu.RLock()`: the invariant's current state `j`, `ls` (at least `i`: the
history's `mono_list` lower bound); `leaseMap[id]`: the live object or `nil`; `lessorAt γ j ls`
snapshot; `RUnlock`. A writer passes `lessorAt γ n ls` from its `lessorState γ n ls`
(`lessorState_at`), and gets `j = n`, the state `ls` (`lessorState_le`, `lessorAt_agree`).

**Changes** (from `specs-ref`'s `lessor__Lookup.lean`, the owner's exact read and the history's
`leaseLiveFrom`): one spec for readers and the writer, answered from a state of the lessor's history
at or after the caller's lower bound. **Margin.** None (an object is live or not at the read).
**Round 1.** A reader token (`lessorReaders γ 1`: the slot of the `RWMutex` it read-locks; the
writer borrows one, `lessorState_reader`), the bounds plan's reader slots.
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

/-- **Look lease `id` up** (any goroutine): at a state `j ≥ i` of the lessor's history, its object
if live, else `nil`. -/
def lessor.Lookup.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (i : Nat) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorReaders γ 1 ∗ lessorLb γ i }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Lookup")) (Val #id))
  {{ (l : Loc), RET #l; lessorReaders γ 1 ∗ ∃ (j : Nat) (ls : LessorState), ⌜i ≤ j⌝ ∗ lessorAt γ j ls ∗
      ⌜ls.leases (sint.Z id) = none ∧ l = null ∨
        ∃ e, ls.leases (sint.Z id) = some e ∧ l = e.obj⌝ }}

end spec
end Lease
end EtcdGrove
end Perennial
