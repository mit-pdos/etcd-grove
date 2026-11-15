/-
## `(*Lease).Keys()` (`lease.go:106`)

**Users.** The writer: `Revoke` (`lessor.go:347`). Readers (2c): `checkLeaseRenew`
(`v3_server.go:594`), `checkLeaseTimeToLive` (`:626`), `leaseTimeToLive` (`:653`), on an object
`Lookup` returned (possibly revoked since). Snippets `lessor.go` (`ReqAttachDetach`,
`ReqReaderLowerBound`).

**Proof sketch.** `l.mu.RLock()`: the object's lock invariant holds its `itemSet` at `ls.keys l` of
the lessor's current state `j ≥ i` (every writer changing an object's set holds both `le.mu` and
`l.mu` and appends the history under both: the history's authority is in an invariant both locks'
holders open); a fresh slice of the set's keys (map iteration: each once, any order); `RUnlock`.

**Changes** (from `specs-ref`'s `Lease__Keys.lean`, the owner's item set): one spec for any caller,
from a state of the history. **Margin.** A state of the history may be one in the middle of an
applied entry (between two `Detach`es of a revocation's deletes, two `Attach`es of a transaction's
puts), so a reader may see a key set no revision had:
`nonissues/etcd-lease-keys-mid-apply.md`; the server's tie of the history to its own (2d) says which.
**Round 1.** A reader token (`lessorReaders γ 1`: the slot of the `RWMutex` it read-locks; the
writer borrows one, `lessorState_reader`), the bounds plan's reader slots.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.lease.Api

set_option autoImplicit false
set_option linter.iris.dupNamespace false

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

/-- **The keys attached to the object `l`** (any goroutine): at a state `j ≥ i`, its item set, each
key once, in some order, in a fresh slice. -/
def Lease.Keys.spec : Prop :=
  ∀ (γ : Names) (l : Loc) (id ttl : Int) (i : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ leaseObj γ l id ttl ∗
      lessorReaders γ 1 ∗ lessorLb γ i }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.Lease.ty @!!
      go!"Keys")) (Val #()))
  {{ (sl : GoSlice), RET #sl; lessorReaders γ 1 ∗ ∃ (j : Nat) (ls : LessorState) (ks : List Key),
      ⌜i ≤ j⌝ ∗ lessorAt γ j ls ∗ sl ↦* ks ∗ ⌜ks.Nodup ∧ ∀ k, k ∈ ks ↔ ls.keys l k⌝ }}

end spec
end Lease
end EtcdGrove
end Perennial
