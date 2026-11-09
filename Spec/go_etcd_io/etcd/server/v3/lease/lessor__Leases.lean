/-
## `(*lessor).Leases()` (`lessor.go:472`)

**Users.** 2c's `EtcdServer.LeaseLeases` (`v3_server.go:738`), any goroutine: the ids of the
member's live leases (each `ls[i].ID`). Snippet `lessor.go` (`ReqLeasesList`).

**Proof sketch.** `le.mu.RLock()`; `unsafeLeases()` (`lessor.unsafeLeases.spec`: a fresh slice of
the map's objects, each once, at the current state `j ≥ i`, snapshot `lessorAt γ j ls`); `RUnlock`;
`sort.Sort(leasesByExpiry(ls))` (`GoSort.Sort.anyLessSpec`, the trust-boundary spec of Go's sort
with any `Less`: `leasesByExpiry`'s `Len`, `Less` through `Remaining()` (any answer: time), `Swap`
give `sorterAny`; at most `2^62` objects, from the map's size as `Revoke`'s keys): a permutation of
the objects. The ids: each object's `leaseObj` (`lessorAt_obj`), distinct as map
keys.

**Changes** (from `specs-ref`'s `lessor__Leases.lean`): from a state of the history at or after the
caller's bound; the answer as ids (the objects in some order). **Margin.** The order (by remaining
time) is not modelled. Perennial's `sort.Sort` spec wants a consistent order, which `Less` (two clock
reads) is not: `Spec/sort/SortAnyLess.lean` is the any-`Less` spec (Go's sort bounds every index by
the slice's, never by `Less`'s answers). The `2^62` bound is Perennial's sort limitation (Go's heapsort
index arithmetic): a `[]*Lease` of more than `2^61` elements cannot exist in a 64-bit address space,
but Perennial's slice model does not say so; open (batch-3c.md), no premise here.
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

/-- **The live leases** (any goroutine): at a state `j ≥ i`, a fresh slice of the live leases'
objects, each once, in some order (`ids` their ids). -/
def lessor.Leases.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (i : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorReaders γ 1 ∗ lessorLb γ i }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Leases")) (Val #()))
  {{ (sl : GoSlice), RET #sl; lessorReaders γ 1 ∗ ∃ (j : Nat) (ls : LessorState) (ps : List Loc) (ids : List Int),
      ⌜i ≤ j⌝ ∗ lessorAt γ j ls ∗ sl ↦* ps ∗
      ⌜ids.Nodup ∧ (∀ x, x ∈ ids ↔ ls.leases x ≠ none) ∧
        List.Forall₂ (fun p x => ∃ e, ls.leases x = some e ∧ p = e.obj) ps ids⌝ }}

end spec
end Lease
end EtcdGrove
end Perennial
