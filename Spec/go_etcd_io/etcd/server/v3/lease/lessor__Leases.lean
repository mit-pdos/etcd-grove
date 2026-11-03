/-
`(*lessor).Leases` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); the lease-read plan
(`notes/lease-read-plan.md`, 2026-10-31).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.Leases()` (read-locked, then sorted by `Remaining()`), on any goroutine, with the lessor's
reader pool (`lessorRdPool`; a reader slot of its lock until the lease-src plan, 2026-11-02: the
read lock is released before the sort, `lessor.go:472-477`, so the slot is borrowed with the token
and given back first), a lower bound `m` of its history and a thread token (the sort's `Remaining()`
borrows a slot of each lease's `expiryMu`, at most `2^30 - 1` live threads; the sort takes at most
`2^62` elements, and the lease map has fewer leases than the execution has steps, at most `2^62`): a fresh slice of the
leases of the lease map at an index `i` no earlier than `m` (the one its read lock saw), each with
its id once (`leaseMapAt`), in some order (by remaining time, read off the clock: none stated), each
a lease of the lessor (`isLeaseObj`) whose `ID` field is its id. -/
abbrev lease.lessor.Leases.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorRdPool γl ∗ lessorLb γl m ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      ⌜receiptBound GF ≤ 2 ^ 62⌝ }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Leases")) (Val #()))
  {{ (sl : GoSlice) (ls : List (Loc × w64)), RET #sl; threadTok ∗
      sl ↦* ls.map Prod.fst ∗ (∃ i : Nat, ⌜m ≤ i⌝ ∗ leaseMapAt γl i ls) ∗
      [∗list] x ∈ ls, isLeaseObj γl x.1 ∗ lsF go!"ID" x.1 ↦□ x.2 }}

end spec

end EtcdGrove
end Perennial
