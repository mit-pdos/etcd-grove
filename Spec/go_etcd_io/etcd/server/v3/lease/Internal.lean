/-
# `server/lease`: the internal vocabulary (batch 3c)

What the internal helpers' specs (the lessor's own proofs: `Grant`, `Revoke`, `Leases`, `Demote`,
`Recover` call them) are stated over. No client of the package imports this module.

* `lessorFields le c dq ls` (exclusive at `DFrac.own 1`, fractional): the holder of `le.mu` (for
  writing: `own 1`; a reader's share otherwise) sees the lessor's mutable fields at the state `ls`:
  `leaseMap` (the live objects, each object's `remainingTTL` field), `itemMap` at `ls.items`, `b =
  ls.be`, `rd = ls.rd`, `demotec`, the notifier (`notifierAt`) and the checkpoint heap (`queueAt`),
  and (at `own 1`) the lease bucket `beLeases ls.be ls.bkt`; with the read-only fields of `c`
  (`minLeaseTTL = c.minTTL`). Realization: what `le.mu`'s invariant (in `isLessor`) holds, the
  ghost state aside.
* `leaseFresh l id ttl` (exclusive): `NewLease`'s object: every field owned (`ID`, `ttl`,
  `remainingTTL = 0`, a zero expiry, an empty item set, a fresh `revokec` with its close right).
* `leaseExpiry l` (persistent): the object's `expiryMu` and the invariant it protects (the `expiry`
  field, any time).
* `lwtAt p id dq`: a `*LeaseWithTime` cell of lease `id` (its time and index any).
* `queueAt s xs dq`: the `LeaseQueue` slice `s` of the cells `xs` (pointer, id), each cell's `index`
  its position.
* `notifierAt np dq`: a `*LeaseExpiredNotifier` whose map agrees with its queue (one cell per id);
  `notifierQ np`: the same with the map not yet rebuilt (`Init`'s pre).
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

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- The holder of `le.mu` sees its mutable fields at `ls` (see the header). -/
opaque lessorFields (le : Loc) (c : Cfg) (dq : DFrac) (ls : LessorState) : IProp GF := iprop(True)

/-- `NewLease`'s fresh object (exclusive). -/
opaque leaseFresh (l : Loc) (id ttl : Int) : IProp GF := iprop(True)

/-- The object's expiry lock (persistent). -/
opaque leaseExpiry (l : Loc) : IProp GF := iprop(True)

/-- A `*LeaseWithTime` cell of lease `id`. -/
opaque lwtAt (p : Loc) (id : w64) (dq : DFrac) : IProp GF := iprop(True)

/-- A `LeaseQueue` slice of the cells `xs`, each at its index. -/
opaque queueAt (s : GoSlice) (xs : List (Loc × w64)) (dq : DFrac) : IProp GF := iprop(True)

/-- A well-formed `*LeaseExpiredNotifier`. -/
opaque notifierAt (np : Loc) (dq : DFrac) : IProp GF := iprop(True)

/-- A `*LeaseExpiredNotifier` whose queue is well-formed, its map any (`Init`'s pre). -/
opaque notifierQ (np : Loc) : IProp GF := iprop(True)

def leaseExpiry_persistent.spec : Prop := ∀ l, Persistent (leaseExpiry (GF := GF) l)

end res

end Lease
end EtcdGrove
end Perennial
