/-
**The lessor from a reader** (the lease-keys plan, Part B, 2026-10-31): `Lookup` and `Lease.Keys`
by a goroutine other than the lease owner (the server's API layer). Lean-first (no Rocq
counterpart). Each function's owner triple is its `Spec` file's (`lessor.Lookup.spec`,
`Lease.Keys.spec`); the reader's is a second triple of the same function, stated here with its proof
(as the auth package's `specLb`s, `auth/FreshWrap.lean`). The vocabulary is `InvLessor.lean`'s
"The lessor from a reader".
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

/-- **`le.Lookup(id)` by a reader** with a lower bound `m` of the lessor's history: the lease map
of an index no earlier than `m` (the one the read lock found): `nil` and no lease of `id` there, or
a lease `l` of `id` there. -/
def lease.lessor.Lookup.specRd : Prop :=
  ∀ (lp : Loc) (γl : GName) (id : w64) (m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorRd lp γl ∗ lessorLb γl m }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Lookup")) (Val #id))
  {{ (l : Loc), RET #l; lessorRd lp γl ∗
      ((⌜l = null⌝ ∗ leaseAbsentFrom γl m id) ∨ (isLeaseObj γl l ∗ leaseLiveFrom γl m id l)) }}

/-- **`l.Keys()` by a reader** of the lessor `γl` (`lessorReader`: it borrows a reader slot of
`l.mu` for the call), for a lease `l` of `id` at an index no earlier than `m`: the keys of `l`'s item
set, which are the keys the item map attaches to `id` at an index no earlier than `m` where the lease
map has `l` (the last such index: `setsOk`), without duplicates. -/
def lease.Lease.Keys.specRd : Prop :=
  ∀ (γl : GName) (l : Loc) (id : w64) (m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLeaseObj γl l ∗
      leaseLiveFrom γl m id l ∗ lessorReader γl }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"Keys")) (Val #()))
  {{ (s : GoSlice) (ks : List GoString), RET #s; s ↦* ks ∗ lessorReader γl ∗
      leaseKeysFrom γl m id l ks ∗ ⌜ks.Nodup⌝ }}

end spec

end EtcdGrove
end Perennial
