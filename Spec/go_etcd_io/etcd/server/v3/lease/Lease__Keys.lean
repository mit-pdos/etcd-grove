/-
`(*Lease).Keys` (`server/lease/lease.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `l.Keys()` (read-locked; unit T3, 2026-10-25): the keys of the lease's item set, a fresh
slice, no key twice; by the lease owner (its half of the set, `leaseItemsOwn l I id`, and a
reader slot of the lease's lock), so the keys are those the owner's item map `I` puts on `id`. -/
abbrev lease.Lease.Keys.spec : Prop :=
  ∀ (l : Loc) (I : GMap LeaseItem w64) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLeaseObj l ∗
      sync.ownRWMutex (lsF go!"mu" l) (leaseItems l) ∗ leaseItemsOwn l I id }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"Keys")) (Val #()))
  {{ (s : GoSlice) (ks : List GoString), RET #s; s ↦* ks ∗
      sync.ownRWMutex (lsF go!"mu" l) (leaseItems l) ∗ leaseItemsOwn l I id ∗
      ⌜(∀ k : GoString, k ∈ ks ↔ I.lookup (LeaseItem.mk k) = some id) ∧ ks.Nodup⌝ }}

end spec

end EtcdGrove
end Perennial
