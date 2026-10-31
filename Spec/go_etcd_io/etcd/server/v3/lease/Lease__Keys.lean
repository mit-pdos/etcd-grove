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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `l.Keys()` (read-locked; unit T3, 2026-10-25): the keys of the lease's item set, a fresh
slice, no key twice. By the lease owner (`.owner I`: its half of the set, `leaseItemsOwn l I id`,
and a reader slot of the lease's lock), the keys are those the owner's item map `I` puts on `id`; by
a reader (`.reader m`, the lease-keys plan's Part B, 2026-10-31: `l` the lease of `id` at an index
no earlier than `m`, and a thread token, with which it borrows a slot of the lock from the lease's
pool, at most `2^30` live threads), the keys the item map puts on `id` at an index no earlier than
`m` where the lease map has `l` (`leaseKeysFrom`; the last such index, `setsOk`). -/
abbrev lease.Lease.Keys.spec : Prop :=
  ∀ (γl : GName) (l : Loc) (id : w64) (K : KeysBy),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLeaseObj γl l ∗
      keysPre γl l id K }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"Keys")) (Val #()))
  {{ (s : GoSlice) (ks : List GoString), RET #s; s ↦* ks ∗ keysPre γl l id K ∗
      keysPost γl l id ks K ∗ ⌜ks.Nodup⌝ }}

end spec

end EtcdGrove
end Perennial
