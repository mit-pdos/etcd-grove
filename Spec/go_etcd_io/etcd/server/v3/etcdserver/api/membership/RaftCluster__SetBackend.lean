/-
`membership.RaftCluster.SetBackend(be)` (`cluster.go`): names-only. Lean-first (no Rocq
counterpart); D22 receiver epochs, S8c (2026-10-24), for `applySnapshot`; an axiom at the trust
boundary (`Proof/.../membership/RaftCluster__SetBackend.lean`), why it is true of the Go code below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`c.SetBackend(mb)`** of the cluster `c` on the real backend at `oldbe` (its `be` field, owned:
`clusterBeOn`), `mb` a schema membership backend over the real backend `d` (`NewMembershipBackend`'s
fields, a logger): the cluster on `d`, the three membership buckets of `d` already present
(created again, unchanged), at one write-back token.

Why it is true of the Go code (`cluster.go:247-250` and `schema/membership.go:171-178` at the etcd
pin): `SetBackend` stores `be` into `c.be` (no lock: the apply thread is the field's only reader and
writer, which the owned field says) and calls `MustCreateBackendBuckets`: `be.BatchTx()`,
`LockOutsideApply` (the backend open: the share `qo`), three `UnsafeCreateBucket`s of `Members`,
`MembersRemoved` and `Cluster` (bbolt's `CreateBucket` returns `ErrBucketExists` for a present
bucket, which the backend's `UnsafeCreateBucket` ignores: no change to the data, the tracked
buckets' half `rbOwn d.γB r` unchanged; each counts a pending operation), then `Unlock` (the
pending operations written back: one write-back token; a commit if the batch limit is reached,
paid by that write-back, its hooks at the backend's registered names: `SetBackend` runs after
`ci.SetBackend`). No panic: the backend is open, the buckets exist. -/
abbrev membership.RaftCluster.SetBackend.spec : Prop :=
  ∀ (c oldbe mbl lg : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
    (r : GMap GoString backend.BktData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      clusterBeOn c oldbe ∗ ⌜lg ≠ null⌝ ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"be" mbl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"lg" mbl ↦□ lg ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      backend.rbOwn d.γB r ∗
      ⌜(r.lookup go!"members").isSome ∧ (r.lookup go!"members_removed").isSome ∧
        (r.lookup go!"cluster").isSome⌝ }}
    (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"SetBackend"))
      (Val #(clusterBkIface mbl)))
  {{ RET #(); clusterBeOn c d.be ∗ backend.bOpen d.γB qo ∗ backend.rbOwn d.γB r }}

end spec

end EtcdGrove
end Perennial
