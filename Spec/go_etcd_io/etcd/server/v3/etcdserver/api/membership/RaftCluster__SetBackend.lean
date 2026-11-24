/-
`membership.RaftCluster.SetBackend(be)` (`cluster.go`). Lean-first (no Rocq counterpart); D22 receiver
epochs, S8c (2026-10-24), for `applySnapshot`; until 2026-11-22 names-only, an axiom at the trust
boundary; since then translated with its body and proved (prove-ps2-members), over
`MustCreateBackendBuckets`' proof.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.MemberBktsFresh

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
(created again, unchanged), at one write-back token; **a part of any bucket set `S` containing
them comes back idle** (`rbPart d.γB S r` in, `rbOwnIn d.γB S r` out: 2026-11-01, the
backend-auth-split stage; until then the whole writer's half `rbOwn`, in and out).
(prove-ps2-members, 2026-11-22, when it was proved) The three buckets are in the backend's table
(`d.P.has`: what the backend's `UnsafeCreateBucket` takes, so that they are among its ghost names; the
server's backends' parameters, `bootOk`'s, the user's approval of 2026-11-22) and schema is initialized
(`isPkgInit` of `schema`, whose methods and bucket variables it calls: membership does not import
schema, its caller does); until then neither, the axiom's statement.

Why it is true of the Go code (`cluster.go:247-250` and `schema/membership.go:171-178` at the etcd
pin): `SetBackend` stores `be` into `c.be` (no lock: the apply thread is the field's only reader and
writer, which the owned field says) and calls `MustCreateBackendBuckets`: `be.BatchTx()`,
`LockOutsideApply` (the backend open: the share `qo`), three `UnsafeCreateBucket`s of `Members`,
`MembersRemoved` and `Cluster` (bbolt's `CreateBucket` returns `ErrBucketExists` for a present
bucket, which the backend's `UnsafeCreateBucket` ignores: no change to the data, the writer's
contents on `S` unchanged, the part at `r`; each counts a pending operation), then `Unlock` (the
pending operations written back: one write-back token; a commit if the batch limit is reached,
paid by that write-back, its hooks at the backend's registered names: `SetBackend` runs after
`ci.SetBackend`), which writes the session's puts back and commits a pending delete (the file
header's Go basis): after it the readers see the writer's contents on every bucket, `S`'s
included. No panic: the backend is open, the buckets exist. -/
abbrev membership.RaftCluster.SetBackend.spec : Prop :=
  ∀ (c oldbe mbl lg : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
    (S : GoString → Prop) (r : GMap GoString backend.BktData),
  (∀ n, membership.clusterBkts n → S n) →
  d.P.has mvcc.membersBI → d.P.has mvcc.membersRemovedBI → d.P.has mvcc.clusterBI →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      clusterBeOn c oldbe ∗ ⌜lg ≠ null⌝ ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"be" mbl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"lg" mbl ↦□ lg ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      backend.rbPart d.γB S r ∗
      ⌜(r.lookup go!"members").isSome ∧ (r.lookup go!"members_removed").isSome ∧
        (r.lookup go!"cluster").isSome⌝ }}
    (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"SetBackend"))
      (Val #(clusterBkIface mbl)))
  {{ RET #(); clusterBeOn c d.be ∗ backend.bOpen d.γB qo ∗ backend.rbOwnIn d.γB S r }}

/-- **`c.SetBackend(mb)` on a backend whose membership buckets may be absent** (claim #34, stage 2,
2026-11-25: `bootstrap`'s `Finalize` on a new backend): as `spec`, the part's absent membership
buckets created empty (`schema.withMemBkts`; `MustCreateBackendBuckets.specFresh`); the cluster's `be`
field holding any value before (a new cluster's is nil, no `clusterBeOn`). -/
abbrev membership.RaftCluster.SetBackend.specFresh : Prop :=
  ∀ (c : Loc) (oldv : GoInterface) (mbl lg : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
    (S : GoString → Prop) (r : GMap GoString backend.BktData),
  (∀ n, membership.clusterBkts n → S n) →
  d.P.has mvcc.membersBI → d.P.has mvcc.membersRemovedBI → d.P.has mvcc.clusterBI →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster go!"be" c ↦ oldv ∗
      ⌜lg ≠ null⌝ ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"be" mbl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"lg" mbl ↦□ lg ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      backend.rbPart d.γB S r }}
    (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"SetBackend"))
      (Val #(clusterBkIface mbl)))
  {{ RET #(); clusterBeOn c d.be ∗ backend.bOpen d.γB qo ∗
      backend.rbOwnIn d.γB S (schema.withMemBkts r) }}

end spec

end EtcdGrove
end Perennial
