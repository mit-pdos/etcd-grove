/-
`(*membershipBackend).MustCreateBackendBuckets()` (`server/storage/schema/membership.go:168`). Lean-first
(no Rocq counterpart); for `RaftCluster.SetBackend` (prove-ps2-members, 2026-11-22).
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

/-- **`mb.MustCreateBackendBuckets()`** of the membership backend `mb` over the real backend `d`, the
three membership buckets in its table (`d.P.has`) and present in a part of any bucket set `S` containing
them (created again, unchanged), at one write-back token and an open share: the part comes back idle.
Go: `be.BatchTx()`, `LockOutsideApply`, `UnsafeCreateBucket` of `Members`, `MembersRemoved`, `Cluster`
(bbolt's `ErrBucketExists`, which the backend ignores: no change), the deferred `Unlock` (a write-back,
which leaves the readers seeing the writer's contents on `S`). -/
abbrev schema.membershipBackend.MustCreateBackendBuckets.spec : Prop :=
  ∀ (mbl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
    (S : GoString → Prop) (r : GMap GoString backend.BktData),
  (∀ n, membership.clusterBkts n → S n) →
  d.P.has mvcc.membersBI → d.P.has mvcc.membersRemovedBI → d.P.has mvcc.clusterBI →
  (r.lookup go!"members").isSome → (r.lookup go!"members_removed").isSome →
  (r.lookup go!"cluster").isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"be" mbl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      backend.rbPart d.γB S r }}
    (App (Val (mbl @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!! go!"MustCreateBackendBuckets"))
      (Val #()))
  {{ RET #(); backend.bOpen d.γB qo ∗ backend.rbOwnIn d.γB S r }}

/-- **`mb.MustCreateBackendBuckets()` on a backend whose membership buckets may be absent** (claim
#34, stage 2, 2026-11-25: `bootstrap`'s `Finalize` on a new backend): as `spec`, the buckets absent
from the part created empty (`schema.withMemBkts`: bbolt's `CreateBucket`), present ones unchanged. -/
abbrev schema.membershipBackend.MustCreateBackendBuckets.specFresh : Prop :=
  ∀ (mbl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
    (S : GoString → Prop) (r : GMap GoString backend.BktData),
  (∀ n, membership.clusterBkts n → S n) →
  d.P.has mvcc.membersBI → d.P.has mvcc.membersRemovedBI → d.P.has mvcc.clusterBI →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"be" mbl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      backend.rbPart d.γB S r }}
    (App (Val (mbl @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!! go!"MustCreateBackendBuckets"))
      (Val #()))
  {{ RET #(); backend.bOpen d.γB qo ∗ backend.rbOwnIn d.γB S (schema.withMemBkts r) }}

end spec

end EtcdGrove
end Perennial
