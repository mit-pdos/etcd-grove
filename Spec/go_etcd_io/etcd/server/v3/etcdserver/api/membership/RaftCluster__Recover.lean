/-
`membership.RaftCluster.Recover(onSet)` (`cluster.go`): names-only. Lean-first (no Rocq
counterpart); D22 receiver epochs, S8d (2026-10-25, W6), for `applySnapshot`; an axiom at the trust
boundary (`Proof/.../membership/RaftCluster__Recover.lean`), why it is true of the Go code below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`c.Recover(api.UpdateCapability)`** of the cluster `c` on the real backend `d` (its `be`
field, owned: `clusterBeOn`, after `SetBackend`), with a reader token of `d` (`bkRTx`) and the
backend's tracked buckets `r` (`rbOwn`), whose membership buckets are a good image for `c` of the
members `mem'` (`clusterImageOk c r mem'`), and the cluster's in-memory members at `mem`
(`clusterMem`): it returns, the in-memory members `mem'`, everything else given back. (2026-10-25,
the user's decision: until then the axiom did not take `clusterMem`, which `Recover` changes.)

Why it is true of the Go code (`cluster.go:256-302` and `schema/membership.go` at the etcd pin):
`Recover` takes `c`'s mutex (`isRaftCluster`: its invariant `rcLockInv c`), and `UnsafeLoad` reads
`d` through `be.ReadTx()` under its read lock (the reader token's slot; read-only, so the tracked
buckets are unchanged): the cluster version (`Cluster` bucket), the members and removed members
(`MustReadMembersFromBackend`, which panics on a key or a JSON value it cannot decode) and the
downgrade info. `clusterImageOk c r` says the three buckets of `r` decode, hold `c`'s local member
(`c.localID`, among the members) and no removed member (a static cluster: `rcLockInv`'s empty
`removed`), a cluster version that `MustDetectDowngrade` accepts for this server's version (no
downgrade: not above it, and not below its minor by more than one) and, if present, a valid
downgrade record; so nothing panics, and the new members map (fresh `*Member`s, owned) and removed
map re-establish `rcLockInv c` (its size: the bucket's entries, a handful); `c.members` now holds
the members the buckets decode to, `mem'` (`clusterMem c mem'`). `buildMembershipMetric`
and the logs read the members under the lock; `onSet = api.UpdateCapability` takes its own global
mutex and updates the capability map (never panics: a `nil` version returns at once). The `be`
field is only read (the owned points-to given back). The members' peer URLs are those of the
image: what the cluster's `Members()` returns afterwards is the boot contract's (the members of the
static cluster, the directory's URLs: `bootOk`'s `Hmembers`, true for good because every image a
member of the static cluster applies holds the same members, which `clusterImageOk` includes). -/
abbrev membership.RaftCluster.Recover.spec : Prop :=
  ∀ (c : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (r : GMap GoString backend.BktData)
    (mem mem' : GMap w64 apply.MemberM),
  membership.clusterImageOk c r mem' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api ∗
      membership.isRaftCluster c ∗ clusterBeOn c d.be ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ mvcc.bkRTx d.γB d.P d.be ∗ backend.rbOwn d.γB r ∗
      membership.clusterMem c mem }}
    (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Recover"))
      (Val #(functions go_etcd_io.etcd.server.v3.etcdserver.api.UpdateCapability [])))
  {{ RET #(); clusterBeOn c d.be ∗ mvcc.bkRTx d.γB d.P d.be ∗ backend.rbOwn d.γB r ∗
      membership.clusterMem c mem' }}

end spec

end EtcdGrove
end Perennial
