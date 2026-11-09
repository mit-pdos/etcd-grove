/-
# The cluster's membership (`etcdserver/api/membership`): vocabulary (batch 2e)

`RaftCluster` is a member's **applied view of the cluster's members**: the apply thread writes it
(`AddMember`, `RemoveMember`, `UpdateAttributes`, `UpdateRaftAttributes`, `PromoteMember`, `Recover`
at a snapshot or a restart: batch 2d), the request path and the transport read it (`Members`,
`IsIDRemoved`, `IsMemberExist`, `IsLocalMemberLearner`: 2c, 2d's `Process`, 2a's interceptors), all
under its mutex. A client of etcd sees the members through W0's model (`State.members`); this
package's state is one member's copy of it at its applied index, which the server's invariant ties
to the committed log's state (2d's realization).

## Vocabulary

* `memberIdOf urls token` (opaque, pure): the id `computeMemberID` gives a member of an initial
  cluster with these peer URLs in a cluster of this token (SHA-1 of the sorted URLs and the token,
  its first 8 bytes big-endian; `member.go:63-76`). Trusted: what Go computes; a program learns a
  concrete value only by running Go (`examples/specreq/etcdserverboot/boot.go` prints them).
* `initialMembers token cl` (transparent): the members `NewClusterFromURLsMap` builds from an
  initial-cluster map (`cluster.go:81-95`): each name with its peer URLs, no client URL, a voter.
  `bootstrap` fails on two equal ids or an id `0` (the same lines), so no premise on them.
* `ClusterSt` (transparent): a view: the members (each as W0's `Member`) and the removed ids.
* `CNames` (opaque): a view's ghost names.
* `isCluster c γ cid lid` (persistent): `c` is a `*RaftCluster` of cluster id `cid` whose local
  member is `lid`, its view named `γ`. Intended realization: `c`'s mutex with its lock invariant
  (the `members` and `removed` maps holding the authoritative half of a ghost variable of the
  view, the backend handle, the version and downgrade fields, the notifier), read-only `cid`,
  `localID`, `lg`.
* `clusterSt γ st` (exclusive, timeless): **the view `γ` is `st`**: the other half. Every method
  takes an atomic update over it (TaDa: the server's invariant holds it, and keeps the relation to
  `State.members`; a read fires its update with the state unchanged).
* `memberPts p dq m` (fractional): a `*Member` at `p` holding `m` (its id, its `RaftAttributes`'
  peer URLs and learner flag, its `Attributes`' name and client URLs: the slices' contents too).
* `membersOwn sl ms`: a fresh `[]*Member` of the members `ms` (each `memberPts … (own 1)`).

## Laws

`isCluster_persistent`, `isCluster_agree`, `clusterSt_timeless`, `clusterSt_excl`,
`memberPts_fractional`, `memberPts_agree`.

## Requirement snippets

`examples/specreq/etcdserverboot/members.go`: the request path's reads (a removed id stays removed,
a member listed after its add), the apply thread's writes.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.Model
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.membership
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.membership

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Membership

open Iris Iris.BI EtcdModel

/-- `computeMemberID(urls, token, nil)` (see the header). -/
opaque memberIdOf (urls : List GoString) (token : GoString) : Nat

/-- The members `NewClusterFromURLsMap(token, cl)` builds (in any order: the map's). -/
def initialMembers (token : GoString) (cl : List (GoString × List GoString)) : List Member :=
  cl.map (fun p => { id := memberIdOf p.2 token, name := p.1, peerURLs := p.2, clientURLs := [],
                     isLearner := false })

/-- A member's view of the cluster's members. -/
structure ClusterSt where
  members : List Member
  removed : List Nat

/-- The view after member `m` is added (`AddMember`; replacing a member of its id). -/
def ClusterSt.add (st : ClusterSt) (m : Member) : ClusterSt :=
  { st with members := st.members.filter (·.id ≠ m.id) ++ [m] }

/-- The view after member `id` is removed (`RemoveMember`: recorded as removed even if absent). -/
def ClusterSt.remove (st : ClusterSt) (id : Nat) : ClusterSt :=
  { members := st.members.filter (·.id ≠ id), removed := id :: st.removed }

/-- The view with member `id` changed by `f` (no change if `id` is not a member). -/
def ClusterSt.update (st : ClusterSt) (id : Nat) (f : Member → Member) : ClusterSt :=
  { st with members := st.members.map (fun m => if m.id = id then f m else m) }

/-- A view's members without the removed ones: the cluster's members as `State.members` has
them (the server's invariant: `st.members` is a permutation of the applied state's). -/
def ClusterSt.isMember (st : ClusterSt) (id : Nat) : Prop := ∃ m ∈ st.members, m.id = id

/-- A view's ghost names (opaque). -/
opaque CNames : Type := Unit

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `c` is a `*RaftCluster` of cluster id `cid` and local member `lid`, its view named `γ`. -/
opaque isCluster (c : Loc) (γ : CNames) (cid lid : w64) : IProp GF := iprop(True)

/-- **The view `γ` is `st`** (exclusive). -/
opaque clusterSt (γ : CNames) (st : ClusterSt) : IProp GF := iprop(True)

/-- A `*Member` at `p` holding `m`. -/
opaque memberPts (p : Loc) (dq : DFrac) (m : Member) : IProp GF := iprop(True)

/-- A fresh `[]*Member` of the members `ms`. -/
def membersOwn (sl : GoSlice) (ms : List Member) : IProp GF :=
  iprop(∃ ps : List Loc, ownSlice sl ps (DFrac.own 1) ∗ ⌜ps.length = ms.length⌝ ∗
    [∗list] pm ∈ ps.zip ms, memberPts pm.1 (DFrac.own 1) pm.2)

def isCluster_persistent.spec : Prop := ∀ c γ cid lid, Persistent (isCluster (GF := GF) c γ cid lid)

def isCluster_agree.spec : Prop := ∀ c γ γ' cid cid' lid lid',
  isCluster (GF := GF) c γ cid lid ∗ isCluster c γ' cid' lid' ⊢ ⌜γ = γ' ∧ cid = cid' ∧ lid = lid'⌝

def clusterSt_timeless.spec : Prop := ∀ γ st, Timeless (clusterSt (GF := GF) γ st)

def clusterSt_excl.spec : Prop := ∀ γ st st',
  clusterSt (GF := GF) γ st ∗ clusterSt γ st' ⊢ iprop(False)

def memberPts_fractional.spec : Prop := ∀ p m (q₁ q₂ : Qp),
  memberPts (GF := GF) p (DFrac.own (q₁ + q₂)) m ⊣⊢
    memberPts p (DFrac.own q₁) m ∗ memberPts p (DFrac.own q₂) m

def memberPts_agree.spec : Prop := ∀ p dq dq' m m',
  memberPts (GF := GF) p dq m ∗ memberPts p dq' m' ⊢ ⌜m = m'⌝

end res

end Membership
end EtcdGrove
end Perennial
