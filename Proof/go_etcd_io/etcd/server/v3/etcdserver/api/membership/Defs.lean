/-
The membership package's predicates (unit P1b, 2026-10-14): what the server's request path
knows of its `*RaftCluster`. Lean-first (no Rocq counterpart).

* `clusterCid c cid`: `c.cid` is `cid`, read-only (written once, by `SetID` at bootstrap, before
  the server serves requests).
* `memberIs m id`: a `*Member` `m` owned, field by field (the embedded `RaftAttributes` and
  `Attributes` split), its `ID` `id`, its two URL slices owned; `ownMember m`: some id.
* `isRaftCluster c` (persistent): `c`'s embedded `sync.Mutex` guards the `members` map, whose
  values are owned members and which has an entry for the local member `c.localID` (read-only;
  2026-10-18: `localKept`, until then an axiomatized predicate) (`RaftCluster`'s other fields,
  also guarded, are not described: `Members` reads only the map). The map's size is at most `2 ^ 62` (`sort.Sort`'s bound; a
  cluster has a handful of members). A contract of names-only code (the cluster's mutators,
  `AddMember` etc., are not translated): a premise of the server's start.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev membership.mIDAddr (m : Loc) : Loc := structFieldRef membership.Member go!"ID" m
abbrev membership.mRaftAttrAddr (m : Loc) : Loc :=
  structFieldRef membership.Member go!"RaftAttributes" m
abbrev membership.mAttrAddr (m : Loc) : Loc := structFieldRef membership.Member go!"Attributes" m
abbrev membership.mPeerURLsAddr (m : Loc) : Loc :=
  structFieldRef membership.RaftAttributes go!"PeerURLs" (membership.mRaftAttrAddr m)
abbrev membership.mIsLearnerAddr (m : Loc) : Loc :=
  structFieldRef membership.RaftAttributes go!"IsLearner" (membership.mRaftAttrAddr m)
abbrev membership.mNameAddr (m : Loc) : Loc :=
  structFieldRef membership.Attributes go!"Name" (membership.mAttrAddr m)
abbrev membership.mClientURLsAddr (m : Loc) : Loc :=
  structFieldRef membership.Attributes go!"ClientURLs" (membership.mAttrAddr m)

abbrev membership.rcMutexAddr (c : Loc) : Loc := structFieldRef membership.RaftCluster go!"Mutex" c
abbrev membership.rcMembersAddr (c : Loc) : Loc :=
  structFieldRef membership.RaftCluster go!"members" c
abbrev membership.rcLocalIDAddr (c : Loc) : Loc :=
  structFieldRef membership.RaftCluster go!"localID" c

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `c.cid` holds `cid`, read-only (persistent). -/
def membership.clusterCid (c : Loc) (cid : w64) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster go!"cid" c
    ↦□ cid)

instance membership.clusterCid_persistent (c : Loc) (cid : w64) :
    Persistent (membership.clusterCid (GF := GF) c cid) := by
  unfold membership.clusterCid; infer_instance

/-- **Peer URLs that parse** (opaque; unit N4, D14e, 2026-10-17): `types.NewURLs(us)` returns no
error (each string a URL with a scheme and a host, no path). The transport's `AddRemote`/`AddPeer`
panic otherwise; a cluster's members' URLs were parsed when they were added (the initial cluster
by `NewURLsMap`, later members by the client's `MemberAdd`), which the model of the cluster
records (`memberIs`) as a premise from bootstrap. -/
opaque membership.peerURLsOk (us : List GoString) : Prop

/-- The member `m`, owned, with the id `id` (its fields, and its URL slices' elements, its peer
URLs parsing: `peerURLsOk`, unit N4, 2026-10-17). -/
def membership.memberIs (m : Loc) (id : w64) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ (pu cu : GoSlice) (il : Bool) (nm : GoString) (pus cus : List GoString),
    membership.mIDAddr m ↦ id ∗ membership.mPeerURLsAddr m ↦ pu ∗
    membership.mIsLearnerAddr m ↦ il ∗ membership.mNameAddr m ↦ nm ∗
    membership.mClientURLsAddr m ↦ cu ∗ pu ↦* pus ∗ cu ↦* cus ∗ ⌜membership.peerURLsOk pus⌝)

/-- The member `m`, owned (some id). -/
def membership.ownMember (m : Loc) : IProp GF :=
  iprop(∃ id : w64, membership.memberIs m id)

/-- The slice `sl` of members `ms`, owned (`Members()`' result). -/
def membership.membersAt (sl : GoSlice) (ms : List Loc) : IProp GF :=
  iprop(sl ↦* ms ∗ [∗list] m ∈ ms, membership.ownMember m)

/-- The local member's entry (persistent): `c.localID` holds `lid`, read-only (`SetID` writes it
at bootstrap, before the cluster is shared), and the members map `ms` has an entry for it. -/
def membership.rcLocalIn (c : Loc) (ms : GMap w64 Loc) : IProp GF :=
  iprop(∃ lid : w64, membership.rcLocalIDAddr c ↦□ lid ∗ ⌜ms !! lid ≠ none⌝)

instance membership.rcLocalIn_persistent (c : Loc) (ms : GMap w64 Loc) :
    Persistent (membership.rcLocalIn (GF := GF) c ms) := by
  unfold membership.rcLocalIn; infer_instance

/-- What `c`'s mutex guards (of it, what `Members` and `IsLocalMemberLearner` read): the members
map, its members owned, the local member among them (`rcLocalIn`: `membership.localKept`). -/
def membership.rcLockInv (c : Loc) : IProp GF :=
  iprop(∃ (mp : Loc) (ms : GMap w64 Loc), membership.rcMembersAddr c ↦ mp ∗ mp ↦$ ms ∗
    ⌜GMap.size ms ≤ 2 ^ 62⌝ ∗ ([∗map] _k ↦ m ∈ ms, membership.ownMember m) ∗
    membership.rcLocalIn c ms)

/-- **The cluster `c`** (persistent): its mutex, guarding `rcLockInv c`. -/
def membership.isRaftCluster (c : Loc) : IProp GF :=
  sync.isMutex (membership.rcMutexAddr c) (membership.rcLockInv c)

instance membership.isRaftCluster_persistent (c : Loc) :
    Persistent (membership.isRaftCluster (GF := GF) c) := by
  unfold membership.isRaftCluster; infer_instance

/-- **The cluster `c`'s local member stays in its members map** (persistent; until 2026-10-18 an
axiomatized predicate, unit P3b): `c` is the cluster whose mutex guards a members map that has an
entry for `c.localID` whenever the mutex is free (`rcLockInv`'s `rcLocalIn`). So
`RaftCluster.IsLocalMemberLearner`, which panics (`c.lg.Panic`) when `c.members` has no entry for
`c.localID`, does not panic. A fact that holds forever by construction: `bootstrap`'s contract
gives the cluster with its local member (a new cluster's members are the boot peers, the local
one among them: `NewClusterFromURLsMap`, `SetID`), and no writer of the map in the verified run
removes it -- the only removal, `applyConfChange`'s `RemoveNode`, is outside the changes the
server takes (`ccApplyOk`, audit B3: an `AddNode` of a member, `AddMember` of it, which keeps the
entry). In general etcd the local member is removed when the server applies its own removal, after
which it stops (`issues/etcd-unary-interceptor-learner-removed.md`: the server's unary
interceptor's `IsMemberExist(MemberID()) && IsLearner()` races with that removal); that run is
outside this model. The same fact as `isRaftCluster c` (`localKept_of_isRaftCluster`), named for
the specs that rely on it (`EtcdServer.IsLearner`'s and the interceptors'). -/
def membership.localKept (c : Loc) : IProp GF := membership.isRaftCluster c

instance membership.localKept_persistent (c : Loc) :
    Persistent (membership.localKept (GF := GF) c) := by
  unfold membership.localKept; infer_instance

theorem membership.localKept_of_isRaftCluster (c : Loc) :
    membership.isRaftCluster (GF := GF) c ⊢ membership.localKept c := .rfl

end defs


section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A member's `ID` field, borrowed. -/
theorem membership.memberIs_id_acc (m : Loc) (id : w64) :
    membership.memberIs (GF := GF) m id ⊢
      membership.mIDAddr m ↦ id ∗ (membership.mIDAddr m ↦ id -∗ membership.memberIs m id) := by
  unfold membership.memberIs
  iintro ⟨%Hnn, %pu, %cu, %il, %nm, %pus, %cus, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus, %Hpok⟩
  iframe Hid
  iintro Hid
  isplitr
  · ipureintro; exact Hnn
  iexists pu, cu, il, nm, pus, cus
  iframe
  ipureintro; exact Hpok

/-- One member of a list of (pointer, id) members, borrowed. -/
theorem membership.membersL_acc (l : List (Loc × w64)) (k : Nat) (x : Loc × w64)
    (h : l[k]? = some x) :
    ([∗list] p ∈ l, membership.memberIs (GF := GF) p.1 p.2) ⊢
      membership.memberIs x.1 x.2 ∗
        (membership.memberIs x.1 x.2 -∗ [∗list] p ∈ l, membership.memberIs p.1 p.2) := by
  have hs : l.set k x = l := by
    apply List.ext_getElem?
    intro n
    rw [List.getElem?_set]
    split
    · rename_i hn; subst hn; rw [h]; simp [(List.getElem?_eq_some_iff.1 h).1]
    · rfl
  refine (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
    (Φ := fun (_ : Nat) (y : Loc × w64) => membership.memberIs (GF := GF) y.1 y.2) h).1.trans ?_
  iintro ⟨H, Hw⟩
  iframe H
  iintro H
  ihave Hr := Hw $$ %x H
  rw [hs]
  iexact Hr

/-- The (pointer, id) members, as owned members. -/
theorem membership.membersL_own (l : List (Loc × w64)) :
    ([∗list] p ∈ l, membership.memberIs (GF := GF) p.1 p.2) ⊢
      [∗list] m ∈ l.map Prod.fst, membership.ownMember m := by
  induction l with
  | nil =>
    iintro -
    simp only [List.map_nil]
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons x l ih =>
    iintro Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hx, Hl⟩
    simp only [List.map_cons]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hx]
    · iunfold membership.ownMember; iexists x.2; iexact Hx
    · iapply ih $$ Hl

end lemmas

end EtcdGrove
end Perennial
