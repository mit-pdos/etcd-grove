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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.MemberModel

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
abbrev membership.rcVersionChangedAddr (c : Loc) : Loc :=
  structFieldRef membership.RaftCluster go!"versionChanged" c
abbrev membership.rcRemovedAddr (c : Loc) : Loc :=
  structFieldRef membership.RaftCluster go!"removed" c
abbrev membership.rcLgAddr (c : Loc) : Loc := structFieldRef membership.RaftCluster go!"lg" c
abbrev membership.rcBeAddr (c : Loc) : Loc := structFieldRef membership.RaftCluster go!"be" c
abbrev membership.rcCidAddr (c : Loc) : Loc := structFieldRef membership.RaftCluster go!"cid" c

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

/-- The member `m`, owned, with the id `id` (its fields, and its URL slices' elements; until D43
M5e, 2026-10-26, also its peer URLs parsing, `peerURLsOk`, which no reader of the cluster used:
`NewServer` takes it from the bootstrap contract's directory facts). -/
def membership.memberIs (m : Loc) (id : w64) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ (pu cu : GoSlice) (il : Bool) (nm : GoString) (pus cus : List GoString),
    membership.mIDAddr m ↦ id ∗ membership.mPeerURLsAddr m ↦ pu ∗
    membership.mIsLearnerAddr m ↦ il ∗ membership.mNameAddr m ↦ nm ∗
    membership.mClientURLsAddr m ↦ cu ∗ pu ↦* pus ∗ cu ↦* cus)

/-- **The member `m` at the fraction `q`, with the value `mm`** (D43 M5b, 2026-10-26): its fields
and its URL slices' elements at `q` (no `peerURLsOk` since D43 M5e, as `memberIs`). The cluster's lock
holds half of each member it lists, the apply thread (`clusterMem`) the other half. -/
def membership.memberAt (m : Loc) (q : Qp) (mm : apply.MemberM) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ (pu cu : GoSlice),
    membership.mIDAddr m ↦{DFrac.own q} mm.id ∗ membership.mPeerURLsAddr m ↦{DFrac.own q} pu ∗
    membership.mIsLearnerAddr m ↦{DFrac.own q} mm.isLearner ∗
    membership.mNameAddr m ↦{DFrac.own q} mm.name ∗
    membership.mClientURLsAddr m ↦{DFrac.own q} cu ∗ pu ↦*{DFrac.own q} mm.peerURLs ∗
    cu ↦*{DFrac.own q} mm.clientURLs)

/-- A member record `l` the backend's read made, with its peer URLs `pus`. -/
def membership.memberURLsAt (l : Loc) (pus : List GoString) : IProp GF :=
  iprop(∃ pu : GoSlice, ⌜l ≠ null⌝ ∗ membership.mPeerURLsAddr l ↦ pu ∗ pu ↦* pus)

/-- The members map `mp` the backend's read returns, of the members' peer URLs `mems`. -/
def membership.membersRead (mp : Loc) (mems : GMap w64 (List GoString)) : IProp GF :=
  iprop(∃ ml : GMap w64 Loc, mp ↦$ ml ∗ ⌜∀ k, (ml !! k).isSome = (mems !! k).isSome⌝ ∗
    [∗map] k ↦ l ∈ ml, ∃ pus : List GoString, ⌜mems !! k = some pus⌝ ∗ membership.memberURLsAt l pus)

/-- The members map and their values have the same keys (and so the same size). -/
def membership.memDom (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM) : Prop :=
  (∀ k, (ms !! k).isSome = (mem !! k).isSome) ∧ GMap.size ms = GMap.size mem

/-- **The cluster `c`'s members map at the fraction `q`** (D43 M5b, 2026-10-26): `c.members` is
`mp`, holding the members `ms`, each member at `q` with its value in `mem` (the two maps with the
same keys). The cluster's lock holds it at half; the apply thread's `clusterMem` the other half. -/
def membership.memAt (c : Loc) (q : Qp) (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM) :
    IProp GF :=
  iprop(∃ mp : Loc, membership.rcMembersAddr c ↦{DFrac.own q} mp ∗ mp ↦${DFrac.own q} ms ∗
    ⌜membership.memDom ms mem⌝ ∗
    [∗map] k ↦ m ∈ ms, membership.memberAt m q ((mem !! k).getD default))

/-- **The cluster `c`'s in-memory members are `mem`** (exclusive; D22, 2026-10-23, option (i) of
"D22c decided": `c.members`, each member as the record its JSON unmarshals to; opaque until D43
M5b, 2026-10-26, now defined, the user's decision): the apply thread's half of the members map
(`memAt`), whose other half the cluster's lock holds. `bootstrap`'s contract gives it at the boot
log's members (`memBoot`); the cluster's writers take it and give it back changed. -/
def membership.clusterMem (c : Loc) (mem : GMap w64 apply.MemberM) : IProp GF :=
  iprop(∃ ms : GMap w64 Loc, membership.memAt c (1 : Qp).half ms mem)

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

/-- What `c`'s mutex guards (of it, what `Members`, `IsLocalMemberLearner` and `IsIDRemoved`
read): the members map, its members (since D43 M5b, 2026-10-26, half of the map and of each member,
`memAt`: the apply thread's `clusterMem` holds the other half, which its writers combine with this
one under the lock; owned whole until then), the local member among them (`rcLocalIn`:
`membership.localKept`); and (D21 M2, 2026-10-19) the removed members' map, empty: a static
cluster booted once removes none (`removed`'s writers, `RemoveMember` and `UnsafeLoad` from
`Recover` -- a restart or an applied snapshot -- are outside the run; `NewClusterFromURLsMap`
makes it empty). -/
def membership.rcLockInv (c : Loc) : IProp GF :=
  iprop(∃ (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM),
    membership.memAt c (1 : Qp).half ms mem ∗ ⌜GMap.size ms ≤ 2 ^ 62⌝ ∗
    membership.rcLocalIn c ms ∗
    ∃ rp : Loc, membership.rcRemovedAddr c ↦ rp ∗ rp ↦$ (∅ : GMap w64 Bool))

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

/-- The type of the lock invariant's side condition: of the local id, the members map and the
removed map. -/
abbrev membership.RcSide (GF : BundledGFunctors) := w64 → GMap w64 Loc → GMap w64 Bool → IProp GF

/-- **The cluster's lock invariant, generally** (D43 M4, 2026-10-26): `rcLockInv` with the side
condition `RM` of the local id (`c.localID`, read-only: `SetID` writes it at bootstrap), the
members map and the removed map (`rcLockInv` is the static instance, `rcStatic`; the dynamic one
tracks the removed map, `rcDyn`); half of the members (`memAt`, D43 M5b, as `rcLockInv`). -/
def membership.rcLockInvG (c : Loc) (RM : membership.RcSide GF) : IProp GF :=
  iprop(∃ (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM),
    membership.memAt c (1 : Qp).half ms mem ∗ ⌜GMap.size ms ≤ 2 ^ 62⌝ ∗
    ∃ (lid : w64) (rp : Loc) (rm : GMap w64 Bool), membership.rcLocalIDAddr c ↦□ lid ∗
      membership.rcRemovedAddr c ↦ rp ∗ rp ↦$ rm ∗ RM lid ms rm)

/-- **The cluster `c`, generally** (persistent): its mutex, guarding `rcLockInvG c RM`. -/
def membership.isRaftClusterG (c : Loc) (RM : membership.RcSide GF) : IProp GF :=
  sync.isMutex (membership.rcMutexAddr c) (membership.rcLockInvG c RM)

instance membership.isRaftClusterG_persistent (c : Loc) (RM : membership.RcSide GF) :
    Persistent (membership.isRaftClusterG (GF := GF) c RM) := by
  unfold membership.isRaftClusterG; infer_instance

/-- The static side condition: the local member in the map, the removed map empty. -/
def membership.rcStatic : membership.RcSide GF :=
  fun lid ms rm => iprop(⌜ms !! lid ≠ none ∧ rm = ∅⌝)

/-- The dynamic side condition: the removed map, half of it the apply thread's
(`membership.rcRemovedOwn`), which `RemoveMember` extends. -/
def membership.rcDyn (γ : GName) : membership.RcSide GF :=
  fun _ _ rm => dghostVar γ (DFrac.own (1 : Qp).half) rm

/-- The writer's half of the removed map (the apply thread's, in the dynamic instance). -/
def membership.rcRemovedOwn (γ : GName) (rm : GMap w64 Bool) : IProp GF :=
  dghostVar γ (DFrac.own (1 : Qp).half) rm

/-- `rcLockInv` is the static instance. -/
theorem membership.rcLockInv_static (c : Loc) :
    membership.rcLockInv (GF := GF) c ⊣⊢ membership.rcLockInvG c membership.rcStatic := by
  unfold membership.rcLockInv membership.rcLockInvG membership.rcStatic membership.rcLocalIn
  constructor
  · iintro ⟨%ms, %mem, Hmems, %Hsz, ⟨%lid, #Hlid, %Hin⟩, %rp, Hrf, Hrm⟩
    iexists ms, mem
    iframe Hmems
    isplitr
    · ipureintro; exact Hsz
    iexists lid, rp, ∅
    iframe Hrf Hrm Hlid
    ipureintro; exact ⟨Hin, rfl⟩
  · iintro ⟨%ms, %mem, Hmems, %Hsz, %lid, %rp, %rm, #Hlid, Hrf, Hrm, %Hside⟩
    obtain ⟨Hin, Hrm0⟩ := Hside
    subst Hrm0
    iexists ms, mem
    iframe Hmems
    isplitr
    · ipureintro; exact Hsz
    isplitr
    · iexists lid; iframe Hlid; ipureintro; exact Hin
    iexists rp
    iframe

/-- `isRaftCluster` is the static instance. -/
theorem membership.isRaftCluster_static (c : Loc) :
    membership.isRaftCluster (GF := GF) c ⊣⊢ membership.isRaftClusterG c membership.rcStatic := by
  unfold membership.isRaftCluster membership.isRaftClusterG
  rw [(membership.rcLockInv_static c).to_eq]
  exact .rfl

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
  iintro ⟨%Hnn, %pu, %cu, %il, %nm, %pus, %cus, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
  iframe Hid
  iintro Hid
  isplitr
  · ipureintro; exact Hnn
  iexists pu, cu, il, nm, pus, cus
  iframe

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

/-- A member at `q1 + q2` is two parts. -/
theorem membership.memberAt_split (m : Loc) (q1 q2 : Qp) (mm : apply.MemberM) :
    membership.memberAt (GF := GF) m (q1 + q2) mm ⊣⊢
      membership.memberAt m q1 mm ∗ membership.memberAt m q2 mm := by
  unfold membership.memberAt
  have hpt := fun {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) =>
    typedPointsto_frac_add (GF := GF) l v q1 q2
  have hsl := fun {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (sl : GoSlice) (vs : List V) =>
    (ownSlice_fractional (GF := GF) sl vs).fractional q1 q2
  refine ⟨?_, ?_⟩
  · iintro ⟨%Hnn, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
    icases (hpt _ _).1 $$ Hid with ⟨Hid1, Hid2⟩
    icases (hpt _ _).1 $$ Hpu with ⟨Hpu1, Hpu2⟩
    icases (hpt _ _).1 $$ Hil with ⟨Hil1, Hil2⟩
    icases (hpt _ _).1 $$ Hnm with ⟨Hnm1, Hnm2⟩
    icases (hpt _ _).1 $$ Hcu with ⟨Hcu1, Hcu2⟩
    icases (hsl _ _).1 $$ Hpus with ⟨Hpus1, Hpus2⟩
    icases (hsl _ _).1 $$ Hcus with ⟨Hcus1, Hcus2⟩
    isplitl [Hid1 Hpu1 Hil1 Hnm1 Hcu1 Hpus1 Hcus1]
    · isplitr; (ipureintro; exact Hnn)
      iexists pu, cu; iframe
    · isplitr; (ipureintro; exact Hnn)
      iexists pu, cu; iframe
  · iintro ⟨⟨%Hnn, %pu, %cu, Hid1, Hpu1, Hil1, Hnm1, Hcu1, Hpus1, Hcus1⟩,
      ⟨-, %pu', %cu', Hid2, Hpu2, Hil2, Hnm2, Hcu2, Hpus2, Hcus2⟩⟩
    ihave %Hpu := typedPointsto_agree_wand _ _ _ _ _ $$ Hpu1 Hpu2
    ihave %Hcu := typedPointsto_agree_wand _ _ _ _ _ $$ Hcu1 Hcu2
    subst Hpu Hcu
    isplitr; (ipureintro; exact Hnn)
    iexists pu, cu
    isplitl [Hid1 Hid2]; (iapply (hpt _ _).2; iframe)
    isplitl [Hpu1 Hpu2]; (iapply (hpt _ _).2; iframe)
    isplitl [Hil1 Hil2]; (iapply (hpt _ _).2; iframe)
    isplitl [Hnm1 Hnm2]; (iapply (hpt _ _).2; iframe)
    isplitl [Hcu1 Hcu2]; (iapply (hpt _ _).2; iframe)
    isplitl [Hpus1 Hpus2]; (iapply (hsl _ _).2; iframe)
    iapply (hsl _ _).2; iframe

/-- Two parts of a member agree on its value. -/
theorem membership.memberAt_agree (m : Loc) (q1 q2 : Qp) (mm1 mm2 : apply.MemberM) :
    membership.memberAt (GF := GF) m q1 mm1 ∗ membership.memberAt m q2 mm2 ⊢ ⌜mm1 = mm2⌝ := by
  unfold membership.memberAt
  iintro ⟨⟨-, %pu, %cu, Hid1, Hpu1, Hil1, Hnm1, Hcu1, Hpus1, Hcus1⟩,
    ⟨-, %pu', %cu', Hid2, Hpu2, Hil2, Hnm2, Hcu2, Hpus2, Hcus2⟩⟩
  ihave %Hpu := typedPointsto_agree_wand _ _ _ _ _ $$ Hpu1 Hpu2
  ihave %Hcu := typedPointsto_agree_wand _ _ _ _ _ $$ Hcu1 Hcu2
  subst Hpu Hcu
  ihave %Hid := typedPointsto_agree_wand _ _ _ _ _ $$ Hid1 Hid2
  ihave %Hil := typedPointsto_agree_wand _ _ _ _ _ $$ Hil1 Hil2
  ihave %Hnm := typedPointsto_agree_wand _ _ _ _ _ $$ Hnm1 Hnm2
  ihave %Hpus := ownSlice_agree _ _ _ _ _ $$ Hpus1 Hpus2
  ihave %Hcus := ownSlice_agree _ _ _ _ _ $$ Hcus1 Hcus2
  ipureintro
  cases mm1; cases mm2
  simp_all

/-- An owned member with id `id` is a whole member whose value has the id `id`. -/
theorem membership.memberIs_iff_memberAt (m : Loc) (id : w64) :
    membership.memberIs (GF := GF) m id ⊣⊢
      ∃ mm : apply.MemberM, ⌜mm.id = id⌝ ∗ membership.memberAt m 1 mm := by
  unfold membership.memberIs membership.memberAt
  refine ⟨?_, ?_⟩
  · iintro ⟨%Hnn, %pu, %cu, %il, %nm, %pus, %cus, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
    iexists ⟨id, pus, il, nm, cus⟩
    isplitr; (ipureintro; rfl)
    isplitr; (ipureintro; exact Hnn)
    iexists pu, cu; iframe
  · iintro ⟨%mm, %Hmid, %Hnn, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
    subst Hmid
    isplitr; (ipureintro; exact Hnn)
    iexists pu, cu, mm.isLearner, mm.name, mm.peerURLs, mm.clientURLs
    iframe

/-- The members map at `q1 + q2` is two parts. -/
theorem membership.memAt_split (c : Loc) (q1 q2 : Qp) (ms : GMap w64 Loc)
    (mem : GMap w64 apply.MemberM) :
    membership.memAt (GF := GF) c (q1 + q2) ms mem ⊣⊢
      membership.memAt c q1 ms mem ∗ membership.memAt c q2 ms mem := by
  unfold membership.memAt
  have hmf := (ownMap_fractional (GF := GF) (V := Loc) (K := w64))
  refine ⟨?_, ?_⟩
  · iintro ⟨%mp, Hf, Hm, %Hdom, Hms⟩
    icases (typedPointsto_frac_add (GF := GF) _ _ q1 q2).1 $$ Hf with ⟨Hf1, Hf2⟩
    icases ((hmf mp ms).fractional q1 q2).1 $$ Hm with ⟨Hm1, Hm2⟩
    ihave Hms' := BigSepM.bigSepM_mono (Ψ := fun k m => iprop(
        membership.memberAt (GF := GF) m q1 ((mem !! k).getD default) ∗
        membership.memberAt m q2 ((mem !! k).getD default)))
      (fun _ => (membership.memberAt_split _ q1 q2 _).1) $$ Hms
    icases (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ Hms' with ⟨Hms1, Hms2⟩
    isplitl [Hf1 Hm1 Hms1]
    · iexists mp; iframe; ipureintro; exact Hdom
    · iexists mp; iframe; ipureintro; exact Hdom
  · iintro ⟨⟨%mp, Hf1, Hm1, %Hdom, Hms1⟩, ⟨%mp', Hf2, Hm2, -, Hms2⟩⟩
    ihave %Hmp := typedPointsto_agree_wand _ _ _ _ _ $$ Hf1 Hf2
    subst Hmp
    iexists mp
    isplitl [Hf1 Hf2]; (iapply (typedPointsto_frac_add (GF := GF) _ _ q1 q2).2; iframe)
    isplitl [Hm1 Hm2]; (iapply ((hmf mp ms).fractional q1 q2).2; iframe)
    isplitr; (ipureintro; exact Hdom)
    ihave Hms := (BiEntails.of_eq (BigSepM.bigSepM_sep_eq
        (Φ := fun k m => membership.memberAt (GF := GF) m q1 ((mem !! k).getD default))
        (Ψ := fun k m => membership.memberAt (GF := GF) m q2 ((mem !! k).getD default))
        (m := ms))).2 $$ [Hms1 Hms2]
    · iframe
    iapply BigSepM.bigSepM_mono (fun _ => (membership.memberAt_split _ q1 q2 _).2) $$ Hms

/-- Two parts of the members map agree on the members and their values. -/
theorem membership.memAt_agree (c : Loc) (q1 q2 : Qp) (ms ms' : GMap w64 Loc)
    (mem mem' : GMap w64 apply.MemberM) :
    membership.memAt (GF := GF) c q1 ms mem ∗ membership.memAt c q2 ms' mem' ⊢
      ⌜ms = ms' ∧ mem = mem'⌝ := by
  unfold membership.memAt
  iintro ⟨⟨%mp, Hf1, Hm1, %Hdom, Hms1⟩, ⟨%mp', Hf2, Hm2, %Hdom', Hms2⟩⟩
  ihave %Hmp := typedPointsto_agree_wand _ _ _ _ _ $$ Hf1 Hf2
  subst Hmp
  ihave %Hms := ownMap_agree mp _ _ ms ms' $$ [Hm1 Hm2]
  · iframe
  subst Hms
  ihave Hb := (BiEntails.of_eq (BigSepM.bigSepM_sep_eq
      (Φ := fun k m => membership.memberAt (GF := GF) m q1 ((mem !! k).getD default))
      (Ψ := fun k m => membership.memberAt (GF := GF) m q2 ((mem' !! k).getD default))
      (m := ms))).2 $$ [Hms1 Hms2]
  · iframe
  ihave %Hall := (BigSepM.bigSepM_mono (Ψ := fun k _ =>
      iprop(⌜(mem !! k).getD default = (mem' !! k).getD default⌝ : IProp GF))
    (fun _ => membership.memberAt_agree _ _ _ _ _)).trans BigSepM.bigSepM_pure_intro $$ Hb
  ipureintro
  refine ⟨rfl, GMap.ext fun k => ?_⟩
  have hd := Hdom.1 k
  have hd' := Hdom'.1 k
  cases hk : ms !! k with
  | none =>
    rw [hk] at hd hd'
    cases h1 : mem.lookup k <;> cases h2 : mem'.lookup k <;> simp_all [GMap.lookup]
  | some m =>
    have := Hall k m hk
    rw [hk] at hd hd'
    cases h1 : mem.lookup k <;> cases h2 : mem'.lookup k <;> simp_all [GMap.lookup]

/-- A member's `IsLearner` field at `q`, borrowed. -/
theorem membership.memberAt_isLearner_acc (m : Loc) (q : Qp) (mm : apply.MemberM) :
    membership.memberAt (GF := GF) m q mm ⊢
      membership.mIsLearnerAddr m ↦{DFrac.own q} mm.isLearner ∗
      (membership.mIsLearnerAddr m ↦{DFrac.own q} mm.isLearner -∗ membership.memberAt m q mm) := by
  unfold membership.memberAt
  iintro ⟨%Hnn, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
  iframe Hil
  iintro Hil
  isplitr; (ipureintro; exact Hnn)
  iexists pu, cu; iframe

/-- The members map's half, opened: its map and members, and the way back. -/
theorem membership.memAt_open (c : Loc) (q : Qp) (ms : GMap w64 Loc)
    (mem : GMap w64 apply.MemberM) :
    membership.memAt (GF := GF) c q ms mem ⊢ ∃ mp : Loc,
      membership.rcMembersAddr c ↦{DFrac.own q} mp ∗ mp ↦${DFrac.own q} ms ∗
      ([∗map] k ↦ m ∈ ms, membership.memberAt m q ((mem !! k).getD default)) ∗
      (membership.rcMembersAddr c ↦{DFrac.own q} mp -∗ mp ↦${DFrac.own q} ms -∗
        ([∗map] k ↦ m ∈ ms, membership.memberAt m q ((mem !! k).getD default)) -∗
        membership.memAt c q ms mem) := by
  unfold membership.memAt
  iintro ⟨%mp, Hf, Hm, %Hdom, Hms⟩
  iexists mp
  iframe Hf Hm Hms
  iintro Hf Hm Hms
  iexists mp; iframe; ipureintro; exact Hdom

/-- The lock's half and the apply thread's half of the members map make the whole map. -/
theorem membership.memAt_join (c : Loc) (ms ms' : GMap w64 Loc)
    (mem mem' : GMap w64 apply.MemberM) :
    membership.memAt (GF := GF) c (1 : Qp).half ms mem ∗ membership.memAt c (1 : Qp).half ms' mem' ⊢
      ⌜ms' = ms ∧ mem' = mem⌝ ∗ membership.memAt c 1 ms mem := by
  iintro ⟨H1, H2⟩
  ihave %Hag := membership.memAt_agree c _ _ ms ms' mem mem' $$ [H1 H2]
  · iframe
  obtain ⟨rfl, rfl⟩ := Hag
  isplitr; (ipureintro; exact ⟨rfl, rfl⟩)
  have h := (membership.memAt_split (GF := GF) c (1 : Qp).half (1 : Qp).half ms mem).2
  rw [Qp.half_add_half] at h
  iapply h; iframe

/-- The whole members map in two halves. -/
theorem membership.memAt_halve (c : Loc) (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM) :
    membership.memAt (GF := GF) c 1 ms mem ⊢
      membership.memAt c (1 : Qp).half ms mem ∗ membership.memAt c (1 : Qp).half ms mem := by
  have h := (membership.memAt_split (GF := GF) c (1 : Qp).half (1 : Qp).half ms mem).1
  rw [Qp.half_add_half] at h
  exact h

/-- The members of a map with `id` deleted (from both the map and the values). -/
theorem membership.memMembers_delete (q : Qp) (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM)
    (id : w64) (m : Loc) (h : ms !! id = some m) :
    ([∗map] k ↦ x ∈ ms, membership.memberAt (GF := GF) x q ((mem !! k).getD default)) ⊢
      membership.memberAt m q ((mem !! id).getD default) ∗
      [∗map] k ↦ x ∈ GMap.delete id ms,
        membership.memberAt x q (((GMap.delete id mem) !! k).getD default) := by
  iintro H
  icases (BigSepM.bigSepM_delete (Φ := fun k x => membership.memberAt (GF := GF) x q
    ((mem !! k).getD default)) h).1 $$ H with ⟨Hm, H⟩
  iframe Hm
  iapply BigSepM.bigSepM_mono (fun {k _} hk => by
    have hne : id ≠ k := fun he => by
      rw [Iris.Std.LawfulPartialMap.get?_delete_eq he] at hk; cases hk
    rw [GMap.lookup_delete_ne _ hne]) $$ H

/-- The keys of the two maps, with `id` deleted from both. -/
theorem membership.memDom_delete (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM) (id : w64)
    (h : membership.memDom ms mem) :
    membership.memDom (GMap.delete id ms) (GMap.delete id mem) := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hk : id = k
    · subst hk; simp
    · rw [GMap.lookup_delete_ne _ hk, GMap.lookup_delete_ne _ hk]; exact h.1 k
  · rw [GMap.map_size_delete, GMap.map_size_delete, h.1 id, h.2]

/-- The keys of the two maps, with `id` inserted into both. -/
theorem membership.memDom_insert (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM) (id : w64)
    (m : Loc) (mm : apply.MemberM) (h : membership.memDom ms mem) :
    membership.memDom (GMap.insert id m ms) (GMap.insert id mm mem) := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hk : id = k
    · subst hk; simp [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ hk, GMap.lookup_insert_ne _ _ hk]; exact h.1 k
  · rw [GMap.map_size_insert, GMap.map_size_insert, h.1 id, h.2]

/-- The members of a map with the member `m` of value `mm` put at `id` (in the map and the values),
replacing the old member there (dropped). -/
theorem membership.memMembers_insert (q : Qp) (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM)
    (id : w64) (m : Loc) (mm : apply.MemberM) :
    ([∗map] k ↦ x ∈ ms, membership.memberAt (GF := GF) x q ((mem !! k).getD default)) ∗
      membership.memberAt m q mm ⊢
      [∗map] k ↦ x ∈ GMap.insert id m ms,
        membership.memberAt x q (((GMap.insert id mm mem) !! k).getD default) := by
  iintro ⟨H, Hm⟩
  ihave H' : iprop([∗map] k ↦ x ∈ GMap.delete id ms,
      membership.memberAt (GF := GF) x q (((GMap.insert id mm mem) !! k).getD default)) $$ [H]
  · cases h : ms !! id with
    | none =>
      rw [GMap.delete_notin _ _ h]
      iapply BigSepM.bigSepM_mono (fun {k _} hk => by
        have hne : id ≠ k := fun he => by
          subst he
          have : (Iris.Std.get? ms id) = ms !! id := rfl
          rw [this, h] at hk; cases hk
        rw [GMap.lookup_insert_ne _ _ hne]) $$ H
    | some m0 =>
      icases membership.memMembers_delete q ms mem id m0 h $$ H with ⟨-, H⟩
      iapply BigSepM.bigSepM_mono (fun {k _} hk => by
        have hne : id ≠ k := fun he => by
          subst he
          have : (Iris.Std.get? (GMap.delete id ms) id) = (GMap.delete id ms) !! id := rfl
          rw [this, GMap.lookup_delete] at hk; cases hk
        rw [GMap.lookup_insert_ne _ _ hne, GMap.lookup_delete_ne _ hne]) $$ H
  iapply (BigSepM.bigSepM_insert_delete (Φ := fun k x => membership.memberAt (GF := GF) x q
    (((GMap.insert id mm mem) !! k).getD default)) (m := ms) (i := id) (x := m)).2
  iframe H'
  rw [GMap.lookup_insert]
  simp only [Option.getD_some]
  iexact Hm

end lemmas

end EtcdGrove
end Perennial
