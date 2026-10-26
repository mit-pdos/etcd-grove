/-
**The rest buckets at the applied log** (D22, 2026-10-23: the backend over every bucket;
`notes/decisions.md`, "D22c decided" and "D22 the backend over every bucket carried out").
Lean-first (no Rocq counterpart).

The backend tracks etcd's rest buckets (`mvcc.restBuckets`; `KBReal.P`'s `RB`): a put in, delete
from, creation or deletion of one needs the client's half of them (`backend.rbOwn`). The server's
apply thread holds it with the cluster's in-memory member list (option (i) of "D22c decided":
`membership.clusterMem`, exception 7) at their **model of the applied log** (`restModel`), the
environment's `AEnv.RO` (`srvRestOwn`):

* `restBoot bootLog`: what `bootstrap` and `NewServer`'s constructors leave on a fresh data
  directory: every rest bucket empty but `auth`, which holds the revision `1` (`authBoot`,
  `NewAuthStore`'s `commitRevision`); the in-memory members the boot log's (`memBoot`: the
  members whose JSON the bootstrap entries' contexts are);
* `restEntry c0 m`: a normal entry's request through `dispatch` (`apply.restAfter`: the cluster
  version and the member attributes), with `v3` iff above `c0`; a conf change through
  `applyConfChange` (`ccRest`: with `v3`, a validated `AddNode` saves the context's member, a
  validated `RemoveNode` deletes the member and records its removal);
* `restModel c0 bootLog L`: their fold over the raft log `L` from `restBoot bootLog`.

It is a function of the log and of cluster-wide values (`c0`, the boot log): every member's
apply thread computes the same buckets, which is what a snapshot's image carries
(`InvImage.lean`'s `bkRestAt`). Nothing else writes them: the stores' other writers take the
environment's write right `AEnv.RW` (`srvRestRW`: the same half, which the apply thread never
lends), and the workload admits none of their requests (`apply.rqOk`, `plainCover`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestModel
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The membership's model -/

/-- **The member a conf change's context unmarshals to** (`json.Unmarshal` into a
`membership.ConfigChangeContext`'s embedded `Member`; opaque, as `ccContextOf`, a function of the
bytes): what `applyConfChange`'s `AddMember` saves. -/
opaque membership.ccMemberOf [FfiSyntax] : List w8 → apply.MemberM

/-- A peer URL some member of `mems` (each member's peer URLs) has. -/
def membership.urlTaken (mems : GMap w64 (List GoString)) (u : GoString) : Prop :=
  ∃ k pus, mems !! k = some pus ∧ u ∈ pus

/-- **The verdict of `ValidateConfigurationChange` with `shouldApplyV3`**, on the members' peer URLs
`mems` and the removed members `rmv` the backend holds: not a removed id; an `AddNode` (not a
promotion: the scope's) of an id not a member, whose peer URLs (the context's member's) no member
has; a `RemoveNode` of a member. -/
def membership.ccValidM [FfiSyntax] (mems : GMap w64 (List GoString)) (rmv : GMap w64 Bool) (m : CCV1M) : Prop :=
  (rmv !! m.nodeId).getD false = false ∧
  (if m.type = W32 0 then mems !! m.nodeId = none ∧
      ∀ u, u ∈ (membership.ccMemberOf m.context).peerURLs → ¬ membership.urlTaken mems u
    else (mems !! m.nodeId).isSome = true)

/-- **The members and the removed members the `members` and `members_removed` buckets decode to**
(opaque, a function of the tracked buckets; D43 M5b′, 2026-10-26, the user's decision):
`MustReadMembersFromBackend`'s answer -- each member's id (its key, `mustParseMemberIDFromBytes`)
with the peer URLs its JSON value unmarshals to, and the ids under `members_removed` -- as its
read contract states it (`schema.membershipBackend.MustReadMembersFromBackend.spec`). -/
opaque membership.membersOfBk [FfiSyntax] :
    GMap GoString backend.BktData → GMap w64 (List GoString) × GMap w64 Bool

open Classical in
/-- **`ValidateConfigurationChange`'s verdict with `shouldApplyV3`** (D43 M5b′, 2026-10-26, the
user's decision: defined, until then opaque): `ccValidM` of what the backend's read returns at the
tracked buckets `bk` (`membersOfBk`); `true` when it returns `nil`. -/
def membership.ccValidOn [FfiSyntax] (bk : GMap GoString backend.BktData) (m : CCV1M) : Bool :=
  decide (membership.ccValidM (membership.membersOfBk bk).1 (membership.membersOfBk bk).2 m)

/-- **The member an `AddNode`'s `AddMember` adds** (D43 M5e, 2026-10-26): the context's member
(`ccMemberOf`) with the change's node as its id (`json.Unmarshal`'s `ID` field, which
`applyConfChange` checks against the change's `NodeId`). -/
def membership.ccMemberAt [FfiSyntax] (m : CCV1M) : apply.MemberM :=
  { membership.ccMemberOf m.context with id := m.nodeId }

/-- **The change `applyConfChange` hands raft for `m`** (with `v3`; D43 M5d, 2026-10-26): the change
itself when it validates against the tracked buckets `bk` (`ccValidOn`), else the change with
`NodeId` `0` (`cc.NodeId = raft.None`), which raft's `confchange` skips. -/
def membership.ccRaftEff [FfiSyntax] (bk : GMap GoString backend.BktData) (m : CCV1M) : CCV1M :=
  if membership.ccValidOn bk m = true then m else { m with nodeId := W64 0 }

/-- The value `MustDeleteMemberFromBackend` puts under a removed member's key in
`members_removed` (`[]byte("removed")`). -/
def membership.removedVal [FfiSyntax] : GoString := go!"removed"

/-- **What `applyConfChange(cc, ep, v3)` does to the rest buckets and the members** (D22,
2026-10-23; D43 M5b′, 2026-10-26: with `RemoveNode`): with `v3`, a change that validates
(`ccValidOn`): an `AddNode` adds the context's member (`ccMemberAt`), in memory and in `members` (`AddMember`'s
`MustSaveMemberToBackend` and `c.members[m.ID] = m`); a `RemoveNode` deletes the member from
`members` and records it in `members_removed` (`RemoveMember`'s `MustDeleteMemberFromBackend`)
and from memory (`delete(c.members, id)`). Anything else nothing (a failed validation; without
`v3`, the writers write nothing; the server's policy admits no other change, `ccApplyOk`). -/
def ccRest [FfiSyntax] (v3 : Bool) (m : CCV1M) (r : apply.RestM) : apply.RestM :=
  if v3 = true ∧ membership.ccValidOn r.bk m = true then
    if m.type = W32 0 then
      ({ r with mem := r.mem.insert m.nodeId (membership.ccMemberAt m) } : apply.RestM).putIn
        go!"members" (apply.memberKey m.nodeId) (apply.memberEnc (membership.ccMemberAt m))
    else if m.type = W32 1 then
      (({ r with mem := r.mem.delete m.nodeId } : apply.RestM).delIn go!"members"
        (apply.memberKey m.nodeId)).putIn go!"members_removed" (apply.memberKey m.nodeId)
        membership.removedVal
    else r
  else r

/-! ## The model of the applied log -/

/-- The auth bucket `NewAuthStore` leaves on a fresh backend: the revision `1`
(`commitRevision`), auth disabled (no `authEnabled` key). -/
def authBoot [FfiSyntax] : backend.BktData := GMap.insert go!"authRevision" (u64Be (W64 1)) ∅

/-- **The rest buckets after `NewServer`'s constructors on a fresh data directory**. -/
def restBootBk [FfiSyntax] : GMap GoString backend.BktData :=
  ((((((((∅ : GMap GoString backend.BktData).insert go!"lease" ∅).insert go!"alarm" ∅).insert
    go!"auth" authBoot).insert go!"authUsers" ∅).insert go!"authRoles" ∅).insert go!"members" ∅).insert
    go!"members_removed" ∅).insert go!"cluster" ∅

/-- **The in-memory members `bootstrap` makes** for the boot log `bootLog`: each bootstrap
entry's change's node, the member its context (the member's JSON) unmarshals to. -/
def memBoot [FfiSyntax] (bootLog : List EntryM) : GMap w64 apply.MemberM :=
  bootLog.foldl (fun mem e => match ccDecodeV1 e.Data' with
    | some cc => mem.insert cc.nodeId (membership.ccMemberOf cc.context)
    | none => mem) ∅

/-- **The rest buckets and members at the start** (see the file header). -/
def restBoot [FfiSyntax] (bootLog : List EntryM) : apply.RestM := ⟨restBootBk, memBoot bootLog⟩

/-- **One committed entry's effect** (see the file header): `v3` iff above `c0`. -/
def restEntry [FfiSyntax] (c0 : w64) (m : EntryModel) (r : apply.RestM) : apply.RestM :=
  if m.typ = W32 0 then
    if m.data = [] then r
    else match apply.irrDecode m.data with
      | some rq => apply.restAfter rq (decide (uint.Z c0 < uint.Z m.index)) r
      | none => r
  else match ccDecodeV1 m.data with
    | some cc => ccRest (decide (uint.Z c0 < uint.Z m.index)) cc r
    | none => r

/-- **The rest buckets and members at the committed log `L`** (see the file header). -/
def restModel [FfiSyntax] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel) : apply.RestM :=
  L.foldl (fun r m => restEntry c0 m r) (restBoot bootLog)

/-- A put in another bucket leaves a bucket. -/
theorem putIn_other (r : apply.RestM) (n k v n' : GoString) (h : n ≠ n') :
    (r.putIn n k v).bk.lookup n' = r.bk.lookup n' := by
  simp [apply.RestM.putIn, GMap.lookup_insert_eq_iff, h]

/-- A delete from another bucket leaves a bucket. -/
theorem delIn_other (r : apply.RestM) (n k n' : GoString) (h : n ≠ n') :
    (r.delIn n k).bk.lookup n' = r.bk.lookup n' := by
  simp [apply.RestM.delIn, GMap.lookup_insert_eq_iff, h]

/-- **An entry changes only the `members`, `members_removed` and `cluster` buckets.** -/
theorem restEntry_keep [FfiSyntax] (c0 : w64) (m : EntryModel) (r : apply.RestM) (n : GoString)
    (h1 : go!"members" ≠ n) (h2 : go!"cluster" ≠ n) (h3 : go!"members_removed" ≠ n) :
    (restEntry c0 m r).bk.lookup n = r.bk.lookup n := by
  have hsv : ∀ v3 s r', (apply.restSetVersion v3 s r').bk.lookup n = r'.bk.lookup n := by
    intro v3 s r'; unfold apply.restSetVersion; split
    · exact putIn_other _ _ _ _ _ h2
    · rfl
  have hua : ∀ v3 a r', (apply.restUpdateAttrs v3 a r').bk.lookup n = r'.bk.lookup n := by
    intro v3 a r'; unfold apply.restUpdateAttrs; split
    · rfl
    · split
      · exact putIn_other _ _ _ _ _ h1
      · rfl
  have hra : ∀ rq v3 r', (apply.restAfter rq v3 r').bk.lookup n = r'.bk.lookup n := by
    intro rq v3 r'; unfold apply.restAfter; split
    · exact hsv _ _ _
    · split
      · exact hua _ _ _
      · rfl
  have hcc : ∀ v3 cc r', (ccRest v3 cc r').bk.lookup n = r'.bk.lookup n := by
    intro v3 cc r'; unfold ccRest; split
    · split
      · exact putIn_other _ _ _ _ _ h1
      · split
        · rw [putIn_other _ _ _ _ _ h3, delIn_other _ _ _ _ h1]
        · rfl
    · rfl
  unfold restEntry
  split
  · split
    · rfl
    · split
      · exact hra _ _ _
      · rfl
  · split
    · exact hcc _ _ _
    · rfl

theorem restModel_keep [FfiSyntax] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel)
    (n : GoString) (h1 : go!"members" ≠ n) (h2 : go!"cluster" ≠ n)
    (h3 : go!"members_removed" ≠ n) :
    (restModel c0 bootLog L).bk.lookup n = (restBoot bootLog).bk.lookup n := by
  unfold restModel
  generalize restBoot bootLog = r0
  induction L generalizing r0 with
  | nil => rfl
  | cons m L ih => rw [List.foldl_cons, ih, restEntry_keep _ _ _ _ h1 h2 h3]

theorem restModel_nil [FfiSyntax] (c0 : w64) (bootLog : List EntryM) :
    restModel c0 bootLog [] = restBoot bootLog := rfl

theorem restModel_append [FfiSyntax] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel)
    (m : EntryModel) :
    restModel c0 bootLog (L ++ [m]) = restEntry c0 m (restModel c0 bootLog L) := by
  unfold restModel; rw [List.foldl_append]; rfl

/-! ## The model's steps -/

/-- **`apply.Apply`'s effect on a covered request** (`plainCover`): it is neither skipped nor
rejected (a covered request has no side-effect-free and no admin field), so the effect is
`dispatch`'s. -/
theorem restOut_plain [FfiSyntax] (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (r : apply.RestM) (hp : plainCover rq)
    (h : apply.applyStep rq v3 x x' out) :
    apply.restOut rq v3 out r = apply.restAfter rq v3 r := by
  have hns : apply.noSideEffect rq = false ∧ apply.needAdminPermission rq = false := by
    unfold plainCover at hp
    cases hk : apply.dispatchKind rq <;> simp only [hk] at hp
    all_goals first
      | exact hp.elim
      | exact ⟨hp.1, hp.2.1⟩
      | exact ⟨hp.1, hp.2⟩
  cases out with
  | skipped => exact absurd h.1 (by rw [hns.1]; decide)
  | rejected => exact absurd h.1 (by rw [hns.2]; decide)
  | dispatched o skip => rfl

/-- A normal entry with a request: its effect is `dispatch`'s. -/
theorem restEntry_normal [FfiSyntax] (c0 : w64) (m : EntryModel) (rq : apply.IRRModel)
    (r : apply.RestM) (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq) :
    restEntry c0 m r = apply.restAfter rq (decide (uint.Z c0 < uint.Z m.index)) r := by
  unfold restEntry; rw [if_pos ht, if_neg hd, hdec]

/-- A normal entry with no data does nothing. -/
theorem restEntry_nodata [FfiSyntax] (c0 : w64) (m : EntryModel) (r : apply.RestM)
    (ht : m.typ = W32 0) (hd : m.data = []) : restEntry c0 m r = r := by
  unfold restEntry; rw [if_pos ht, if_pos hd]

/-- A conf change: `applyConfChange`'s effect. -/
theorem restEntry_cc [FfiSyntax] (c0 : w64) (m : EntryModel) (cc : CCV1M) (r : apply.RestM)
    (ht : m.typ ≠ W32 0) (hdec : ccDecodeV1 m.data = some cc) :
    restEntry c0 m r = ccRest (decide (uint.Z c0 < uint.Z m.index)) cc r := by
  unfold restEntry; rw [if_neg ht, hdec]

/-! ## The real backend's tracked buckets -/

/-- The real instance's tracked buckets are the rest buckets. -/
theorem rbData_real_lookup (d : mvcc.KBReal) (D : backend.Data) (n : GoString)
    (h : n ∈ mvcc.restBuckets) : (backend.rbData d.P D).lookup n = D.lookup n := by
  rw [backend.rbData_lookup]
  have : d.P.RB n = true := by show decide (n ∈ mvcc.restBuckets) = true; simpa using h
  rw [this]; rfl

/-- **The constructors' rest buckets on a fresh data directory** (`bootOk`'s facts): the lessor's,
the auth store's and the alarm store's created (the auth bucket at `authBoot`), the membership's
as `bootstrap` left them: `restBootBk`. -/
theorem restBootBk_of_fresh [FfiSyntax] (d : mvcc.KBReal) (D : backend.Data)
    (h : (∀ n ∈ mvcc.restBuckets, (D.lookup n).getD ∅ = ∅) ∧ D.lookup go!"members" = some ∅ ∧
      D.lookup go!"members_removed" = some ∅ ∧ D.lookup go!"cluster" = some ∅) :
    ((((((backend.rbData d.P D).insert go!"lease" ∅).insert go!"auth" authBoot).insert
      go!"authUsers" ∅).insert go!"authRoles" ∅).insert go!"alarm" ∅) = restBootBk := by
  obtain ⟨-, hm, hmr, hc⟩ := h
  apply GMap.ext
  intro n
  simp only [restBootBk, GMap.lookup_insert_eq_iff]
  by_cases hn : n ∈ mvcc.restBuckets
  · rw [rbData_real_lookup d D n hn]
    simp only [mvcc.restBuckets, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hm, hmr, hc]
  · rw [backend.rbData_lookup]
    have : d.P.RB n = false := by show decide (n ∈ mvcc.restBuckets) = false; simpa using hn
    rw [this]
    simp only [mvcc.restBuckets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hn
    simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7,
      Ne.symm h8]

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/- `membership.clusterMem` (the cluster's in-memory members) is defined in the membership
package's `Defs.lean` since D43 M5b (2026-10-26; opaque here until then). -/

/-- **The server's `AEnv.RO`**: the backend `γB`'s tracked buckets' client half and the cluster
`c`'s in-memory members, at `r`. -/
def srvRestOwn (γB : backend.BNames) (c : Loc) (r : apply.RestM) : IProp GF :=
  iprop(backend.rbOwn γB r.bk ∗ membership.clusterMem c r.mem)

/-- **The server's `AEnv.RW`**: the backend's tracked buckets' client half at some value (what
the stores' writers the workload does not reach would need; the apply thread holds it at its
model in `srvRestOwn` and never lends it). -/
def srvRestRW (γB : backend.BNames) : IProp GF := iprop(∃ r, backend.rbOwn γB r)

/-- **The server's `AEnv.RO` with its objects' backend parts `H`** (D22 receiver epochs, S7c,
2026-10-23): `srvRestOwn` and `H`, the halves of the backend fields of the objects that write the
backend (the alarm store's `alarmBeOn`, the auth store's `authBeOn`): the apply thread holds them
with the rest buckets; the objects' writers' contracts take them in their write right
(`srvRestRWH`), so that each names the backend the object is on, and their `Recover`s replace
them. -/
def srvRestOwnH (γB : backend.BNames) (c : Loc) (H : IProp GF) (r : apply.RestM) : IProp GF :=
  iprop(srvRestOwn γB c r ∗ H)

/-- **The server's `AEnv.RW` with its objects' backend parts `H`** (S7c). -/
def srvRestRWH (γB : backend.BNames) (H : IProp GF) : IProp GF := iprop(srvRestRW γB ∗ H)

/-- **`RW` lends `X`** (persistent; S7c): a write right holding the resources `X` a contract's
writes take and give back (`srvRestRWH` lends each object's part). -/
def rwLens (RW X : IProp GF) : IProp GF := iprop(□ (RW -∗ X ∗ (X -∗ RW)))

instance rwLens_persistent (RW X : IProp GF) : Persistent (rwLens RW X) := by
  unfold rwLens; infer_instance

/-- The schema auth backend `*authBackend` `abl` as an interface value. -/
abbrev authBkIface (abl : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty)
    #abl

/-- **The auth store `st` is on the real backend at `be`** (D22 receiver epochs, S7c, 2026-10-23;
not persistent): its user's half of `st.be` (the other half `beMu`'s, `auth.beP`), a schema auth
backend over `be` with a logger (read-only). -/
def authBeOn (st be : Loc) : IProp GF :=
  iprop(∃ (abl lg : Loc), ⌜lg ≠ null⌝ ∗
    auth.aF go!"be" st ↦{DFrac.own (1 : Qp).half} authBkIface abl ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #be : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg)

/-- The schema membership backend `*membershipBackend` `mbl` as an interface value. -/
abbrev clusterBkIface (mbl : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty)
    #mbl

/-- **The cluster `c` is on the real backend at `be`** (D22 receiver epochs, S7e, 2026-10-23; not
persistent): its `be` field, owned (no lock guards it: the apply thread is its only reader and
writer, `SetBackend` included), a schema membership backend over `be` with a logger (read-only). -/
def clusterBeOn (c be : Loc) : IProp GF :=
  iprop(∃ (mbl lg : Loc), ⌜lg ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster go!"be" c ↦
      clusterBkIface mbl ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"be" mbl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #be : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"lg" mbl ↦□ lg)

/-- **The membership buckets of an image good for the cluster `c`** (opaque, a premise about the
images a member applies; D22 receiver epochs, S8d, W6, 2026-10-25): the `members`,
`members_removed` and `cluster` buckets (`mem`, `rem`, `cl`) decode (`MustReadMembersFromBackend`'s
keys and JSON values, the cluster version, the downgrade record), the members include `c`'s local
member and are the static cluster's (those of `bootOk`'s `Members()` contract, with the directory's
peer URLs), none removed, and the cluster version is one `MustDetectDowngrade` accepts for this
server (no downgrade). -/
opaque membership.memBucketsOk (c : Loc) (mem rem cl : Option backend.BktData) : Prop

/-- **The tracked buckets `r` hold an image good for the cluster `c`** (`memBucketsOk` of its three
membership buckets; what `RaftCluster.Recover`'s axiom takes). -/
def membership.clusterImageOk (c : Loc) (r : GMap GoString backend.BktData) : Prop :=
  membership.memBucketsOk c (r.lookup go!"members") (r.lookup go!"members_removed")
    (r.lookup go!"cluster")

/-- **The server's objects on the backend at `be`** (D22 receiver epochs, S7c, S7e): the alarm
store `al`'s, the auth store `st`'s and the lessor `lp`'s user halves of their backend fields and
the cluster `c`'s field, the server's `H` of its environment's rest resource and write right
(`srvRestOwnH`, `srvRestRWH`). -/
def srvObjsOn (al st lp c be : Loc) : IProp GF :=
  iprop(alarmBeOn al be ∗ authBeOn st be ∗ lease.lessorBeOn lp be ∗ clusterBeOn c be)

/-- **`RO` lends `X`** (persistent; S7e): a rest resource holding, at every value, the resources
`X` a contract's writes take at that value and give back at another (`srvRestOwnH`'s). -/
def roLens (RO X : apply.RestM → IProp GF) : IProp GF :=
  iprop(□ ∀ r : apply.RestM, RO r -∗ X r ∗ (∀ r' : apply.RestM, X r' -∗ RO r'))

instance roLens_persistent (RO X : apply.RestM → IProp GF) : Persistent (roLens RO X) := by
  unfold roLens; infer_instance

/-- **The apply thread's rest buckets at the applied log `A`** (`AEnv.RO` at `restModel` of the
log through `A`, from the start's consistent index and the boot log). -/
def srvRest (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) : IProp GF :=
  E.RO (restModel γr.kv.c0 γr.raft.raft.reBoot (γr.raft.pre ++ A))

/-- The rest buckets one entry later. -/
theorem srvRest_snoc (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel) :
    srvRest E γr (A ++ [m]) =
      E.RO (restEntry γr.kv.c0 m (restModel γr.kv.c0 γr.raft.raft.reBoot (γr.raft.pre ++ A))) := by
  unfold srvRest; rw [← List.append_assoc, restModel_append]

/-- An entry with no data leaves them. -/
theorem srvRest_nodata (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (ht : m.typ = W32 0) (hd : m.data = []) : srvRest E γr (A ++ [m]) = srvRest E γr A := by
  rw [srvRest_snoc, restEntry_nodata _ _ _ ht hd]; rfl

/-- **A covered request applied by `apply.Apply`** (`v3` the entry's): its rest buckets one entry
later. -/
theorem srvRest_apply (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)) (hp : plainCover rq)
    (hs : apply.applyStep rq v3 x x' out) :
    E.RO (apply.restOut rq v3 out (restModel γr.kv.c0 γr.raft.raft.reBoot (γr.raft.pre ++ A))) =
      srvRest E γr (A ++ [m]) := by
  rw [srvRest_snoc, restEntry_normal _ _ rq _ ht hd hdec, restOut_plain rq v3 x x' out _ hp hs, hv3]

end defs

end EtcdGrove
end Perennial
