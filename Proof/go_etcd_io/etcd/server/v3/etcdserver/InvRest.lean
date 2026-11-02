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
  members whose JSON the bootstrap entries' contexts are, each keyed by and with its entry's node
  as its id, `ccMemberAt`; 2026-11-02, the backend-auth-split stage);
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
opaque membership.ccMemberOf [GooseExts] : List w8 → apply.MemberM

/-- A peer URL some member of `mems` (each member's peer URLs) has. -/
def membership.urlTaken (mems : GMap w64 (List GoString)) (u : GoString) : Prop :=
  ∃ k pus, mems !! k = some pus ∧ u ∈ pus

/-- **The verdict of `ValidateConfigurationChange` with `shouldApplyV3`**, on the members' peer URLs
`mems` and the removed members `rmv` the backend holds: not a removed id; an `AddNode` (not a
promotion: the scope's) of an id not a member, whose peer URLs (the context's member's) no member
has; a `RemoveNode` of a member. -/
def membership.ccValidM [GooseExts] (mems : GMap w64 (List GoString)) (rmv : GMap w64 Bool) (m : ConfChangeM) : Prop :=
  (rmv !! m.nodeId).getD false = false ∧
  (if m.type = W32 0 then mems !! m.nodeId = none ∧
      ∀ u, u ∈ (membership.ccMemberOf m.context).peerURLs → ¬ membership.urlTaken mems u
    else (mems !! m.nodeId).isSome = true)

/-- **The members and the removed members the `members` and `members_removed` buckets decode to**
(opaque, a function of the tracked buckets; D43 M5b′, 2026-10-26, the user's decision):
`MustReadMembersFromBackend`'s answer -- each member's id (its key, `mustParseMemberIDFromBytes`)
with the peer URLs its JSON value unmarshals to, and the ids under `members_removed` -- as its
read contract states it (`schema.membershipBackend.MustReadMembersFromBackend.spec`). -/
opaque membership.membersOfBk [GooseExts] :
    GMap GoString backend.BktData → GMap w64 (List GoString) × GMap w64 Bool

open Classical in
/-- **`ValidateConfigurationChange`'s verdict with `shouldApplyV3`** (D43 M5b′, 2026-10-26, the
user's decision: defined, until then opaque): `ccValidM` of what the backend's read returns at the
tracked buckets `bk` (`membersOfBk`); `true` when it returns `nil`. -/
def membership.ccValidOn [GooseExts] (bk : GMap GoString backend.BktData) (m : ConfChangeM) : Bool :=
  decide (membership.ccValidM (membership.membersOfBk bk).1 (membership.membersOfBk bk).2 m)

/-- **Buckets with no records decode to no members** (2026-10-31, the user's decision; a trust-boundary
axiom on the opaque `membersOfBk`, `notes/axiom-review/members-empty.md`: survives). `readMembersFromBackend`
(`server/storage/schema/membership.go:91-123`) makes both maps and writes them only in the
`UnsafeForEach` callbacks over the `members` and `members_removed` buckets, so over buckets with no
keys (or absent ones, which read empty) it returns two empty maps and no error. What makes a fresh
backend's first boot `AddNode` validate (`ccValidOn_boot`). -/
axiom membership.membersOfBk_empty [GooseExts] (bk : GMap GoString backend.BktData)
    (hm : (bk.lookup go!"members").getD ∅ = ∅) (hr : (bk.lookup go!"members_removed").getD ∅ = ∅) :
    membership.membersOfBk bk = (∅, ∅)

/-- The membership buckets `MustReadMembersFromBackend` reads: `members`, `members_removed`. -/
def membership.memberBkts [GooseExts] (n : GoString) : Prop :=
  n = go!"members" ∨ n = go!"members_removed"
/-- The buckets `RaftCluster.Recover` reads (`UnsafeLoad`): the members' and `cluster`. -/
def membership.clusterBkts [GooseExts] (n : GoString) : Prop :=
  membership.memberBkts n ∨ n = go!"cluster"
/-- The auth buckets (`auth`, `authUsers`, `authRoles`: schema's `Auth`, `AuthUsers`, `AuthRoles`),
which `NewAuthStore` creates and the auth store's `Recover` reads (2026-11-02, the
backend-auth-split stage). -/
def auth.authBkts [GooseExts] (n : GoString) : Prop :=
  n = go!"auth" ∨ n = go!"authUsers" ∨ n = go!"authRoles"

/-- **The membership buckets of `bk` are as the apply thread writes them** (defined, 2026-11-01:
the backend-auth-split stage's review, in place of an opaque decoding premise): every entry of
`members` is a member's key and encoding (`memberKey id ↦ memberEnc mm`: `BackendMemberKey`'s
canonical hex, `json.Marshal` of a non-nil `*Member`, never `null`), every key of
`members_removed` a member's key. What `MustReadMembersFromBackend` needs to return a record per
key and not panic. -/
def membership.membersDecode [GooseExts] (bk : GMap GoString backend.BktData) : Prop :=
  (∀ k v, ((bk.lookup go!"members").getD ∅).lookup k = some v →
    ∃ mm : apply.MemberM, k = apply.memberKey mm.id ∧ v = apply.memberEnc mm) ∧
  (∀ k v, ((bk.lookup go!"members_removed").getD ∅).lookup k = some v → ∃ id, k = apply.memberKey id)

/-- Empty membership buckets decode (no entry; 2026-11-02, the backend-auth-split stage). -/
theorem membership.membersDecode_empty [GooseExts] (bk : GMap GoString backend.BktData)
    (hm : (bk.lookup go!"members").getD ∅ = ∅) (hr : (bk.lookup go!"members_removed").getD ∅ = ∅) :
    membership.membersDecode bk := by
  refine ⟨fun k v h => ?_, fun k v h => ?_⟩
  · rw [hm] at h; simp at h
  · rw [hr] at h; simp at h

/-- A put in another bucket keeps the decoding (`restSetVersion`'s `cluster` put). -/
theorem membership.membersDecode_other [GooseExts] (bk : GMap GoString backend.BktData)
    (n k v : GoString) (h : ¬ membership.memberBkts n) (hd : membership.membersDecode bk) :
    membership.membersDecode (apply.bkPut bk n k v) := by
  unfold membership.memberBkts at h
  have h1 : n ≠ go!"members" := fun e => h (Or.inl e)
  have h2 : n ≠ go!"members_removed" := fun e => h (Or.inr e)
  unfold apply.bkPut
  rw [membership.membersDecode, GMap.lookup_insert_ne _ _ h1, GMap.lookup_insert_ne _ _ h2]
  exact hd

/-- A member's record saved under its own id's key keeps the decoding (`restUpdateAttrs`,
`ccRest`'s `AddNode`). -/
theorem membership.membersDecode_putMember [GooseExts] (bk : GMap GoString backend.BktData)
    (mm : apply.MemberM) (hd : membership.membersDecode bk) :
    membership.membersDecode
      (apply.bkPut bk go!"members" (apply.memberKey mm.id) (apply.memberEnc mm)) := by
  have hne : go!"members" ≠ go!"members_removed" := by decide
  unfold apply.bkPut
  rw [membership.membersDecode, GMap.lookup_insert_ne _ _ hne, GMap.lookup_insert]
  refine ⟨fun k v h => ?_, hd.2⟩
  simp only [Option.getD_some, GMap.lookup_insert_eq_iff] at h
  split at h
  next e => cases h; exact ⟨mm, e.symm, rfl⟩
  next => exact hd.1 k v h

/-- A delete from `members` keeps the decoding (`ccRest`'s `RemoveNode`). -/
theorem membership.membersDecode_delMember [GooseExts] (bk : GMap GoString backend.BktData)
    (k : GoString) (hd : membership.membersDecode bk) :
    membership.membersDecode (apply.bkDel bk go!"members" k) := by
  have hne : go!"members" ≠ go!"members_removed" := by decide
  unfold apply.bkDel
  rw [membership.membersDecode, GMap.lookup_insert_ne _ _ hne, GMap.lookup_insert]
  refine ⟨fun k' v h => ?_, hd.2⟩
  simp only [Option.getD_some, GMap.lookup_delete_iff] at h
  split at h
  · cases h
  · exact hd.1 k' v h

/-- A removed member's key recorded keeps the decoding (`ccRest`'s `RemoveNode`). -/
theorem membership.membersDecode_putRemoved [GooseExts] (bk : GMap GoString backend.BktData)
    (id : w64) (v : GoString) (hd : membership.membersDecode bk) :
    membership.membersDecode (apply.bkPut bk go!"members_removed" (apply.memberKey id) v) := by
  have hne : go!"members_removed" ≠ go!"members" := by decide
  unfold apply.bkPut
  rw [membership.membersDecode, GMap.lookup_insert_ne _ _ hne, GMap.lookup_insert]
  refine ⟨hd.1, fun k v' h => ?_⟩
  simp only [Option.getD_some, GMap.lookup_insert_eq_iff] at h
  split at h
  next e => exact ⟨id, e.symm⟩
  next => exact hd.2 k v' h

/-- **The member an `AddNode`'s `AddMember` adds** (D43 M5e, 2026-10-26): the context's member
(`ccMemberOf`) with the change's node as its id (`json.Unmarshal`'s `ID` field, which
`applyConfChange` checks against the change's `NodeId`). -/
def membership.ccMemberAt [GooseExts] (m : ConfChangeM) : apply.MemberM :=
  { membership.ccMemberOf m.context with id := m.nodeId }

/-- **The change `applyConfChange` hands raft for `m`** (with `v3`; D43 M5d, 2026-10-26): the change
itself when it validates against the tracked buckets `bk` (`ccValidOn`), else the change with
`NodeId` `0` (`cc.NodeId = raft.None`), which raft's `confchange` skips. -/
def membership.ccRaftEff [GooseExts] (bk : GMap GoString backend.BktData) (m : ConfChangeM) : ConfChangeM :=
  if membership.ccValidOn bk m = true then m else { m with nodeId := W64 0 }

/-- The value `MustDeleteMemberFromBackend` puts under a removed member's key in
`members_removed` (`[]byte("removed")`). -/
def membership.removedVal [GooseExts] : GoString := go!"removed"

/-- **What `applyConfChange(cc, ep, v3)` does to the rest buckets and the members** (D22,
2026-10-23; D43 M5b′, 2026-10-26: with `RemoveNode`): with `v3`, a change that validates
(`ccValidOn`): an `AddNode` adds the context's member (`ccMemberAt`), in memory and in `members` (`AddMember`'s
`MustSaveMemberToBackend` and `c.members[m.ID] = m`); a `RemoveNode` deletes the member from
`members` and records it in `members_removed` (`RemoveMember`'s `MustDeleteMemberFromBackend`)
and from memory (`delete(c.members, id)`). Anything else nothing (a failed validation; without
`v3`, the writers write nothing; the server's policy admits no other change, `ccApplyOk`). -/
def ccRest [GooseExts] (v3 : Bool) (m : ConfChangeM) (r : apply.RestM) : apply.RestM :=
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
def authBoot [GooseExts] : backend.BktData := GMap.insert go!"authRevision" (u64Be (W64 1)) ∅

/-- **The rest buckets after `NewServer`'s constructors on a fresh data directory**. -/
def restBootBk [GooseExts] : GMap GoString backend.BktData :=
  ((((((((∅ : GMap GoString backend.BktData).insert go!"lease" ∅).insert go!"alarm" ∅).insert
    go!"auth" authBoot).insert go!"authUsers" ∅).insert go!"authRoles" ∅).insert go!"members" ∅).insert
    go!"members_removed" ∅).insert go!"cluster" ∅

/-- **The in-memory members `bootstrap` makes** for the boot log `bootLog`: each bootstrap
entry's change's node, the member its context (the member's JSON) unmarshals to, with the node as
its id (`ccMemberAt`; 2026-11-02, the backend-auth-split stage: until then `ccMemberOf cc.context`,
whose id the model left open). True of Go: `bootstrapRaftFromCluster` builds each peer's context as
`json.Marshal(cl.Member(id))` with `Peer{ID: uint64(id)}`, and the cluster's map is keyed by the
member's own `ID` (`membership.NewClusterFromURLsMap`, `cl.members[m.ID] = m`), so the member in
memory under `nodeId` has id `nodeId`. -/
def memBoot [GooseExts] (bootLog : List EntryM) : GMap w64 apply.MemberM :=
  bootLog.foldl (fun mem e => match ccDecodeV1 e.Data' with
    | some cc => mem.insert cc.nodeId (membership.ccMemberAt cc)
    | none => mem) ∅

/-- **The rest buckets and members at the start** (see the file header). -/
def restBoot [GooseExts] (bootLog : List EntryM) : apply.RestM := ⟨restBootBk, memBoot bootLog⟩

/-- **One committed entry's effect** (see the file header): `v3` iff above `c0`. -/
def restEntry [GooseExts] (c0 : w64) (m : EntryModel) (r : apply.RestM) : apply.RestM :=
  if m.typ = W32 0 then
    if m.data = [] then r
    else match apply.irrDecode m.data with
      | some rq => apply.restAfter rq (decide (uint.Z c0 < uint.Z m.index)) r
      | none => r
  else match ccDecodeV1 m.data with
    | some cc => ccRest (decide (uint.Z c0 < uint.Z m.index)) cc r
    | none => r

/-- **The rest buckets and members at the committed log `L`** (see the file header). -/
def restModel [GooseExts] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel) : apply.RestM :=
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
theorem restEntry_keep [GooseExts] (c0 : w64) (m : EntryModel) (r : apply.RestM) (n : GoString)
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

theorem restModel_keep [GooseExts] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel)
    (n : GoString) (h1 : go!"members" ≠ n) (h2 : go!"cluster" ≠ n)
    (h3 : go!"members_removed" ≠ n) :
    (restModel c0 bootLog L).bk.lookup n = (restBoot bootLog).bk.lookup n := by
  unfold restModel
  generalize restBoot bootLog = r0
  induction L generalizing r0 with
  | nil => rfl
  | cons m L ih => rw [List.foldl_cons, ih, restEntry_keep _ _ _ _ h1 h2 h3]

theorem restModel_nil [GooseExts] (c0 : w64) (bootLog : List EntryM) :
    restModel c0 bootLog [] = restBoot bootLog := rfl

/-- (2026-10-31, S5) **A fresh backend validates an `AddNode`**: its members buckets are empty
(`membersOfBk_empty`), so no member, no removed one, no peer URL taken. -/
theorem ccValidOn_boot [GooseExts] (m : ConfChangeM) (ht : m.type = W32 0) :
    membership.ccValidOn restBootBk m = true := by
  unfold membership.ccValidOn
  rw [membership.membersOfBk_empty restBootBk (by simp [restBootBk, GMap.lookup_insert_ne, GMap.lookup_insert])
    (by simp [restBootBk, GMap.lookup_insert_ne, GMap.lookup_insert])]
  simp only [decide_eq_true_eq]
  refine ⟨by simp, ?_⟩
  rw [if_pos ht]
  refine ⟨by simp, fun u _ ⟨k, pus, hk, _⟩ => by simp at hk⟩

theorem restModel_append [GooseExts] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel)
    (m : EntryModel) :
    restModel c0 bootLog (L ++ [m]) = restEntry c0 m (restModel c0 bootLog L) := by
  unfold restModel; rw [List.foldl_append]; rfl

/-! ## The model's steps -/

/-- **`apply.Apply`'s effect on a covered request** (`plainCover`): it is neither skipped nor
rejected (a covered request has no side-effect-free and no admin field), so the effect is
`dispatch`'s. -/
theorem restOut_plain [GooseExts] (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
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
theorem restEntry_normal [GooseExts] (c0 : w64) (m : EntryModel) (rq : apply.IRRModel)
    (r : apply.RestM) (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq) :
    restEntry c0 m r = apply.restAfter rq (decide (uint.Z c0 < uint.Z m.index)) r := by
  unfold restEntry; rw [if_pos ht, if_neg hd, hdec]

/-- A normal entry with no data does nothing. -/
theorem restEntry_nodata [GooseExts] (c0 : w64) (m : EntryModel) (r : apply.RestM)
    (ht : m.typ = W32 0) (hd : m.data = []) : restEntry c0 m r = r := by
  unfold restEntry; rw [if_pos ht, if_pos hd]

/-- A conf change: `applyConfChange`'s effect. -/
theorem restEntry_cc [GooseExts] (c0 : w64) (m : EntryModel) (cc : ConfChangeM) (r : apply.RestM)
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
theorem restBootBk_of_fresh [GooseExts] (d : mvcc.KBReal) (D : backend.Data)
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

/-- **Every member the model keeps has its key as its id** (moved here from `RestMemId.lean`
2026-11-02, the backend-auth-split stage: `srvRestOwn` holds it). -/
def memIdOk (mem : GMap w64 apply.MemberM) : Prop :=
  ∀ id m, mem.lookup id = some m → m.id = id

section present
variable [GooseExts]

/-- **The rest buckets are present in `bk`**: every bucket `NewServer`'s constructors make
(`restBootBk`: `lease`, `alarm`, `auth`, `authUsers`, `authRoles`, `members`, `members_removed`,
`cluster`). Their writers (the cluster's rows and `applyConfChange`; the alarm store's and the
auth store's, through `RW`; the lessor's revocation, an `UnsafeDelete` in `lease`, through `RO`'s
lens) `UnsafePut`/`UnsafeDelete` in them, fatal on a missing bucket
(`batch_tx.go:169-173,229-237`); no Go code deletes a rest bucket at run time. The lessor's put
right, drawn from `RW` without this fact, is a separate follow-up. -/
def restPresent (bk : GMap GoString backend.BktData) : Prop :=
  ∀ n, (restBootBk.lookup n).isSome = true → (bk.lookup n).isSome = true

end present

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/- `membership.clusterMem` (the cluster's in-memory members) is defined in the membership
package's `Defs.lean` since D43 M5b (2026-10-26; opaque here until then). -/

/-- **The server's `AEnv.RO`** (restated 2026-11-01, the backend-auth-split stage): the backend
`γB`'s tracked buckets at `r.bk` — **the cluster's buckets idle** (`rbOwnIn γB
membership.clusterBkts`: `members`, `members_removed`, `cluster`, which the apply thread's readers
`MustReadMembersFromBackend` and `RaftCluster.Recover` read through read transactions) and the
others as a part (`rbPart γB (¬ clusterBkts ·)`: the lessor's, the auth store's, the alarm store's;
the alarm and auth stores write them through `RW`, only the lessor's revocation through this part,
inside sessions whose contracts give back a part) — and the cluster `c`'s in-memory members
at `r.mem`, each member under its own id (`memIdOk r.mem`, 2026-11-02, round 5: Go saves a member
under `BackendMemberKey(m.ID)`, the model's `restUpdateAttrs` under `memberKey a.memberID`; they
agree because the member under `a.memberID` has that id; true of Go: `c.members` is keyed by each
member's `ID`), and **the rest buckets present** (`restPresent r.bk`, 2026-11-02, the cluster-rows
stage: the rows' `MustSave…`s are fatal on a missing bucket; every rest state of the model has
them, `restModel_present`). Until 2026-11-01 the whole writer's half `rbOwn γB r.bk`. -/
def srvRestOwn (γB : backend.BNames) (c : Loc) (r : apply.RestM) : IProp GF :=
  iprop(backend.rbOwnIn γB membership.clusterBkts r.bk ∗
    backend.rbPart γB (fun n => ¬ membership.clusterBkts n) r.bk ∗ membership.clusterMem c r.mem ∗
    ⌜memIdOk r.mem ∧ restPresent r.bk⌝)


/-- **The server's `AEnv.RW`**: the backend's tracked buckets' client half at some value, **the
rest buckets present** (what the stores' writers the workload does not reach would need:
`SetDowngradeInfo`'s `MustSaveDowngradeToBackend` puts in `cluster`, the alarm store's
`MustPutAlarm` in `alarm`, the auth store's writers in theirs, each fatal on a missing bucket;
2026-11-02, the cluster-rows stage, until then any value; the lessor's put right, drawn from it
without the presence fact, is a separate follow-up; the apply thread holds the half at its model
in `srvRestOwn` and never lends it). -/
def srvRestRW (γB : backend.BNames) : IProp GF :=
  iprop(∃ r, backend.rbOwn γB r ∗ ⌜restPresent r⌝)

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
`members_removed` and `cluster` buckets (`mem`, `rem`, `cl`) are as the apply thread writes them:
every `members` entry a member's key and encoding under its own id (`memberKey mm.id ↦ memberEnc
mm`, a JSON object, as `membersDecode`; so `mem'` keeps each member under its id, `json.Unmarshal`
setting `ID` from the JSON: so `UnsafeLoad`'s `MustReadMembersFromBackend` gives a non-nil member
per key, which `Recover`'s loop dereferences), every `members_removed` key a member's key,
`cluster` the version `semverNorm` writes and no downgrade record; the members include `c`'s local
member and are the static cluster's (those of `bootOk`'s `Members()` contract, with the directory's
peer URLs), none removed, and the cluster version is one `MustDetectDowngrade` accepts for this
server (no downgrade); (2026-10-25, the user's decision) the members it decodes to are `ms`
(`c.members` after `UnsafeLoad`, each as the record its JSON unmarshals to, `clusterMem`'s). -/
opaque membership.memBucketsOk (c : Loc) (ms : GMap w64 apply.MemberM)
  (mem rem cl : Option backend.BktData) : Prop

/-- **The tracked buckets `r` hold an image good for the cluster `c`, of the members `ms`**
(`memBucketsOk` of its three membership buckets; what `RaftCluster.Recover`'s axiom takes). -/
def membership.clusterImageOk (c : Loc) (r : GMap GoString backend.BktData)
    (ms : GMap w64 apply.MemberM) : Prop :=
  membership.memBucketsOk c ms (r.lookup go!"members") (r.lookup go!"members_removed")
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
  E.RO (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))

/-- The rest buckets one entry later. -/
theorem srvRest_snoc (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel) :
    srvRest E γr (A ++ [m]) =
      E.RO (restEntry γr.kv.c0 m (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) := by
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
    E.RO (apply.restOut rq v3 out (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) =
      srvRest E γr (A ++ [m]) := by
  rw [srvRest_snoc, restEntry_normal _ _ rq _ ht hd hdec, restOut_plain rq v3 x x' out _ hp hs, hv3]

end defs

end EtcdGrove
end Perennial
