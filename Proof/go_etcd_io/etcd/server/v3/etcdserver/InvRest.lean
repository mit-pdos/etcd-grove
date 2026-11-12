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
public import Proof.unicode.utf8.Valid
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AppliedTable
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
(opaque, a function of those two buckets' contents, `none` for an absent bucket; D43 M5b′,
2026-10-26, the user's decision; a function of the two buckets only since 2026-11-03, the user's
(A), `notes/lease-grant-plan.md`, "Plumbing": `readMembersFromBackend`,
`server/storage/schema/membership.go:91-123`, reads no other bucket): `MustReadMembersFromBackend`'s
answer -- each member's id (its key, `mustParseMemberIDFromBytes`) with the peer URLs its JSON value
unmarshals to, and the ids under `members_removed` -- as its read contract states it
(`schema.membershipBackend.MustReadMembersFromBackend.spec`). -/
opaque membership.membersOf [GooseExts] :
    Option backend.BktData → Option backend.BktData → GMap w64 (List GoString) × GMap w64 Bool

/-- **What the tracked buckets `bk` decode to** (`membersOf` of their `members` and
`members_removed` buckets; until 2026-11-03 itself opaque over the whole map). -/
def membership.membersOfBk [GooseExts] (bk : GMap GoString backend.BktData) :
    GMap w64 (List GoString) × GMap w64 Bool :=
  membership.membersOf (bk.lookup go!"members") (bk.lookup go!"members_removed")

open Classical in
/-- **`ValidateConfigurationChange`'s verdict with `shouldApplyV3`** (D43 M5b′, 2026-10-26, the
user's decision: defined, until then opaque): `ccValidM` of what the backend's read returns at the
tracked buckets `bk` (`membersOfBk`); `true` when it returns `nil`. -/
def membership.ccValidOn [GooseExts] (bk : GMap GoString backend.BktData) (m : ConfChangeM) : Bool :=
  decide (membership.ccValidM (membership.membersOfBk bk).1 (membership.membersOfBk bk).2 m)

/-- **Buckets with no records decode to no members** (2026-10-31, the user's decision; a trust-boundary
axiom on the opaque `membersOf`, `notes/axiom-review/members-empty.md`: survives; restated
2026-11-03 over `membersOf`, the user's (A), axiom review pending). `readMembersFromBackend`
(`server/storage/schema/membership.go:91-123`) makes both maps and writes them only in the
`UnsafeForEach` callbacks over the `members` and `members_removed` buckets, so over buckets with no
keys (or absent ones, which read empty) it returns two empty maps and no error. What makes a fresh
backend's first boot `AddNode` validate (`ccValidOn_boot`). -/
axiom membership.membersOfBk_empty [GooseExts] (bm br : Option backend.BktData)
    (hm : bm.getD ∅ = ∅) (hr : br.getD ∅ = ∅) :
    membership.membersOf bm br = (∅, ∅)

/-- **Buckets the apply thread wrote decode to the members it wrote** (2026-11-04, the restart
plan's R2b-3d gap 3, the user's approval; a trust-boundary axiom on the opaque `membersOf`).
Suppose the `members` bucket's entries are exactly some members' records under their own ids
(`memberKey mm.id ↦ memberEnc mm`, ids distinct), and the `members_removed` bucket's keys are exactly
the ids `rs`'s keys. Then the members read are those members' peer URLs by id, and the removed are
`rs`. `readMembersFromBackend` (`server/storage/schema/membership.go:91-123`) keys each member by
`mustParseMemberIDFromBytes` of its key, which is `types.IDFromString` of `BackendMemberKey`'s hex,
so the id back. Each value is `json.Unmarshal`led into a `Member`, which inverts `json.Marshal` of a
non-nil `*Member`, so the member back, provided its strings are valid UTF-8 (`hu`): `json.Marshal`
coerces invalid UTF-8 to U+FFFD, so a peer URL that is not valid reads back changed
(`notes/axiom-review/members-decode.md`, the review's refutation of the draft without `hu`). Each
removed key gives `removed[id] = true`. -/
axiom membership.membersOf_decode [GooseExts] (bm br : Option backend.BktData)
    (ms : List apply.MemberM) (rs : List w64)
    (hm : ∀ k v, (bm.getD ∅).lookup k = some v ↔
      ∃ mm ∈ ms, k = apply.memberKey mm.id ∧ v = apply.memberEnc mm)
    (hnd : (ms.map (·.id)).Nodup) (hu : ∀ mm ∈ ms, ∀ u ∈ mm.peerURLs, utf8Valid u)
    (hr : ∀ k, ((br.getD ∅).lookup k).isSome = true ↔ ∃ id ∈ rs, k = apply.memberKey id) :
    (∀ id, (membership.membersOf bm br).1 !! id = (ms.find? (·.id = id)).map (·.peerURLs)) ∧
    (∀ id, (membership.membersOf bm br).2 !! id = if id ∈ rs then some true else none)

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

/-- **The buckets of the rest resource's part in the mode `M`** (the auth-on snapshot plan's Prove
step, P5, 2026-11-03; the Freeze's "`srvRestOwn` mode-indexed"): the tracked buckets not the
cluster's; in `on` also not the auth store's, whose write authority and contents are the auth
realization's (the history's last state, `authHistTie`), not the rest model's (which keeps them at
`authBoot`). -/
def restSet [GooseExts] (M : auth.AuthMode) (n : GoString) : Prop :=
  match M with
  | .on _ => ¬ membership.clusterBkts n ∧ ¬ auth.authBkts n
  | _ => ¬ membership.clusterBkts n

/-- **The apply thread's share of a server backend's open token, by the mode** (the auth-on
snapshot plan's decision 5; review R1's F1, R2's N1; P5, 2026-11-03): a quarter in `on`, the auth
realization keeping the other quarter of the constructors' half (`authOpenQ`); the half otherwise. -/
def srvOpenQ (M : auth.AuthMode) : Qp :=
  match M with
  | .on _ => (1 : Qp).half.half
  | _ => (1 : Qp).half

theorem srvOpenQ_off : srvOpenQ .off = (1 : Qp).half := rfl

theorem restSet_off [GooseExts] : restSet .off = fun n => ¬ membership.clusterBkts n := rfl

theorem restSet_ncl [GooseExts] (M : auth.AuthMode) (n : GoString) (h : restSet M n) :
    ¬ membership.clusterBkts n := by
  cases M <;> simp only [restSet] at h <;> first | exact h | exact h.1

/-- The rest part's buckets include every tracked bucket neither the cluster's nor the auth
store's (the lessor's, the alarm store's, ...). -/
theorem restSet_of [GooseExts] (M : auth.AuthMode) (n : GoString) (hc : ¬ membership.clusterBkts n)
    (ha : ¬ auth.authBkts n) : restSet M n := by
  cases M <;> simp only [restSet] <;> first | exact hc | exact ⟨hc, ha⟩

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

/-- (Sweep repairs 1, S4) **A committed entry's cluster requests are ones `Recover` accepts**: a
normal entry with data decodes, if at all, to a request whose cluster version, if set, parses and is
not above the server's (`semverValid`, `semverAtMostServer`: `Recover`'s `MustDetectDowngrade`
panics above it; `restAfter` stores any set `clusterVersionSet`), and which is no
`DowngradeInfoSet` (no downgrade record is stored). -/
def clusterVerEntryOk [GooseExts] (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    (∀ v, rq.clusterVersionSet = some v → apply.semverValid v ∧ apply.semverAtMostServer v) ∧
    apply.dispatchKind rq ≠ .downgradeInfoSet

/-- (Sweep repairs 1, S4; `notes/axiom-review/membership-alarm.md`, attack 8) **Every committed
entry's cluster requests are ones `Recover` accepts** (`clusterVerEntryOk`). The KV invariant's
workload fact gives it of a committed log (`kv_log_verOk`, `kv_log_verOkOn`: `logShape`'s `rqOk`,
which the monitors' proposals meet, `monitorReq`). -/
def clusterVerLogOk [GooseExts] (L : List EntryModel) : Prop := ∀ m ∈ L, clusterVerEntryOk m

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
  unfold membership.ccValidOn membership.membersOfBk
  rw [membership.membersOfBk_empty _ _ (by simp [restBootBk, GMap.lookup_insert_ne, GMap.lookup_insert])
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

/-- **The voters are members of the rest state** at the applied log `A` (`srvMemOk`'s converse;
the cluster-rows stage, 2026-11-02). -/
def srvMemCover (γs : ServerRaftNames) (c0 : w64) (A : List EntryModel) : Prop :=
  ∀ k, k ∈ γs.raft.cfg → ((restModel c0 γs.raft.boot (γs.pre ++ A)).mem !! k).isSome = true

/-- **The glue at `applyEntryNormal`'s call of `apply.Apply`**: the next entry's request, of a
committed log whose attribute requests name voters (`attrEntryOk`, `entryWaitOk`'s), meets the
rest state's premise at the applied log `A`, whose members include the voters (`srvMemCover`,
`srvApRes`'s `srvMemOk`). -/
theorem restReqOk_of_attr (γs : ServerRaftNames) (c0 : w64) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (hmc : srvMemCover γs c0 A) (ha : attrEntryOk γs.raft.cfg m)
    (ht : m.typ = W32 0) (hne : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq) :
    apply.restReqOk rq (restModel c0 γs.raft.boot (γs.pre ++ A)) := by
  intro hk a ha'
  exact hmc _ ((ha ht hne rq hdec hk).2 a ha')

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
them, `restModel_present`). Until 2026-11-01 the whole writer's half `rbOwn γB r.bk`. Indexed by
the auth mode `M` since the auth-on snapshot plan's P5 (2026-11-03): the part is over `restSet M`,
which in `on` leaves out the auth store's buckets. -/
def srvRestOwn (M : auth.AuthMode) (γB : backend.BNames) (c : Loc) (r : apply.RestM) : IProp GF :=
  iprop(backend.rbOwnIn γB membership.clusterBkts r.bk ∗
    backend.rbPart γB (restSet M) r.bk ∗ membership.clusterMem c r.mem ∗
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
def srvRestOwnH (M : auth.AuthMode) (γB : backend.BNames) (c : Loc) (H : IProp GF)
    (r : apply.RestM) : IProp GF :=
  iprop(srvRestOwn M γB c r ∗ H)

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

/-- **The server may grant every lease** (the lease-grant stage, 2.9, S2; persistent): every id is
one its lessor may grant (`leaseGranted`). What `srvRest`'s leased arm carries to `applyEntryNormal`
(`grantPermRq`). True of a server whose cluster grants leases (its guard holds of every id). (The
lease-expiry plan's X2, 2026-11-04: until then also the lessor monotone, `lessorModeIs … true`,
false in the revocable mode.) (X7, 2026-11-04) And the lessor's mode at the environment's lease mode
(`lessorModeIs … (decide (E.lm = .mono))`, `srvSnapRO`'s): revocable at `E.lm = .revocable`, what
`applyEntryNormal` hands a revocation (`revokeOwn`). -/
def srvGrantable (E : apply.AEnv GF) : IProp GF :=
  iprop(□ (∀ id : w64, lease.leaseGranted (mvcc.api.mvccLeases E.γ) id) ∗
    lease.lessorModeIs (mvcc.api.mvccLeases E.γ) (decide (E.lm = .mono)))

instance srvGrantable_persistent (E : apply.AEnv GF) : Persistent (srvGrantable (GF := GF) E) := by
  unfold srvGrantable; infer_instance

/-- **The revocable-mode grant ids of the applied log's entries with data** (E3 (c)): the apply
thread applies no entry without data, so these are the ids it can have granted. -/
def srvGrantLog (A : List EntryModel) : List w64 :=
  logRevGrantIds .revocable (A.filter fun m => decide (m.data ≠ []))

theorem srvGrantLog_snoc_sub (A : List EntryModel) (m : EntryModel) (u : w64)
    (h : u ∈ srvGrantLog A) : u ∈ srvGrantLog (A ++ [m]) := by
  unfold srvGrantLog at h ⊢
  rw [List.filter_append]
  unfold logRevGrantIds at h ⊢
  rw [List.filterMap_append]
  exact List.mem_append_left _ h

theorem srvGrantLog_snoc_data (A : List EntryModel) (m : EntryModel) (hd : m.data ≠ []) :
    srvGrantLog (A ++ [m]) = srvGrantLog A ++ (entryRevGrantId .revocable m).toList := by
  unfold srvGrantLog
  rw [List.filter_append]
  have h1 : [m].filter (fun m => decide (m.data ≠ [])) = [m] := by simp [hd]
  rw [h1]
  exact logRevGrantIds_snoc _ _ _

/-- **The ids the lessor ever had, `U`, at the applied log `A`** (the lease-expiry plan's E3 (c),
2026-11-05): none in a cluster that grants none; in the revocable mode, each the revocable-mode grant
id of an entry of `A` with data (`srvGrantLog`), so that a grant's id, distinct from the log's earlier ones,
is new to `U`. -/
def srvEverOk (E : apply.AEnv GF) (A : List EntryModel) (U : List w64) : Prop :=
  (E.lg = false → U = []) ∧ (E.lm = .revocable → ∀ u ∈ U, u ∈ srvGrantLog A)

/-- **The apply thread's half of the ids the lessor ever had** (E3 (c)): `apply.everOwn` at some
`U` good for `A` (`srvEverOk`). -/
def srvEver (E : apply.AEnv GF) (A : List EntryModel) : IProp GF :=
  iprop(∃ U : List w64, apply.everOwn E U ∗ ⌜srvEverOk E A U⌝)

/-- **The requests of the table `T`'s leases** (the lease-expiry plan's S2–S4, F7, DRAFT
2026-11-05; persistent): every lease of the table was requested at the table's TTL
(`lease.leaseReqIs`), as `Grant` issued it (`grantAnswer`'s). What a snapshot's `Recover` needs of
a record whose id the lessor had before (its request premise). -/
def srvReqs (E : apply.AEnv GF) (T : LeaseTable) : IProp GF :=
  iprop(□ ∀ p : w64 × w64, ⌜p ∈ T⌝ -∗ lease.leaseReqIs (mvcc.api.mvccLeases E.γ) p.1 p.2)

instance srvReqs_persistent (E : apply.AEnv GF) (T : LeaseTable) :
    Persistent (srvReqs (GF := GF) E T) := by
  unfold srvReqs; infer_instance

open Iris.ProofMode in
/-- A smaller table's requests. -/
theorem srvReqs_sub (E : apply.AEnv GF) (T T' : LeaseTable) (h : ∀ p ∈ T', p ∈ T) :
    srvReqs (GF := GF) E T ⊢ srvReqs E T' := by
  unfold srvReqs
  iintro #H !> %p %hp
  iapply H; ipureintro; exact h p hp

open Iris.ProofMode in
/-- The empty table's. -/
theorem srvReqs_nil (E : apply.AEnv GF) : ⊢ srvReqs (GF := GF) E [] := by
  unfold srvReqs
  iintro !> %p %hp
  exact absurd hp List.not_mem_nil

/-- `srvReqs` in a cluster that grants leases, `True` otherwise (persistent). -/
def srvReqsIf (E : apply.AEnv GF) (T : LeaseTable) : IProp GF :=
  if E.lg then srvReqs E T else iprop(True)

instance srvReqsIf_persistent (E : apply.AEnv GF) (T : LeaseTable) :
    Persistent (srvReqsIf (GF := GF) E T) := by
  unfold srvReqsIf; split <;> infer_instance

/-- **The rest buckets at a table `T` and an image `r`** (internal: the laws' common form). (The
lease-expiry plan's S2–S4, Q-S6 (A-ii), 2026-11-05) The records' TTLs `f` at least the table's
requests (`leaseTTLsGeReq`); (F7, DRAFT 2026-11-05) the requests themselves (`srvReqs`). -/
def srvRestAt (E : apply.AEnv GF) (T : LeaseTable) (r : apply.RestM) : IProp GF :=
  if E.lg then
    iprop((∃ f : w64 → w64, ⌜leaseTTLsGeReq T f⌝ ∗ E.RO (apply.restLeasesWith f T.ids r)) ∗
      apply.ltHalf E T.ids ∗ srvGrantable E ∗ srvReqs E T)
  else E.RO r

/-- **The apply thread's rest buckets at the applied log `A`** (`AEnv.RO` at `restModel` of the
log through `A`, from the start's consistent index and the boot log). (The lease-grant stage, 2.9,
2026-11-03) In a cluster that grants leases (`E.lg`), with the record of every lease of the applied
table (`appliedTable`), at some TTLs (`∃ f`, B1; since S2–S4, Q-S6 (A-ii), at least the
table's requests), the apply thread's half of the lessor's live set
at those ids (`ltHalf`) and `srvGrantable`; at `E.lg = false` what it was (`srvRest_false`). (The
lease-expiry plan's E3 (c), 2026-11-05) In a cluster that grants leases, also the apply thread's
half of the ids the lessor ever had (`srvEver`). -/
def srvRest (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) : IProp GF :=
  if E.lg then
    iprop(srvRestAt E (appliedTable γr A) (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) ∗
      srvEver E A)
  else E.RO (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))

/-- In a cluster that grants none, what it was. -/
theorem srvRest_false (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (h : E.lg = false) :
    srvRest E γr A = E.RO (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) := by
  unfold srvRest; rw [h]; rfl

open Iris.ProofMode in
/-- **The receive side's refutation of the leased arm** (2.9, S-A; the lease-expiry plan's X2,
2026-11-04, mode-generic): a revocable lessor (`applySnapshot`'s pre) whose mode is `decide (m =
mono)` (`lease.srvInv`'s, `srvSnapRO`'s) at a mode `m` other than `revocable` whose grant flag is
the environment's: so `m = none`, the cluster grants none, and the image is what it was. (Until then
`srvGrantable` carried the monotone mode, which refuted a revocable lessor in any granting cluster;
the revocable mode's granting cluster is restored from a snapshot only from S4 on.) -/
theorem srvRest_revocable [go_etcd_io.etcd.server.v3.lease.Assumptions] (E : apply.AEnv GF)
    (γr : ReadNames) (A : List EntryModel) (m : lease.Mode) (hm : m ≠ .revocable)
    (hlg : E.lg = decide (m ≠ .none)) :
    lease.lessorModeIs (mvcc.api.mvccLeases E.γ) (decide (m = .mono)) ∗ lease.lessorRevocable (mvcc.api.mvccLeases E.γ) ∗
      srvRest E γr A ⊢
      ⌜E.lg = false⌝ ∗ E.RO (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) := by
  cases m with
  | none =>
    have h : E.lg = false := by simpa using hlg
    rw [srvRest_false E γr A h]
    iintro ⟨-, -, H⟩; iframe H; ipureintro; exact h
  | mono =>
    iintro ⟨#Hm, #Hrv, -⟩
    ihave %Hab := lease.lessorModeIs_agree (mvcc.api.mvccLeases E.γ) false (decide (lease.Mode.mono = .mono))
      $$ [$Hrv $Hm]
    simp at Hab
  | revocable => exact absurd rfl hm

open Iris.ProofMode in
/-- In a cluster that grants none, the ids are none. -/
theorem srvEver_false (E : apply.AEnv GF) (A : List EntryModel) (h : E.lg = false) :
    ⊢ srvEver (GF := GF) E A := by
  iunfold srvEver
  iexists []
  rw [apply.everOwn_false E [] h]
  isplitl
  · itrivial
  ipureintro; exact ⟨fun _ => rfl, fun _ u hu => absurd hu List.not_mem_nil⟩

open Iris.ProofMode in
/-- **`srvRest` at the table and the image, with the ids** (at any `E.lg`). -/
theorem srvRest_eq_at (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) :
    srvRest E γr A ⊣⊢ srvRestAt E (appliedTable γr A)
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) ∗ srvEver E A := by
  unfold srvRest
  cases h : E.lg
  · have hat : srvRestAt E (appliedTable γr A)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) =
        E.RO (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) := by
      unfold srvRestAt; rw [h]; rfl
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hat]
    constructor
    · iintro H; iframe H; iapply srvEver_false E A h
    · iintro ⟨H, -⟩; iexact H
  · simp only [↓reduceIte]
    exact .rfl

/-- **The ids one entry later** (the log only grows: `srvGrantLog_snoc_sub`). -/
theorem srvEverOk_snoc (E : apply.AEnv GF) (A : List EntryModel) (m : EntryModel) (U : List w64)
    (h : srvEverOk E A U) : srvEverOk E (A ++ [m]) U :=
  ⟨h.1, fun hm u hu => srvGrantLog_snoc_sub A m u (h.2 hm u hu)⟩

open Iris.ProofMode in
theorem srvEver_snoc (E : apply.AEnv GF) (A : List EntryModel) (m : EntryModel) :
    srvEver (GF := GF) E A ⊢ srvEver E (A ++ [m]) := by
  iunfold srvEver
  iintro ⟨%U, HU, %Hok⟩
  iexists U
  iframe HU
  ipureintro; exact srvEverOk_snoc E A m U Hok

/-- The ids after `grantIdsA`: those before, and a grant's own. -/
theorem grantIdsA_sub (rq : apply.IRRModel) (v3 : Bool) (out : apply.ApplyOut) (L : List w64)
    (u : w64) (hu : u ∈ apply.grantIdsA rq v3 out L) :
    u ∈ L ∨ (apply.dispatchKind rq = .leaseGrant ∧ ∃ g, rq.leaseGrant = some g ∧ u = g.id) := by
  by_cases hk : apply.dispatchKind rq = .leaseGrant
  · cases hgl : rq.leaseGrant with
    | none => rw [apply.grantIdsA_none _ _ _ _ hgl] at hu; exact .inl hu
    | some g =>
      cases out with
      | skipped => exact .inl hu
      | rejected => exact .inl hu
      | dispatched o sk =>
        simp only [apply.grantIdsA, apply.grantIds, hgl] at hu
        split at hu
        · cases o with
          | rejected e => exact .inl hu
          | applied l ns =>
            rcases List.mem_append.1 hu with hu | hu
            · exact .inl hu
            · exact .inr ⟨hk, g, rfl, List.mem_singleton.1 hu⟩
        · exact .inl hu
  · rw [apply.grantIdsA_nonGrant _ _ _ _ hk] at hu; exact .inl hu

/-- **The ids after a request's grant** (`grantIdsA`): an applied grant's id is the entry's
revocable-mode grant id; a grant only where the cluster grants. -/
theorem srvEverOk_grant (E : apply.AEnv GF) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (out : apply.ApplyOut) (U : List w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hlg : apply.dispatchKind rq = .leaseGrant → E.lg = true)
    (h : srvEverOk E A U) : srvEverOk E (A ++ [m]) (apply.grantIdsA rq v3 out U) := by
  refine ⟨fun hf => ?_, fun hm u hu => ?_⟩
  · have hU := h.1 hf
    subst hU
    apply List.eq_nil_iff_forall_not_mem.2
    intro u hu
    rcases grantIdsA_sub rq v3 out [] u hu with hu | ⟨hk, -⟩
    · exact absurd hu List.not_mem_nil
    · rw [hlg hk] at hf; cases hf
  · rw [srvGrantLog_snoc_data A m hd]
    rcases grantIdsA_sub rq v3 out U u hu with hu | ⟨hk, g, hg, rfl⟩
    · exact List.mem_append_left _ (h.2 hm u hu)
    · apply List.mem_append_right
      have he : entryRevGrantId .revocable m = some g.id := by
        unfold entryRevGrantId rqRevGrantId
        rw [if_pos ht, hdec]
        simp [hk, hg]
      rw [he]; simp


/-- The ids the image holds records of: the table's in a cluster that grants leases, none
otherwise. -/
def srvIds (E : apply.AEnv GF) (T : List w64) : List w64 := if E.lg then T else []

/-- `srvGrantable` in a cluster that grants leases, `True` otherwise (persistent). -/
def srvGrantIf (E : apply.AEnv GF) : IProp GF := if E.lg then srvGrantable E else iprop(True)

instance srvGrantIf_persistent (E : apply.AEnv GF) : Persistent (srvGrantIf (GF := GF) E) := by
  unfold srvGrantIf; split <;> infer_instance

open Iris.ProofMode in
/-- **`srvRestAt` opened, at any `E.lg`**: the image of `srvIds` at some `f` (at least the table's
requests where the cluster grants), its half, the permits. -/
theorem srvRestAt_open (E : apply.AEnv GF) (T : LeaseTable) (r : apply.RestM) :
    srvRestAt E T r ⊣⊢ ∃ f : w64 → w64, ⌜E.lg = true → leaseTTLsGeReq T f⌝ ∗
      E.RO (apply.restLeasesWith f (srvIds E T.ids) r) ∗
      apply.ltHalf E (srvIds E T.ids) ∗ srvGrantIf E ∗ srvReqsIf E T := by
  unfold srvRestAt srvIds srvGrantIf srvReqsIf
  cases h : E.lg
  · simp only [Bool.false_eq_true, ↓reduceIte, apply.restLeasesWith_nil, apply.ltHalf, h]
    constructor
    · iintro H; iexists (fun _ => W64 0); iframe H
      isplitr
      · ipureintro; intro h'; cases h'
      isplitl <;> (try isplitl) <;> itrivial
    · iintro ⟨%_, -, H, -, -⟩; iexact H
  · simp only [↓reduceIte]
    constructor
    · iintro ⟨⟨%f, %Hf, H⟩, HL, #HG, #HQ⟩; iexists f; iframe H HL HG HQ; ipureintro; exact fun _ => Hf
    · iintro ⟨%f, %Hf, H, HL, #HG, #HQ⟩; iframe HL HG HQ; iexists f; iframe H; ipureintro; exact Hf trivial

open Iris.ProofMode in
/-- **The image through a writer that commutes with the lease records** (`g`: a conf change's
`ccRest`, a request's `restAfter`): open the image at some `r'`, close it at `g r'`. -/
theorem srvRestAt_map (E : apply.AEnv GF) (T : LeaseTable) (r : apply.RestM)
    (g : apply.RestM → apply.RestM)
    (hg : ∀ id t r, g (apply.restGrantT id t r) = apply.restGrantT id t (g r)) :
    srvRestAt E T r ⊢ ∃ r' : apply.RestM, E.RO r' ∗ (E.RO (g r') -∗ srvRestAt E T (g r)) := by
  iintro H
  ihave ⟨%f, %Hf, HR, HL, #HG, #HQ⟩ := (srvRestAt_open E T r).1 $$ H
  iexists _
  iframe HR
  iintro HR
  iapply (srvRestAt_open E T (g r)).2
  iexists f
  iframe HL HG HQ
  isplitr
  · ipureintro; exact Hf
  rw [← apply.restLeasesWith_comm g hg]
  iexact HR

open Iris.ProofMode in
/-- **Its permits give a request's** (`grantPermRq`): a grant only where the cluster grants. -/
theorem srvGrantIf_perm [go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions] (E : apply.AEnv GF) (rq : apply.IRRModel)
    (h : apply.dispatchKind rq = .leaseGrant → E.lg = true) :
    srvGrantIf E ⊢ apply.grantPermRq E rq := by
  by_cases hk : apply.dispatchKind rq = .leaseGrant
  · unfold srvGrantIf; rw [h hk]; simp only [↓reduceIte]
    iintro #HG
    iunfold srvGrantable at HG
    icases HG with ⟨#HG, -⟩
    iunfold apply.grantPermRq
    iintro !> %_ %g %_
    iapply HG
  · iintro -; iapply (apply.grantPermRq_of_not_grant E rq hk)

/-- **`srvRest` opened, at any `E.lg`** (`srvRestAt_open`): what `applyEntryNormal` hands
`apply.Apply` (the image `rs`, the half at `T := srvIds …`, the permits). -/
theorem srvRest_open (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) :
    srvRest E γr A ⊢ ∃ f : w64 → w64, ⌜E.lg = true → leaseTTLsGeReq (appliedTable γr A) f⌝ ∗
      E.RO (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) ∗
      apply.ltHalf E (srvIds E (appliedTable γr A).ids) ∗ srvGrantIf E ∗
      srvReqsIf E (appliedTable γr A) ∗ srvEver E A := by
  iintro H
  ihave ⟨H, HU⟩ := (srvRest_eq_at E γr A).1 $$ H
  ihave ⟨%f, %Hf, H1, H2, H3, H4⟩ := (srvRestAt_open E _ _).1 $$ H
  iexists f
  iframe H1 H2 H3 H4 HU
  ipureintro; exact Hf

open Iris.ProofMode in
/-- **`srvRest` closed again** (`srvRest_open`'s converse). -/
theorem srvRest_close (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) :
    (∃ f : w64 → w64, ⌜E.lg = true → leaseTTLsGeReq (appliedTable γr A) f⌝ ∗
      E.RO (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) ∗
      apply.ltHalf E (srvIds E (appliedTable γr A).ids) ∗ srvGrantIf E ∗
      srvReqsIf E (appliedTable γr A) ∗ srvEver E A) ⊢
      srvRest E γr A := by
  iintro ⟨%f, %Hf, H1, H2, H3, H4, HU⟩
  iapply (srvRest_eq_at E γr A).2
  iframe HU
  iapply (srvRestAt_open E _ _).2
  iexists f
  iframe H1 H2 H3 H4
  ipureintro; exact Hf

open Iris.ProofMode in
/-- **The ids opened** (`srvEver`): the apply thread's half at some `U` good for `A`. -/
theorem srvEver_open (E : apply.AEnv GF) (A : List EntryModel) :
    srvEver (GF := GF) E A ⊢ ∃ U : List w64, apply.everOwn E U ∗ ⌜srvEverOk E A U⌝ := by
  iunfold srvEver; iintro H; iexact H

open Iris.ProofMode in
/-- **The ids closed again, one entry later, after a request** (`grantIdsA`). -/
theorem srvEver_grant (E : apply.AEnv GF) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (out : apply.ApplyOut) (U : List w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hlg : apply.dispatchKind rq = .leaseGrant → E.lg = true) (h : srvEverOk E A U) :
    apply.everOwn (GF := GF) E (apply.grantIdsA rq v3 out U) ⊢ srvEver E (A ++ [m]) := by
  iintro HU
  iunfold srvEver
  iexists _
  iframe HU
  ipureintro; exact srvEverOk_grant E A m rq v3 out U ht hd hdec hlg h

open Iris.ProofMode in
/-- **A grant's id is new to the lessor** (`apply.grantFresh`, E3 (c)): in the monotone mode the
lessor's mode (`srvGrantIf`'s `lessorModeIs true`); in the revocable mode the id is new to `U`, whose
ids are the applied log's grant ids (`srvEverOk`), which the id is not (`hfr`); no grant otherwise. -/
theorem srvGrantFresh (E : apply.AEnv GF) (A : List EntryModel) (U : List w64) (rq : apply.IRRModel)
    (h : srvEverOk E A U) (hlg : apply.dispatchKind rq = .leaseGrant → E.lg = true)
    (hfr : E.lm = .revocable → apply.dispatchKind rq = .leaseGrant →
      ∀ g : apply.LeaseGrantModel, rq.leaseGrant = some g → g.id ∉ srvGrantLog A) :
    srvGrantIf E ⊢ apply.grantFresh E rq U := by
  unfold srvGrantIf srvGrantable
  iintro #HG
  iunfold apply.grantFresh
  iintro !> %hk %g %hg
  have hl := hlg hk
  irevert HG
  simp only [hl, ↓reduceIte]
  iintro ⟨-, #Hm⟩
  cases hm : E.lm with
  | none => exact absurd hm (apply.AEnv.lm_of_lg_true hl)
  | mono =>
    ileft
    irevert Hm
    simp only [hm, decide_true]
    iintro #Hm
    iexact Hm
  | revocable =>
    iright
    ipureintro
    intro hu
    exact hfr hm hk g hg (h.2 hm g.id hu)

open Iris.ProofMode in
/-- **The ids closed again, one entry later, unchanged.** -/
theorem srvEver_same (E : apply.AEnv GF) (A : List EntryModel) (m : EntryModel) (U : List w64)
    (h : srvEverOk E A U) :
    apply.everOwn (GF := GF) E U ⊢ srvEver E (A ++ [m]) := by
  iintro HU
  iunfold srvEver
  iexists _
  iframe HU
  ipureintro; exact srvEverOk_snoc E A m U h

open Iris.ProofMode in
/-- **The rest buckets at the start** (`NewServer`, 2.13): with an empty prefix the table is empty,
so the image is the boot's, at any TTLs; (E3 (c)) the lessor has had no lease. -/
theorem srvRest_init (E : apply.AEnv GF) (γr : ReadNames) (h : γr.raft.pre = []) :
    E.RO (restModel γr.kv.c0 γr.raft.raft.boot []) ∗ apply.ltHalf E [] ∗ srvGrantIf E ∗
      apply.everOwn E [] ⊢ srvRest E γr [] := by
  have hT : srvIds E (appliedTable γr []).ids = [] := by
    unfold srvIds appliedTable; rw [h]; split <;> rfl
  have hT0 : (appliedTable γr []).ids = [] := by unfold appliedTable; rw [h]; rfl
  have hTn : appliedTable γr [] = [] := by unfold appliedTable; rw [h]; rfl
  iintro ⟨HR, HL, HG, HU⟩
  iapply srvRest_close
  rw [hT, h, List.append_nil]
  iexists (fun _ => W64 0)
  rw [apply.restLeasesWith_nil]
  iframe HR HL HG
  isplitr
  · ipureintro; exact fun _ => leaseTTLsGeReq_of_ids_nil hT0 _
  isplitr
  · rw [hTn]; unfold srvReqsIf; split
    · iapply srvReqs_nil
    · itrivial
  iunfold srvEver
  iexists []
  iframe HU
  ipureintro; exact ⟨fun _ => rfl, fun _ u hu => absurd hu List.not_mem_nil⟩

open Iris.ProofMode in
/-- **The rest buckets one entry later**, of an entry that leaves the lease table (`restEntry`). -/
theorem srvRest_snoc (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (hT : appliedTable γr (A ++ [m]) = appliedTable γr A) :
    srvRestAt E (appliedTable γr A)
        (restEntry γr.kv.c0 m (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) ∗
      srvEver E A ⊢ srvRest E γr (A ++ [m]) := by
  iintro ⟨H, HU⟩
  iapply (srvRest_eq_at E γr (A ++ [m])).2
  rw [hT, ← List.append_assoc, restModel_append]
  iframe H
  iapply srvEver_snoc $$ HU

open Iris.ProofMode in
/-- An entry with no data leaves them. -/
theorem srvRest_nodata (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (ht : m.typ = W32 0) (hd : m.data = []) : srvRest E γr A ⊢ srvRest E γr (A ++ [m]) := by
  iintro H
  ihave ⟨H, HU⟩ := (srvRest_eq_at E γr A).1 $$ H
  iapply srvRest_snoc E γr A m (appliedTable_nodata γr A m ht hd)
  rw [restEntry_nodata _ _ _ ht hd]
  iframe H HU

/-- **An applied grant's request** (the lease-expiry plan's S2–S4, F7, DRAFT 2026-11-05;
persistent): if `Apply` applied `rq` as the grant `g` (dispatched with `v3`), the lease's request
at the grant's TTL (`lease.leaseReqIs`, `grantAnswer`'s; `grantReqA_of_res`). -/
def grantReqA (E : apply.AEnv GF) (rq : apply.IRRModel) (v3 : Bool) (out : apply.ApplyOut) :
    IProp GF :=
  iprop(□ ∀ g : apply.LeaseGrantModel, ⌜apply.dispatchKind rq = .leaseGrant ∧ v3 = true ∧
    rq.leaseGrant = some g ∧ ∃ o sk l ns, out = .dispatched o sk ∧ o = .applied l ns⌝ -∗
    lease.leaseReqIs (mvcc.api.mvccLeases E.γ) g.id g.ttl)

instance grantReqA_persistent (E : apply.AEnv GF) (rq : apply.IRRModel) (v3 : Bool)
    (out : apply.ApplyOut) : Persistent (grantReqA (GF := GF) E rq v3 out) := by
  unfold grantReqA; infer_instance

open Iris.ProofMode in
/-- No applied grant, no request needed. -/
theorem grantReqA_vac (E : apply.AEnv GF) (rq : apply.IRRModel) (v3 : Bool) (out : apply.ApplyOut)
    (h : ∀ g : apply.LeaseGrantModel, ¬ (apply.dispatchKind rq = .leaseGrant ∧ v3 = true ∧
      rq.leaseGrant = some g ∧ ∃ o sk l ns, out = .dispatched o sk ∧ o = .applied l ns)) :
    ⊢ grantReqA (GF := GF) E rq v3 out := by
  unfold grantReqA
  iintro !> %g %hg
  exact absurd hg (h g)

theorem grantReqA_nonGrant (E : apply.AEnv GF) (rq : apply.IRRModel) (v3 : Bool)
    (out : apply.ApplyOut) (hk : apply.dispatchKind rq ≠ .leaseGrant) :
    ⊢ grantReqA (GF := GF) E rq v3 out :=
  grantReqA_vac E rq v3 out (fun _ h => hk h.1)

theorem grantReqA_noV3 (E : apply.AEnv GF) (rq : apply.IRRModel) (out : apply.ApplyOut) :
    ⊢ grantReqA (GF := GF) E rq false out :=
  grantReqA_vac E rq false out (fun _ h => Bool.false_ne_true h.2.1)

open Iris.ProofMode in
/-- **The requests one request later** (F7): the table `dispatch` leaves, of a request that
revokes nothing, holds the old table's leases and an applied grant's (`dispatchTableA_mem`). -/
theorem srvReqs_dispatchA (E : apply.AEnv GF) (rq : apply.IRRModel) (v3 : Bool)
    (x x' : apply.ApplyKV) (out : apply.ApplyOut) (lt : LeaseTable)
    (hr : apply.dispatchKind rq ≠ .leaseRevoke)
    (hg : apply.dispatchKind rq = .leaseGrant → apply.grantKindOk rq)
    (hs : apply.applyStep rq v3 x x' out) (hgo : apply.grantOutOkA x.chain rq v3 lt.ids out) :
    srvReqs (GF := GF) E lt ∗ grantReqA E rq v3 out ⊢
      srvReqs E (dispatchTable x.chain rq v3 lt) := by
  unfold srvReqs grantReqA
  iintro ⟨#H, #G⟩ !> %p %hp
  rcases dispatchTableA_mem rq v3 x x' out lt hr hg hs hgo p hp with h | ⟨hk, hv, g, hgl, rfl, ho⟩
  · iapply H; ipureintro; exact h
  · iapply G; ipureintro; exact ⟨hk, hv, hgl, ho⟩

open Iris.ProofMode in
/-- **The rest buckets one entry later, after `apply.Apply`** (the lease-grant stage, 2.9;
generic in `E.lg`, so the auth-on arm uses it too, m5): from `Apply`'s post at the image `rs` of
`srvRestAt_open` (the half, the record at its TTL `t`, the outcome's verdict `grantOutOkA`), a
request that revokes nothing and, if a grant, one the cluster admits (`grantPropOk`), whose rest
effect is `restAfter`'s. -/
theorem srvRest_applyG (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) (f : w64 → w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)) (hch : x.chain = γr.kv.ch0)
    (hrev : apply.dispatchKind rq ≠ .leaseRevoke)
    (hg : apply.dispatchKind rq = .leaseGrant → grantPropOk E.lm rq)
    (hr : ∀ r, apply.restOut rq v3 out r = apply.restAfter rq v3 r)
    (hs : apply.applyStep rq v3 x x' out)
    (hfb : E.lg = true → leaseTTLsGeReq (appliedTable γr A) f) :
    srvGrantIf E ∗ srvReqsIf E (appliedTable γr A) ∗ grantReqA E rq v3 out ∗
      ⌜apply.grantOutOkA x.chain rq v3 (srvIds E (appliedTable γr A).ids) out⌝ ∗
      apply.ltHalf E (apply.grantIdsA rq v3 out (srvIds E (appliedTable γr A).ids)) ∗
      (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.grantRestA t rq v3 out (apply.restOut rq v3 out
        (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)))))) ∗
      srvEver E (A ++ [m]) ⊢
      srvRest E γr (A ++ [m]) := by
  have hre : restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ (A ++ [m])) =
      apply.restAfter rq v3 (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) := by
    rw [← List.append_assoc, restModel_append, restEntry_normal _ _ rq _ ht hd hdec, ← hv3]
  have hcomm := apply.restLeasesWith_comm (apply.restAfter rq v3)
    (fun id t r => apply.restAfter_restGrantT rq v3 id t r)
  simp only [hr, hcomm]
  iintro ⟨#Hgi, #Hrq, #Hgr, %Hgo, HL, ⟨%t, %Htt, HR⟩, HU⟩
  cases hlg : E.lg
  · have hk : apply.dispatchKind rq ≠ .leaseGrant := fun hk => by
      exact (hg hk).1 (apply.AEnv.lm_of_lg_false hlg)
    rw [srvRest_false E γr _ hlg, hre]
    simp only [srvIds, hlg, Bool.false_eq_true, ↓reduceIte, apply.restLeasesWith_nil,
      apply.grantRestA_nonGrant _ _ _ _ _ hk]
    iexact HR
  · have hgk : apply.dispatchKind rq = .leaseGrant → apply.grantKindOk rq := fun hk => (hg hk).2
    simp only [srvIds, hlg, ↓reduceIte] at Hgo
    simp only [srvIds, hlg, ↓reduceIte]
    obtain ⟨f', hf', hfT, hfN⟩ := apply.grantRestA_leasesF x.chain t rq v3 out f
      (appliedTable γr A).ids
      (apply.restAfter rq v3 (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) Hgo
    have hTt : appliedTable γr (A ++ [m]) = dispatchTable x.chain rq v3 (appliedTable γr A) := by
      rw [appliedTable_snoc]
      unfold kvTable
      rw [if_pos ht, if_neg hd]
      simp only [hdec]
      rw [← hv3, ← hch]
    have hT : apply.grantIdsA rq v3 out (appliedTable γr A).ids = (appliedTable γr (A ++ [m])).ids := by
      rw [hTt]
      exact (dispatchTableA_ids rq v3 x x' out _ hrev hgk hs Hgo).symm
    have hb : leaseTTLsGeReq (appliedTable γr (A ++ [m])) f' := by
      rw [hTt]
      exact dispatchTableA_ttls rq v3 x x' out _ hrev hgk hs Hgo f' t
        (leaseTTLsGeReq_congr (hfb hlg) hfT) Htt hfN
    unfold srvRest srvRestAt srvGrantIf
    irevert Hrq
    unfold srvReqsIf
    simp only [hlg, ↓reduceIte]
    iintro #Hrq
    rw [hf', hT, ← hre]
    iframe HL Hgi HU
    isplitl [HR]
    · iexists f'
      iframe HR
      ipureintro; exact hb
    rw [hTt]
    iapply srvReqs_dispatchA E rq v3 x x' out _ hrev hgk hs Hgo
    iframe Hrq Hgr

end defs

end EtcdGrove
end Perennial
