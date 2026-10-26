/-
**The rest buckets and the cluster's members, as the apply thread writes them** (D22, 2026-10-23:
the backend over every bucket; `notes/decisions.md`, "D22c decided" and "D22 the backend over
every bucket carried out"). Lean-first (no Rocq counterpart).

The backend tracks its rest buckets (`backend.BParams.RB`, `mvcc.restBuckets`: the lessor's, the
alarm store's, the auth store's and the membership's) in a ghost variable whose client half
(`backend.rbOwn`) a put in, delete from, creation or deletion of one needs. The apply thread holds
it with the cluster's in-memory members (`membership.clusterMem`): `RestM`, a pure record, and the
environment's `AEnv.RO` its resource. Of the writers the apply path reaches:

* the cluster's `SetVersion(ver, onSet, v3)` (`ClusterVersionSet`): with `v3`,
  `cluster/clusterVersion := ver.String()` (`schema.MustSaveClusterVersionToBackend`), `ver` the
  version `semver.MustParse` parsed from the request's `Ver` (`semverIs`), so the value is
  `semverNorm Ver` (`restSetVersion`);
* the cluster's `UpdateAttributes(id, attr, v3)` (`ClusterMemberAttrSet`): for a member of the
  in-memory list, its attributes replaced in memory (whatever `v3`) and, with `v3`, the member
  saved (`members/<id> := json(member)`, `MustSaveMemberToBackend`: the **in-memory** member,
  exception 7, which is why the in-memory list is part of the state); for another id nothing
  (a removed member's: a warning; neither: a panic the contract does not model, as before);
* the server's `applyConfChange` (`AddNode`, `membership.ccRest`, server-level).

The writers the workload does not reach (the alarm store's `Activate`/`Deactivate`, the auth
store's writes, the lessor's `Grant`/`Checkpoint`, the cluster's `SetDowngradeInfo`) take the
environment's write right `AEnv.RW` instead, which leaves `RO`'s state alone: the server's is
`False` (their requests are not admitted: `rqOk`).

`memberKey`, `memberEnc` and `semverNorm` are opaque pure functions, each named in one writer's
statement (`schema.BackendMemberKey`'s hex id, `json.Marshal` of a member, `semver.MustParse(v)
.String()`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

/-- **A cluster member, as a value** (`membership.Member`: its id, its `RaftAttributes`' peer
URLs and learner flag, its `Attributes`' name and client URLs): what `json.Unmarshal` of a
member's JSON gives (the members' records and a conf change's context are the members' JSON). -/
structure MemberM where
  id : w64
  peerURLs : List GoString
  isLearner : Bool
  name : GoString
  clientURLs : List GoString
  deriving Inhabited

/-- **The rest buckets and the cluster's in-memory members** (see the file header): each rest
bucket's contents (absent if absent: `backend.rbData`'s value) and the cluster's member list. -/
structure RestM where
  bk : GMap GoString backend.BktData
  mem : GMap w64 MemberM

/-- **`schema.BackendMemberKey(id)`**: a member's key in `members` (its id in hex; opaque). -/
opaque memberKey : w64 → GoString

/-- **`json.Marshal(m)` of a member** (`MustSaveMemberToBackend`'s value; opaque). -/
opaque memberEnc : MemberM → GoString

/-- **`semver.MustParse(v).String()`** (opaque): the cluster version `SetVersion` saves for the
request's version `v` (its `String()` normalizes it). -/
opaque semverNorm : GoString → GoString

/-- The `cluster` bucket's version key (`schema.ClusterClusterVersionKeyName`). -/
def clusterVersionKey [GooseExts] : GoString := go!"clusterVersion"

/-- `n/k := v` in the rest buckets (the bucket created if absent). -/
def RestM.putIn (r : RestM) (n k v : GoString) : RestM :=
  { r with bk := r.bk.insert n (((r.bk.lookup n).getD ∅).insert k v) }

/-- **`SetVersion` of the version `MustParse(s)`** (see the file header). -/
def restSetVersion [GooseExts] (v3 : Bool) (s : GoString) (r : RestM) : RestM :=
  if v3 then r.putIn go!"cluster" clusterVersionKey (semverNorm s) else r

/-- A member with the attributes `a`. -/
def MemberM.withAttrs (m : MemberM) (a : MemberAttrModel) : MemberM :=
  { m with name := a.name, clientURLs := a.clientURLs }

/-- **`UpdateAttributes(a.memberID, a, v3)`** (see the file header). -/
def restUpdateAttrs [GooseExts] (v3 : Bool) (a : MemberAttrModel) (r : RestM) : RestM :=
  match r.mem.lookup a.memberID with
  | none => r
  | some m =>
    let r1 : RestM := { r with mem := r.mem.insert a.memberID (m.withAttrs a) }
    if v3 then r1.putIn go!"members" (memberKey a.memberID) (memberEnc (m.withAttrs a)) else r1

/-- **What `dispatch(rq, v3)` does to the rest buckets and the members** (see the file header):
the cluster version's and the member attributes' requests (`dispatch`'s first two cases, in its
order: `dispatchKind`); nothing else (the writers it does not reach take `AEnv.RW`). -/
def restAfter [GooseExts] (rq : IRRModel) (v3 : Bool) (r : RestM) : RestM :=
  match rq.clusterVersionSet with
  | some v => restSetVersion v3 v r
  | none =>
    match rq.clusterMemberAttrSet with
    | some a => restUpdateAttrs v3 a r
    | none => r

/-- A request of another kind leaves them. -/
theorem restAfter_other [GooseExts] (rq : IRRModel) (v3 : Bool) (r : RestM)
    (h1 : rq.clusterVersionSet = none) (h2 : rq.clusterMemberAttrSet = none) :
    restAfter rq v3 r = r := by
  unfold restAfter; rw [h1, h2]

/-- **A cluster method's request** (`ClusterVersionSet`, `ClusterMemberAttrSet`,
`DowngradeInfoSet`), as a value. -/
inductive ClusterReq where
  | ver (v : GoString)
  | attr (a : MemberAttrModel)
  | dg (d : DowngradeModel)

/-- What a cluster method does to `RestM` (`DowngradeInfoSet` writes through `AEnv.RW`). -/
def ClusterReq.eff [GooseExts] : ClusterReq → Bool → RestM → RestM
  | .ver v, v3, r => restSetVersion v3 v r
  | .attr a, v3, r => restUpdateAttrs v3 a r
  | .dg _, _, r => r

section defs
open Iris Iris.BI
variable {GF : BundledGFunctors}

/-- The opaque core of `semverIs`. -/
opaque semverIsCore (v : Loc) (s : GoString) : IProp GF

/-- **`v` is the version `semver.MustParse(s)` returned** (persistent, opaque core; D22,
2026-10-23): what `MustParse`'s axiom gives of its result, so that the cluster's `SetVersion`
of `v` saves `semverNorm s` (`v.String()`). -/
def semverIs (v : Loc) (s : GoString) : IProp GF := iprop(□ semverIsCore v s)

instance semverIs_persistent (v : Loc) (s : GoString) : Persistent (semverIs (GF := GF) v s) := by
  unfold semverIs; infer_instance

end defs

/-- The method a cluster request is for. -/
def ClusterReq.method [GooseExts] : ClusterReq → GoString
  | .ver _ => go!"ClusterVersionSet"
  | .attr _ => go!"ClusterMemberAttrSet"
  | .dg _ => go!"DowngradeInfoSet"

end apply
end EtcdGrove
end Perennial
