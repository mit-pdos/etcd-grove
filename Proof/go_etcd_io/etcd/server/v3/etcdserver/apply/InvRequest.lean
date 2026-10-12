/-
The raft request as the apply package reads it (`server/v3/etcdserver/apply`): the shared
vocabulary of the package's specs. Lean-first (no Rocq counterpart); plan: `notes/decisions.md`,
"The server's apply: the hook through mvcc, the chain as triples, compaction out of the model".

**The request as a pure value** (`IRRModel`): the request's `ID`, its `Header` (`HeaderModel`:
the fields `authApplierV3.Apply` and `apply.Apply` read), and one field per request of
`InternalRaftRequest` (a protobuf oneof in spirit, a struct of pointers in Go: nothing makes at
most one non-nil; `dispatchKind` is the first set field in `dispatch`'s order). The four KV
requests are the txn package's models (`OpFull` for a range, a put, a delete; `TxnModel`), so the
apply package's statements are in the client model's terms; the others record the fields the
package reads (`dispatch`, the backend's methods, `needAdminPermission`, `noSideEffect`), or only
whether they are set (`Bool`) when the package passes them on unread (to the auth store).

**Decoding** (`irrDecode`, opaque): the request protobuf's decoding of an entry's bytes, as the
names-only `pbutil.MustUnmarshalMessage` computes it, modulo what the model leaves out; `none` for
bytes that do not decode (`MustUnmarshalMessage` panics on them). A decoder, not an encoder (the
plan's `irrEncode`): protobuf encodings are not canonical, and the model forgets the unread
requests' contents, so "the entry's data is the encoding of some model" would fail of real
entries; "the entry's data decodes to some model" does not.

**In the heap** (`internalRaftRequestIs p rq`, persistent): the struct at `p` holds `rq`, every
field read-only (the package only reads them), each set request pointer not nil and holding its
model (`txn.rangeRequestIs`, `putRequestIs`, `deleteRangeRequestIs`, `txnRequestIs` for the KV
four), an unset one nil.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-! ## The request, purely -/

/-- A request's `Header`: what `apply.Apply` (`ID`) and `authApplierV3.Apply` (`Username`,
`AuthRevision`) read. -/
structure HeaderModel where
  id : w64
  username : GoString
  authRevision : w64

/-- An `AlarmRequest`: its `Action` (`GET` 0, `ACTIVATE` 1, `DEACTIVATE` 2), `Alarm` (an
`AlarmType`) and `MemberID`. -/
structure AlarmModel where
  action : w32
  alarm : w32
  memberID : w64

/-- A `LeaseGrantRequest`'s `ID` and `TTL`. -/
structure LeaseGrantModel where
  id : w64
  ttl : w64

/-- A `LeaseCheckpoint`'s `ID` and `Remaining_TTL`. -/
structure CheckpointModel where
  id : w64
  remainingTTL : w64

/-- An `InternalAuthenticateRequest`'s `Name`, `Password` and `SimpleToken`. -/
structure AuthenticateModel where
  name : GoString
  password : GoString
  simpleToken : GoString

/-- A `ClusterMemberAttrSetRequest`'s `Member_ID` and its `MemberAttributes`' `Name` and
`ClientUrls`. -/
structure MemberAttrModel where
  memberID : w64
  name : GoString
  clientURLs : List GoString

/-- A `DowngradeInfoSetRequest`'s `Enabled` and `Ver`. -/
structure DowngradeModel where
  enabled : Bool
  ver : GoString

/-- **An `InternalRaftRequest`**, as the apply package reads it. -/
structure IRRModel where
  id : w64
  header : Option HeaderModel
  range : Option OpFull
  put : Option OpFull
  deleteRange : Option OpFull
  txn : Option TxnModel
  compaction : Option w64
  leaseGrant : Option LeaseGrantModel
  leaseRevoke : Option w64
  alarm : Option AlarmModel
  leaseCheckpoint : Option (List CheckpointModel)
  authEnable : Bool
  authDisable : Bool
  authStatus : Bool
  authenticate : Option AuthenticateModel
  authUserAdd : Bool
  authUserDelete : Bool
  authUserGet : Option GoString
  authUserChangePassword : Bool
  authUserGrantRole : Bool
  authUserRevokeRole : Bool
  authUserList : Bool
  authRoleList : Bool
  authRoleAdd : Bool
  authRoleDelete : Bool
  authRoleGet : Option GoString
  authRoleGrantPermission : Bool
  authRoleRevokePermission : Bool
  clusterVersionSet : Option GoString
  clusterMemberAttrSet : Option MemberAttrModel
  downgradeInfoSet : Option DowngradeModel
  downgradeVersionTest : Bool

/-- **Trust boundary (the encoding).** The request a committed normal entry's bytes decode to
(`pbutil.MustUnmarshalMessage` into an `InternalRaftRequest`, read as `IRRModel`); `none`: they
do not decode (it panics). Opaque, as mvcc's `kvEncode`: only the decoder's axiom
(`Spec/go_etcd_io/etcd/pkg/v3/pbutil/MustUnmarshalMessage.lean`) says anything of it. -/
opaque irrDecode : List w8 → Option IRRModel

/-- **Trust boundary (semver).** Whether a version string parses (`semver.NewVersion` accepts
it): `semver.MustParse` returns a version for it, and panics otherwise (its axiom,
`Spec/github_com/Masterminds/semver/v3/MustParse.lean`). Opaque: the premise of a
`ClusterVersionSet` request (its `Ver` parses: the server proposes only versions it parsed). -/
opaque semverValid : GoString → Prop

/-- The request's id as `apply.Apply` computes it: `ID`, or the header's if `ID` is 0; `none`
if neither (`Apply` panics: a pre-3.0 entry without a header). -/
def irrId (rq : IRRModel) : Option w64 :=
  if rq.id ≠ W64 0 then some rq.id else rq.header.map HeaderModel.id

/-- The requests `dispatch` handles, in its order. -/
inductive ReqKind where
  | clusterVersionSet | clusterMemberAttrSet | downgradeInfoSet | downgradeVersionTest
  | range | put | deleteRange | txn | compaction | leaseGrant | leaseRevoke | leaseCheckpoint
  | alarm | authenticate | authEnable | authDisable | authStatus | authUserAdd | authUserDelete
  | authUserChangePassword | authUserGrantRole | authUserGet | authUserRevokeRole | authRoleAdd
  | authRoleGrantPermission | authRoleGet | authRoleRevokePermission | authRoleDelete
  | authUserList | authRoleList
  /-- No field set: `dispatch`'s `default` (`lg.Panic("not implemented apply")`). -/
  | none
  deriving DecidableEq

/-- **What `dispatch` does with `rq`**: the first set field in its order (its two `switch`es:
the cluster requests and `DowngradeVersionTest` first, whatever `shouldApplyV3`; then the
others). No premise that at most one is set: the code's order decides. -/
def dispatchKind (rq : IRRModel) : ReqKind :=
  if rq.clusterVersionSet.isSome then .clusterVersionSet
  else if rq.clusterMemberAttrSet.isSome then .clusterMemberAttrSet
  else if rq.downgradeInfoSet.isSome then .downgradeInfoSet
  else if rq.downgradeVersionTest then .downgradeVersionTest
  else if rq.range.isSome then .range
  else if rq.put.isSome then .put
  else if rq.deleteRange.isSome then .deleteRange
  else if rq.txn.isSome then .txn
  else if rq.compaction.isSome then .compaction
  else if rq.leaseGrant.isSome then .leaseGrant
  else if rq.leaseRevoke.isSome then .leaseRevoke
  else if rq.leaseCheckpoint.isSome then .leaseCheckpoint
  else if rq.alarm.isSome then .alarm
  else if rq.authenticate.isSome then .authenticate
  else if rq.authEnable then .authEnable
  else if rq.authDisable then .authDisable
  else if rq.authStatus then .authStatus
  else if rq.authUserAdd then .authUserAdd
  else if rq.authUserDelete then .authUserDelete
  else if rq.authUserChangePassword then .authUserChangePassword
  else if rq.authUserGrantRole then .authUserGrantRole
  else if rq.authUserGet.isSome then .authUserGet
  else if rq.authUserRevokeRole then .authUserRevokeRole
  else if rq.authRoleAdd then .authRoleAdd
  else if rq.authRoleGrantPermission then .authRoleGrantPermission
  else if rq.authRoleGet.isSome then .authRoleGet
  else if rq.authRoleRevokePermission then .authRoleRevokePermission
  else if rq.authRoleDelete then .authRoleDelete
  else if rq.authUserList then .authUserList
  else if rq.authRoleList then .authRoleList
  else .none

/-- `noSideEffect(r)` (`apply.go`): a range, a user or role get, or the auth status: `Apply`
skips such a request when no one waits for its result. -/
def noSideEffect (rq : IRRModel) : Bool :=
  [rq.range.isSome, rq.authUserGet.isSome, rq.authRoleGet.isSome, rq.authStatus].or

/-- `needAdminPermission(r)` (`auth.go`): the auth requests that change users or roles, enable
or disable auth, or list users or roles. -/
def needAdminPermission (rq : IRRModel) : Bool :=
  [rq.authEnable, rq.authDisable, rq.authUserAdd, rq.authUserDelete, rq.authUserChangePassword,
    rq.authUserGrantRole, rq.authUserRevokeRole, rq.authRoleAdd, rq.authRoleGrantPermission,
    rq.authRoleRevokePermission, rq.authRoleDelete, rq.authUserList, rq.authRoleList].or

/-- A KV request: what the txn package applies (and the corrupt applier rejects). -/
def isKVKind : ReqKind → Bool
  | .range | .put | .deleteRange | .txn => true
  | _ => false

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The request in the heap -/

section typeRepr
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `TypeRepr` of `InternalRaftRequest` (named and underlying), straight from its
`TypeAssumptions` (as `InvRaftpb.lean` does for `raftpb`'s, `Cache/InvStore.lean` for the
cache's messages): the decoder's spec owns the whole struct (`apply.Apply` allocates it). -/
instance (priority := high) internalRaftRequest_typeRepr :
    TypeRepr etcdserverpb.InternalRaftRequest.ty etcdserverpb.InternalRaftRequest :=
  go.type_repr_underlying (u := etcdserverpb.InternalRaftRequest.underlying)

instance (priority := high) internalRaftRequest_typeRepr_u :
    TypeRepr etcdserverpb.InternalRaftRequest.underlying etcdserverpb.InternalRaftRequest :=
  go.type_repr_underlying (u := etcdserverpb.InternalRaftRequest.underlying)

end typeRepr

/-- An optional request field `l`: `nil` if unset, else `P l a` (which says `l ≠ nil`). -/
def optReqIs {α : Type} (l : Loc) (o : Option α) (P : Loc → α → IProp GF) : IProp GF :=
  match o with
  | none => iprop(⌜l = null⌝)
  | some a => P l a

instance optReqIs_persistent {α : Type} (l : Loc) (o : Option α) (P : Loc → α → IProp GF)
    [∀ l a, Persistent (P l a)] : Persistent (optReqIs l o P) := by
  unfold optReqIs; cases o <;> infer_instance

/-- A request field the package passes on unread: set (`b`) iff not nil. -/
def presentIs (l : Loc) (b : Bool) : IProp GF :=
  iprop(⌜l ≠ null ↔ b = true⌝)

instance presentIs_persistent (l : Loc) (b : Bool) : Persistent (presentIs (GF := GF) l b) := by
  unfold presentIs; infer_instance

/-- The `*pb.RequestHeader` `h` (not nil) holds `hm`, read-only. -/
def headerIs (h : Loc) (hm : HeaderModel) : IProp GF :=
  iprop(⌜h ≠ null⌝ ∗
    structFieldRef etcdserverpb.RequestHeader go!"ID" h ↦□ hm.id ∗
    structFieldRef etcdserverpb.RequestHeader go!"Username" h ↦□ hm.username ∗
    structFieldRef etcdserverpb.RequestHeader go!"AuthRevision" h ↦□ hm.authRevision)

/-- The `*pb.CompactionRequest` `c` (not nil): its `Revision`, read-only. -/
def compactionIs (c : Loc) (rev : w64) : IProp GF :=
  iprop(⌜c ≠ null⌝ ∗ structFieldRef etcdserverpb.CompactionRequest go!"Revision" c ↦□ rev)

/-- The `*pb.LeaseGrantRequest` `l` (not nil): its `ID` and `TTL`, read-only. -/
def leaseGrantIs (l : Loc) (g : LeaseGrantModel) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ structFieldRef etcdserverpb.LeaseGrantRequest go!"ID" l ↦□ g.id ∗
    structFieldRef etcdserverpb.LeaseGrantRequest go!"TTL" l ↦□ g.ttl)

/-- The `*pb.LeaseRevokeRequest` `l` (not nil): its `ID`, read-only. -/
def leaseRevokeIs (l : Loc) (id : w64) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ structFieldRef etcdserverpb.LeaseRevokeRequest go!"ID" l ↦□ id)

/-- The `*pb.AlarmRequest` `a` (not nil): its `Action`, `Alarm` and `MemberID`, read-only. -/
def alarmRequestIs (a : Loc) (am : AlarmModel) : IProp GF :=
  iprop(⌜a ≠ null⌝ ∗ structFieldRef etcdserverpb.AlarmRequest go!"Action" a ↦□ am.action ∗
    structFieldRef etcdserverpb.AlarmRequest go!"Alarm" a ↦□ am.alarm ∗
    structFieldRef etcdserverpb.AlarmRequest go!"MemberID" a ↦□ am.memberID)

/-- The `*pb.LeaseCheckpoint` `c` (not nil): its `ID` and `Remaining_TTL`, read-only. -/
def checkpointIs (c : Loc) (cm : CheckpointModel) : IProp GF :=
  iprop(⌜c ≠ null⌝ ∗ structFieldRef etcdserverpb.LeaseCheckpoint go!"ID" c ↦□ cm.id ∗
    structFieldRef etcdserverpb.LeaseCheckpoint go!"Remaining_TTL" c ↦□ cm.remainingTTL)

/-- The `*pb.LeaseCheckpointRequest` `l` (not nil): its `Checkpoints`, each not nil (`LeaseCheckpoint`
dereferences them). -/
def leaseCheckpointIs (l : Loc) (cms : List CheckpointModel) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.LeaseCheckpointRequest go!"Checkpoints" l ↦□ sl ∗
    sl ↦*□ ps ∗ ⌜ps.length = cms.length⌝ ∗
    [∗list] pc ∈ ps.zip cms, checkpointIs pc.1 pc.2)

/-- The `*pb.InternalAuthenticateRequest` `a` (not nil): its fields, read-only. -/
def authenticateIs (a : Loc) (am : AuthenticateModel) : IProp GF :=
  iprop(⌜a ≠ null⌝ ∗
    structFieldRef etcdserverpb.InternalAuthenticateRequest go!"Name" a ↦□ am.name ∗
    structFieldRef etcdserverpb.InternalAuthenticateRequest go!"Password" a ↦□ am.password ∗
    structFieldRef etcdserverpb.InternalAuthenticateRequest go!"SimpleToken" a ↦□ am.simpleToken)

/-- The `*pb.AuthUserGetRequest` `u` (not nil): its `Name`, read-only. -/
def authUserGetIs (u : Loc) (name : GoString) : IProp GF :=
  iprop(⌜u ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserGetRequest go!"Name" u ↦□ name)

/-- The `*pb.AuthRoleGetRequest` `r` (not nil): its `Role`, read-only. -/
def authRoleGetIs (r : Loc) (role : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthRoleGetRequest go!"Role" r ↦□ role)

/-- The `*membershippb.ClusterVersionSetRequest` `c` (not nil): its `Ver`, read-only. -/
def clusterVersionSetIs (c : Loc) (ver : GoString) : IProp GF :=
  iprop(⌜c ≠ null⌝ ∗
    structFieldRef membershippb.ClusterVersionSetRequest go!"Ver" c ↦□ ver)

/-- The `*membershippb.ClusterMemberAttrSetRequest` `c` (not nil): its `Member_ID` and its
`MemberAttributes` (not nil: `ClusterMemberAttrSet` dereferences it), read-only. -/
def memberAttrSetIs (c : Loc) (m : MemberAttrModel) : IProp GF :=
  iprop(⌜c ≠ null⌝ ∗ ∃ (a : Loc) (sl : GoSlice),
    structFieldRef membershippb.ClusterMemberAttrSetRequest go!"Member_ID" c ↦□ m.memberID ∗
    structFieldRef membershippb.ClusterMemberAttrSetRequest go!"MemberAttributes" c ↦□ a ∗
    ⌜a ≠ null⌝ ∗ structFieldRef membershippb.Attributes go!"Name" a ↦□ m.name ∗
    structFieldRef membershippb.Attributes go!"ClientUrls" a ↦□ sl ∗ sl ↦*□ m.clientURLs)

/-- The `*membershippb.DowngradeInfoSetRequest` `d` (not nil): its `Enabled` and `Ver`,
read-only. -/
def downgradeInfoSetIs (d : Loc) (dm : DowngradeModel) : IProp GF :=
  iprop(⌜d ≠ null⌝ ∗
    structFieldRef membershippb.DowngradeInfoSetRequest go!"Enabled" d ↦□ dm.enabled ∗
    structFieldRef membershippb.DowngradeInfoSetRequest go!"Ver" d ↦□ dm.ver)

/-- An `InternalRaftRequest` field: its value `l` and what it holds. -/
abbrev irrField (p : Loc) (f : GoString) (Q : Loc → IProp GF) : IProp GF :=
  iprop(∃ l : Loc, structFieldRef etcdserverpb.InternalRaftRequest f p ↦□ l ∗ Q l)

/-- **The `*pb.InternalRaftRequest` `p` (not nil) holds `rq`**: every field read-only. -/
def internalRaftRequestIs (p : Loc) (rq : IRRModel) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗
    structFieldRef etcdserverpb.InternalRaftRequest go!"ID" p ↦□ rq.id ∗
    irrField p go!"Header" (fun l => optReqIs l rq.header headerIs) ∗
    irrField p go!"Range" (fun l => optReqIs l rq.range txn.rangeRequestIs) ∗
    irrField p go!"Put" (fun l => optReqIs l rq.put txn.putRequestIs) ∗
    irrField p go!"DeleteRange" (fun l => optReqIs l rq.deleteRange txn.deleteRangeRequestIs) ∗
    irrField p go!"Txn" (fun l => optReqIs l rq.txn txn.txnRequestIs) ∗
    irrField p go!"Compaction" (fun l => optReqIs l rq.compaction compactionIs) ∗
    irrField p go!"LeaseGrant" (fun l => optReqIs l rq.leaseGrant leaseGrantIs) ∗
    irrField p go!"LeaseRevoke" (fun l => optReqIs l rq.leaseRevoke leaseRevokeIs) ∗
    irrField p go!"Alarm" (fun l => optReqIs l rq.alarm alarmRequestIs) ∗
    irrField p go!"LeaseCheckpoint" (fun l => optReqIs l rq.leaseCheckpoint leaseCheckpointIs) ∗
    irrField p go!"AuthEnable" (fun l => presentIs l rq.authEnable) ∗
    irrField p go!"AuthDisable" (fun l => presentIs l rq.authDisable) ∗
    irrField p go!"AuthStatus" (fun l => presentIs l rq.authStatus) ∗
    irrField p go!"Authenticate" (fun l => optReqIs l rq.authenticate authenticateIs) ∗
    irrField p go!"AuthUserAdd" (fun l => presentIs l rq.authUserAdd) ∗
    irrField p go!"AuthUserDelete" (fun l => presentIs l rq.authUserDelete) ∗
    irrField p go!"AuthUserGet" (fun l => optReqIs l rq.authUserGet authUserGetIs) ∗
    irrField p go!"AuthUserChangePassword" (fun l => presentIs l rq.authUserChangePassword) ∗
    irrField p go!"AuthUserGrantRole" (fun l => presentIs l rq.authUserGrantRole) ∗
    irrField p go!"AuthUserRevokeRole" (fun l => presentIs l rq.authUserRevokeRole) ∗
    irrField p go!"AuthUserList" (fun l => presentIs l rq.authUserList) ∗
    irrField p go!"AuthRoleList" (fun l => presentIs l rq.authRoleList) ∗
    irrField p go!"AuthRoleAdd" (fun l => presentIs l rq.authRoleAdd) ∗
    irrField p go!"AuthRoleDelete" (fun l => presentIs l rq.authRoleDelete) ∗
    irrField p go!"AuthRoleGet" (fun l => optReqIs l rq.authRoleGet authRoleGetIs) ∗
    irrField p go!"AuthRoleGrantPermission" (fun l => presentIs l rq.authRoleGrantPermission) ∗
    irrField p go!"AuthRoleRevokePermission" (fun l => presentIs l rq.authRoleRevokePermission) ∗
    irrField p go!"ClusterVersionSet" (fun l => optReqIs l rq.clusterVersionSet clusterVersionSetIs) ∗
    irrField p go!"ClusterMemberAttrSet"
      (fun l => optReqIs l rq.clusterMemberAttrSet memberAttrSetIs) ∗
    irrField p go!"DowngradeInfoSet" (fun l => optReqIs l rq.downgradeInfoSet downgradeInfoSetIs) ∗
    irrField p go!"DowngradeVersionTest" (fun l => presentIs l rq.downgradeVersionTest))

instance internalRaftRequestIs_persistent (p : Loc) (rq : IRRModel) :
    Persistent (internalRaftRequestIs (GF := GF) p rq) := by
  unfold internalRaftRequestIs headerIs compactionIs leaseGrantIs leaseRevokeIs alarmRequestIs
    leaseCheckpointIs checkpointIs authenticateIs authUserGetIs authRoleGetIs clusterVersionSetIs
    memberAttrSetIs downgradeInfoSetIs
  infer_instance

end defs

end apply
end EtcdGrove
end Perennial
