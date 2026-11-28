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

**Decoding** (`irrDecode`: opaque until 2026-11-23, now its `AuthUserGrantRole` field the Lean
reader `IrrWire.irrUgrDecodeRaw` and the rest the opaque `irrDecodeRest`): the request protobuf's decoding of an entry's bytes, as the
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
public import Proof.go_etcd_io.etcd.server.v3.auth.Requests
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.IrrWire

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

/-- An `AuthUserAddRequest`'s `Name`, `Password`, `HashedPassword` and its options' `NoPassword`
(`Options` nil reads as `false`, as `UserAdd` does). The auth plan's E2t (2026-10-26): the request
model keeps the password choice, which decides `UserAdd`'s `ErrNoPasswordUser`. -/
structure UserAddModel where
  name : GoString
  password : GoString
  hashed : GoString
  noPassword : Bool

/-- **The password choice cannot fail** (`UserAdd`'s `ErrNoPasswordUser` is not possible): no
password asked for, or the server's own form of a password (`EtcdServer.UserAdd`, since 3.5: the
password cleared and its bcrypt hash in `HashedPassword`, base64-encoded), which `selectPassword`
decodes without an error. -/
def UserAddModel.pwSure (m : UserAddModel) : Prop :=
  auth.pwSureP m.password m.hashed m.noPassword

/-- An `AuthUserChangePasswordRequest`'s `Name`, `Password` and `HashedPassword` (nomode D3,
2026-11-28: the request model keeps what `UserChangePassword` reads). -/
structure ChangePasswordModel where
  name : GoString
  password : GoString
  hashed : GoString

/-- **The password choice cannot fail** (`UserChangePassword`'s `ErrNoPasswordUser` is not
possible): an empty `Password` with a base64-encoded `HashedPassword`, which `selectPassword` decodes
without an error (`EtcdServer.UserChangePassword` proposes this form when a password is set: its
bcrypt hash, base64-encoded, `Password` cleared); a user without a password selects none. -/
def ChangePasswordModel.pwSure (m : ChangePasswordModel) : Prop :=
  auth.pwSureP m.password m.hashed false

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
  /-- the transaction as the wire has it (the auth plan's E3e, 2026-10-27: a `TxnModel` until then;
  a put keeps its `PrevKv`, which the auth layer's checks read); `IRRModel.txn` is its `TxnModel` -/
  txnW : Option txn.TxnModelW
  compaction : Option w64
  leaseGrant : Option LeaseGrantModel
  leaseRevoke : Option w64
  alarm : Option AlarmModel
  leaseCheckpoint : Option (List CheckpointModel)
  authEnable : Bool
  authDisable : Bool
  authStatus : Bool
  authenticate : Option AuthenticateModel
  /-- the user's name (unit N4, D14g, 2026-10-17: a `Bool` until then; the auth store's
  `UserAdd` makes it a bbolt key, `issues/etcd-auth-useradd-long-name-fatal.md`; with its passwords
  and options since the auth plan's E2t, 2026-10-26, `UserAddModel`) -/
  authUserAdd : Option UserAddModel
  /-- the user's name (nomode D3, 2026-11-28: a `Bool` until then, as the five below) -/
  authUserDelete : Option GoString
  authUserGet : Option GoString
  /-- the user's name and passwords -/
  authUserChangePassword : Option ChangePasswordModel
  /-- the user's and the role's names (the auth plan's E2n, 2026-10-26: a `Bool` until then; the
  step specs bound the user's name, `apply.adminKindOk`) -/
  authUserGrantRole : Option (GoString × GoString)
  /-- the user's and the role's names -/
  authUserRevokeRole : Option (GoString × GoString)
  authUserList : Bool
  authRoleList : Bool
  /-- the role's name (as `authUserAdd`'s) -/
  authRoleAdd : Option GoString
  /-- the role's name -/
  authRoleDelete : Option GoString
  authRoleGet : Option GoString
  /-- the role's name and the permission (as `authUserGrantRole`'s) -/
  authRoleGrantPermission : Option (GoString × Option auth.PermW)
  /-- the role's name, the key and the range end -/
  authRoleRevokePermission : Option (GoString × GoString × GoString)
  clusterVersionSet : Option GoString
  clusterMemberAttrSet : Option MemberAttrModel
  downgradeInfoSet : Option DowngradeModel
  downgradeVersionTest : Bool

/-- **The request's transaction** (`TxnModel`, the client's model: a put through `putTxnOp`, its
`PrevKv` forgotten): the wire transaction's (`txnW`) model. -/
def IRRModel.txn (rq : IRRModel) : Option TxnModel := rq.txnW.map txn.TxnModelW.toModel

/-- **Every key and value the request `rq` puts is at most `n` bytes** (2026-10-31,
`notes/vallen.md`): its `Put`'s key and value, and its transaction's puts' at any depth
(`TxnModel.putsLe`; a put keeping the stored value bounds its key only). -/
def irrPutsLe (n : Nat) (rq : IRRModel) : Prop :=
  (∀ o, rq.put = some o → o.key.length ≤ n ∧ o.val.length ≤ n) ∧
    (∀ t, rq.txn = some t → t.putsLe n)

theorem irrPutsLe.mono {n m : Nat} (h : n ≤ m) {rq : IRRModel} (hk : irrPutsLe n rq) :
    irrPutsLe m rq :=
  ⟨fun o ho => ⟨Nat.le_trans (hk.1 o ho).1 h, Nat.le_trans (hk.1 o ho).2 h⟩,
    fun t ht => TxnModel.putsLe_mono h (hk.2 t ht)⟩

@[simp] theorem IRRModel.txnW_map (rq : IRRModel) :
    rq.txnW.map txn.TxnModelW.toModel = rq.txn := rfl

/-- `IRRModel.txn` of a record built field by field (`{ rq with ... }`): its `txnW`'s model. -/
@[simp] theorem IRRModel.txn_mk {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32} :
    (IRRModel.mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32).txn = a6.map txn.TxnModelW.toModel := rfl

/-- **Trust boundary (the encoding), the fields but `AuthUserGrantRole`.** What
`pbutil.MustUnmarshalMessage` into an `InternalRaftRequest` makes of a committed normal entry's
bytes, read as `IRRModel`, but its `authUserGrantRole` (which `irrDecode` replaces by
`IrrWire.irrUgrDecodeRaw`'s); `none`: they do not decode (it panics). Opaque, as mvcc's
`kvEncode`: only the encoding's axioms (`proto.MarshalIRR`, through `irrDecode`) say anything of
it. (Protobuf stage S2, 2026-11-23: until then all of `irrDecode`.) -/
opaque irrDecodeRest : List w8 → Option IRRModel

/-- **The request a committed normal entry's bytes decode to** (`pbutil.MustUnmarshalMessage` into
an `InternalRaftRequest`, read as `IRRModel`); `none`: they do not decode (it panics). The
`AuthUserGrantRole` request is `IrrWire.irrUgrDecodeRaw`'s, protobuf-go's reading of that field as
a Lean function (checked against protobuf-go by `IrrWireVectors.lean`), the other fields the opaque
`irrDecodeRest`'s, and the bytes decode iff both readers succeed: true of protobuf-go, whose
`Unmarshal` succeeds only where the field reader does and then reads the same field
(`IrrWire.lean`'s header). (Protobuf stage S2, 2026-11-23: until then opaque, and
`irrDecode_utf8` an axiom.) -/
def irrDecode (bs : List w8) : Option IRRModel :=
  match irrDecodeRest bs, IrrWire.irrUgrDecodeRaw bs with
  | some rq, some ugr => some { rq with authUserGrantRole := ugr }
  | _, _ => none

/-- The decoded request's strings that the auth store writes into a proto3 `string` field are
valid UTF-8 (S0's F4, 2026-11-12): a `UserGrantRole`'s role, which `UserGrantRole` appends to the
user's `Roles` (`authpb.User.roles`, a `repeated string`, which `UnsafePutUser`'s `Marshal`
refuses otherwise). -/
def irrUtf8 (rq : IRRModel) : Prop :=
  ∀ ur, rq.authUserGrantRole = some ur → utf8Valid ur.2

/-- **A decoded request's `UserGrantRole` role is valid UTF-8** (until 2026-11-23, protobuf stage
S2, an axiom at the trust boundary; now a theorem of `irrDecode`'s definition):
`AuthUserGrantRoleRequest.role` is a proto3 `string` field (`api/etcdserverpb/rpc.proto`), and
protobuf-go (v2, the server pin's `etcdserverpb`) rejects on unmarshal a proto3 `string` that is
not valid UTF-8, which `IrrWire.irrUgrDecodeRaw` does too. Go evidence for the reader:
`IrrWireVectors.lean`; and `TestAuthFixIrrDecodeRejectsInvalidUTF8` (the Freeze package of
auth-schema-fix; `MustUnmarshalMessage` panics on an `InternalRaftRequest` whose
`AuthUserGrantRole.role` is `"\xff"`, at the server pin). -/
theorem irrDecode_utf8 (bs : List w8) (rq : IRRModel) (h : irrDecode bs = some rq) : irrUtf8 rq := by
  unfold irrDecode at h
  split at h
  · rename_i rq0 ugr _ hu
    simp only [Option.some.injEq] at h
    subst h
    intro ur hur
    simp only at hur
    subst hur
    exact IrrWire.irrUgrDecodeRaw_utf8 hu
  · simp at h

/-- **Trust boundary (semver).** Whether a version string parses (`semver.NewVersion` accepts
it): `semver.MustParse` returns a version for it, and panics otherwise (its axiom,
`Spec/github_com/Masterminds/semver/v3/MustParse.lean`). Opaque: the premise of a
`ClusterVersionSet` request (its `Ver` parses: the server proposes only versions it parsed). -/
opaque semverValid : GoString → Prop

/-- **Trust boundary (semver and the server's version).** The version `semver.MustParse(s)` is
not above this server's: not greater (`semver.Version.LessThan`, SemVer's order, prerelease below
release) than the major and minor version of `version.Version` with patch `0` (`3.8.0` at the fork
pin: `MustDetectDowngrade(lg, MustParse(version.Version), cv)` compares
`semver.New(sv.Major(), sv.Minor(), 0, "", "")` with `cv` and panics when it is less,
`server/etcdserver/version/downgrade.go:42-54`). Opaque, as `semverValid`: the premise of a
`ClusterVersionSet` request, which only the leader's monitor proposes, of the minimum of the
members' server versions with patch `0` (`version.Monitor.UpdateClusterVersionIfNeeded`), or
`MinClusterVersion` (`3.0.0`) while the cluster has no version and a member does not answer: the
leader's own `version.Version` is among the versions (`getMembersVersions` records the local
member's, the local member being in `c.members`), which bounds the proposal by the proposer's
major.minor. The applying member's bound is the proposer's because every member runs this binary
(the model's deployment: one program, the verified one); a member restarted on an older binary
between the proposal and its apply panics, by design (`MustDetectDowngrade`). The monitor's
downgrade branch (`monitor.go:80-99`, which could propose above the bound: `allowedDowngradeVersion`
wraps `Minor()-1` at minor `0`) is not reached: no `DowngradeInfoSet` is admitted (`rqOk`), and the
boot and snapshot images carry no enabled downgrade record. Its axiom is
`EtcdServer.monitorClusterVersions`'s, through `monitorReq`. -/
opaque semverAtMostServer : GoString → Prop

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
  else if rq.authUserAdd.isSome then .authUserAdd
  else if rq.authUserDelete.isSome then .authUserDelete
  else if rq.authUserChangePassword.isSome then .authUserChangePassword
  else if rq.authUserGrantRole.isSome then .authUserGrantRole
  else if rq.authUserGet.isSome then .authUserGet
  else if rq.authUserRevokeRole.isSome then .authUserRevokeRole
  else if rq.authRoleAdd.isSome then .authRoleAdd
  else if rq.authRoleGrantPermission.isSome then .authRoleGrantPermission
  else if rq.authRoleGet.isSome then .authRoleGet
  else if rq.authRoleRevokePermission.isSome then .authRoleRevokePermission
  else if rq.authRoleDelete.isSome then .authRoleDelete
  else if rq.authUserList then .authUserList
  else if rq.authRoleList then .authRoleList
  else .none

theorem ite_eq_iff' {α : Sort _} {c : Prop} [Decidable c] {a b k : α} :
    (if c then a else b) = k ↔ (c ∧ a = k) ∨ (¬c ∧ b = k) := by
  by_cases h : c <;> simp [h]

theorem dispatchKind_authenticate (rq : IRRModel) (h : dispatchKind rq = .authenticate) :
    rq.authenticate.isSome = true := by
  simp only [dispatchKind, ite_eq_iff', reduceCtorEq, and_false, false_or, or_false] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `noSideEffect(r)` (`apply.go`): a range, a user or role get, or the auth status: `Apply`
skips such a request when no one waits for its result. -/
def noSideEffect (rq : IRRModel) : Bool :=
  [rq.range.isSome, rq.authUserGet.isSome, rq.authRoleGet.isSome, rq.authStatus].or

/-- `needAdminPermission(r)` (`auth.go`): the auth requests that change users or roles, enable
or disable auth, or list users or roles. -/
def needAdminPermission (rq : IRRModel) : Bool :=
  [rq.authEnable, rq.authDisable, rq.authUserAdd.isSome, rq.authUserDelete.isSome,
    rq.authUserChangePassword.isSome, rq.authUserGrantRole.isSome, rq.authUserRevokeRole.isSome,
    rq.authRoleAdd.isSome, rq.authRoleGrantPermission.isSome,
    rq.authRoleRevokePermission.isSome, rq.authRoleDelete.isSome, rq.authUserList, rq.authRoleList].or

/-- A KV request: what the txn package applies (and the corrupt applier rejects). -/
def isKVKind : ReqKind → Bool
  | .range | .put | .deleteRange | .txn => true
  | _ => false

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- The `*pb.AuthUserAddRequest` `u` (not nil): its `Name` (unit N4, 2026-10-17), its passwords
and its options' `NoPassword` (the auth plan's E2n and E2t, 2026-10-26), read-only. It gives the
auth store's request model (`auth.userAddReqIs`, `authUserAddIs_req`), which its `UserAdd` reads. -/
def authUserAddIs (u : Loc) (m : UserAddModel) : IProp GF :=
  iprop(⌜u ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserAddRequest go!"Name" u ↦□ m.name ∗
    structFieldRef etcdserverpb.AuthUserAddRequest go!"Password" u ↦□ m.password ∗
    structFieldRef etcdserverpb.AuthUserAddRequest go!"HashedPassword" u ↦□ m.hashed ∗
    ∃ o : Loc, structFieldRef etcdserverpb.AuthUserAddRequest go!"Options" u ↦□ o ∗
      auth.userOptsAt o m.noPassword)

/-- The request model gives the auth store's (`auth.userAddReqIs`). -/
theorem authUserAddIs_req (u : Loc) (m : UserAddModel) :
    authUserAddIs (GF := GF) u m ⊢ auth.userAddReqIs u m.name := by
  unfold authUserAddIs auth.userAddReqIs
  iintro ⟨%hu, #Hn, #Hp, #Hh, %o, #Ho, #Hb⟩
  isplit; · ipureintro; exact hu
  isplit; · iexact Hn
  isplit; · iexists m.password, m.hashed; isplit <;> iassumption
  iexists o, m.noPassword; isplit <;> iassumption

/-- A request whose model's password choice cannot fail gives the auth store's `userAddSure`
(the auth plan's E2u: `UserAdd.specSure`). -/
theorem authUserAddIs_sure (u : Loc) (m : UserAddModel) (h : m.pwSure) :
    authUserAddIs (GF := GF) u m ⊢ auth.userAddSure u := by
  unfold authUserAddIs auth.userAddSure
  iintro ⟨%hu, #Hn, #Hp, #Hh, %o, #Ho, #Hb⟩
  iexists m.password, m.hashed, o, m.noPassword
  iframe Hp Hh Ho Hb
  ipureintro; exact h

/-- The `*pb.AuthRoleAddRequest` `r` (not nil): its `Name`, read-only (unit N4, 2026-10-17). -/
def authRoleAddIs (r : Loc) (name : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthRoleAddRequest go!"Name" r ↦□ name)

/-- The `*pb.AuthUserGrantRoleRequest` `r` (not nil): its `User` and `Role`, read-only (the auth
store's request model, `auth.userGrantRoleReqIs`; the auth plan's E2n). -/
def authUserGrantRoleIs (r : Loc) (ur : GoString × GoString) : IProp GF :=
  auth.userGrantRoleReqIs r ur.1 ur.2

/-- The `*pb.AuthRoleGrantPermissionRequest` `r` (not nil): its `Name` and its `Perm`, read-only
(`auth.roleGrantPermissionReqIs`; the auth plan's E2n). -/
def authRoleGrantPermissionIs (r : Loc) (nw : GoString × Option auth.PermW) : IProp GF :=
  auth.roleGrantPermissionReqIs r nw.1 nw.2

instance authUserGrantRoleIs_persistent (r : Loc) (ur : GoString × GoString) :
    Persistent (authUserGrantRoleIs (GF := GF) r ur) := by
  unfold authUserGrantRoleIs; infer_instance

instance authRoleGrantPermissionIs_persistent (r : Loc) (nw : GoString × Option auth.PermW) :
    Persistent (authRoleGrantPermissionIs (GF := GF) r nw) := by
  unfold authRoleGrantPermissionIs; infer_instance

theorem authUserGrantRoleIs_nn (l : Loc) (ur : GoString × GoString) :
    authUserGrantRoleIs (GF := GF) l ur ⊢ ⌜l ≠ null⌝ := by
  unfold authUserGrantRoleIs auth.userGrantRoleReqIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem authRoleGrantPermissionIs_nn (l : Loc) (nw : GoString × Option auth.PermW) :
    authRoleGrantPermissionIs (GF := GF) l nw ⊢ ⌜l ≠ null⌝ := by
  unfold authRoleGrantPermissionIs auth.roleGrantPermissionReqIs; iintro ⟨%h, -⟩; ipureintro; exact h

/-- The `*pb.AuthUserDeleteRequest` `r` (not nil): its `Name`, read-only (the auth store's request
model, `auth.userDeleteReqIs`; nomode D3, 2026-11-28, as the four below). -/
def authUserDeleteIs (r : Loc) (name : GoString) : IProp GF :=
  auth.userDeleteReqIs r name

/-- The `*pb.AuthUserChangePasswordRequest` `u` (not nil): its `Name`, `Password` and
`HashedPassword`, read-only. It gives the auth store's request model
(`auth.userChangePasswordReqIs`, `authUserChangePasswordIs_req`). -/
def authUserChangePasswordIs (u : Loc) (m : ChangePasswordModel) : IProp GF :=
  iprop(⌜u ≠ null⌝ ∗
    structFieldRef etcdserverpb.AuthUserChangePasswordRequest go!"Name" u ↦□ m.name ∗
    structFieldRef etcdserverpb.AuthUserChangePasswordRequest go!"Password" u ↦□ m.password ∗
    structFieldRef etcdserverpb.AuthUserChangePasswordRequest go!"HashedPassword" u ↦□ m.hashed)

/-- The `*pb.AuthUserRevokeRoleRequest` `r` (not nil): its `Name` and `Role`, read-only
(`auth.userRevokeRoleReqIs`). -/
def authUserRevokeRoleIs (r : Loc) (nr : GoString × GoString) : IProp GF :=
  auth.userRevokeRoleReqIs r nr.1 nr.2

/-- The `*pb.AuthRoleDeleteRequest` `r` (not nil): its `Role`, read-only (`auth.roleDeleteReqIs`). -/
def authRoleDeleteIs (r : Loc) (role : GoString) : IProp GF :=
  auth.roleDeleteReqIs r role

/-- The `*pb.AuthRoleRevokePermissionRequest` `r` (not nil): its `Role`, and its `Key` and
`RangeEnd` holding the key and the range end, read-only (`auth.roleRevokePermissionReqIs`). -/
def authRoleRevokePermissionIs (r : Loc) (rke : GoString × GoString × GoString) : IProp GF :=
  auth.roleRevokePermissionReqIs r rke.1 rke.2.1 rke.2.2

/-- The request model gives the auth store's (`auth.userChangePasswordReqIs`). -/
theorem authUserChangePasswordIs_req (u : Loc) (m : ChangePasswordModel) :
    authUserChangePasswordIs (GF := GF) u m ⊢ auth.userChangePasswordReqIs u m.name := by
  unfold authUserChangePasswordIs auth.userChangePasswordReqIs
  iintro ⟨%hu, #Hn, #Hp, #Hh⟩
  isplit; · ipureintro; exact hu
  isplit; · iexact Hn
  iexists m.password, m.hashed; isplit <;> iassumption

/-- A request whose model's password choice cannot fail gives the auth store's
`userChangePasswordSure`. -/
theorem authUserChangePasswordIs_sure (u : Loc) (m : ChangePasswordModel) (h : m.pwSure) :
    authUserChangePasswordIs (GF := GF) u m ⊢ auth.userChangePasswordSure u := by
  unfold authUserChangePasswordIs auth.userChangePasswordSure
  iintro ⟨%hu, #Hn, #Hp, #Hh⟩
  iexists m.password, m.hashed
  iframe Hp Hh
  ipureintro; exact h

instance authUserDeleteIs_persistent (r : Loc) (name : GoString) :
    Persistent (authUserDeleteIs (GF := GF) r name) := by
  unfold authUserDeleteIs; infer_instance

instance authUserChangePasswordIs_persistent (u : Loc) (m : ChangePasswordModel) :
    Persistent (authUserChangePasswordIs (GF := GF) u m) := by
  unfold authUserChangePasswordIs; infer_instance

instance authUserRevokeRoleIs_persistent (r : Loc) (nr : GoString × GoString) :
    Persistent (authUserRevokeRoleIs (GF := GF) r nr) := by
  unfold authUserRevokeRoleIs; infer_instance

instance authRoleDeleteIs_persistent (r : Loc) (role : GoString) :
    Persistent (authRoleDeleteIs (GF := GF) r role) := by
  unfold authRoleDeleteIs; infer_instance

instance authRoleRevokePermissionIs_persistent (r : Loc) (rke : GoString × GoString × GoString) :
    Persistent (authRoleRevokePermissionIs (GF := GF) r rke) := by
  unfold authRoleRevokePermissionIs; infer_instance

theorem authUserDeleteIs_nn (l : Loc) (n : GoString) :
    authUserDeleteIs (GF := GF) l n ⊢ ⌜l ≠ null⌝ := by
  unfold authUserDeleteIs auth.userDeleteReqIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem authUserChangePasswordIs_nn (l : Loc) (m : ChangePasswordModel) :
    authUserChangePasswordIs (GF := GF) l m ⊢ ⌜l ≠ null⌝ := by
  unfold authUserChangePasswordIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem authUserRevokeRoleIs_nn (l : Loc) (nr : GoString × GoString) :
    authUserRevokeRoleIs (GF := GF) l nr ⊢ ⌜l ≠ null⌝ := by
  unfold authUserRevokeRoleIs auth.userRevokeRoleReqIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem authRoleDeleteIs_nn (l : Loc) (r : GoString) :
    authRoleDeleteIs (GF := GF) l r ⊢ ⌜l ≠ null⌝ := by
  unfold authRoleDeleteIs auth.roleDeleteReqIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem authRoleRevokePermissionIs_nn (l : Loc) (rke : GoString × GoString × GoString) :
    authRoleRevokePermissionIs (GF := GF) l rke ⊢ ⌜l ≠ null⌝ := by
  unfold authRoleRevokePermissionIs auth.roleRevokePermissionReqIs; iintro ⟨%h, -⟩; ipureintro; exact h

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

instance headerIs_persistent (h : Loc) (hm : HeaderModel) : Persistent (headerIs (GF := GF) h hm) := by
  unfold headerIs; infer_instance

instance compactionIs_persistent (c : Loc) (rev : w64) : Persistent (compactionIs (GF := GF) c rev) := by
  unfold compactionIs; infer_instance

instance leaseGrantIs_persistent (l : Loc) (g : LeaseGrantModel) : Persistent (leaseGrantIs (GF := GF) l g) := by
  unfold leaseGrantIs; infer_instance

instance leaseRevokeIs_persistent (l : Loc) (id : w64) : Persistent (leaseRevokeIs (GF := GF) l id) := by
  unfold leaseRevokeIs; infer_instance

instance alarmRequestIs_persistent (a : Loc) (am : AlarmModel) : Persistent (alarmRequestIs (GF := GF) a am) := by
  unfold alarmRequestIs; infer_instance

instance leaseCheckpointIs_persistent (l : Loc) (cms : List CheckpointModel) : Persistent (leaseCheckpointIs (GF := GF) l cms) := by
  unfold leaseCheckpointIs checkpointIs; infer_instance

instance authenticateIs_persistent (a : Loc) (am : AuthenticateModel) : Persistent (authenticateIs (GF := GF) a am) := by
  unfold authenticateIs; infer_instance

instance authUserGetIs_persistent (u : Loc) (name : GoString) : Persistent (authUserGetIs (GF := GF) u name) := by
  unfold authUserGetIs; infer_instance

instance authRoleGetIs_persistent (r : Loc) (role : GoString) : Persistent (authRoleGetIs (GF := GF) r role) := by
  unfold authRoleGetIs; infer_instance

instance authUserAddIs_persistent (u : Loc) (m : UserAddModel) : Persistent (authUserAddIs (GF := GF) u m) := by
  unfold authUserAddIs; infer_instance

instance authRoleAddIs_persistent (r : Loc) (name : GoString) : Persistent (authRoleAddIs (GF := GF) r name) := by
  unfold authRoleAddIs; infer_instance

instance clusterVersionSetIs_persistent (c : Loc) (ver : GoString) : Persistent (clusterVersionSetIs (GF := GF) c ver) := by
  unfold clusterVersionSetIs; infer_instance

instance memberAttrSetIs_persistent (c : Loc) (m : MemberAttrModel) : Persistent (memberAttrSetIs (GF := GF) c m) := by
  unfold memberAttrSetIs; infer_instance

instance downgradeInfoSetIs_persistent (d : Loc) (dm : DowngradeModel) : Persistent (downgradeInfoSetIs (GF := GF) d dm) := by
  unfold downgradeInfoSetIs; infer_instance

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
    irrField p go!"Txn" (fun l => optReqIs l rq.txnW txn.txnRequestIsW) ∗
    irrField p go!"Compaction" (fun l => optReqIs l rq.compaction compactionIs) ∗
    irrField p go!"LeaseGrant" (fun l => optReqIs l rq.leaseGrant leaseGrantIs) ∗
    irrField p go!"LeaseRevoke" (fun l => optReqIs l rq.leaseRevoke leaseRevokeIs) ∗
    irrField p go!"Alarm" (fun l => optReqIs l rq.alarm alarmRequestIs) ∗
    irrField p go!"LeaseCheckpoint" (fun l => optReqIs l rq.leaseCheckpoint leaseCheckpointIs) ∗
    irrField p go!"AuthEnable" (fun l => presentIs l rq.authEnable) ∗
    irrField p go!"AuthDisable" (fun l => presentIs l rq.authDisable) ∗
    irrField p go!"AuthStatus" (fun l => presentIs l rq.authStatus) ∗
    irrField p go!"Authenticate" (fun l => optReqIs l rq.authenticate authenticateIs) ∗
    irrField p go!"AuthUserAdd" (fun l => optReqIs l rq.authUserAdd authUserAddIs) ∗
    irrField p go!"AuthUserDelete" (fun l => optReqIs l rq.authUserDelete authUserDeleteIs) ∗
    irrField p go!"AuthUserGet" (fun l => optReqIs l rq.authUserGet authUserGetIs) ∗
    irrField p go!"AuthUserChangePassword"
      (fun l => optReqIs l rq.authUserChangePassword authUserChangePasswordIs) ∗
    irrField p go!"AuthUserGrantRole" (fun l => optReqIs l rq.authUserGrantRole authUserGrantRoleIs) ∗
    irrField p go!"AuthUserRevokeRole" (fun l => optReqIs l rq.authUserRevokeRole authUserRevokeRoleIs) ∗
    irrField p go!"AuthUserList" (fun l => presentIs l rq.authUserList) ∗
    irrField p go!"AuthRoleList" (fun l => presentIs l rq.authRoleList) ∗
    irrField p go!"AuthRoleAdd" (fun l => optReqIs l rq.authRoleAdd authRoleAddIs) ∗
    irrField p go!"AuthRoleDelete" (fun l => optReqIs l rq.authRoleDelete authRoleDeleteIs) ∗
    irrField p go!"AuthRoleGet" (fun l => optReqIs l rq.authRoleGet authRoleGetIs) ∗
    irrField p go!"AuthRoleGrantPermission"
      (fun l => optReqIs l rq.authRoleGrantPermission authRoleGrantPermissionIs) ∗
    irrField p go!"AuthRoleRevokePermission"
      (fun l => optReqIs l rq.authRoleRevokePermission authRoleRevokePermissionIs) ∗
    irrField p go!"ClusterVersionSet" (fun l => optReqIs l rq.clusterVersionSet clusterVersionSetIs) ∗
    irrField p go!"ClusterMemberAttrSet"
      (fun l => optReqIs l rq.clusterMemberAttrSet memberAttrSetIs) ∗
    irrField p go!"DowngradeInfoSet" (fun l => optReqIs l rq.downgradeInfoSet downgradeInfoSetIs) ∗
    irrField p go!"DowngradeVersionTest" (fun l => presentIs l rq.downgradeVersionTest))

instance internalRaftRequestIs_persistent (p : Loc) (rq : IRRModel) :
    Persistent (internalRaftRequestIs (GF := GF) p rq) := by
  unfold internalRaftRequestIs headerIs compactionIs leaseGrantIs leaseRevokeIs alarmRequestIs
    leaseCheckpointIs checkpointIs authenticateIs authUserGetIs authRoleGetIs authUserAddIs
    authRoleAddIs authUserGrantRoleIs authRoleGrantPermissionIs clusterVersionSetIs
    memberAttrSetIs downgradeInfoSetIs
  infer_instance

/-- **The request's `Txn` field, in the model's terms** (E3e): the wire transaction's
`txnRequestIsW` gives its model's `txnRequestIs`. -/
theorem optReqIs_txnW (l : Loc) (rq : IRRModel) :
    optReqIs (GF := GF) l rq.txnW txn.txnRequestIsW ⊢ optReqIs l rq.txn txn.txnRequestIs := by
  unfold IRRModel.txn
  cases rq.txnW with
  | none => simp only [optReqIs, Option.map]; iintro H; iexact H
  | some tw => simp only [optReqIs, Option.map]; iapply txn.txnRequestIsW_plain

/-- **The `*InternalRaftRequestWrapper` `r`** (not nil; `apply.Apply` builds it): its request
`rq` and its `SkipRangeExecution` `skip`, read-only; (S0's F4) `rq` decoded, so its auth strings
valid UTF-8 (`irrUtf8`, from `irrDecode_utf8`). -/
def irrWrapperIs (r : Loc) (rq : IRRModel) (skip : Bool) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ ∃ p : Loc,
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.InternalRaftRequestWrapper
      go!"InternalRaftRequest" r ↦□ p ∗ internalRaftRequestIs p rq ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.InternalRaftRequestWrapper
      go!"SkipRangeExecution" r ↦□ skip ∗ ⌜irrUtf8 rq⌝)

instance irrWrapperIs_persistent (r : Loc) (rq : IRRModel) (skip : Bool) :
    Persistent (irrWrapperIs (GF := GF) r rq skip) := by
  unfold irrWrapperIs; infer_instance

end defs

end apply
end EtcdGrove
end Perennial
