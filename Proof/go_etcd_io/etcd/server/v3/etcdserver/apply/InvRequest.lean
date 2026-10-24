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

namespace protowire

/-- **`protowire.ConsumeTag(b)`**: the field number, wire type, and positive byte count `n`
(`1 ≤ n ≤ b.length`), or `none` on a negative error code (`n < 0`). -/
opaque consumeTag : List w8 → Option (w32 × w8 × Nat)

/-- **`protowire.ConsumeVarint(b)`**: the `uint64` value and byte count `n` (`0 ≤ n ≤ b.length`),
or `none` on a negative error code (`n < 0`). -/
opaque consumeVarint : List w8 → Option (w64 × Nat)

/-- **`protowire.ConsumeBytes(b)`**: the byte slice value and total byte count `n`
(`0 ≤ n ≤ b.length`), or `none` on a negative error code (`n < 0`). -/
opaque consumeBytes : List w8 → Option (List w8 × Nat)

/-- **`protowire.ConsumeFieldValue(num, typ, b)`**: the byte count `n` (`0 ≤ n ≤ b.length`),
or `none` on a negative error code (`n < 0`). -/
opaque consumeFieldValue : w32 → w8 → List w8 → Option Nat

end protowire

namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

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
  /-- the user's name (unit N4, D14g, 2026-10-17: a `Bool` until then; the auth store's
  `UserAdd` makes it a bbolt key, `issues/etcd-auth-useradd-long-name-fatal.md`) -/
  authUserAdd : Option GoString
  authUserDelete : Bool
  authUserGet : Option GoString
  authUserChangePassword : Bool
  authUserGrantRole : Bool
  authUserRevokeRole : Bool
  authUserList : Bool
  authRoleList : Bool
  /-- the role's name (as `authUserAdd`'s) -/
  authRoleAdd : Option GoString
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

/-- The request with nothing set (`&pb.InternalRaftRequest{}`). -/
def irrEmpty : IRRModel where
  id := W64 0
  header := none
  range := none
  put := none
  deleteRange := none
  txn := none
  compaction := none
  leaseGrant := none
  leaseRevoke := none
  alarm := none
  leaseCheckpoint := none
  authEnable := false
  authDisable := false
  authStatus := false
  authenticate := none
  authUserAdd := none
  authUserDelete := false
  authUserGet := none
  authUserChangePassword := false
  authUserGrantRole := false
  authUserRevokeRole := false
  authUserList := false
  authRoleList := false
  authRoleAdd := none
  authRoleDelete := false
  authRoleGet := none
  authRoleGrantPermission := false
  authRoleRevokePermission := false
  clusterVersionSet := none
  clusterMemberAttrSet := none
  downgradeInfoSet := none
  downgradeVersionTest := false

/-- **`requestV2.Unmarshal`'s wire loop** (`legacy_request.go`): consumes tag-value pairs from `bs`
using the four `protowire` primitives (`consumeTag`, `consumeVarint`, `consumeBytes`,
`consumeFieldValue`), updating `req` on fields `1` (`ID`, varint), `2` (`Method`, bytes),
`3` (`Path`, bytes), and `4` (`Val`, bytes), skipping other fields via `consumeFieldValue`, and
returning `none` on any wire-type mismatch or negative `protowire` return code. -/
def v2UnmarshalLoop [FfiSyntax] (bs : List w8)
    (req : go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2) :
    Option go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2 :=
  if _hbs : bs = [] then some req
  else
    match protowire.consumeTag bs with
    | none => none
    | some (num, typ, nt) =>
      if _hnt : 1 ≤ nt then
        let bs1 := bs.drop nt
        if num = W32 1 then
          if typ ≠ W8 0 then none
          else
            match protowire.consumeVarint bs1 with
            | none => none
            | some (v, nv) =>
              v2UnmarshalLoop (bs1.drop nv) { req with ID' := v }
        else if num = W32 4 ∨ num = W32 3 ∨ num = W32 2 then
          if typ ≠ W8 2 then none
          else
            match protowire.consumeBytes bs1 with
            | none => none
            | some (v, nv) =>
              let req' :=
                if num = W32 2 then { req with Method' := v }
                else if num = W32 3 then { req with Path' := v }
                else if num = W32 4 then { req with Val' := v }
                else req
              v2UnmarshalLoop (bs1.drop nv) req'
        else
          match protowire.consumeFieldValue num typ bs1 with
          | none => none
          | some nv =>
            v2UnmarshalLoop (bs1.drop nv) req
      else none
termination_by bs.length
decreasing_by
  all_goals
    have : bs.length ≠ 0 := by cases bs; exact absurd rfl _hbs; simp
    simp only [List.length_drop]
    omega

/-- **`requestV2.Unmarshal(data)`**: `v2UnmarshalLoop` starting from `requestV2{}`. -/
def v2Decode [FfiSyntax] (bs : List w8) :
    Option go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2 :=
  v2UnmarshalLoop bs zeroValDef

/-- **`re.MatchString(s)`** for a compiled `*regexp.Regexp` of pattern `pat`. -/
opaque regexpMatch : GoString → GoString → Bool

/-- **`path.Dir(p)`**. -/
opaque pathDir : GoString → GoString

/-- **`membership.MustParseMemberIDFromKey(lg, key)`**: the parsed `types.ID` (`uint64`), or `none`
when `MustParseMemberIDFromKey` panics. -/
opaque parseMemberIDFromKey : GoString → Option w64

/-- **`json.Unmarshal([]byte(s), &attributes)`** into a `membership.Attributes`: `(Name, ClientURLs)`
on `nil` error, `none` on error (`toInternalRaftRequest` panics). -/
opaque jsonDecodeAttributes : GoString → Option (GoString × List GoString)

/-- `membership.StoreClusterVersionKey()`: `"/0/version"`. -/
def storeClusterVersionKey [FfiSyntax] : GoString := go!"/0/version"

/-- The pattern of `memberAttributePathRegexp` (`legacy_request.go`):
`path.Join(membership.StoreMembersPrefix, "[[:xdigit:]]{1,16}", "attributes")`. -/
def memberAttrPat [FfiSyntax] : GoString := go!"/0/members/[[:xdigit:]]{1,16}/attributes"

/-- The `InternalRaftRequest` that `requestV2.toInternalRaftRequest` builds for a legacy cluster
version update (`/0/version`). -/
def legacyClusterVersionIRR (id : w64) (ver : GoString) : IRRModel :=
  { irrEmpty with
    header := some { id := id, username := go!"", authRevision := W64 0 }
    clusterVersionSet := some ver }

/-- The `InternalRaftRequest` that `requestV2.toInternalRaftRequest` builds for a legacy member
attributes update (`/0/members/<hex>/attributes`). -/
def legacyMemberAttrIRR (reqID : w64) (m : MemberAttrModel) : IRRModel :=
  { irrEmpty with
    header := some { id := reqID, username := go!"", authRevision := W64 0 }
    clusterMemberAttrSet := some m }

/-- **`requestV2.toInternalRaftRequest(lg)`**: converts a legacy v2 `PUT` request on a member
attributes path or `/0/version` into the corresponding v3 `InternalRaftRequest`, or returns `none`
when `toInternalRaftRequest` panics. -/
def legacyToIRR [FfiSyntax]
    (r : go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2) : Option IRRModel :=
  if r.Method' ≠ go!"PUT" then none
  else if regexpMatch memberAttrPat r.Path' then
    match parseMemberIDFromKey (pathDir r.Path') with
    | none => none
    | some mid =>
      match jsonDecodeAttributes r.Val' with
      | none => none
      | some (name, urls) =>
        some (legacyMemberAttrIRR r.ID' { memberID := mid, name := name, clientURLs := urls })
  else if r.Path' = storeClusterVersionKey then
    some (legacyClusterVersionIRR r.ID' r.Val')
  else none

/-- **What `apply.Apply` decodes from a committed normal entry's bytes `bs`** (`etcd#22634`):
first `proto.Unmarshal(e.Data, &raftReq)` (`irrDecode bs`), and on error
`pbutil.MustUnmarshal(&legacyReq, e.Data)` (`v2Decode bs`) followed by
`legacyReq.toInternalRaftRequest(lg)` (`legacyToIRR`). -/
def entryDecode [FfiSyntax] (bs : List w8) : Option IRRModel :=
  match irrDecode bs with
  | some rq => some rq
  | none => (v2Decode bs).bind legacyToIRR

theorem entryDecode_of_irrDecode [FfiSyntax] {bs : List w8} {rq : IRRModel}
    (h : irrDecode bs = some rq) : entryDecode bs = some rq := by
  simp [entryDecode, h]

theorem entryDecode_of_legacy [FfiSyntax] {bs : List w8}
    {r : go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2} {rq : IRRModel}
    (h1 : irrDecode bs = none) (h2 : v2Decode bs = some r) (h3 : legacyToIRR r = some rq) :
    entryDecode bs = some rq := by
  simp [entryDecode, h1, h2, h3]

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
  else if rq.authUserDelete then .authUserDelete
  else if rq.authUserChangePassword then .authUserChangePassword
  else if rq.authUserGrantRole then .authUserGrantRole
  else if rq.authUserGet.isSome then .authUserGet
  else if rq.authUserRevokeRole then .authUserRevokeRole
  else if rq.authRoleAdd.isSome then .authRoleAdd
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
  [rq.authEnable, rq.authDisable, rq.authUserAdd.isSome, rq.authUserDelete, rq.authUserChangePassword,
    rq.authUserGrantRole, rq.authUserRevokeRole, rq.authRoleAdd.isSome, rq.authRoleGrantPermission,
    rq.authRoleRevokePermission, rq.authRoleDelete, rq.authUserList, rq.authRoleList].or

/-- A KV request: what the txn package applies (and the corrupt applier rejects). -/
def isKVKind : ReqKind → Bool
  | .range | .put | .deleteRange | .txn => true
  | _ => false

theorem irrId_legacyClusterVersionIRR (id : w64) (ver : GoString) :
    irrId (legacyClusterVersionIRR id ver) = some id := by
  simp [irrId, legacyClusterVersionIRR, irrEmpty]

theorem dispatchKind_legacyClusterVersionIRR (id : w64) (ver : GoString) :
    dispatchKind (legacyClusterVersionIRR id ver) = .clusterVersionSet := by
  simp [dispatchKind, legacyClusterVersionIRR]

theorem noSideEffect_legacyClusterVersionIRR (id : w64) (ver : GoString) :
    noSideEffect (legacyClusterVersionIRR id ver) = false := by
  simp [noSideEffect, legacyClusterVersionIRR, irrEmpty]

theorem needAdminPermission_legacyClusterVersionIRR (id : w64) (ver : GoString) :
    needAdminPermission (legacyClusterVersionIRR id ver) = false := by
  simp [needAdminPermission, legacyClusterVersionIRR, irrEmpty]

theorem irrId_legacyMemberAttrIRR (reqID : w64) (m : MemberAttrModel) :
    irrId (legacyMemberAttrIRR reqID m) = some reqID := by
  simp [irrId, legacyMemberAttrIRR, irrEmpty]

theorem dispatchKind_legacyMemberAttrIRR (reqID : w64) (m : MemberAttrModel) :
    dispatchKind (legacyMemberAttrIRR reqID m) = .clusterMemberAttrSet := by
  simp [dispatchKind, legacyMemberAttrIRR, irrEmpty]

theorem noSideEffect_legacyMemberAttrIRR (reqID : w64) (m : MemberAttrModel) :
    noSideEffect (legacyMemberAttrIRR reqID m) = false := by
  simp [noSideEffect, legacyMemberAttrIRR, irrEmpty]

theorem needAdminPermission_legacyMemberAttrIRR (reqID : w64) (m : MemberAttrModel) :
    needAdminPermission (legacyMemberAttrIRR reqID m) = false := by
  simp [needAdminPermission, legacyMemberAttrIRR, irrEmpty]

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

/-- The `*pb.AuthUserAddRequest` `u` (not nil): its `Name`, read-only (unit N4, 2026-10-17). -/
def authUserAddIs (u : Loc) (name : GoString) : IProp GF :=
  iprop(⌜u ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserAddRequest go!"Name" u ↦□ name)

/-- The `*pb.AuthRoleAddRequest` `r` (not nil): its `Name`, read-only (unit N4, 2026-10-17). -/
def authRoleAddIs (r : Loc) (name : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthRoleAddRequest go!"Name" r ↦□ name)

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

instance authUserAddIs_persistent (u : Loc) (name : GoString) : Persistent (authUserAddIs (GF := GF) u name) := by
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
    irrField p go!"AuthUserAdd" (fun l => optReqIs l rq.authUserAdd authUserAddIs) ∗
    irrField p go!"AuthUserDelete" (fun l => presentIs l rq.authUserDelete) ∗
    irrField p go!"AuthUserGet" (fun l => optReqIs l rq.authUserGet authUserGetIs) ∗
    irrField p go!"AuthUserChangePassword" (fun l => presentIs l rq.authUserChangePassword) ∗
    irrField p go!"AuthUserGrantRole" (fun l => presentIs l rq.authUserGrantRole) ∗
    irrField p go!"AuthUserRevokeRole" (fun l => presentIs l rq.authUserRevokeRole) ∗
    irrField p go!"AuthUserList" (fun l => presentIs l rq.authUserList) ∗
    irrField p go!"AuthRoleList" (fun l => presentIs l rq.authRoleList) ∗
    irrField p go!"AuthRoleAdd" (fun l => optReqIs l rq.authRoleAdd authRoleAddIs) ∗
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
    leaseCheckpointIs checkpointIs authenticateIs authUserGetIs authRoleGetIs authUserAddIs
    authRoleAddIs clusterVersionSetIs
    memberAttrSetIs downgradeInfoSetIs
  infer_instance

/-- **The `*InternalRaftRequestWrapper` `r`** (not nil; `apply.Apply` builds it): its request
`rq` and its `SkipRangeExecution` `skip`, read-only. -/
def irrWrapperIs (r : Loc) (rq : IRRModel) (skip : Bool) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ ∃ p : Loc,
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.InternalRaftRequestWrapper
      go!"InternalRaftRequest" r ↦□ p ∗ internalRaftRequestIs p rq ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.InternalRaftRequestWrapper
      go!"SkipRangeExecution" r ↦□ skip)

instance irrWrapperIs_persistent (r : Loc) (rq : IRRModel) (skip : Bool) :
    Persistent (irrWrapperIs (GF := GF) r rq skip) := by
  unfold irrWrapperIs; infer_instance

/-- **An `etcdserverpb.InternalRaftRequest` struct value `v` holds `rq`**: every pointer field
holds its read-only sub-struct (as in `internalRaftRequestIs`, before `v` is stored into `raftReq`). -/
def internalRaftRequestValIs (v : etcdserverpb.InternalRaftRequest) (rq : IRRModel) : IProp GF :=
  iprop(⌜v.ID' = rq.id⌝ ∗
    optReqIs v.Header' rq.header headerIs ∗
    optReqIs v.Range' rq.range txn.rangeRequestIs ∗
    optReqIs v.Put' rq.put txn.putRequestIs ∗
    optReqIs v.DeleteRange' rq.deleteRange txn.deleteRangeRequestIs ∗
    optReqIs v.Txn' rq.txn txn.txnRequestIs ∗
    optReqIs v.Compaction' rq.compaction compactionIs ∗
    optReqIs v.LeaseGrant' rq.leaseGrant leaseGrantIs ∗
    optReqIs v.LeaseRevoke' rq.leaseRevoke leaseRevokeIs ∗
    optReqIs v.Alarm' rq.alarm alarmRequestIs ∗
    optReqIs v.LeaseCheckpoint' rq.leaseCheckpoint leaseCheckpointIs ∗
    presentIs v.AuthEnable' rq.authEnable ∗
    presentIs v.AuthDisable' rq.authDisable ∗
    presentIs v.AuthStatus' rq.authStatus ∗
    optReqIs v.Authenticate' rq.authenticate authenticateIs ∗
    optReqIs v.AuthUserAdd' rq.authUserAdd authUserAddIs ∗
    presentIs v.AuthUserDelete' rq.authUserDelete ∗
    optReqIs v.AuthUserGet' rq.authUserGet authUserGetIs ∗
    presentIs v.AuthUserChangePassword' rq.authUserChangePassword ∗
    presentIs v.AuthUserGrantRole' rq.authUserGrantRole ∗
    presentIs v.AuthUserRevokeRole' rq.authUserRevokeRole ∗
    presentIs v.AuthUserList' rq.authUserList ∗
    presentIs v.AuthRoleList' rq.authRoleList ∗
    optReqIs v.AuthRoleAdd' rq.authRoleAdd authRoleAddIs ∗
    presentIs v.AuthRoleDelete' rq.authRoleDelete ∗
    optReqIs v.AuthRoleGet' rq.authRoleGet authRoleGetIs ∗
    presentIs v.AuthRoleGrantPermission' rq.authRoleGrantPermission ∗
    presentIs v.AuthRoleRevokePermission' rq.authRoleRevokePermission ∗
    optReqIs v.ClusterVersionSet' rq.clusterVersionSet clusterVersionSetIs ∗
    optReqIs v.ClusterMemberAttrSet' rq.clusterMemberAttrSet memberAttrSetIs ∗
    optReqIs v.DowngradeInfoSet' rq.downgradeInfoSet downgradeInfoSetIs ∗
    presentIs v.DowngradeVersionTest' rq.downgradeVersionTest)

instance internalRaftRequestValIs_persistent (v : etcdserverpb.InternalRaftRequest)
    (rq : IRRModel) :
    Persistent (internalRaftRequestValIs (GF := GF) v rq) := by
  unfold internalRaftRequestValIs headerIs compactionIs leaseGrantIs leaseRevokeIs alarmRequestIs
    leaseCheckpointIs checkpointIs authenticateIs authUserGetIs authRoleGetIs authUserAddIs
    authRoleAddIs clusterVersionSetIs memberAttrSetIs downgradeInfoSetIs
  infer_instance

end defs

section valToHeap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- Persisting all fields of `p ↦ v` when `v` satisfies `internalRaftRequestValIs v rq` yields
`internalRaftRequestIs p rq`. -/
theorem internalRaftRequestIs_of_val (p : Loc) (v : etcdserverpb.InternalRaftRequest)
    (rq : IRRModel) :
    iprop(p ↦ v ∗ internalRaftRequestValIs (GF := GF) v rq) ⊢ |==> internalRaftRequestIs p rq := by
  iintro ⟨Hp, #Hval⟩
  ihave ⟨Hp, %Hpn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hp
  iStructNamed Hp
  ipersist ID
  ipersist Header
  ipersist Range
  ipersist Put
  ipersist DeleteRange
  ipersist Txn
  ipersist Compaction
  ipersist LeaseGrant
  ipersist LeaseRevoke
  ipersist Alarm
  ipersist LeaseCheckpoint
  ipersist AuthEnable
  ipersist AuthDisable
  ipersist AuthStatus
  ipersist Authenticate
  ipersist AuthUserAdd
  ipersist AuthUserDelete
  ipersist AuthUserGet
  ipersist AuthUserChangePassword
  ipersist AuthUserGrantRole
  ipersist AuthUserRevokeRole
  ipersist AuthUserList
  ipersist AuthRoleList
  ipersist AuthRoleAdd
  ipersist AuthRoleDelete
  ipersist AuthRoleGet
  ipersist AuthRoleGrantPermission
  ipersist AuthRoleRevokePermission
  ipersist ClusterVersionSet
  ipersist ClusterMemberAttrSet
  ipersist DowngradeInfoSet
  ipersist DowngradeVersionTest
  iunfold internalRaftRequestValIs at Hval
  icases Hval with ⟨%hID, #H0, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9, #H10, #H11, #H12,
    #H13, #H14, #H15, #H16, #H17, #H18, #H19, #H20, #H21, #H22, #H23, #H24, #H25, #H26, #H27,
    #H28, #H29, #H30⟩
  imodintro
  iunfold internalRaftRequestIs
  rw [hID]
  isplitr
  · ipureintro; exact Hpn
  iframe #
  repeat (isplitr; · iexists _; iframe #)
  iexists _; iframe #

end valToHeap

end apply
end EtcdGrove
end Perennial
