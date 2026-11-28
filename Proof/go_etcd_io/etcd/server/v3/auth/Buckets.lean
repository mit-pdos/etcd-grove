/-
**The auth backend's records** (the auth plan's S1, 2026-10-23; `notes/auth-plan.md`,
`notes/decisions.md`, "S1 of the auth plan"): what the auth backend (`storage/schema/auth.go`,
`auth_users.go`, `auth_roles.go`) stores in the `authUsers` and `authRoles` buckets, as data. An
`authpb.User` is a user record (`UserRec`: `Name`, `Password`, the hash, `Roles`, `Options`'s
`NoPassword`), an `authpb.Role` a role record (`RoleRec`: `Name`, `KeyPermission`, each a
permission on the wire, `PermW`: its type as the `int32` the message carries). Their protobuf
encodings are opaque (`userEncode`, `roleEncode`): the trust-boundary specs of `proto.Unmarshal`
on the two messages (`Spec/google_golang_org/protobuf/proto/Unmarshal{User,Role}.lean`) decode
them, as `mvcc.kvEncode` for `mvccpb.KeyValue`.

`ownUser p u` / `ownRole p r`: the message `*authpb.User` / `*authpb.Role` at `p` (owned: the
backend allocates it for the caller) holds the record, its byte fields fresh read-only slices (as
`proto.Unmarshal` leaves them), a role's permissions read-only messages. The model's `User`
(`Model.lean`) is the record's role names; its `Role` the record's permissions, every type
(`permOfWire`, `RoleRec.toRole`: the checks ignore an unknown type, `Perm.grants`).

`userOut u st name` / `roleOut r st name`: what the backend's `UnsafeGetUser(name)` /
`UnsafeGetRole(name)` return of the state `st`: nil if `st` has no such user or role, else a
message holding a record whose roles or permissions are the state's (a user's roles sorted:
`UserGrantRole` sorts them, `hasRootRole` binary-searches them). `authSnap M st`: a read
transaction's state in the mode `M` (`InvAuth.lean`, `authReadTxOk`): auth `off`, never enabled;
`any`, nothing; `on γa`, a recorded state of the history.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Model
public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Proof.google_golang_org.protobuf.proto.UfWire

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-! ## The records -/

/-- `authpb.UserAddOptions`'s schema (`ufWire`): field 1, `no_password`, a `bool` (varint). -/
def userOptsSchema : FieldSchema := [(1, [0])]

/-- The `Options` of a user record as far as its encoding goes beyond `NoPassword`: `none`, no
`Options` message (nil: field 4 absent); `some u`, a message whose unknown fields are the bytes `u`,
valid wire format for it (`ufWire userOptsSchema u`: what protobuf-go's decoder leaves). -/
def userOptsUfOk (ou : Option GoString) : Prop := ∀ u, ou = some u → ufWire userOptsSchema u

theorem userOptsUfOk_none : userOptsUfOk none := fun _ h => by cases h

theorem userOptsUfOk_empty : userOptsUfOk (some []) := fun _ h => by
  cases h; exact ufWire_nil _

/-- An `authpb.User` as data: `Name`, `Password` (the hash), `Roles`, `Options.NoPassword`, and the
rest of the `Options` its encoding carries (`optsUF`: none for a nil `Options`, else the message's
unknown fields, valid wire format: `optsOk`). The unknown fields are part of the record because etcd
keeps them: `UserAdd` stores the request's `Options` message as it is (`Options: options`,
store.go), and a newer client's fields in it come through gRPC's decode, the raft entry's encoding
and back (auth-schema-fix, the review's MAJ-2: without them one record had two encodings, Go test
`zz_review_optsuf_test.go`); a nil `Options` (`UnsafePutUser` of a message without one) is encoded
without field 4, unlike an empty one, hence the `Option`. Every later put of the user copies the
stored message (`UserChangePassword`, `UserGrantRole`, `UserRevokeRole`, `RoleDelete`), so the
stored value carries on. -/
structure UserRec where
  name : GoString
  password : GoString
  roles : List GoString
  noPassword : Bool
  optsUF : Option GoString
  optsOk : userOptsUfOk optsUF

instance : Inhabited UserRec := ⟨⟨[], [], [], false, none, userOptsUfOk_none⟩⟩

/-- An `authpb.Permission` as data, its type as the `int32` on the wire (`permOfWire`). -/
structure PermW where
  ty : w32
  key : GoString
  rangeEnd : GoString
  deriving Inhabited

/-- An `authpb.Role` as data: `Name`, `KeyPermission`. -/
structure RoleRec where
  name : GoString
  perms : List PermW
  deriving Inhabited

/-- The model's permission of one on the wire: its key, range end and type, whatever the type
(`RoleGrantPermission` stores any, `store.go:845-849`; the checks ignore an unknown one,
`Perm.grants`; nomode X-a4). -/
def permOfWire (p : PermW) : Perm := ⟨p.key, p.rangeEnd, p.ty⟩

/-- The model's role of a role record: its permissions as stored, in order. -/
def RoleRec.toRole (r : RoleRec) : Role := r.perms.map permOfWire

/-- The protobuf encoding of a user record (`proto.Marshal`): opaque. -/
opaque userEncode : UserRec → GoString

/-- The protobuf encoding of a role record (`proto.Marshal`): opaque. -/
opaque roleEncode : RoleRec → GoString

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The messages -/

/-- The namespace of the invariants holding the size caches of the auth messages' nested messages
(`userOptsIs`, `ownPermW`, `ownPermS`; auth-schema-srv A3). One namespace for every such cache: a
cell must never carry two such invariants that could be opened together, and none does, since every
invariant here is allocated over the cache of a fresh message (a freshly allocated or decoded one),
once. -/
def pbSizeCacheN : Namespace := nroot .@ "authpb.sizeCache"

/-- The `*authpb.UserAddOptions` `o` holds `NoPassword = b` and the rest `ou` of a user record's
`Options` (`UserRec.optsUF`): nil (`GetNoPassword()` is false; `ou = none`), or a message whose wire
fields are read-only (`NoPassword`, and its unknown fields, a read-only slice holding the bytes `u`,
`ou = some u`) and whose size cache is in an invariant (`pbSizeCacheN`, any value): protobuf-go's
`Marshal` of a message holding it (a `User`, `proto.MarshalUser`; a request, `proto.MarshalIRR`, the
gRPC send) stores it, atomically, and every protobuf-go size pass over it (`Marshal`, `proto.Size`)
stores the same value, the size of its read-only content, so concurrent passes over messages
sharing it agree (auth-schema-srv A3, 2026-11-17: until then the whole struct was `↦□`, the cache
with it, which was false of Go; Go tests `TestMarshalWritesNestedSizeCache`,
`TestConcurrentSharedNested`). Its `state` (protobuf-go's message info, which `ProtoReflect` stores
once, atomically, on any reflective use, `String()` included: `TestStateWrites`) is not held: no
spec reads it, and Marshal and Unmarshal of the parent never touch a nested message's. -/
def userOptsIs (o : Loc) (b : Bool) (ou : Option GoString) : IProp GF :=
  iprop(⌜o = null ∧ b = false ∧ ou = none⌝ ∨
    (⌜o ≠ null⌝ ∗ ∃ (uf : GoSlice) (u : GoString),
      ⌜ou = some u⌝ ∗
      structFieldRef authpb.UserAddOptions go!"NoPassword" o ↦□ b ∗
      structFieldRef authpb.UserAddOptions go!"unknownFields" o ↦□ uf ∗ uf ↦*□ u ∗
      inv pbSizeCacheN (∃ sc : w32, structFieldRef authpb.UserAddOptions go!"sizeCache" o ↦ sc)))

instance userOptsIs_persistent (o : Loc) (b : Bool) (ou : Option GoString) :
    Persistent (userOptsIs (GF := GF) o b ou) := by
  unfold userOptsIs; infer_instance

/-- The `*authpb.UserAddOptions` `o` of a request holds `NoPassword = b`: nil, or a read-only
message whose unknown fields are valid wire format (`userOptsUfOk`: gRPC's decoder produced them;
a client builds its message without any). -/
def userOptsAt (o : Loc) (b : Bool) : IProp GF :=
  iprop(∃ ou : Option GoString, ⌜userOptsUfOk ou⌝ ∗ userOptsIs o b ou)

instance userOptsAt_persistent (o : Loc) (b : Bool) : Persistent (userOptsAt (GF := GF) o b) := by
  unfold userOptsAt; infer_instance

/-- The `*authpb.User` at `p` (owned) holds the record `u`, its byte fields read-only slices, and no
unknown fields (`unknownFields` nil: protobuf-go's `Marshal` copies them into the encoding unchecked,
so garbage there would make the stored bytes fail the next `Unmarshal`; etcd builds its messages
fresh or decodes them from its own bytes, and `proto.Unmarshal` resets the message, leaving the
field nil when the bytes carry no unknown field: the axiom re-review of auth-schema-fix, M1, and
its Go test). The `Options` message's are the record's (`userOptsIs`, `UserRec.optsUF`: they come
from the client's request, valid wire format, and are decoded back unchanged; the review's MAJ-2). -/
def ownUser (p : Loc) (u : UserRec) : IProp GF :=
  iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (name pw roles : GoSlice)
    (o : Loc) (sc : w32),
    p ↦ ({
      state' := st, Name' := name, Password' := pw, Roles' := roles, Options' := o,
      unknownFields' := slice.nil, sizeCache' := sc } : authpb.User) ∗
    name ↦*□ u.name ∗ pw ↦*□ u.password ∗ roles ↦*□ u.roles ∗ userOptsIs o u.noPassword u.optsUF)

/-- The `*authpb.Permission` at `p` (not nil) holds the wire permission `w`, whose key fits a Go slice
with room for one more byte (`NewBytesAffinePoint` appends `"\x00"` to it: a key of `2^63 - 1` bytes
cannot be unmarshalled; the auth plan's S2): its wire fields read-only, its size cache in an
invariant and its `state` not held, as `userOptsIs` (auth-schema-srv A3). The permission of a
request (`roleGrantPermissionReqIs`): its unknown fields are any bytes `ub`, read-only (a client's
newer fields, which `proto.MarshalIRR` copies into the request's encoding; etcd never stores this
message, `ownPermS`). -/
def ownPermW (p : Loc) (w : PermW) : IProp GF :=
  iprop(⌜p ≠ null ∧ w.key.length < 2 ^ 63 - 1⌝ ∗ ∃ (k re uf : GoSlice) (ub : GoString),
    structFieldRef authpb.Permission go!"PermType" p ↦□ w.ty ∗
    structFieldRef authpb.Permission go!"Key" p ↦□ k ∗
    structFieldRef authpb.Permission go!"RangeEnd" p ↦□ re ∗
    structFieldRef authpb.Permission go!"unknownFields" p ↦□ uf ∗ uf ↦*□ ub ∗
    inv pbSizeCacheN (∃ sc : w32, structFieldRef authpb.Permission go!"sizeCache" p ↦ sc) ∗
    k ↦*□ w.key ∗ re ↦*□ w.rangeEnd)

instance ownPermW_persistent (p : Loc) (w : PermW) : Persistent (ownPermW (GF := GF) p w) := by
  unfold ownPermW; infer_instance

/-- **A stored role's permission** `*authpb.Permission` at `p` (not nil): as `ownPermW`, and no unknown
fields (`unknownFields` nil, as `ownRole`'s own: protobuf-go's `Marshal` copies them into the role's
encoding unchecked, so garbage there makes the next `GetRole` panic; the review of auth-schema-fix,
MAJ-1, Go test `zz_review_garbage_test.go`). etcd builds every permission it stores fresh
(`RoleGrantPermission`'s `newPerm`, store.go) or decodes it from a stored role (`proto.Unmarshal` of a
`roleEncode` leaves it nil). Its size cache in an invariant (`proto.MarshalRole` stores it; a
permission may be shared by two roles, or twice by one), its `state` not held (auth-schema-srv A3). -/
def ownPermS (p : Loc) (w : PermW) : IProp GF :=
  iprop(⌜p ≠ null ∧ w.key.length < 2 ^ 63 - 1⌝ ∗ ∃ (k re : GoSlice),
    structFieldRef authpb.Permission go!"PermType" p ↦□ w.ty ∗
    structFieldRef authpb.Permission go!"Key" p ↦□ k ∗
    structFieldRef authpb.Permission go!"RangeEnd" p ↦□ re ∗
    structFieldRef authpb.Permission go!"unknownFields" p ↦□ slice.nil ∗
    inv pbSizeCacheN (∃ sc : w32, structFieldRef authpb.Permission go!"sizeCache" p ↦ sc) ∗
    k ↦*□ w.key ∗ re ↦*□ w.rangeEnd)

instance ownPermS_persistent (p : Loc) (w : PermW) : Persistent (ownPermS (GF := GF) p w) := by
  unfold ownPermS; infer_instance

theorem ownPermS_W (p : Loc) (w : PermW) : ownPermS (GF := GF) p w ⊢ ownPermW p w := by
  unfold ownPermS ownPermW
  iintro ⟨%Hp, %k, %re, #Ht, #Hk, #Hre, #Huf, #Hi, #Hkb, #Hrb⟩
  isplitr
  · ipureintro; exact Hp
  iexists k, re, slice.nil, []
  iframe Ht Hk Hre Huf Hi Hkb Hrb
  iapply (ownSlice_nil (V := w8) DFrac.discard)

/-- The `*authpb.Role` at `p` (owned) holds the record `r`: its name a read-only slice, its
`KeyPermission` a read-only slice of read-only permission messages (`ownPermS`: no unknown fields either), and no unknown fields
(`unknownFields` nil, as `ownUser`). -/
def ownRole (p : Loc) (r : RoleRec) : IProp GF :=
  iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (name kp : GoSlice)
    (ps : List Loc) (sc : w32),
    p ↦ ({
      state' := st, Name' := name, KeyPermission' := kp, unknownFields' := slice.nil,
      sizeCache' := sc } : authpb.Role) ∗
    name ↦*□ r.name ∗ kp ↦*□ ps ∗ ⌜ps.length = r.perms.length⌝ ∗
    [∗list] x ∈ ps.zip r.perms, ownPermS x.1 x.2)

/-! ## The messages as `proto.Unmarshal` returns them: owned (the auth plan's S4c) -/

/-- The `*authpb.User` at `p` as `proto.Unmarshal` returns it (the auth plan's S4c, 2026-10-24):
as `ownUser`, but its `Roles` slice owned with its capacity (Go's decoder allocates it for the
caller: `UserGrantRole` appends to it and sorts it in place); no unknown fields, as `ownUser`
(`proto.Unmarshal` resets the message, and `userEncode` bytes carry none). -/
def ownUserX (p : Loc) (u : UserRec) : IProp GF :=
  iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (name pw roles : GoSlice)
    (o : Loc) (sc : w32),
    p ↦ ({
      state' := st, Name' := name, Password' := pw, Roles' := roles, Options' := o,
      unknownFields' := slice.nil, sizeCache' := sc } : authpb.User) ∗
    name ↦*□ u.name ∗ pw ↦*□ u.password ∗ roles ↦* u.roles ∗
    ownSliceCap GoString roles (DFrac.own 1) ∗ userOptsIs o u.noPassword u.optsUF)

/-- The `*authpb.Permission` at `p` as `proto.Unmarshal` returns it: as `ownPermS` (a stored
role's permission, no unknown fields), but owned (as the decoder leaves it; `RoleGrantPermission`
only reads the existing entries: it keeps those off the new permission's range and appends a fresh
`newPerm`, store.go). -/
def ownPermX (p : Loc) (w : PermW) : IProp GF :=
  iprop(⌜p ≠ null ∧ w.key.length < 2 ^ 63 - 1⌝ ∗ ∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
    (k re : GoSlice) (sc : w32),
    p ↦ ({
      state' := st, PermType' := w.ty, Key' := k, RangeEnd' := re, unknownFields' := slice.nil,
      sizeCache' := sc } : authpb.Permission) ∗
    k ↦*□ w.key ∗ re ↦*□ w.rangeEnd)

/-- The `*authpb.Role` at `p` as `proto.Unmarshal` returns it: as `ownRole`, but its
`KeyPermission` slice owned with its capacity and its permission messages owned
(`RoleGrantPermission` appends to the slice, sorts it, and writes an entry). Fewer than `2^62`
permissions (the auth plan's S4d, 2026-10-24: `sort.Sort`'s bound, after the append): each
permission of the encoding is a length-delimited field, at least a tag byte and a length byte, and
the encoding is a Go slice, below `2^63` bytes; so a decoded record holds fewer than `2^62`. No
unknown fields, as `ownUserX`. -/
def ownRoleX (p : Loc) (r : RoleRec) : IProp GF :=
  iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (name kp : GoSlice)
    (ps : List Loc) (sc : w32),
    p ↦ ({
      state' := st, Name' := name, KeyPermission' := kp, unknownFields' := slice.nil,
      sizeCache' := sc } : authpb.Role) ∗
    name ↦*□ r.name ∗ kp ↦* ps ∗ ownSliceCap Loc kp (DFrac.own 1) ∗
    ⌜ps.length = r.perms.length ∧ r.perms.length < 2 ^ 62⌝ ∗
    [∗list] x ∈ ps.zip r.perms, ownPermX x.1 x.2)

/-- A permission message's size cache into its invariant (`pbSizeCacheN`): the message is fresh. -/
theorem permSizeCache_alloc (E : CoPset) (p : Loc) (sc : w32) :
    structFieldRef authpb.Permission go!"sizeCache" p ↦ sc ⊢ |={E}=>
      inv (GF := GF) pbSizeCacheN (∃ sc : w32, structFieldRef authpb.Permission go!"sizeCache" p ↦ sc) := by
  iintro Hsc
  iapply inv_alloc pbSizeCacheN E
  inext; iexists sc; iexact Hsc

/-- A fresh permission message with no unknown fields, frozen (`newPerm`; a decoded stored one,
`ownPermX_persist`): its wire fields read-only, its size cache into its invariant. -/
theorem ownPermS_freeze (E : CoPset) (p : Loc) (w : PermW)
    (st : google_golang_org.protobuf.internal.impl.MessageState) (k re : GoSlice) (sc : w32) :
    ⌜p ≠ null ∧ w.key.length < 2 ^ 63 - 1⌝ ∗
    p ↦ ({
      state' := st, PermType' := w.ty, Key' := k, RangeEnd' := re, unknownFields' := slice.nil,
      sizeCache' := sc } : authpb.Permission) ∗
    k ↦*□ w.key ∗ re ↦*□ w.rangeEnd ⊢ |={E}=> ownPermS (GF := GF) p w := by
  unfold ownPermS
  iintro ⟨%Hp, Hm, #Hk, #Hre⟩
  iStructNamed Hm
  ipersist PermType
  ipersist Key
  ipersist RangeEnd
  ipersist unknownFields
  imod permSizeCache_alloc E p sc $$ sizeCache with #Hi
  imodintro
  isplitr
  · ipureintro; exact Hp
  iexists k, re
  iframe PermType Key RangeEnd unknownFields Hi Hk Hre

/-- A fresh request permission, frozen (`ownPermW`; gRPC's decoder, a client's literal): its wire
fields read-only, its size cache into its invariant. -/
theorem ownPermW_freeze (E : CoPset) (p : Loc) (w : PermW)
    (st : google_golang_org.protobuf.internal.impl.MessageState) (k re uf : GoSlice) (ub : GoString)
    (sc : w32) :
    ⌜p ≠ null ∧ w.key.length < 2 ^ 63 - 1⌝ ∗
    p ↦ ({
      state' := st, PermType' := w.ty, Key' := k, RangeEnd' := re, unknownFields' := uf,
      sizeCache' := sc } : authpb.Permission) ∗
    uf ↦*□ ub ∗ k ↦*□ w.key ∗ re ↦*□ w.rangeEnd ⊢ |={E}=> ownPermW (GF := GF) p w := by
  unfold ownPermW
  iintro ⟨%Hp, Hm, #Hub, #Hk, #Hre⟩
  iStructNamed Hm
  ipersist PermType
  ipersist Key
  ipersist RangeEnd
  ipersist unknownFields
  imod permSizeCache_alloc E p sc $$ sizeCache with #Hi
  imodintro
  isplitr
  · ipureintro; exact Hp
  iexists k, re, uf, ub
  iframe PermType Key RangeEnd unknownFields Hub Hi Hk Hre

/-- A fresh `Options` message, frozen (`userOptsIs`; gRPC's decoder, a client's literal): its wire
fields read-only, its size cache into its invariant. -/
theorem userOptsIs_freeze (E : CoPset) (o : Loc)
    (st : google_golang_org.protobuf.internal.impl.MessageState) (b : Bool) (uf : GoSlice)
    (u : GoString) (sc : w32) :
    o ↦ ({ state' := st, NoPassword' := b, unknownFields' := uf, sizeCache' := sc } :
      authpb.UserAddOptions) ∗ uf ↦*□ u ⊢ |={E}=> userOptsIs (GF := GF) o b (some u) := by
  unfold userOptsIs
  iintro ⟨Hm, #Hu⟩
  ihave ⟨Hm, %Hn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hm
  iStructNamed Hm
  ipersist NoPassword
  ipersist unknownFields
  imod inv_alloc pbSizeCacheN E
    (iprop(∃ sc : w32, structFieldRef authpb.UserAddOptions go!"sizeCache" o ↦ sc)) $$ [sizeCache]
    with #Hi
  · inext; iexists sc; iexact sizeCache
  imodintro
  iright
  isplitr
  · ipureintro; exact Hn
  iexists uf, u
  isplitr
  · ipureintro; rfl
  iframe NoPassword unknownFields Hu Hi

theorem ownPermX_persist (E : CoPset) (p : Loc) (w : PermW) :
    ownPermX (GF := GF) p w ⊢ |={E}=> ownPermS p w := by
  unfold ownPermX
  iintro ⟨%Hp, %st, %k, %re, %sc, Hm, #Hk, #Hre⟩
  iapply ownPermS_freeze E p w st k re sc
  iframe Hm Hk Hre
  ipureintro; exact Hp

theorem ownUserX_persist (p : Loc) (u : UserRec) : ownUserX (GF := GF) p u ⊢ |==> ownUser p u := by
  unfold ownUserX ownUser
  iintro ⟨%st, %name, %pw, %roles, %o, %sc, Hm, #Hn, #Hpw, Hr, -, #Ho⟩
  ipersist Hr
  imodintro
  iexists st, name, pw, roles, o, sc
  iframe Hm Hn Hpw Hr Ho

theorem ownRoleX_persist (E : CoPset) (p : Loc) (r : RoleRec) :
    ownRoleX (GF := GF) p r ⊢ |={E}=> ownRole p r := by
  unfold ownRoleX ownRole
  iintro ⟨%st, %name, %kp, %ps, %sc, Hm, #Hn, Hkp, -, %Hlen, Hps⟩
  ipersist Hkp
  ihave Hps' : |={E}=> [∗list] x ∈ ps.zip r.perms, ownPermS x.1 x.2 $$ [Hps]
  · iapply BigSepL2.bigSepL_fupd E
    iapply (BigSepL.bigSepL_mono (fun {_ x} _ => ownPermX_persist E x.1 x.2)) $$ Hps
  imod Hps'
  imodintro
  iexists st, name, kp, ps, sc
  iframe Hm Hn Hkp Hps'
  ipureintro; exact Hlen.1

/-! ## What the backend's reads return of a state -/

/-- What `UnsafeGetUser(name)` returns of the state `st`: nil if `st` has no such user, else a
message holding a record of that name whose roles are the state's, sorted, and whose `NoPassword` is
the state's (`AuthState.noPw`; nomode D3 follow-up (a), 2026-11-28). -/
def userOut (u : Loc) (st : AuthState) (name : GoString) : IProp GF :=
  match st.users.lookup name with
  | none => iprop(⌜u = null⌝)
  | some roles => iprop(∃ ur : UserRec,
      ⌜ur.name = name ∧ ur.roles = roles ∧ roles.Pairwise go.GoStringLt ∧
        ur.noPassword = st.noPw name⌝ ∗ ownUser u ur)

/-- What `UnsafeGetRole(name)` returns of the state `st`: nil if `st` has no such role, else a
message holding a record of that name whose permissions of a known type are the state's, which are
sorted by (key, range end) (`permLt`, strictly: distinct ranges; `RoleGrantPermission` sorts by
`permSlice.Less`, nomode X-a1). -/
def roleOut (r : Loc) (st : AuthState) (name : GoString) : IProp GF :=
  match st.roles.lookup name with
  | none => iprop(⌜r = null⌝)
  | some ps => iprop(∃ rr : RoleRec,
      ⌜rr.name = name ∧ rr.toRole = ps ∧ ps.Pairwise permLt⌝ ∗ ownRole r rr)

/-- `userOut` with the message as `proto.Unmarshal` returns it (`ownUserX`): what a batch
transaction's `UnsafeGetUser` returns (the auth plan's S4c). -/
def userOutX (u : Loc) (st : AuthState) (name : GoString) : IProp GF :=
  match st.users.lookup name with
  | none => iprop(⌜u = null⌝)
  | some roles => iprop(∃ ur : UserRec,
      ⌜ur.name = name ∧ ur.roles = roles ∧ roles.Pairwise go.GoStringLt ∧
        ur.noPassword = st.noPw name⌝ ∗ ownUserX u ur)

/-- `roleOut` with the message as `proto.Unmarshal` returns it (`ownRoleX`). -/
def roleOutX (r : Loc) (st : AuthState) (name : GoString) : IProp GF :=
  match st.roles.lookup name with
  | none => iprop(⌜r = null⌝)
  | some ps => iprop(∃ rr : RoleRec,
      ⌜rr.name = name ∧ rr.toRole = ps ∧ ps.Pairwise permLt⌝ ∗ ownRoleX r rr)

theorem userOutX_persist (u : Loc) (st : AuthState) (name : GoString) :
    userOutX (GF := GF) u st name ⊢ |==> userOut u st name := by
  unfold userOutX userOut
  cases st.users.lookup name with
  | none => iintro H; imodintro; iexact H
  | some roles =>
    iintro ⟨%ur, %H, Hu⟩
    imod ownUserX_persist u ur $$ Hu with Hu
    imodintro; iexists ur; iframe Hu; ipureintro; exact H

theorem roleOutX_persist (E : CoPset) (r : Loc) (st : AuthState) (name : GoString) :
    roleOutX (GF := GF) r st name ⊢ |={E}=> roleOut r st name := by
  unfold roleOutX roleOut
  cases st.roles.lookup name with
  | none => iintro H; imodintro; iexact H
  | some ps =>
    iintro ⟨%rr, %H, Hr⟩
    imod ownRoleX_persist E r rr $$ Hr with Hr
    imodintro; iexists rr; iframe Hr; ipureintro; exact H

/-- A read transaction's state `st` in the mode `M`: auth `off`, never enabled; `any`, nothing;
`on γa`, a recorded state of the history. -/
def authSnap (M : AuthMode) (st : AuthState) : IProp GF :=
  match M with
  | .off => iprop(⌜st.enabled = false⌝)
  | .any => iprop(True)
  | .on γa => iprop(∃ i : Nat, authStateAt γa i st)

instance authSnap_persistent (M : AuthMode) (st : AuthState) :
    Persistent (authSnap (GF := GF) M st) := by
  unfold authSnap; cases M <;> infer_instance

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A reader's lower bound of the published index** `i` in the mode `M` (persistent; the auth
plan's E3g): in `on γa`, `authPubLb γa i`; otherwise nothing. -/
def authPubLbM (M : AuthMode) (i : Nat) : IProp GF :=
  match M with
  | .on γa => authPubLb γa i
  | _ => iprop(True)

instance authPubLbM_persistent (M : AuthMode) (i : Nat) :
    Persistent (authPubLbM (GF := GF) M i) := by
  unfold authPubLbM; cases M <;> infer_instance

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


/-- **A state of the mode no older than the index `i`** (persistent; the auth plan's E3g): as
`authSnap`, in `on γa` recorded at an index at least `i`. -/
def authSnapFrom (M : AuthMode) (i : Nat) (st : AuthState) : IProp GF :=
  match M with
  | .off => iprop(⌜st.enabled = false⌝)
  | .any => iprop(True)
  | .on γa => iprop(∃ j : Nat, authStateAt γa j st ∗ ⌜i ≤ j⌝)

instance authSnapFrom_persistent (M : AuthMode) (i : Nat) (st : AuthState) :
    Persistent (authSnapFrom (GF := GF) M i st) := by
  unfold authSnapFrom; cases M <;> infer_instance

/-- A state no older than an index is a state of the mode. -/
theorem authSnapFrom_snap (M : AuthMode) (i : Nat) (st : AuthState) :
    authSnapFrom (GF := GF) M i st ⊢ authSnap M st := by
  cases M
  · simp only [authSnapFrom, authSnap]; iintro H; iexact H
  · simp only [authSnapFrom, authSnap]; iintro -; itrivial
  · simp only [authSnapFrom, authSnap]
    iintro ⟨%j, #H, -⟩
    iexists j; iexact H

/-- Every state of the mode is no older than `0`. -/
theorem authSnapFrom_zero (M : AuthMode) (st : AuthState) :
    authSnap (GF := GF) M st ⊢ authSnapFrom M 0 st := by
  cases M
  · simp only [authSnapFrom, authSnap]; iintro H; iexact H
  · simp only [authSnapFrom, authSnap]; iintro -; itrivial
  · simp only [authSnapFrom, authSnap]
    iintro ⟨%j, #H⟩
    iexists j; iframe H; ipureintro; omega

theorem authSnap_any (st : AuthState) : ⊢ authSnap (GF := GF) .any st := by
  unfold authSnap; ipureintro; trivial

/-! ## A read transaction's view: a state per bucket (2026-11-16)

A read transaction of the auth buckets sees each bucket at a recorded state, not all three at one
(`notes/auth-schema-srv-refuted.md`, "Second refutation"; Q1 (a) of
`notes/auth-schema-srv-scope.md`, approved by the user via etcd-grove-02): the backend's batch
`Unlock` writes a step's puts back to the read buffer and releases the read lock before it commits
the step's deletes, so a reader in between sees the buckets the step put into at the step's state
and those it deleted from at the state before. The `auth` bucket (the flag and the revision) is
only ever put into, so it is never behind the users' bucket. -/

/-- **What a read transaction sees** of the auth buckets: the state its `auth` bucket (the flag
and the revision, `atAuth`), its `authUsers` bucket (`atUsers`) and its `authRoles` bucket
(`atRoles`) are at. -/
structure BkView where
  atAuth : AuthState
  atUsers : AuthState
  atRoles : AuthState

/-- The view of every bucket at one state `st`. -/
def BkView.uni (st : AuthState) : BkView := ⟨st, st, st⟩

/-- **A read transaction's view in the mode `M`, each bucket at a state no older than `i`**
(persistent): in `on γa`, each bucket at a recorded state of the history at an index at least
`i`, the users' and the roles' buckets' indices not above the `auth` bucket's (the `auth` bucket is
only ever put into, so in the backend's window it is at the session's state; `CheckPassword`, the
one reader of two buckets, relies on the users' half; the A0 review's F1: Go gives both); otherwise
each bucket at a state of the mode (`authSnapFrom`). -/
def authViewSnapFrom (M : AuthMode) (i : Nat) (v : BkView) : IProp GF :=
  match M with
  | .on γa => iprop(∃ ja ju jr : Nat, authStateAt γa ja v.atAuth ∗ authStateAt γa ju v.atUsers ∗
      authStateAt γa jr v.atRoles ∗ ⌜i ≤ ju ∧ i ≤ jr ∧ ju ≤ ja ∧ jr ≤ ja⌝)
  | _ => iprop(authSnapFrom M i v.atAuth ∗ authSnapFrom M i v.atUsers ∗ authSnapFrom M i v.atRoles)

instance authViewSnapFrom_persistent (M : AuthMode) (i : Nat) (v : BkView) :
    Persistent (authViewSnapFrom (GF := GF) M i v) := by
  unfold authViewSnapFrom; cases M <;> infer_instance

/-- **A read transaction's view in the mode `M`**: as `authViewSnapFrom` with no lower bound. -/
def authViewSnap (M : AuthMode) (v : BkView) : IProp GF := authViewSnapFrom M 0 v

instance authViewSnap_persistent (M : AuthMode) (v : BkView) :
    Persistent (authViewSnap (GF := GF) M v) := by
  unfold authViewSnap; infer_instance

/-- The users' bucket of a view no older than `i` is a state no older than `i`. -/
theorem authViewSnapFrom_users (M : AuthMode) (i : Nat) (v : BkView) :
    authViewSnapFrom (GF := GF) M i v ⊢ authSnapFrom M i v.atUsers := by
  cases M
  · simp only [authViewSnapFrom]; iintro ⟨-, H, -⟩; iexact H
  · simp only [authViewSnapFrom]; iintro ⟨-, H, -⟩; iexact H
  · simp only [authViewSnapFrom, authSnapFrom]
    iintro ⟨%ja, %ju, %jr, -, #H, -, %Hj⟩
    iexists ju; iframe H; ipureintro; exact Hj.1

/-- The users' bucket of a view is a state of the mode. -/
theorem authViewSnap_users (M : AuthMode) (v : BkView) :
    authViewSnap (GF := GF) M v ⊢ authSnap M v.atUsers := by
  unfold authViewSnap
  iintro H
  iapply authSnapFrom_snap
  iapply authViewSnapFrom_users $$ H

/-- A view no older than `i` is a view. -/
theorem authViewSnapFrom_snap (M : AuthMode) (i : Nat) (v : BkView) :
    authViewSnapFrom (GF := GF) M i v ⊢ authViewSnap M v := by
  unfold authViewSnap
  cases M
  · simp only [authViewSnapFrom]
    iintro ⟨#Ha, #Hu, #Hr⟩
    isplitl []; · iapply authSnapFrom_zero; iapply authSnapFrom_snap $$ Ha
    isplitl []; · iapply authSnapFrom_zero; iapply authSnapFrom_snap $$ Hu
    iapply authSnapFrom_zero; iapply authSnapFrom_snap $$ Hr
  · simp only [authViewSnapFrom, authSnapFrom]
    iintro -; isplitl []; · itrivial
    isplitl [] <;> itrivial
  · simp only [authViewSnapFrom]
    iintro ⟨%ja, %ju, %jr, #Ha, #Hu, #Hr, %Hj⟩
    iexists ja, ju, jr; iframe Ha Hu Hr; ipureintro; omega

end defs

end auth
end EtcdGrove
end Perennial
