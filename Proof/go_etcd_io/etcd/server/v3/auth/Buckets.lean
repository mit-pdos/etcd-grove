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
(`Model.lean`) is the record's role names; its `Role` the record's permissions of a known type
(`permOfWire`: `getMergedPerms` grants nothing for another `PermType`, `RoleRec.toRole`).

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

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-! ## The records -/

/-- An `authpb.User` as data: `Name`, `Password` (the hash), `Roles`, `Options.NoPassword`. -/
structure UserRec where
  name : GoString
  password : GoString
  roles : List GoString
  noPassword : Bool
  deriving Inhabited

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

/-- The model's permission of one on the wire: `READ` (0), `WRITE` (1), `READWRITE` (2); none of
another type (`getMergedPerms` grants nothing for it). -/
def permOfWire (p : PermW) : Option Perm :=
  if p.ty = W32 0 then some ⟨p.key, p.rangeEnd, .read⟩
  else if p.ty = W32 1 then some ⟨p.key, p.rangeEnd, .write⟩
  else if p.ty = W32 2 then some ⟨p.key, p.rangeEnd, .readwrite⟩
  else none

/-- The model's role of a role record: its permissions of a known type. -/
def RoleRec.toRole (r : RoleRec) : Role := r.perms.filterMap permOfWire

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

/-- The `*authpb.UserAddOptions` `o` holds `NoPassword = b`: nil (`GetNoPassword()` is false), or a
read-only message. -/
def userOptsAt (o : Loc) (b : Bool) : IProp GF :=
  iprop(⌜o = null ∧ b = false⌝ ∨
    (⌜o ≠ null⌝ ∗ ∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (uf : GoSlice)
      (sc : w32),
      o ↦□ ({
        state' := st, NoPassword' := b, unknownFields' := uf, sizeCache' := sc } :
        authpb.UserAddOptions)))

instance userOptsAt_persistent (o : Loc) (b : Bool) : Persistent (userOptsAt (GF := GF) o b) := by
  unfold userOptsAt; infer_instance

/-- The `*authpb.User` at `p` (owned) holds the record `u`, its byte fields read-only slices. -/
def ownUser (p : Loc) (u : UserRec) : IProp GF :=
  iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (name pw roles : GoSlice)
    (o : Loc) (uf : GoSlice) (sc : w32),
    p ↦ ({
      state' := st, Name' := name, Password' := pw, Roles' := roles, Options' := o,
      unknownFields' := uf, sizeCache' := sc } : authpb.User) ∗
    name ↦*□ u.name ∗ pw ↦*□ u.password ∗ roles ↦*□ u.roles ∗ userOptsAt o u.noPassword)

/-- The `*authpb.Permission` at `p` (not nil, read-only) holds the wire permission `w`, whose key
fits a Go slice with room for one more byte (`NewBytesAffinePoint` appends `"\x00"` to it: a key
of `2^63 - 1` bytes cannot be unmarshalled; the auth plan's S2). -/
def ownPermW (p : Loc) (w : PermW) : IProp GF :=
  iprop(⌜p ≠ null ∧ w.key.length < 2 ^ 63 - 1⌝ ∗ ∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
    (k re : GoSlice) (uf : GoSlice) (sc : w32),
    p ↦□ ({
      state' := st, PermType' := w.ty, Key' := k, RangeEnd' := re, unknownFields' := uf,
      sizeCache' := sc } : authpb.Permission) ∗
    k ↦*□ w.key ∗ re ↦*□ w.rangeEnd)

instance ownPermW_persistent (p : Loc) (w : PermW) : Persistent (ownPermW (GF := GF) p w) := by
  unfold ownPermW; infer_instance

/-- The `*authpb.Role` at `p` (owned) holds the record `r`: its name a read-only slice, its
`KeyPermission` a read-only slice of read-only permission messages. -/
def ownRole (p : Loc) (r : RoleRec) : IProp GF :=
  iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (name kp : GoSlice)
    (ps : List Loc) (uf : GoSlice) (sc : w32),
    p ↦ ({
      state' := st, Name' := name, KeyPermission' := kp, unknownFields' := uf,
      sizeCache' := sc } : authpb.Role) ∗
    name ↦*□ r.name ∗ kp ↦*□ ps ∗ ⌜ps.length = r.perms.length⌝ ∗
    [∗list] x ∈ ps.zip r.perms, ownPermW x.1 x.2)

/-! ## The messages as `proto.Unmarshal` returns them: owned (the auth plan's S4c) -/

/-- The `*authpb.User` at `p` as `proto.Unmarshal` returns it (the auth plan's S4c, 2026-10-24):
as `ownUser`, but its `Roles` slice owned with its capacity (Go's decoder allocates it for the
caller: `UserGrantRole` appends to it and sorts it in place). -/
def ownUserX (p : Loc) (u : UserRec) : IProp GF :=
  iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (name pw roles : GoSlice)
    (o : Loc) (uf : GoSlice) (sc : w32),
    p ↦ ({
      state' := st, Name' := name, Password' := pw, Roles' := roles, Options' := o,
      unknownFields' := uf, sizeCache' := sc } : authpb.User) ∗
    name ↦*□ u.name ∗ pw ↦*□ u.password ∗ roles ↦* u.roles ∗
    ownSliceCap GoString roles (DFrac.own 1) ∗ userOptsAt o u.noPassword)

/-- The `*authpb.Permission` at `p` as `proto.Unmarshal` returns it: as `ownPermW`, but owned
(`RoleGrantPermission` writes an existing entry's `PermType`). -/
def ownPermX (p : Loc) (w : PermW) : IProp GF :=
  iprop(⌜p ≠ null ∧ w.key.length < 2 ^ 63 - 1⌝ ∗ ∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
    (k re : GoSlice) (uf : GoSlice) (sc : w32),
    p ↦ ({
      state' := st, PermType' := w.ty, Key' := k, RangeEnd' := re, unknownFields' := uf,
      sizeCache' := sc } : authpb.Permission) ∗
    k ↦*□ w.key ∗ re ↦*□ w.rangeEnd)

/-- The `*authpb.Role` at `p` as `proto.Unmarshal` returns it: as `ownRole`, but its
`KeyPermission` slice owned with its capacity and its permission messages owned
(`RoleGrantPermission` appends to the slice, sorts it, and writes an entry). Fewer than `2^62`
permissions (the auth plan's S4d, 2026-10-24: `sort.Sort`'s bound, after the append): each
permission of the encoding is a length-delimited field, at least a tag byte and a length byte, and
the encoding is a Go slice, below `2^63` bytes; so a decoded record holds fewer than `2^62`. -/
def ownRoleX (p : Loc) (r : RoleRec) : IProp GF :=
  iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (name kp : GoSlice)
    (ps : List Loc) (uf : GoSlice) (sc : w32),
    p ↦ ({
      state' := st, Name' := name, KeyPermission' := kp, unknownFields' := uf,
      sizeCache' := sc } : authpb.Role) ∗
    name ↦*□ r.name ∗ kp ↦* ps ∗ ownSliceCap Loc kp (DFrac.own 1) ∗
    ⌜ps.length = r.perms.length ∧ r.perms.length < 2 ^ 62⌝ ∗
    [∗list] x ∈ ps.zip r.perms, ownPermX x.1 x.2)

theorem ownPermX_persist (p : Loc) (w : PermW) : ownPermX (GF := GF) p w ⊢ |==> ownPermW p w := by
  unfold ownPermX ownPermW
  iintro ⟨%Hp, %st, %k, %re, %uf, %sc, Hm, #Hk, #Hre⟩
  ipersist Hm
  imodintro
  isplitr
  · ipureintro; exact Hp
  iexists st, k, re, uf, sc
  iframe Hm Hk Hre

theorem ownUserX_persist (p : Loc) (u : UserRec) : ownUserX (GF := GF) p u ⊢ |==> ownUser p u := by
  unfold ownUserX ownUser
  iintro ⟨%st, %name, %pw, %roles, %o, %uf, %sc, Hm, #Hn, #Hpw, Hr, -, #Ho⟩
  ipersist Hr
  imodintro
  iexists st, name, pw, roles, o, uf, sc
  iframe Hm Hn Hpw Hr Ho

theorem ownRoleX_persist (p : Loc) (r : RoleRec) : ownRoleX (GF := GF) p r ⊢ |==> ownRole p r := by
  unfold ownRoleX ownRole
  iintro ⟨%st, %name, %kp, %ps, %uf, %sc, Hm, #Hn, Hkp, -, %Hlen, Hps⟩
  ipersist Hkp
  ihave Hps' : |==> [∗list] x ∈ ps.zip r.perms, ownPermW x.1 x.2 $$ [Hps]
  · iapply BigSepL.bigSepL_bupd
    iapply (BigSepL.bigSepL_mono (fun {_ x} _ => ownPermX_persist x.1 x.2)) $$ Hps
  imod Hps'
  imodintro
  iexists st, name, kp, ps, uf, sc
  iframe Hm Hn Hkp Hps'
  ipureintro; exact Hlen.1

/-! ## What the backend's reads return of a state -/

/-- What `UnsafeGetUser(name)` returns of the state `st`: nil if `st` has no such user, else a
message holding a record of that name whose roles are the state's, sorted. -/
def userOut (u : Loc) (st : AuthState) (name : GoString) : IProp GF :=
  match st.users.lookup name with
  | none => iprop(⌜u = null⌝)
  | some roles => iprop(∃ ur : UserRec,
      ⌜ur.name = name ∧ ur.roles = roles ∧ roles.Pairwise go.GoStringLt⌝ ∗ ownUser u ur)

/-- What `UnsafeGetRole(name)` returns of the state `st`: nil if `st` has no such role, else a
message holding a record of that name whose permissions of a known type are the state's. -/
def roleOut (r : Loc) (st : AuthState) (name : GoString) : IProp GF :=
  match st.roles.lookup name with
  | none => iprop(⌜r = null⌝)
  | some ps => iprop(∃ rr : RoleRec, ⌜rr.name = name ∧ rr.toRole = ps⌝ ∗ ownRole r rr)

/-- `userOut` with the message as `proto.Unmarshal` returns it (`ownUserX`): what a batch
transaction's `UnsafeGetUser` returns (the auth plan's S4c). -/
def userOutX (u : Loc) (st : AuthState) (name : GoString) : IProp GF :=
  match st.users.lookup name with
  | none => iprop(⌜u = null⌝)
  | some roles => iprop(∃ ur : UserRec,
      ⌜ur.name = name ∧ ur.roles = roles ∧ roles.Pairwise go.GoStringLt⌝ ∗ ownUserX u ur)

/-- `roleOut` with the message as `proto.Unmarshal` returns it (`ownRoleX`). -/
def roleOutX (r : Loc) (st : AuthState) (name : GoString) : IProp GF :=
  match st.roles.lookup name with
  | none => iprop(⌜r = null⌝)
  | some ps => iprop(∃ rr : RoleRec, ⌜rr.name = name ∧ rr.toRole = ps⌝ ∗ ownRoleX r rr)

theorem userOutX_persist (u : Loc) (st : AuthState) (name : GoString) :
    userOutX (GF := GF) u st name ⊢ |==> userOut u st name := by
  unfold userOutX userOut
  cases st.users.lookup name with
  | none => iintro H; imodintro; iexact H
  | some roles =>
    iintro ⟨%ur, %H, Hu⟩
    imod ownUserX_persist u ur $$ Hu with Hu
    imodintro; iexists ur; iframe Hu; ipureintro; exact H

theorem roleOutX_persist (r : Loc) (st : AuthState) (name : GoString) :
    roleOutX (GF := GF) r st name ⊢ |==> roleOut r st name := by
  unfold roleOutX roleOut
  cases st.roles.lookup name with
  | none => iintro H; imodintro; iexact H
  | some ps =>
    iintro ⟨%rr, %H, Hr⟩
    imod ownRoleX_persist r rr $$ Hr with Hr
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

/-- **A reader's lower bound of the published index** `i` in the mode `M` (persistent; the auth
plan's E3g): in `on γa`, `authPubLb γa i`; otherwise nothing. -/
def authPubLbM (M : AuthMode) (i : Nat) : IProp GF :=
  match M with
  | .on γa => authPubLb γa i
  | _ => iprop(True)

instance authPubLbM_persistent (M : AuthMode) (i : Nat) :
    Persistent (authPubLbM (GF := GF) M i) := by
  unfold authPubLbM; cases M <;> infer_instance

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

end defs

end auth
end EtcdGrove
end Perennial
