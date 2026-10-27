/-
**The auth backend over the buckets** (the auth plan's S1, 2026-10-23; `notes/decisions.md`, "S1 of
the auth plan"): the contracts schema's auth backend (`storage/schema/auth.go`, `auth_users.go`,
`auth_roles.go`) is proved against, and the buckets' contents as the model's state.

**The data** `AuthData`: the three auth buckets (`auth`: the enabled flag at `authEnabled`,
`[]byte{1}` when enabled, the revision at `authRevision`, big-endian; `authUsers`: a user's name
to its message; `authRoles`: a role's name to its message), the bucket snapshot a read
transaction reads. `authWf`: every user and role value an encoding (`auth.userEncode`,
`auth.roleEncode`: `proto.Unmarshal` of anything else is outside its trust-boundary spec, and the
backend panics on an error), the revision 8 bytes (`binary.BigEndian.Uint64` would panic on less).
`enabledOf`, `revisionOf`: what `unsafeReadAuthEnabled` and `unsafeReadAuthRevision` compute.
`userOutD`/`roleOutD`: what `unsafeGetUser`/`unsafeGetRole` return of a bucket. **The buckets
hold the state** `st` (`authBucketsAre st D`): the flag is `st.enabled`, the revision
`st.revision`, the users and roles the state's (`userOutD_are`, `roleOutD_are` turn a bucket's
read into the state's, `auth.userOut`/`auth.roleOut`).

**The contracts** (as `metaReader` and `metaReadTx`, `InvCindex.lean`, for the consistent
index): `authReader r H D`, an `UnsafeReader` whose point reads (`UnsafeRange(b, key, nil, 0)`)
of the three buckets are the snapshot `D`'s under the token `H`, their values readable while `H`
is held (`pointValsA`: the real backend's slices are bbolt's, valid until the reader's `RUnlock`,
`backend.rdB`); `authRTx rt R Held`, a `backend.ReadTx` for the read resource `R`: `RLock` turns
`R` into the token `Held D` of a well-formed snapshot `D`, under which its reads are
`authReader`'s, and `RUnlock` turns it back; `authBE bi R Held`, a `backend.Backend` whose
`ReadTx()` is such a transaction. The real backend meets them through `readTx.RLock`,
`readTx.UnsafeRange` and `readTx.RUnlock` (`rtHeld`, `rtRange_single`) with the auth buckets
tracked (`rbOwn`); the derivation, with the link of the latest history state to the buckets, is
the plan's S4.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex
public import Proof.go_etcd_io.etcd.server.v3.auth.Buckets
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace schema

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

/-! ## The buckets' data -/

/-- The auth buckets' data: `auth`, `authUsers`, `authRoles`. -/
structure AuthData where
  auth : backend.BktData
  users : backend.BktData
  roles : backend.BktData

/-- The `auth` bucket's keys (`AuthEnabledKeyName`, `AuthRevisionKeyName`). -/
def authEnabledKey : GoString := go!"authEnabled"
def authRevisionKey : GoString := go!"authRevision"

/-- Every value of a users bucket is a user record's encoding. -/
def usersWf (m : backend.BktData) : Prop :=
  ∀ n v, m.lookup n = some v → ∃ ur : auth.UserRec, v = auth.userEncode ur

/-- Every value of a roles bucket is a role record's encoding. -/
def rolesWf (m : backend.BktData) : Prop :=
  ∀ n v, m.lookup n = some v → ∃ rr : auth.RoleRec, v = auth.roleEncode rr

/-- The revision of an `auth` bucket, if any, is 8 bytes. -/
def revWf (m : backend.BktData) : Prop :=
  ∀ v, m.lookup authRevisionKey = some v → v.length = 8

/-- The data is well formed. -/
def authWf (D : AuthData) : Prop := usersWf D.users ∧ rolesWf D.roles ∧ revWf D.auth

/-- What `unsafeReadAuthEnabled` computes: exactly one value at `authEnabled`, equal to
`[]byte{1}` (`authEnabled`). -/
def enabledOf (D : AuthData) : Bool := decide (D.auth.lookup authEnabledKey = some [W8 1])

/-- What `unsafeReadAuthRevision` computes: the big-endian value at `authRevision`, `0` if none. -/
def revisionOf (D : AuthData) : w64 :=
  match D.auth.lookup authRevisionKey with
  | some v => beToU64 v
  | none => W64 0

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What `unsafeGetUser(name)` returns of the users bucket `m`: nil if `m` has no such key, else
a message holding the record its value encodes. -/
def userOutD (u : Loc) (m : backend.BktData) (name : GoString) : IProp GF :=
  match m.lookup name with
  | none => iprop(⌜u = null⌝)
  | some v => iprop(∃ ur : auth.UserRec, ⌜v = auth.userEncode ur⌝ ∗ auth.ownUser u ur)

/-- What `unsafeGetRole(name)` returns of the roles bucket `m`. -/
def roleOutD (r : Loc) (m : backend.BktData) (name : GoString) : IProp GF :=
  match m.lookup name with
  | none => iprop(⌜r = null⌝)
  | some v => iprop(∃ rr : auth.RoleRec, ⌜v = auth.roleEncode rr⌝ ∗ auth.ownRole r rr)

/-- `userOutD` with the message as `proto.Unmarshal` returns it (`auth.ownUserX`; the auth plan's
S4c): what schema's `unsafeGetUser` returns. -/
def userOutDX (u : Loc) (m : backend.BktData) (name : GoString) : IProp GF :=
  match m.lookup name with
  | none => iprop(⌜u = null⌝)
  | some v => iprop(∃ ur : auth.UserRec, ⌜v = auth.userEncode ur⌝ ∗ auth.ownUserX u ur)

/-- `roleOutD` with the message as `proto.Unmarshal` returns it (`auth.ownRoleX`). -/
def roleOutDX (r : Loc) (m : backend.BktData) (name : GoString) : IProp GF :=
  match m.lookup name with
  | none => iprop(⌜r = null⌝)
  | some v => iprop(∃ rr : auth.RoleRec, ⌜v = auth.roleEncode rr⌝ ∗ auth.ownRoleX r rr)

theorem userOutDX_persist (u : Loc) (m : backend.BktData) (name : GoString) :
    userOutDX (GF := GF) u m name ⊢ |==> userOutD u m name := by
  unfold userOutDX userOutD
  cases m.lookup name with
  | none => iintro H; imodintro; iexact H
  | some v =>
    iintro ⟨%ur, %H, Hu⟩
    imod auth.ownUserX_persist u ur $$ Hu with Hu
    imodintro; iexists ur; iframe Hu; ipureintro; exact H

theorem roleOutDX_persist (r : Loc) (m : backend.BktData) (name : GoString) :
    roleOutDX (GF := GF) r m name ⊢ |==> roleOutD r m name := by
  unfold roleOutDX roleOutD
  cases m.lookup name with
  | none => iintro H; imodintro; iexact H
  | some v =>
    iintro ⟨%rr, %H, Hr⟩
    imod auth.ownRoleX_persist r rr $$ Hr with Hr
    imodintro; iexists rr; iframe Hr; ipureintro; exact H

/-! ## The buckets hold the state -/

/-- **The auth buckets `D` hold the state `st`**: well formed; the enabled flag `st.enabled`; the
revision `st.revision`, big-endian; a user's value, for each user of `st` and no other, the
encoding of a record of its name whose roles are the state's, sorted; a role's value likewise,
its permissions of a known type the state's. -/
def authBucketsAre (st : auth.AuthState) (D : AuthData) : Prop :=
  authWf D ∧ enabledOf D = st.enabled ∧
  D.auth.lookup authRevisionKey = some (u64Be (W64 st.revision)) ∧
  (∀ n, (D.users.lookup n).isSome ↔ (st.users.lookup n).isSome) ∧
  (∀ n v, D.users.lookup n = some v → ∃ ur : auth.UserRec, v = auth.userEncode ur ∧
    ur.name = n ∧ st.users.lookup n = some ur.roles ∧ ur.roles.Pairwise go.GoStringLt) ∧
  (∀ n, (D.roles.lookup n).isSome ↔ (st.roles.lookup n).isSome) ∧
  (∀ n v, D.roles.lookup n = some v → ∃ rr : auth.RoleRec, v = auth.roleEncode rr ∧
    rr.name = n ∧ st.roles.lookup n = some rr.toRole)

/-- A bucket's read of a user is the state's (`auth.userOut`). The encodings are opaque, so the
record read is the one the predicate names only up to `userEncode`: both records encode to the
same bytes, and the one the predicate names has the state's roles. -/
theorem userOutD_are (st : auth.AuthState) (D : AuthData) (u : Loc) (name : GoString)
    (h : authBucketsAre st D) (hinj : ∀ a b, auth.userEncode a = auth.userEncode b → a = b) :
    userOutD (GF := GF) u D.users name ⊢ auth.userOut u st name := by
  obtain ⟨-, -, -, hu1, hu2, -, -⟩ := h
  unfold userOutD auth.userOut
  cases hl : D.users.lookup name with
  | none =>
    have : st.users.lookup name = none := by
      have := hu1 name; rw [hl] at this; simpa using this
    rw [this]
  | some v =>
    obtain ⟨ur, rfl, hn, hs, hsort⟩ := hu2 name v hl
    rw [hs]
    iintro ⟨%ur', %He, H⟩
    have := hinj _ _ He; subst this
    iexists ur
    iframe H
    ipureintro; exact ⟨hn, rfl, hsort⟩

theorem roleOutD_are (st : auth.AuthState) (D : AuthData) (r : Loc) (name : GoString)
    (h : authBucketsAre st D) (hinj : ∀ a b, auth.roleEncode a = auth.roleEncode b → a = b) :
    roleOutD (GF := GF) r D.roles name ⊢ auth.roleOut r st name := by
  obtain ⟨-, -, -, -, -, hr1, hr2⟩ := h
  unfold roleOutD auth.roleOut
  cases hl : D.roles.lookup name with
  | none =>
    have : st.roles.lookup name = none := by
      have := hr1 name; rw [hl] at this; simpa using this
    rw [this]
  | some v =>
    obtain ⟨rr, rfl, hn, hs⟩ := hr2 name v hl
    rw [hs]
    iintro ⟨%rr', %He, H⟩
    have := hinj _ _ He; subst this
    iexists rr
    iframe H
    ipureintro; exact ⟨hn, rfl⟩

/-! ## The contracts -/

/-- The values a point read returns (`UnsafeRange(b, key, nil, 0)`, read-only outer slice): none
if the key is absent, else one slice, readable while the token `H` is held (the token lent out
meanwhile: the real backend's slices are bbolt's, valid until the reader's `RUnlock`). -/
def pointValsA (H : IProp GF) (vs : GoSlice) (o : Option GoString) : IProp GF :=
  match o with
  | none => iprop(vs ↦*□ ([] : List GoSlice))
  | some v => iprop(∃ s : GoSlice, vs ↦*□ [s] ∗
      □ (H -∗ ∃ dq : DFrac, s ↦*{dq} v ∗ (s ↦*{dq} v -∗ H)))

instance pointValsA_persistent (H : IProp GF) (vs : GoSlice) (o : Option GoString) :
    Persistent (pointValsA H vs o) := by
  unfold pointValsA; split <;> infer_instance

/-- `r.UnsafeRange(b, key, nil, 0)` on the bucket the global `bv` holds, under the token `H`, reads
the key's entry of the bucket data `m`. -/
def authPointSpec (r : GoInterfaceOk) (bv : GoString) (H : IProp GF) (m : backend.BktData) :
    IProp GF :=
  iprop(∀ (b : GoInterface) (key : GoSlice) (kb : GoString) (dq : DFrac),
    {{ globalAddr bv ↦□ b ∗ H ∗ key ↦*{dq} kb }}
      (App (App (App (App (Val #(methods r.ty go!"UnsafeRange" r.v)) (Val #b)) (Val #key))
        (Val #(slice.nil))) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); H ∗ key ↦*{dq} kb ∗ pointValsA H vs (m.lookup kb) }})

/-- **An `UnsafeReader` over the auth buckets** `D` under the token `H` (persistent): its point
reads of `Auth`, `AuthUsers` and `AuthRoles` are `authPointSpec`'s. -/
def authReader (r : GoInterfaceOk) (H : IProp GF) (D : AuthData) : IProp GF :=
  iprop(□ authPointSpec r go_etcd_io.etcd.server.v3.storage.schema.Auth H D.auth ∗
    □ authPointSpec r go_etcd_io.etcd.server.v3.storage.schema.AuthUsers H D.users ∗
    □ authPointSpec r go_etcd_io.etcd.server.v3.storage.schema.AuthRoles H D.roles)

instance authReader_persistent (r : GoInterfaceOk) (H : IProp GF) (D : AuthData) :
    Persistent (authReader r H D) := by
  unfold authReader; infer_instance

/-- **A `backend.ReadTx` over the auth buckets** `rt`, for the read resource `R` (persistent):
`RLock()` turns `R` into the token `Held D` of a well-formed snapshot `D`, under which its reads
are `authReader`'s, and `RUnlock()` turns the token back into `R`. -/
def authRTx (rt : GoInterfaceOk) (R : IProp GF) (Held : AuthData → IProp GF) : IProp GF :=
  iprop(□ ({{ R }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
      {{ RET #(); ∃ D : AuthData, ⌜authWf D⌝ ∗ Held D ∗ authReader rt (Held D) D }}) ∗
    □ (∀ D : AuthData,
      {{ Held D }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); R }}))

instance authRTx_persistent (rt : GoInterfaceOk) (R : IProp GF) (Held : AuthData → IProp GF) :
    Persistent (authRTx rt R Held) := by
  unfold authRTx; infer_instance

/-- **A `backend.Backend` over the auth buckets** `bi` (persistent): `ReadTx()` returns an
`authRTx` for `R`. -/
def authBE (bi : GoInterfaceOk) (R : IProp GF) (Held : AuthData → IProp GF) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
    {{ (rt : GoInterface), RET #rt;
        ∃ rti : GoInterfaceOk, ⌜rt = GoInterface.ok rti⌝ ∗ authRTx rti R Held }}))

instance authBE_persistent (bi : GoInterfaceOk) (R : IProp GF) (Held : AuthData → IProp GF) :
    Persistent (authBE bi R Held) := by
  unfold authBE; infer_instance

end defs

section fields
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&atx.<f>` (a `*authReadTx`). -/
abbrev atxF (f : GoString) (atx : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authReadTx f atx

/-- `&abe.<f>` (a `*authBackend`). -/
abbrev abeF (f : GoString) (abe : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend f abe

end fields

end schema
end EtcdGrove
end Perennial
