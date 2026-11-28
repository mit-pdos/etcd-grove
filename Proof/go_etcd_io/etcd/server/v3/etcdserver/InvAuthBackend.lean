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
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model2

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

/-- **`dU` names the record of each user of the users bucket `m`**: the value at a name `n` is the
encoding of `dU n` (auth-schema-srv A6, F-enc, decided by etcd-grove-03: the encodings are opaque and
not known injective, so a read returns the record its caller names, never one recovered from the bytes;
no injectivity of `auth.userEncode` is assumed, ever). Implies `usersWf`, and follows from it by choice
(`usersWf_dec`). -/
def usersDec (m : backend.BktData) (dU : GoString → auth.UserRec) : Prop :=
  ∀ n v, m.lookup n = some v → v = auth.userEncode (dU n)

/-- **`dR` names the record of each role of the roles bucket `m`** (as `usersDec`). -/
def rolesDec (m : backend.BktData) (dR : GoString → auth.RoleRec) : Prop :=
  ∀ n v, m.lookup n = some v → v = auth.roleEncode (dR n)

theorem usersDec_wf {m : backend.BktData} {dU : GoString → auth.UserRec} (h : usersDec m dU) :
    usersWf m := fun n v hl => ⟨dU n, h n v hl⟩

theorem rolesDec_wf {m : backend.BktData} {dR : GoString → auth.RoleRec} (h : rolesDec m dR) :
    rolesWf m := fun n v hl => ⟨dR n, h n v hl⟩

theorem usersWf_dec {m : backend.BktData} (h : usersWf m) : ∃ d, usersDec m d := by
  have H : ∀ n, ∃ x : auth.UserRec, ∀ v, m.lookup n = some v → v = auth.userEncode x := by
    intro n
    cases hl : m.lookup n with
    | none => exact ⟨default, fun v hv => by cases hv⟩
    | some v0 =>
      obtain ⟨x, hx⟩ := h n v0 hl
      exact ⟨x, fun v hv => by cases hv; exact hx⟩
  exact ⟨fun n => Classical.choose (H n), fun n v hl => Classical.choose_spec (H n) v hl⟩

theorem rolesWf_dec {m : backend.BktData} (h : rolesWf m) : ∃ d, rolesDec m d := by
  have H : ∀ n, ∃ x : auth.RoleRec, ∀ v, m.lookup n = some v → v = auth.roleEncode x := by
    intro n
    cases hl : m.lookup n with
    | none => exact ⟨default, fun v hv => by cases hv⟩
    | some v0 =>
      obtain ⟨x, hx⟩ := h n v0 hl
      exact ⟨x, fun v hv => by cases hv; exact hx⟩
  exact ⟨fun n => Classical.choose (H n), fun n v hl => Classical.choose_spec (H n) v hl⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What `unsafeGetUser(name)` returns of the users bucket `m` whose records `dU` names
(`usersDec`): nil if `m` has no such key, else a message holding the record `dU name`. -/
def userOutD (u : Loc) (m : backend.BktData) (name : GoString) (dU : GoString → auth.UserRec) :
    IProp GF :=
  match m.lookup name with
  | none => iprop(⌜u = null⌝)
  | some _ => iprop(auth.ownUser u (dU name))

/-- What `unsafeGetRole(name)` returns of the roles bucket `m` whose records `dR` names. -/
def roleOutD (r : Loc) (m : backend.BktData) (name : GoString) (dR : GoString → auth.RoleRec) :
    IProp GF :=
  match m.lookup name with
  | none => iprop(⌜r = null⌝)
  | some _ => iprop(auth.ownRole r (dR name))

/-- `userOutD` with the message as `proto.Unmarshal` returns it (`auth.ownUserX`; the auth plan's
S4c): what schema's `unsafeGetUser` returns. -/
def userOutDX (u : Loc) (m : backend.BktData) (name : GoString) (dU : GoString → auth.UserRec) :
    IProp GF :=
  match m.lookup name with
  | none => iprop(⌜u = null⌝)
  | some _ => iprop(auth.ownUserX u (dU name))

/-- `roleOutD` with the message as `proto.Unmarshal` returns it (`auth.ownRoleX`). -/
def roleOutDX (r : Loc) (m : backend.BktData) (name : GoString) (dR : GoString → auth.RoleRec) :
    IProp GF :=
  match m.lookup name with
  | none => iprop(⌜r = null⌝)
  | some _ => iprop(auth.ownRoleX r (dR name))

theorem userOutDX_persist (u : Loc) (m : backend.BktData) (name : GoString)
    (dU : GoString → auth.UserRec) :
    userOutDX (GF := GF) u m name dU ⊢ |==> userOutD u m name dU := by
  unfold userOutDX userOutD
  cases m.lookup name with
  | none => iintro H; imodintro; iexact H
  | some v => iintro Hu; iapply auth.ownUserX_persist u (dU name) $$ Hu

theorem roleOutDX_persist (E : CoPset) (r : Loc) (m : backend.BktData) (name : GoString)
    (dR : GoString → auth.RoleRec) :
    roleOutDX (GF := GF) r m name dR ⊢ |={E}=> roleOutD r m name dR := by
  unfold roleOutDX roleOutD
  cases m.lookup name with
  | none => iintro H; imodintro; iexact H
  | some v => iintro Hr; iapply auth.ownRoleX_persist E r (dR name) $$ Hr

/-! ## The buckets hold the state -/

/-- **The auth buckets `D` hold the state `st`**: well formed; the enabled flag `st.enabled`; the
revision `st.revision`, big-endian; a user's value, for each user of `st` and no other, the
encoding of a record of its name whose roles are the state's, sorted; a role's value likewise,
its permissions of a known type the state's, which are sorted by (key, range end) (`auth.permLt`: Go's
`RoleGrantPermission` sorts by `permSlice.Less`, the model's `grantPerms` inserts in that order; nomode X-a1,
2026-11-27; from auth-schema-srv A6's O-a until then, up to order). -/
def authBucketsAre (st : auth.AuthState) (D : AuthData) : Prop :=
  authWf D ∧ enabledOf D = st.enabled ∧
  D.auth.lookup authRevisionKey = some (u64Be (W64 st.revision)) ∧
  (∀ n, (D.users.lookup n).isSome ↔ (st.users.lookup n).isSome) ∧
  (∀ n v, D.users.lookup n = some v → ∃ ur : auth.UserRec, v = auth.userEncode ur ∧
    ur.name = n ∧ st.users.lookup n = some ur.roles ∧ ur.roles.Pairwise go.GoStringLt) ∧
  (∀ n, (D.roles.lookup n).isSome ↔ (st.roles.lookup n).isSome) ∧
  (∀ n v, D.roles.lookup n = some v → ∃ rr : auth.RoleRec, v = auth.roleEncode rr ∧
    rr.name = n ∧ ∃ ps, st.roles.lookup n = some ps ∧ rr.toRole = ps ∧ ps.Pairwise auth.permLt)

/-- **The users bucket `m` holds the state `st`'s users with the records `dU`** (F-enc): a name
is in `m` iff a user of `st`; its value is `dU n`'s encoding, a record of that name whose roles are
the state's, sorted. -/
def usersAt (st : auth.AuthState) (m : backend.BktData) (dU : GoString → auth.UserRec) : Prop :=
  (∀ n, (m.lookup n).isSome ↔ (st.users.lookup n).isSome) ∧
  ∀ n v, m.lookup n = some v → v = auth.userEncode (dU n) ∧ (dU n).name = n ∧
    st.users.lookup n = some (dU n).roles ∧ (dU n).roles.Pairwise go.GoStringLt

/-- **The roles bucket `m` holds the state `st`'s roles with the records `dR`** (F-enc): a name is in `m`
iff a role of `st`; its value is `dR n`'s encoding, a record of that name whose permissions of a known type are
the state's, sorted by (key, range end) (`auth.roleOut`; nomode X-a1, 2026-11-27: until then up to order). -/
def rolesAt (st : auth.AuthState) (m : backend.BktData) (dR : GoString → auth.RoleRec) : Prop :=
  (∀ n, (m.lookup n).isSome ↔ (st.roles.lookup n).isSome) ∧
  ∀ n v, m.lookup n = some v → v = auth.roleEncode (dR n) ∧ (dR n).name = n ∧
    ∃ ps, st.roles.lookup n = some ps ∧ (dR n).toRole = ps ∧ ps.Pairwise auth.permLt

theorem usersAt_dec {st : auth.AuthState} {m : backend.BktData} {dU : GoString → auth.UserRec}
    (h : usersAt st m dU) : usersDec m dU := fun n v hl => (h.2 n v hl).1

theorem rolesAt_dec {st : auth.AuthState} {m : backend.BktData} {dR : GoString → auth.RoleRec}
    (h : rolesAt st m dR) : rolesDec m dR := fun n v hl => (h.2 n v hl).1

/-- The records `authBucketsAre` says exist, named (by choice: no injectivity of the encoding). -/
theorem authBucketsAre_usersAt {st : auth.AuthState} {D : AuthData} (h : authBucketsAre st D) :
    ∃ dU, usersAt st D.users dU := by
  obtain ⟨-, -, -, hu1, hu2, -, -⟩ := h
  have H : ∀ n, ∃ x : auth.UserRec, ∀ v, D.users.lookup n = some v →
      v = auth.userEncode x ∧ x.name = n ∧ st.users.lookup n = some x.roles ∧ x.roles.Pairwise go.GoStringLt := by
    intro n
    cases hl : D.users.lookup n with
    | none => exact ⟨default, fun v hv => by cases hv⟩
    | some v0 =>
      obtain ⟨x, hx⟩ := hu2 n v0 hl
      exact ⟨x, fun v hv => by cases hv; exact hx⟩
  exact ⟨fun n => Classical.choose (H n), hu1, fun n v hl => Classical.choose_spec (H n) v hl⟩

theorem authBucketsAre_rolesAt {st : auth.AuthState} {D : AuthData} (h : authBucketsAre st D) :
    ∃ dR, rolesAt st D.roles dR := by
  obtain ⟨-, -, -, -, -, hu1, hu2⟩ := h
  have H : ∀ n, ∃ x : auth.RoleRec, ∀ v, D.roles.lookup n = some v →
      v = auth.roleEncode x ∧ x.name = n ∧ ∃ ps, st.roles.lookup n = some ps ∧ x.toRole = ps ∧
        ps.Pairwise auth.permLt := by
    intro n
    cases hl : D.roles.lookup n with
    | none => exact ⟨default, fun v hv => by cases hv⟩
    | some v0 =>
      obtain ⟨x, hx⟩ := hu2 n v0 hl
      exact ⟨x, fun v hv => by cases hv; exact hx⟩
  exact ⟨fun n => Classical.choose (H n), hu1, fun n v hl => Classical.choose_spec (H n) v hl⟩

/-- A bucket's read of a user is the state's (`auth.userOut`): the record read is the one `dU`
names (F-enc; until then the record was recovered from the bytes, which needed `userEncode`'s
injectivity). -/
theorem userOutD_are (st : auth.AuthState) (m : backend.BktData) (u : Loc) (name : GoString)
    (dU : GoString → auth.UserRec) (h : usersAt st m dU) :
    userOutD (GF := GF) u m name dU ⊢ auth.userOut u st name := by
  obtain ⟨hu1, hu2⟩ := h
  unfold userOutD auth.userOut
  cases hl : m.lookup name with
  | none =>
    have : st.users.lookup name = none := by
      have := hu1 name; rw [hl] at this; simpa using this
    rw [this]
  | some v =>
    obtain ⟨-, hn, hs, hsort⟩ := hu2 name v hl
    rw [hs]
    iintro H
    iexists dU name
    iframe H
    ipureintro; exact ⟨hn, rfl, hsort⟩

/-- As `userOutD_are`, the message as `proto.Unmarshal` returns it (`auth.userOutX`). -/
theorem userOutDX_are (st : auth.AuthState) (m : backend.BktData) (u : Loc) (name : GoString)
    (dU : GoString → auth.UserRec) (h : usersAt st m dU) :
    userOutDX (GF := GF) u m name dU ⊢ auth.userOutX u st name := by
  obtain ⟨hu1, hu2⟩ := h
  unfold userOutDX auth.userOutX
  cases hl : m.lookup name with
  | none =>
    have : st.users.lookup name = none := by
      have := hu1 name; rw [hl] at this; simpa using this
    rw [this]
  | some v =>
    obtain ⟨-, hn, hs, hsort⟩ := hu2 name v hl
    rw [hs]
    iintro H
    iexists dU name
    iframe H
    ipureintro; exact ⟨hn, rfl, hsort⟩

theorem roleOutD_are (st : auth.AuthState) (m : backend.BktData) (r : Loc) (name : GoString)
    (dR : GoString → auth.RoleRec) (h : rolesAt st m dR) :
    roleOutD (GF := GF) r m name dR ⊢ auth.roleOut r st name := by
  obtain ⟨hr1, hr2⟩ := h
  unfold roleOutD auth.roleOut
  cases hl : m.lookup name with
  | none =>
    have : st.roles.lookup name = none := by
      have := hr1 name; rw [hl] at this; simpa using this
    rw [this]
  | some v =>
    obtain ⟨-, hn, ps, hs, hp⟩ := hr2 name v hl
    rw [hs]
    iintro H
    iexists dR name
    iframe H
    ipureintro; exact ⟨hn, hp⟩

theorem roleOutDX_are (st : auth.AuthState) (m : backend.BktData) (r : Loc) (name : GoString)
    (dR : GoString → auth.RoleRec) (h : rolesAt st m dR) :
    roleOutDX (GF := GF) r m name dR ⊢ auth.roleOutX r st name := by
  obtain ⟨hr1, hr2⟩ := h
  unfold roleOutDX auth.roleOutX
  cases hl : m.lookup name with
  | none =>
    have : st.roles.lookup name = none := by
      have := hr1 name; rw [hl] at this; simpa using this
    rw [this]
  | some v =>
    obtain ⟨-, hn, ps, hs, hp⟩ := hr2 name v hl
    rw [hs]
    iintro H
    iexists dR name
    iframe H
    ipureintro; exact ⟨hn, hp⟩

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

/-- **The bytes `b` of the slice `s`, readable while the token `H` is held** (persistent; the token
lent out meanwhile): a reader's slices (as `pointValsA`'s: the real backend's are bbolt's, valid
until the reader's `RUnlock`, or the batch transaction's, valid until its next commit). -/
def rdCap (H : IProp GF) (s : GoSlice) (b : GoString) : IProp GF :=
  iprop(□ (H -∗ ∃ dq : DFrac, s ↦*{dq} b ∗ (s ↦*{dq} b -∗ H)))

instance rdCap_persistent (H : IProp GF) (s : GoSlice) (b : GoString) :
    Persistent (rdCap H s b) := by
  unfold rdCap; infer_instance

/-- `r.UnsafeForEach(b, fn)` on the bucket the global `bv` holds, under the token `H`, walks the
entries of the bucket data `m` in some order (`es`, a permutation of `bktEnts m`: a read
transaction's walk is bbolt's entries the read buffer lacks, then the buffer's, `rtForEach`; a batch
transaction's is in key order) and returns `nil`, given a visitor `fn` that returns `nil` on every
entry (auth-schema-srv A5, 2026-11-17: schema's `unsafeGetAllUsers`' visitor appends the value). The
visitor goes from `I vis` (the entries walked so far) to `I (vis ++ [e])` for the entry `e` it is
called on, and gets the value's slice readable under `H` (`rdCap`; `H` itself is lent to the walk). -/
def authForEachSpec (r : GoInterfaceOk) (bv : GoString) (H : IProp GF) (m : backend.BktData) :
    IProp GF :=
  iprop(∀ (b : GoInterface) (fn : GoFunc) (I : List backend.Ent → IProp GF),
    {{ globalAddr bv ↦□ b ∗ H ∗ I [] ∗
        □ (∀ (vis : List backend.Ent) (e : backend.Ent) (k v : GoSlice),
          {{ I vis ∗ rdCap H v e.2 }} (App (App (Val #fn) (Val #k)) (Val #v))
          {{ RET #GoInterface.nil; I (vis ++ [e]) }}) }}
      (App (App (Val #(methods r.ty go!"UnsafeForEach" r.v)) (Val #b)) (Val #fn))
    {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ H ∗
        ∃ es : List backend.Ent, ⌜es.Perm (backend.bktEnts m)⌝ ∗ I es }})

/-- **An `UnsafeReader` over the auth buckets** `D` under the token `H` (persistent): its point
reads of `Auth`, `AuthUsers` and `AuthRoles` are `authPointSpec`'s, and its walk of `AuthUsers`
`authForEachSpec`'s (auth-schema-srv A5, 2026-11-17: `unsafeGetAllUsers`). -/
def authReader (r : GoInterfaceOk) (H : IProp GF) (D : AuthData) : IProp GF :=
  iprop(□ authPointSpec r go_etcd_io.etcd.server.v3.storage.schema.Auth H D.auth ∗
    □ authPointSpec r go_etcd_io.etcd.server.v3.storage.schema.AuthUsers H D.users ∗
    □ authPointSpec r go_etcd_io.etcd.server.v3.storage.schema.AuthRoles H D.roles ∗
    □ authForEachSpec r go_etcd_io.etcd.server.v3.storage.schema.AuthUsers H D.users)

instance authReader_persistent (r : GoInterfaceOk) (H : IProp GF) (D : AuthData) :
    Persistent (authReader r H D) := by
  unfold authReader; infer_instance

/-- **A `backend.ReadTx` over the auth buckets** `rt`, for the read resource `R` (persistent):
`RLock()` turns `R` into the token `Held x D` of a well-formed snapshot `D` (in the session of
bbolt's transaction `x`), under which its reads are `authReader`'s, and `RUnlock()` turns the token
back into `R`. `RLock()` borrows a resource `L i` of the caller's and gives it back (auth-schema-srv A6:
the realization lends its share of the backend's open token against the caller's share of the
currency, `authCur γc q`, or its write token), and later credits (auth-schema-srv A6, form: the realization
redeems `R` for a reader slot kept in its invariant, which is not timeless, and observes after the backend's
`RLock`, which takes no step after; schema's `RLock`/`RUnlock` make the credits from their own steps). -/
def authRTx (rt : GoInterfaceOk) (R : IProp GF) {ι : Type} (L : ι → IProp GF)
    (Held : Loc → AuthData → IProp GF) : IProp GF :=
  iprop(□ (∀ i : ι, {{ R ∗ L i ∗ £ 2 }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
      {{ RET #(); ∃ (x : Loc) (D : AuthData), ⌜authWf D⌝ ∗ Held x D ∗ L i ∗
        authReader rt (Held x D) D }}) ∗
    □ (∀ (x : Loc) (D : AuthData),
      {{ Held x D ∗ £ 1 }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); R }}))

instance authRTx_persistent (rt : GoInterfaceOk) (R : IProp GF) {ι : Type} (L : ι → IProp GF)
    (Held : Loc → AuthData → IProp GF) : Persistent (authRTx rt R L Held) := by
  unfold authRTx; infer_instance

/-- **A `backend.Backend` over the auth buckets** `bi` (persistent): `ReadTx()` returns an
`authRTx` for `R`. -/
def authBE (bi : GoInterfaceOk) (R : IProp GF) {ι : Type} (L : ι → IProp GF)
    (Held : Loc → AuthData → IProp GF) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
    {{ (rt : GoInterface), RET #rt;
        ∃ rti : GoInterfaceOk, ⌜rt = GoInterface.ok rti⌝ ∗ authRTx rti R L Held }}))

instance authBE_persistent (bi : GoInterfaceOk) (R : IProp GF) {ι : Type} (L : ι → IProp GF)
    (Held : Loc → AuthData → IProp GF) : Persistent (authBE bi R L Held) := by
  unfold authBE; infer_instance

/-- The entries `unsafeGetAllRoles`' range returns of the roles bucket `m`: `[0x00, 0xff)`, no limit
(`UnsafeRange(AuthRoles, []byte{0}, []byte{0xff}, -1)`, `auth_roles.go`). -/
def rolesRangeEnts (m : backend.BktData) : List backend.Ent :=
  backend.cursorRange (backend.bktEnts m) [W8 0] [W8 255] (W64 (-1))

/-- **The batch transaction's range of the roles bucket** `m` under the token `H` (persistent;
auth-schema-srv A5, 2026-11-17): `r.UnsafeRange(AuthRoles, []byte{0}, []byte{0xff}, -1)` returns
the values of `rolesRangeEnts m`, each readable under `H` (`rdCap`). Only a batch transaction meets
it (a read transaction's range of a non-safe-range bucket panics,
`nonissues/etcd-auth-readtx-getallroles-panics.md`), hence not part of `authReader`. -/
def authRolesRange (r : GoInterfaceOk) (H : IProp GF) (m : backend.BktData) : IProp GF :=
  iprop(∀ (b : GoInterface) (key endKey : GoSlice) (dk de : DFrac),
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthRoles ↦□ b ∗ H ∗
        key ↦*{dk} [W8 0] ∗ endKey ↦*{de} [W8 255] }}
      (App (App (App (App (Val #(methods r.ty go!"UnsafeRange" r.v)) (Val #b)) (Val #key))
        (Val #endKey)) (Val #(W64 (-1))))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); H ∗ key ↦*{dk} [W8 0] ∗ endKey ↦*{de} [W8 255] ∗
        ∃ ss : List GoSlice, vs ↦* ss ∗ ⌜ss.length = (rolesRangeEnts m).length⌝ ∗
          [∗list] x ∈ ss.zip (rolesRangeEnts m), rdCap H x.1 x.2.2 }})

/-- **What `unsafeGetAllUsers` returns of the users bucket `m` whose records `dU` names**
(auth-schema-srv A5; F-enc): a slice of messages, one per entry of `m` in some order (`es`, a
permutation of `bktEnts m`), each holding the record `dU` names for its key (`ownUser`, persisted from
what `proto.Unmarshal` returns); nil when `m` is empty. -/
def usersOutD (s : GoSlice) (m : backend.BktData) (dU : GoString → auth.UserRec) : IProp GF :=
  iprop(∃ (us : List Loc) (es : List backend.Ent), s ↦* us ∗
    ⌜es.Perm (backend.bktEnts m) ∧ us.length = es.length⌝ ∗
    [∗list] x ∈ us.zip es, auth.ownUser x.1 (dU x.2.1))

/-- **What `unsafeGetAllRoles` returns of the entries `es`** (auth-schema-srv A5; `rolesRangeEnts`
of the roles bucket; F-enc): a slice of messages, one per entry, in order, each holding the record
`dR` names for its key (`ownRole`); nil when there is none. -/
def rolesOutD (s : GoSlice) (es : List backend.Ent) (dR : GoString → auth.RoleRec) : IProp GF :=
  iprop(∃ rs : List Loc, s ↦* rs ∗ ⌜rs.length = es.length⌝ ∗
    [∗list] x ∈ rs.zip es, auth.ownRole x.1 (dR x.2.1))

end defs

section fields
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&atx.<f>` (a `*authReadTx`). -/
abbrev atxF (f : GoString) (atx : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authReadTx f atx

/-- `&abt.<f>` (a `*authBatchTx`). -/
abbrev abtF (f : GoString) (abt : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBatchTx f abt

/-- `&abe.<f>` (a `*authBackend`). -/
abbrev abeF (f : GoString) (abe : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend f abe

end fields

end schema
end EtcdGrove
end Perennial
