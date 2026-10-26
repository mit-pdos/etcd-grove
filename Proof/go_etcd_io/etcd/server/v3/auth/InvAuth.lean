/-
The auth store's request side (`server/auth/store.go`, `range_perm_cache.go`; 2026-10-14, unit
P2): its locks, what they hold, and the contracts of the objects it calls through interfaces.
Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The auth store's request side (unit
P2)".

**The store** `as` (`authInv as R M`, persistent):
- `revision`, an atomic (`Revision()` loads it; `commitRevision`/`setRevision`, the admin side,
  add to or store it): its points-to in an invariant of its own, with the mode's verdict on its
  value (`revisionVerdict`: in `on γa` a recorded state's revision; the auth plan's S3,
  2026-10-23);
- `lg`, `tokenProvider`: read-only (written by `NewAuthStore`);
- `beMu` (an `RWMutex`, since the fork's d52eec43e, D22k (A)) guards the backend `be` with its
  contract (`beP`): `Recover` (names-only) writes it under the write lock, the permission checks
  read it under a read lock (`lockedReadTx`), so a check's read transaction is of the backend
  current when it was locked (the server closes a replaced backend only after `Recover`);
- `enabledMu` (an `RWMutex`) guards `enabled` (`enabledP`), with the mode's verdict on the flag
  (`enabledVerdict`: in `off` false, in `on γa` a recorded state's flag; S3);
- `rangePermCacheMu` (an `RWMutex`) guards the permission cache `rangePermCache` (`cacheP`): a
  map from user name to a `*unifiedRangePermissions` whose two interval trees (`readPerms`,
  `writePerms`) are read-only once built (`refreshRangePermCache` replaces the map whole with
  freshly built trees). The auth plan's S2 (2026-10-23): each entry's trees hold lists of
  bytes-affine entries (`permsAt`, `adt.ownIvtB`), and in the mode `on γa` the whole map is of
  one recorded state (`cacheOk`): its keys are the state's users and each entry's intervals are
  the user's permissions' (`cacheEntryIs`, `PermTree.lean`), so that `isRangeOpPermitted`
  computes the model's `coversPoint`/`coversRange` of that state (`cacheVerdict`).

**Contracts** (the store calls them through interfaces; not yet proved of the real objects):
- the backend `be` (`authBackendOk be R M`: schema's `authBackend` in the server): `ReadTx()`
  returns a transaction whose `RLock()` turns the caller's read resource `R` into the held token
  of a state `st` of the mode `M` (`authSnap`, `Buckets.lean`; the auth plan's S1, 2026-10-23:
  until then the token held no state), under which `UnsafeGetUser(name)`/`UnsafeGetRole(name)`
  return the state's user/role (`userOut`/`roleOut`), `UnsafeGetAllUsers()` its users,
  `UnsafeReadAuthEnabled()`/`UnsafeReadAuthRevision()` its flag and revision (`authReaderOk`, the
  `UnsafeAuthReader` interface's methods, which `refreshRangePermCache` takes), and which
  `RUnlock()` turns back into `R` (the backend's own read transaction needs a reader slot,
  `backend.rdTok`, hence `R`); schema's `authReadTx` meets it over the buckets
  (`etcdserver/InvAuthBackend.lean`, `authBucketsAre`);
- the token provider (`tokenProviderOk`): `info(ctx, token, rev)` returns an auth info (nil, or
  one with read-only fields) and a boolean;
- the cached trees are the interval tree's over bytes-affine keys (`adt.ownIvtB`,
  `adt/BytesIvl.lean`: its `Insert`/`Intersects`/`Contains` axioms pending the tree's comparator
  generalization; until S2 the trees were a contract, `ivtQuery`, returning any boolean).

**The mode** `M` (`AuthMode`, `Model.lean`) of the store's contract: what the backend's states are
(`authSnap`), what the flag and the revision are (`enabledP`, `revInv`); the request side's specs
are proved for every mode and return the mode's verdicts (`permVerdict`, `adminVerdict`,
`enabledVerdict`, `revisionVerdict`: `VerdictLemmas.lean` turns the reads into them; S3).

**The write side** (the auth plan's S4, 2026-10-24): the admin side's authority over the history
(`authOwn`, `Steps.lean`) shares the latest state's ghost variable with `revision`'s invariant
(`revCur`), so that the atomic is the latest state's revision; the batch transaction is a contract
(`authBatchTxLk`: its lock token holds the backend's state, its writes move it); the admin side's
write resource (`authWR`) holds the store's user's half of `be`, the write token and its half of
`enabled` (`enabledHalf`; `enabledMu` guards the other half, `enabledP`).

**The readers** (`authRd as R M`): `IsAuthEnabled` read-locks `enabledMu` and the permission checks
also `rangePermCacheMu` and `beMu`, each needing a reader slot (`sync.ownRWMutex`: Perennial bounds
an `RWMutex`'s readers), and the backend's read transaction needs `R`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Proof.go_etcd_io.etcd.server.v3.auth.Buckets
public import Proof.go_etcd_io.etcd.server.v3.auth.Steps
public import Proof.go_etcd_io.etcd.server.v3.auth.Requests
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.auth.Tokens
public import Proof.go_etcd_io.etcd.server.v3.auth.PermTree
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Link
public import Proof.google_golang_org.grpc.metadata.Incoming

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section fields
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&as.<f>` -/
abbrev aF (f : GoString) (st : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.auth.authStore f st

/-- `&p.<f>` (a `*unifiedRangePermissions`) -/
abbrev upF (f : GoString) (p : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.auth.unifiedRangePermissions f p

/-- `&a.<f>` (an `*AuthInfo`) -/
abbrev aiF (f : GoString) (a : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.auth.AuthInfo f a

/-- The store `as` as an `AuthStore` interface value. -/
abbrev authIface (st : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty) #st

end fields

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- An auth info `a`: `nil`, or one whose `Username` and `Revision` are read-only. -/
def authInfoRO (a : Loc) : IProp GF :=
  iprop(⌜a = null⌝ ∨ ∃ (user : GoString) (rev : w64), ⌜a ≠ null⌝ ∗
    aiF go!"Username" a ↦□ user ∗ aiF go!"Revision" a ↦□ rev)

instance authInfoRO_persistent (a : Loc) : Persistent (authInfoRO (GF := GF) a) := by
  unfold authInfoRO; infer_instance

/-- **A cache entry** `p` (a `*unifiedRangePermissions`, not nil; persistent): its two interval
trees (`*intervalTree`s behind the `IntervalTree` interface), read-only, holding the entries `Lr`
(`readPerms`) and `Lw` (`writePerms`) over bytes-affine keys (`adt.ownIvtB`). -/
def permsAt (p : Loc) (Lr Lw : List adt.Entry) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ ∃ (tr tw : Loc),
    upF go!"readPerms" p ↦□ interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tr ∗
    upF go!"writePerms" p ↦□ interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tw ∗
    adt.ownIvtB tr Lr .discard ∗ adt.ownIvtB tw Lw .discard)

set_option synthInstance.maxSize 512 in
instance permsAt_persistent (p : Loc) (Lr Lw : List adt.Entry) :
    Persistent (permsAt (GF := GF) p Lr Lw) := by
  unfold permsAt; infer_instance

/-- The entry's trees' lists for the user `u` at the state `st` (`getMergedPerms`): the user
exists, and the lists' intervals are, as multisets (the tree orders them), the intervals of the
user's permissions granting reads, resp. writes (`ivlsOf`, `PermTree.lean`). -/
def cacheEntryIs (st : AuthState) (u : GoString) (Lr Lw : List adt.Entry) : Prop :=
  ∃ roles, st.users !! u = some roles ∧
    (Lr.map Prod.fst).Perm (ivlsOf .read (userPerms st roles)) ∧
    (Lw.map Prod.fst).Perm (ivlsOf .write (userPerms st roles))

/-- **The cache's map** `Mp` in the mode `M` (persistent): every entry a `permsAt`; in `on γa`,
all of one recorded state `sta` (`refreshRangePermCache` builds the map from one transaction):
the map's keys are `sta`'s users and each entry's trees hold its user's permissions
(`cacheEntryIs`). -/
def cacheOk (M : AuthMode) (Mp : GMap GoString Loc) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (i : Nat) (sta : AuthState), authStateAt γa i sta ∗
      ⌜∀ u, (Mp !! u).isSome ↔ (sta.users !! u).isSome⌝ ∗
      [∗map] u ↦ p ∈ Mp, ∃ Lr Lw, permsAt p Lr Lw ∗ ⌜cacheEntryIs sta u Lr Lw⌝)
  | _ => iprop([∗map] _u ↦ p ∈ Mp, ∃ Lr Lw, permsAt p Lr Lw)

set_option synthInstance.maxSize 512 in
instance cacheOk_persistent (M : AuthMode) (Mp : GMap GoString Loc) :
    Persistent (cacheOk (GF := GF) M Mp) := by
  unfold cacheOk; cases M <;> infer_instance

/-- **`isRangeOpPermitted`'s verdict** `b` in the mode `M` for the user `user` on `[k, e)` with
the permission type `pt` (persistent): `on γa`, a recorded state in which the user's permissions
of the type cover the point (`e` empty: `checkKeyPoint`) or the range (`checkKeyInterval`)
exactly when the check passed, for a request with a non-empty key and a range that is open-ended
or proper, of a state whose permissions' keys are non-empty (`permKeysOk`, what
`isValidPermissionRange` enforces on grants); a user absent from that state is the check
refusing. In the other modes nothing. -/
def cacheVerdict (M : AuthMode) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (b : Bool) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (i : Nat) (sta : AuthState), authStateAt γa i sta ∗
      ⌜k ≠ [] → (e = [] ∨ isOpenEnded e ∨ go.GoStringLt k e) → permKeysOk sta →
        (b = true ↔ ∃ roles, sta.users !! user = some roles ∧
          (if e = [] then coversPoint sta roles (permOp pt) k
            else coversRange sta roles (permOp pt) k e))⌝)
  | _ => iprop(True)

instance cacheVerdict_persistent (M : AuthMode) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (b : Bool) :
    Persistent (cacheVerdict (GF := GF) M user k e pt b) := by
  unfold cacheVerdict; cases M <;> infer_instance

/-- A cache entry's model in the mode `M`: `on γa`, a recorded state whose user's permissions the
entry's trees hold (`cacheEntryIs`); else nothing. -/
def entryVerdict (M : AuthMode) (user : GoString) (Lr Lw : List adt.Entry) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (i : Nat) (sta : AuthState), authStateAt γa i sta ∗ ⌜cacheEntryIs sta user Lr Lw⌝)
  | _ => iprop(True)

instance entryVerdict_persistent (M : AuthMode) (user : GoString) (Lr Lw : List adt.Entry) :
    Persistent (entryVerdict (GF := GF) M user Lr Lw) := by
  unfold entryVerdict; cases M <;> infer_instance

/-- The cache's entry of a user: its trees' lists, with their model in the mode. -/
theorem cacheOk_lookup (M : AuthMode) (Mp : GMap GoString Loc) (user : GoString) (p : Loc)
    (h : Mp !! user = some p) :
    cacheOk (GF := GF) M Mp ⊢ ∃ Lr Lw, permsAt p Lr Lw ∗ entryVerdict M user Lr Lw := by
  cases M with
  | on γa =>
    unfold cacheOk entryVerdict
    iintro ⟨%i, %sta, #Hst, %Hdom, Hall⟩
    ihave #Hp := BigSepM.bigSepM_lookup (Φ := fun (u : GoString) (p : Loc) =>
      iprop(∃ Lr Lw, permsAt (GF := GF) p Lr Lw ∗ ⌜cacheEntryIs sta u Lr Lw⌝)) h $$ Hall
    icases Hp with ⟨%Lr, %Lw, #Hp, %Hent⟩
    iexists Lr, Lw
    iframe Hp
    iexists i, sta
    iframe Hst
    ipureintro; exact Hent
  | off =>
    unfold cacheOk entryVerdict
    iintro Hall
    ihave #Hp := BigSepM.bigSepM_lookup (Φ := fun (_ : GoString) (p : Loc) =>
      iprop(∃ Lr Lw, permsAt (GF := GF) p Lr Lw)) h $$ Hall
    icases Hp with ⟨%Lr, %Lw, #Hp⟩
    iexists Lr, Lw
    iframe Hp
  | any =>
    unfold cacheOk entryVerdict
    iintro Hall
    ihave #Hp := BigSepM.bigSepM_lookup (Φ := fun (_ : GoString) (p : Loc) =>
      iprop(∃ Lr Lw, permsAt (GF := GF) p Lr Lw)) h $$ Hall
    icases Hp with ⟨%Lr, %Lw, #Hp⟩
    iexists Lr, Lw
    iframe Hp

/-- No entry for the user: the check refuses, and in `on γa` the recorded state has no such user. -/
theorem cacheOk_absent (M : AuthMode) (Mp : GMap GoString Loc) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (h : Mp !! user = none) :
    cacheOk (GF := GF) M Mp ⊢ cacheVerdict M user k e pt false := by
  cases M with
  | on γa =>
    unfold cacheOk cacheVerdict
    iintro ⟨%i, %sta, #Hst, %Hdom, -⟩
    iexists i, sta
    iframe Hst
    ipureintro
    intro _ _ _
    have hu : sta.users !! user = none := by
      have hd := Hdom user
      rw [h] at hd
      cases hs : sta.users !! user with
      | none => rfl
      | some r => rw [hs] at hd; simp at hd
    simp only [hu, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro _ hr; cases hr
  | off => unfold cacheVerdict; iintro -; itrivial
  | any => unfold cacheVerdict; iintro -; itrivial

/-- **The check's result over the entry's trees is the verdict**: the point query or the
coverage of the queried interval over the tree of the permission type (`checkKeyPoint`,
`checkKeyInterval`), for a request with a non-empty key and an empty, open-ended or proper range,
is the model's `coversPoint`/`coversRange` of the entry's state (`PermTree.lean`). -/
theorem cacheVerdict_entry (M : AuthMode) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (b : Bool) (Lr Lw : List adt.Entry)
    (hpt : pt = W32 0 ∨ pt = W32 1)
    (hb : k ≠ [] → (e = [] ∨ isOpenEnded e ∨ go.GoStringLt k e) →
      (b = true ↔ if e = [] then ∃ z ∈ (if pt = W32 0 then Lr else Lw), adt.inIvl z.1 k
        else ∀ x, adt.inIvl (queryIvl k e) x →
          ∃ z ∈ (if pt = W32 0 then Lr else Lw), adt.inIvl z.1 x)) :
    entryVerdict (GF := GF) M user Lr Lw ⊢ cacheVerdict M user k e pt b := by
  cases M with
  | on γa =>
    unfold entryVerdict cacheVerdict
    iintro ⟨%i, %sta, #Hst, %Hent⟩
    iexists i, sta
    iframe Hst
    ipureintro
    intro hk hr hkeys
    obtain ⟨roles, hroles, hLr, hLw⟩ := Hent
    rw [hb hk hr]
    -- the tree of the type holds the intervals of the permissions granting the operation
    have hL : ((if pt = W32 0 then Lr else Lw).map Prod.fst).Perm
        (ivlsOf (permOp pt) (userPerms sta roles)) := by
      unfold permOp
      rcases hpt with rfl | rfl
      · simp only [↓reduceIte]; exact hLr
      · rw [if_neg (by word), if_neg (by word)]; exact hLw
    have hiff : ∀ roles', sta.users !! user = some roles' ↔ roles' = roles := by
      intro roles'; rw [hroles]; constructor
      · intro h; cases h; rfl
      · rintro rfl; rfl
    simp only [hiff, exists_eq_left]
    by_cases he : e = []
    · simp only [he, ↓reduceIte]
      rw [coversPoint_iff sta roles (permOp pt) k hkeys]
      exact exists_inIvl_perm hL k
    · simp only [he, ↓reduceIte]
      rw [coversRange_iff sta roles (permOp pt) k e hk he hkeys]
      constructor
      · intro H x hx; exact (exists_inIvl_perm hL x).1 (H x hx)
      · intro H x hx; exact (exists_inIvl_perm hL x).2 (H x hx)
  | off => unfold cacheVerdict; iintro -; itrivial
  | any => unfold cacheVerdict; iintro -; itrivial

theorem cacheVerdict_any (user k e : GoString) (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type)
    (b : Bool) : ⊢ cacheVerdict (GF := GF) .any user k e pt b := by
  unfold cacheVerdict; itrivial

theorem cacheVerdict_off (user k e : GoString) (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type)
    (b : Bool) : ⊢ cacheVerdict (GF := GF) .off user k e pt b := by
  unfold cacheVerdict; itrivial

/-- What `enabledMu` guards at `q` in the mode `M`: half of `enabled` (the other half is the
admin side's, `enabledHalf`: `UserDelete`, `UserRevokeRole` and `RoleDelete` read the flag
outside the lock, in the apply thread, which alone writes it, under the lock, with both halves;
S4), a recorded state's flag (`enabledVerdict`: in `off` false, in `on γa` some recorded state's;
the auth plan's S3). -/
def enabledP (st : Loc) (M : AuthMode) (q : Qp) : IProp GF :=
  iprop(∃ b : Bool, aF go!"enabled" st ↦{DFrac.own q.half} b ∗ enabledVerdict M b)

/-- **The admin side's half of `enabled`** (S4): the flag at half, with its verdict. -/
def enabledHalf (st : Loc) (M : AuthMode) : IProp GF :=
  iprop(∃ b : Bool, aF go!"enabled" st ↦{DFrac.own (1 : Qp).half} b ∗ enabledVerdict M b)

/-- **The admin side's half of `enabled` at `b`** (the auth plan's E2r): `enabledHalf` with its
value exposed, for the apply thread's checks (`IsAuthEnabled.specL`: the guard's half agrees). -/
def flagAt (st : Loc) (b : Bool) : IProp GF :=
  aF go!"enabled" st ↦{DFrac.own (1 : Qp).half} b

theorem enabledHalf_flagAt (st : Loc) (M : AuthMode) :
    enabledHalf (GF := GF) st M ⊢ ∃ b : Bool, flagAt st b ∗ enabledVerdict M b := by
  unfold enabledHalf flagAt
  iintro ⟨%b, H, #Hv⟩
  iexists b; iframe H Hv

theorem flagAt_enabledHalf (st : Loc) (M : AuthMode) (b : Bool) :
    flagAt (GF := GF) st b ∗ enabledVerdict M b ⊢ enabledHalf st M := by
  unfold enabledHalf flagAt
  iintro ⟨H, #Hv⟩
  iexists b; iframe H Hv

/-- The `*AuthInfo` `a` at `dq` holds `ai`: `none`, a `nil` pointer; `some info`, the message. -/
def authInfoAt (a : Loc) (dq : DFrac) (ai : Option AuthInfo) : IProp GF :=
  match ai with
  | none => iprop(⌜a = null⌝)
  | some info => iprop(a ↦{dq} info)

/-- What `rangePermCacheMu` guards at `q` in the mode `M`: half of the field `rangePermCache`
(the other half is the admin side's, `cacheHalf`: only the apply thread replaces the map,
`refreshRangePermCache`, under the lock, with both halves; the auth plan's E2r, 2026-10-26), the map
it points to, read-only (`refreshRangePermCache` builds a new map and never writes it again), and
its model `cacheOk`. -/
def cacheP (st : Loc) (M : AuthMode) (q : Qp) : IProp GF :=
  iprop(∃ (mp : GoMap) (Mp : GMap GoString Loc), aF go!"rangePermCache" st ↦{DFrac.own q.half} mp ∗
    mp ↦${DFrac.discard} Mp ∗ cacheOk M Mp)

/-- **A cache map of the state `sta`** (persistent): its keys `sta`'s users, each entry the
user's permissions at `sta` (`cacheEntryIs`). -/
def cacheOf (sta : AuthState) (Mp : GMap GoString Loc) : IProp GF :=
  iprop(⌜∀ u, (Mp !! u).isSome ↔ (sta.users !! u).isSome⌝ ∗
    [∗map] u ↦ p ∈ Mp, ∃ Lr Lw, permsAt p Lr Lw ∗ ⌜cacheEntryIs sta u Lr Lw⌝)

set_option synthInstance.maxSize 512 in
instance cacheOf_persistent (sta : AuthState) (Mp : GMap GoString Loc) :
    Persistent (cacheOf (GF := GF) sta Mp) := by
  unfold cacheOf; infer_instance

/-- **The admin side's half of the cache at the state `sta`** (the auth plan's E2r): half of the
field `rangePermCache`, the map it points to (read-only) and the map's model, `sta`'s cache
(`cacheOf`); what `refreshRangePermCache` gives the apply thread back. -/
def cacheAt (st : Loc) (sta : AuthState) : IProp GF :=
  iprop(∃ (mp : GoMap) (Mp : GMap GoString Loc),
    aF go!"rangePermCache" st ↦{DFrac.own (1 : Qp).half} mp ∗ mp ↦${DFrac.discard} Mp ∗ cacheOf sta Mp)

/-- **The admin side's half of the cache** in the mode `M` (the auth plan's E2r; in `authWR`): at
some state of the mode (`authSnap`). -/
def cacheHalf (st : Loc) (M : AuthMode) : IProp GF :=
  iprop(∃ sta : AuthState, cacheAt st sta ∗ authSnap M sta)

theorem cacheHalf_of_at (st : Loc) (M : AuthMode) (sta : AuthState) :
    cacheAt (GF := GF) st sta ⊢ authSnap M sta -∗ cacheHalf st M := by
  iintro H #Hs
  iunfold cacheHalf
  iexists sta
  iframe H Hs

/-- **The reads of an `UnsafeAuthReader`** `ti` (a read or a batch transaction) under the held
token `Hs st` of the state `st`: `UnsafeGetUser(name)` and `UnsafeGetRole(name)` return the
state's user and role (`userOut`, `roleOut`: nil if none, else the message, owned),
`UnsafeReadAuthEnabled()` its flag, `UnsafeReadAuthRevision()` its revision, and
`UnsafeGetAllUsers()` its users (a slice of their messages, the names exactly the state's users,
each once), each keeping the token. -/
def authReaderOk (ti : GoInterfaceOk) (Hs : AuthState → IProp GF) : IProp GF :=
  iprop(□ (∀ (st : AuthState) (name : GoString),
      {{ Hs st }} (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #name))
      {{ (u : Loc), RET #u; Hs st ∗ userOut u st name }}) ∗
    □ (∀ (st : AuthState) (name : GoString),
      {{ Hs st }} (App (Val #(methods ti.ty go!"UnsafeGetRole" ti.v)) (Val #name))
      {{ (r : Loc), RET #r; Hs st ∗ roleOut r st name }}) ∗
    □ (∀ st : AuthState,
      {{ Hs st }} (App (Val #(methods ti.ty go!"UnsafeReadAuthEnabled" ti.v)) (Val #()))
      {{ (b : Bool), RET #b; Hs st ∗ ⌜b = st.enabled⌝ }}) ∗
    □ (∀ st : AuthState,
      {{ Hs st }} (App (Val #(methods ti.ty go!"UnsafeReadAuthRevision" ti.v)) (Val #()))
      {{ (x : w64), RET #x; Hs st ∗ ⌜uint.nat x = st.revision⌝ }}) ∗
    □ (∀ st : AuthState,
      {{ Hs st }} (App (Val #(methods ti.ty go!"UnsafeGetAllUsers" ti.v)) (Val #()))
      {{ (s : GoSlice) (us : List Loc) (names : List GoString), RET #s; Hs st ∗ s ↦* us ∗
          ⌜us.length = names.length ∧ names.Nodup ∧
            ∀ n, n ∈ names ↔ (st.users !! n).isSome⌝ ∗
          [∗list] x ∈ us.zip names, userOut x.1 st x.2 }}))

instance authReaderOk_persistent (ti : GoInterfaceOk) (Hs : AuthState → IProp GF) :
    Persistent (authReaderOk (GF := GF) ti Hs) := by
  unfold authReaderOk; infer_instance

/-- **The transaction's reads under the held token** `Hs st` of the state `st` (the shared part of
`authReadTxOk` and `authReadTxLocked`): the reads (`authReaderOk`), and `RUnlock()` turns the
token back into `R`. -/
def authTxReads (ti : GoInterfaceOk) (R : IProp GF) (Hs : AuthState → IProp GF) : IProp GF :=
  iprop(authReaderOk ti Hs ∗
    □ (∀ st : AuthState,
      {{ Hs st }} (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #())) {{ RET #(); R }}))

instance authTxReads_persistent (ti : GoInterfaceOk) (R : IProp GF) (Hs : AuthState → IProp GF) :
    Persistent (authTxReads (GF := GF) ti R Hs) := by
  unfold authTxReads; infer_instance

/-- **The backend's read transaction** `tx` (an `AuthReadTx`, not nil; a contract) for the read
resource `R` in the mode `M`: `RLock()` turns `R` into the held token `Hs st` of a state `st` of
the mode (`authSnap M st`), under which its reads are the state's (`authTxReads`) and which
`RUnlock()` turns back into `R`; and, for a caller holding the admin side's authority at `hs`
(`authOwn`: outside a batch transaction, so no write is pending), the state is the latest
(`histLast M hs st`; the auth plan's E2r, 2026-10-26: the apply thread, the store's only writer,
reads what its last batch committed; a real backend's `Unlock` writes its batch back to the read
buffer before the next read transaction begins). (The auth plan's S1, 2026-10-23; until then: a
token holding no state, `UnsafeGetUser` returning any pointer.) -/
def authReadTxOk (tx : GoInterface) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗ ∃ Hs : AuthState → IProp GF,
    □ ({{ R }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnap M st }}) ∗
    □ (∀ hs : List AuthState,
      {{ R ∗ authOwn M hs }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnap M st ∗ authOwn M hs ∗ ⌜histLast M hs st⌝ }}) ∗
    authTxReads ti R Hs)

instance authReadTxOk_persistent (tx : GoInterface) (R : IProp GF) (M : AuthMode) :
    Persistent (authReadTxOk (GF := GF) tx R M) := by
  unfold authReadTxOk; infer_instance

/-- **The auth backend** `be` (an `AuthBackend`, not nil; a contract): `ReadTx()` returns a read
transaction (`authReadTxOk`) for `R` in the mode `M`. -/
def authBackendOk (be : GoInterface) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜be = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (tx : GoInterface), RET #tx; authReadTxOk tx R M }}))

instance authBackendOk_persistent (be : GoInterface) (R : IProp GF) (M : AuthMode) :
    Persistent (authBackendOk (GF := GF) be R M) := by
  unfold authBackendOk; infer_instance

/-- **An auth info bound to the token `token`** in the mode `M` (persistent; the auth plan's S5):
not nil, its user (read-only) one the token was issued to (`tokOk`: in `on γa`, `tokIssued`). -/
def infoBound (M : AuthMode) (token : GoString) (a : Loc) : IProp GF :=
  iprop(⌜a ≠ null⌝ ∗ ∃ user : GoString, aiF go!"Username" a ↦□ user ∗ tokOk M token user)

instance infoBound_persistent (M : AuthMode) (token : GoString) (a : Loc) :
    Persistent (infoBound (GF := GF) M token a) := by
  unfold infoBound; infer_instance

/-- **The token a request's context carries** (the auth plan's E2c, 2026-10-25): what
`AuthInfoFromCtx` reads of the context's incoming metadata (`metadata.incomingOf`): the first value
of the key `token` (`rpctypes.TokenFieldNameGRPC`), else of `authorization`
(`TokenFieldNameSwagger`), with a `"Bearer "` prefix trimmed; `none` if the context has no metadata
or neither key. -/
def ctxTokenOf (ctx : GoInterface) : Option GoString :=
  match metadata.incomingOf ctx with
  | none => none
  | some md =>
    match md go!"token" with
    | some (v :: _) => some (strings.trimPrefix v go!"Bearer ")
    | some [] => none
    | none =>
      match md go!"authorization" with
      | some (v :: _) => some (strings.trimPrefix v go!"Bearer ")
      | _ => none

/-- **The auth info the request context `ctx` gives** in the mode `M` (persistent; S5): `nil`, or
one bound to the context's own token (`ctxTokenOf`, the auth plan's E2c, 2026-10-25; until then
"some token"). -/
def ctxBound (M : AuthMode) (ctx : GoInterface) (a : Loc) : IProp GF :=
  iprop(⌜a = null⌝ ∨ ∃ token : GoString, ⌜ctxTokenOf ctx = some token⌝ ∗ infoBound M token a)

instance ctxBound_persistent (M : AuthMode) (ctx : GoInterface) (a : Loc) :
    Persistent (ctxBound (GF := GF) M ctx a) := by
  unfold ctxBound; infer_instance

/-- **An `Authenticate` context** `ctx` in the mode `M` (the auth plan's S5b, 2026-10-24): what
the token providers' `assign` reads of it. Its `Value` method returns, for the key
`AuthenticateParamIndex{}`, a `uint64` raft index `idx`, and for the key
`AuthenticateParamSimpleTokenPrefix{}` a string `pre` (`v3_server.go`'s `Authenticate` puts both
in; other keys are unconstrained), and the caller holds the right to issue the token they make
(`freshOk M (simpleTok pre idx)`: a token is `<prefix>.<raft index>`, issued once; the simple
provider panics on a token issued twice, `assignSimpleTokenToUser`). -/
def authnCtx (M : AuthMode) (ctx : GoInterface) : IProp GF :=
  iprop(∃ (ci : GoInterfaceOk) (idx : w64) (pre : GoString), ⌜ctx = GoInterface.ok ci⌝ ∗
    □ (∀ k : GoInterface,
      {{ True }} (App (Val #(methods ci.ty go!"Value" ci.v)) (Val #k))
      {{ (v : GoInterface), RET #v;
          ⌜(∀ x : AuthenticateParamIndex,
              k = interface.mkOk AuthenticateParamIndex.ty #x → v = interface.mkOk go.uint64 #idx) ∧
           (∀ x : AuthenticateParamSimpleTokenPrefix,
              k = interface.mkOk AuthenticateParamSimpleTokenPrefix.ty #x →
                v = interface.mkOk go.string #pre)⌝ }}) ∗
    freshOk M (simpleTok pre idx))

/-- **The token provider** `tp` (a `TokenProvider`, not nil; a contract) in the mode `M`, with the
admin side's resource `A` (the auth plan's S5d, 2026-10-25):
- `info(ctx, token, rev)` returns an auth info (`authInfoRO`) and a
  boolean; when the boolean is true, the info is bound to the token (`infoBound`: in `on γa`, its
  user is one the token was issued to; the auth plan's S5, 2026-10-24);
- `enable()`, `disable()` and `invalidateUser(name)` return, from `A` and giving it back: the
  admin side's share of the provider (the simple provider's: its keeper field, which
  `invalidateUser` reads outside the provider's mutex; etcd's callers serialize the three:
  `enable`/`disable` under the store's `enabledMu`, `invalidateUser` on the apply thread);
- `assign(ctx, username, rev)` (appended, S5) returns a token and an error; with no error the
  token was issued to `username` (`tokOk`); on an `Authenticate` context (`authnCtx`: its index
  and prefix, and the right to issue the token; S5b).
The simple provider meets it (`auth/TokenSimple.lean`, S5b-S5d) but for `info`'s context premise:
its `info` waits on the raft index its token names and on the context's `Done()`, which this
module (generic in the later credits, Perennial's contexts are not) cannot state; the JWT
provider's binding is its signature's. -/
def tokenProviderOkA (tp : GoInterface) (M : AuthMode) (A : IProp GF) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tp = GoInterface.ok ti⌝ ∗
    □ (∀ (ctx : GoInterface) (token : GoString) (rev : w64),
      {{ True }}
        (App (App (App (Val #(methods ti.ty go!"info" ti.v)) (Val #ctx))
          (Val #token)) (Val #rev))
      {{ (a : Loc) (ok : Bool), RET (PairV #a #ok); authInfoRO a ∗
          (if ok then infoBound M token a else iprop(True)) }}) ∗
    □ ({{ A }} (App (Val #(methods ti.ty go!"enable" ti.v)) (Val #())) {{ RET #(); A }}) ∗
    □ ({{ A }} (App (Val #(methods ti.ty go!"disable" ti.v)) (Val #())) {{ RET #(); A }}) ∗
    □ (∀ name : GoString,
      {{ A }} (App (Val #(methods ti.ty go!"invalidateUser" ti.v)) (Val #name)) {{ RET #(); A }}) ∗
    □ (∀ (ctx : GoInterface) (user : GoString) (rev : w64),
      {{ authnCtx M ctx }}
        (App (App (App (Val #(methods ti.ty go!"assign" ti.v)) (Val #ctx))
          (Val #user)) (Val #rev))
      {{ (t : GoString) (err : GoInterface), RET (PairV #t #err);
          ⌜err ≠ GoInterface.nil⌝ ∨ tokOk M t user }}))

instance tokenProviderOkA_persistent (tp : GoInterface) (M : AuthMode) (A : IProp GF) :
    Persistent (tokenProviderOkA (GF := GF) tp M A) := by
  unfold tokenProviderOkA; infer_instance

/-- **The token provider's contract** (what the store's invariant holds, `authInv`): some admin
resource `A` (`tokenProviderOkA`), whose holder is the store's admin side (`tpAdmin`). -/
def tokenProviderOk (tp : GoInterface) (M : AuthMode) : IProp GF :=
  iprop(∃ (A : IProp GF) (ti : GoInterfaceOk), ⌜tp = GoInterface.ok ti⌝ ∗
    □ (∀ (ctx : GoInterface) (token : GoString) (rev : w64),
      {{ True }}
        (App (App (App (Val #(methods ti.ty go!"info" ti.v)) (Val #ctx))
          (Val #token)) (Val #rev))
      {{ (a : Loc) (ok : Bool), RET (PairV #a #ok); authInfoRO a ∗
          (if ok then infoBound M token a else iprop(True)) }}) ∗
    □ ({{ A }} (App (Val #(methods ti.ty go!"enable" ti.v)) (Val #())) {{ RET #(); A }}) ∗
    □ ({{ A }} (App (Val #(methods ti.ty go!"disable" ti.v)) (Val #())) {{ RET #(); A }}) ∗
    □ (∀ name : GoString,
      {{ A }} (App (Val #(methods ti.ty go!"invalidateUser" ti.v)) (Val #name)) {{ RET #(); A }}) ∗
    □ (∀ (ctx : GoInterface) (user : GoString) (rev : w64),
      {{ authnCtx M ctx }}
        (App (App (App (Val #(methods ti.ty go!"assign" ti.v)) (Val #ctx))
          (Val #user)) (Val #rev))
      {{ (t : GoString) (err : GoInterface), RET (PairV #t #err);
          ⌜err ≠ GoInterface.nil⌝ ∨ tokOk M t user }}))

instance tokenProviderOk_persistent (tp : GoInterface) (M : AuthMode) :
    Persistent (tokenProviderOk (GF := GF) tp M) := by
  unfold tokenProviderOk; infer_instance

/-- What `beMu` guards at `q`: the backend `be` at half the fraction, with its contract
(`Recover` replaces it under the write lock). (D22 receiver epochs, S7c, 2026-10-23: the other half
of `be` is the store's user's, the server's apply thread, `authBeOn`, which `Recover` takes with
the write lock; so the user's half names the backend the store's writes go to. Until then `beMu`
held all of it.) -/
def beP (st : Loc) (R : IProp GF) (M : AuthMode) (q : Qp) : IProp GF :=
  iprop(∃ be : AuthBackend, aF go!"be" st ↦{DFrac.own q.half} be ∗ authBackendOk be R M)

/-- **A locked read transaction** `tx` for the read resource `R` in the mode `M` (what
`lockedReadTx` returns): the held token `Hs sta` of a state `sta` of the mode, under which its
reads are the state's (`authTxReads`) and which `RUnlock()` turns back into `R`. -/
def authReadTxLocked (tx : GoInterface) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗
    ∃ (sta : AuthState) (Hs : AuthState → IProp GF), Hs sta ∗ authSnap M sta ∗ authTxReads ti R Hs)

/-- **A locked read transaction at the latest state** of the admin side's authority `hs` (what
`lockedReadTx` returns to a caller holding `authOwn M hs`; the auth plan's E2r): as
`authReadTxLocked`, the state the latest (`histLast`). -/
def authReadTxLockedL (tx : GoInterface) (R : IProp GF) (M : AuthMode) (hs : List AuthState) :
    IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗
    ∃ (sta : AuthState) (Hs : AuthState → IProp GF), Hs sta ∗ authSnap M sta ∗
      ⌜histLast M hs sta⌝ ∗ authTxReads ti R Hs)

/-- The latest state's revision (S4): in `on γa`, half the ghost variable of the latest state
(`authCurHalf`; the admin side's authority holds the other, `authOwn`), whose revision the atomic
holds; in the other modes nothing. -/
def revCur (M : AuthMode) (r : w64) : IProp GF :=
  match M with
  | .on γa => iprop(∃ st : AuthState, authCurHalf γa st ∗ ⌜uint.nat r = st.revision⌝)
  | _ => iprop(True)

instance revCur_timeless (M : AuthMode) (r : w64) : Timeless (revCur (GF := GF) M r) := by
  unfold revCur authCurHalf; cases M <;> infer_instance

/-- The invariant of `revision` (an atomic) in the mode `M`: a recorded state's revision
(`revisionVerdict`; the auth plan's S3), the latest's (`revCur`; S4). -/
def revInv (st : Loc) (M : AuthMode) : IProp GF :=
  iprop(∃ r : w64, aF go!"revision" st ↦ r ∗ revisionVerdict M r ∗ revCur M r)

/-- **The auth store** at `as` (persistent), its backend's read resource `R`, its mode `M`: the
atomic `revision`'s invariant, the read-only `lg` (not nil) and `tokenProvider` with its contract,
and the guards of its three locks (`beMu`'s holds `be` with its contract in the mode). -/
def authInv (st : Loc) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(⌜st ≠ null⌝ ∗ inv (nroot.@"authRev") (revInv st M) ∗
    (∃ lg : Loc, aF go!"lg" st ↦□ lg ∗ ⌜lg ≠ null⌝) ∗
    sync.isRWMutexGuard (aF go!"beMu" st) (beP st R M) ∗
    (∃ tp : TokenProvider, aF go!"tokenProvider" st ↦□ tp ∗ tokenProviderOk tp M) ∗
    sync.isRWMutexGuard (aF go!"enabledMu" st) (enabledP st M) ∗
    sync.isRWMutexGuard (aF go!"rangePermCacheMu" st) (cacheP st M))

instance authInv_persistent (st : Loc) (R : IProp GF) (M : AuthMode) :
    Persistent (authInv (GF := GF) st R M) := by
  unfold authInv; infer_instance

/-! ## The write side (the auth plan's S4, 2026-10-24) -/

/-- **The batch transaction's lock token** `Lk st X`: the backend's auth buckets hold the state
`st` (pending: the transaction's writes change it), `X` is given back at `Unlock`. The batch
transaction `ti` (an `AuthBatchTx`; a contract, as the lessor's `leaseBatchTx`) with the hook `P
f` (the apply package's: `Lock()` is the backend's `LockInsideApply`, which runs the post-lock
hook, `mvcc.csContract`), the write token `T` (the write-back the real backend's `Unlock` spends,
D14f) and the mode `M`:
- `Lock()`, under the critical-section contract and the token, from the admin side's authority
  `hs`: the token of the state the transaction finds, the latest (`histLast`), and the whole
  authority (`authOwnF`: the lock's share of the history joined, the auth plan's S4f);
- its reads are the state's (`authReaderOk`);
- `UnsafePutUser(u)` of a message holding a record whose roles are sorted (what `userOut`
  promises) and whose name fits a bbolt key (`issues/etcd-auth-useradd-long-name-fatal.md`)
  puts the user (`putUser`; the message kept), `UnsafeDeleteUser(name)` deletes it, likewise the
  roles; `UnsafeSaveAuthEnabled(b)` and `UnsafeSaveAuthRevision(rev)` set the flag and the
  revision;
- `Unlock()`, with the whole authority at a history whose latest state is the token's (the
  admin side appends the step's state before unlocking): `X`, the token and the admin side's
  authority back (the lock keeps its share).
This is the store's view of the backend's contract (`authBatchTxLkR`, which states `Lock()` and
`Unlock()` without the admin side's authority: `authBatchTxLk_of_R`).
The records' sizes are not bounded here (the real backend's put of a record above bbolt's value
bound is fatal: `issues/etcd-auth-record-too-large-fatal.md`, the premise `authRecordsFit` of
`NewAuthStore`'s axiom, which the derivation of this contract from the real backend will take). -/
def authBatchTxLk (ti : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (Lk : AuthState → IProp GF → IProp GF) : IProp GF :=
  iprop(□ (∀ (hs : List AuthState) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post ∗ T ∗ authOwn M hs }}
        (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : AuthState, Lk st Post ∗ authOwnF M hs ∗ ⌜histLast M hs st⌝ }}) ∗
    □ (∀ X : IProp GF, authReaderOk ti (fun st => Lk st X)) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (u : Loc) (ur : UserRec),
      {{ Lk st X ∗ ownUser u ur ∗
          ⌜ur.roles.Pairwise go.GoStringLt ∧ ur.name.length ≤ backend.maxKeySize⌝ }}
        (App (Val #(methods ti.ty go!"UnsafePutUser" ti.v)) (Val #u))
      {{ RET #(); Lk (putUser st ur.name ur.roles) X ∗ ownUser u ur }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (name : GoString),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeDeleteUser" ti.v)) (Val #name))
      {{ RET #(); Lk (delUser st name) X }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (r : Loc) (rr : RoleRec),
      {{ Lk st X ∗ ownRole r rr ∗ ⌜rr.name.length ≤ backend.maxKeySize⌝ }}
        (App (Val #(methods ti.ty go!"UnsafePutRole" ti.v)) (Val #r))
      {{ RET #(); Lk (putRole st rr.name rr.toRole) X ∗ ownRole r rr }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (name : GoString),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeDeleteRole" ti.v)) (Val #name))
      {{ RET #(); Lk { st with roles := GMap.delete name st.roles } X }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (b : Bool),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeSaveAuthEnabled" ti.v)) (Val #b))
      {{ RET #(); Lk { st with enabled := b } X }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (rev : w64),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeSaveAuthRevision" ti.v)) (Val #rev))
      {{ RET #(); Lk { st with revision := uint.nat rev } X }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (hs : List AuthState),
      {{ Lk st X ∗ authOwnF M hs ∗ ⌜histLast M hs st⌝ }}
        (App (Val #(methods ti.ty go!"Unlock" ti.v)) (Val #()))
      {{ RET #(); X ∗ T ∗ authOwn M hs }}) ∗
    -- the reads with the message as `proto.Unmarshal` returns it, the caller's (appended; the
    -- auth plan's S4c): `UserGrantRole` appends to a user's `Roles`, `RoleGrantPermission` to a
    -- role's `KeyPermission` and writes an entry (schema's `unsafeGetUser`/`unsafeGetRole` return
    -- them so: `userOutDX`, `roleOutDX`)
    □ (∀ (st : AuthState) (X : IProp GF) (name : GoString),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #name))
      {{ (u : Loc), RET #u; Lk st X ∗ userOutX u st name }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (name : GoString),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeGetRole" ti.v)) (Val #name))
      {{ (r : Loc), RET #r; Lk st X ∗ roleOutX r st name }}))

instance authBatchTxLk_persistent (ti : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) (Lk : AuthState → IProp GF → IProp GF) :
    Persistent (authBatchTxLk ti M P f T Lk) := by
  unfold authBatchTxLk; infer_instance

/-- **The backend's batch transaction's lock** (the auth plan's S4f, 2026-10-25; what the real
backend's derivation, D22, discharges): as `authBatchTxLk`, but the history's ownership is under
the lock: `Lock()` gives, with the token of the state `st` the buckets hold, the lock's share of a
history whose latest state is `st` (`authLockI`), and `Unlock()` takes it back with the buckets'
state. A real backend meets it with `∃ st, buckets(st) ∗ authLockI M st` among what its batch
lock protects; the store's view (`authBatchTxLk`) follows by joining the share with the admin
side's authority (`authBatchTxLk_of_R`). -/
def authBatchTxLkR (ti : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (Lk : AuthState → IProp GF → IProp GF) : IProp GF :=
  iprop(□ (∀ (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post ∗ T }}
        (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : AuthState, Lk st Post ∗ authLockI M st }}) ∗
    □ (∀ X : IProp GF, authReaderOk ti (fun st => Lk st X)) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (u : Loc) (ur : UserRec),
      {{ Lk st X ∗ ownUser u ur ∗
          ⌜ur.roles.Pairwise go.GoStringLt ∧ ur.name.length ≤ backend.maxKeySize⌝ }}
        (App (Val #(methods ti.ty go!"UnsafePutUser" ti.v)) (Val #u))
      {{ RET #(); Lk (putUser st ur.name ur.roles) X ∗ ownUser u ur }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (name : GoString),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeDeleteUser" ti.v)) (Val #name))
      {{ RET #(); Lk (delUser st name) X }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (r : Loc) (rr : RoleRec),
      {{ Lk st X ∗ ownRole r rr ∗ ⌜rr.name.length ≤ backend.maxKeySize⌝ }}
        (App (Val #(methods ti.ty go!"UnsafePutRole" ti.v)) (Val #r))
      {{ RET #(); Lk (putRole st rr.name rr.toRole) X ∗ ownRole r rr }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (name : GoString),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeDeleteRole" ti.v)) (Val #name))
      {{ RET #(); Lk { st with roles := GMap.delete name st.roles } X }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (b : Bool),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeSaveAuthEnabled" ti.v)) (Val #b))
      {{ RET #(); Lk { st with enabled := b } X }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (rev : w64),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeSaveAuthRevision" ti.v)) (Val #rev))
      {{ RET #(); Lk { st with revision := uint.nat rev } X }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF),
      {{ Lk st X ∗ authLockI M st }}
        (App (Val #(methods ti.ty go!"Unlock" ti.v)) (Val #()))
      {{ RET #(); X ∗ T }}) ∗
    -- the reads with the message as `proto.Unmarshal` returns it, the caller's (appended; the
    -- auth plan's S4c): `UserGrantRole` appends to a user's `Roles`, `RoleGrantPermission` to a
    -- role's `KeyPermission` and writes an entry (schema's `unsafeGetUser`/`unsafeGetRole` return
    -- them so: `userOutDX`, `roleOutDX`)
    □ (∀ (st : AuthState) (X : IProp GF) (name : GoString),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #name))
      {{ (u : Loc), RET #u; Lk st X ∗ userOutX u st name }}) ∗
    □ (∀ (st : AuthState) (X : IProp GF) (name : GoString),
      {{ Lk st X }} (App (Val #(methods ti.ty go!"UnsafeGetRole" ti.v)) (Val #name))
      {{ (r : Loc), RET #r; Lk st X ∗ roleOutX r st name }}))

instance authBatchTxLkR_persistent (ti : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) (Lk : AuthState → IProp GF → IProp GF) :
    Persistent (authBatchTxLkR ti M P f T Lk) := by
  unfold authBatchTxLkR; infer_instance

/-- **The backend's batch transaction** `tx` (a contract): some lock token (`authBatchTxLk`). -/
def authBatchTxOk (tx : GoInterface) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗
    ∃ Lk : AuthState → IProp GF → IProp GF, authBatchTxLk ti M P f T Lk)

instance authBatchTxOk_persistent (tx : GoInterface) (M : AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) : Persistent (authBatchTxOk tx M P f T) := by
  unfold authBatchTxOk; infer_instance

/-- What `GetAllUsers()` returns of the state `st` (the auth plan's E2j): a slice of messages, one
per user of the state, each once (`userOut`, in no promised order; nil when there is none). -/
def usersOut (s : GoSlice) (st : AuthState) : IProp GF :=
  iprop(∃ (us : List Loc) (names : List GoString), s ↦* us ∗
    ⌜us.length = names.length ∧ names.Nodup ∧ ∀ n, n ∈ names ↔ (st.users.lookup n).isSome⌝ ∗
    [∗list] x ∈ us.zip names, userOut x.1 st x.2)

/-- What `GetAllRoles()` returns of the state `st` (the auth plan's E2j): as `usersOut`, the
state's roles (`roleOut`). -/
def rolesOut (s : GoSlice) (st : AuthState) : IProp GF :=
  iprop(∃ (rs : List Loc) (names : List GoString), s ↦* rs ∗
    ⌜rs.length = names.length ∧ names.Nodup ∧ ∀ n, n ∈ names ↔ (st.roles.lookup n).isSome⌝ ∗
    [∗list] x ∈ rs.zip names, roleOut x.1 st x.2)

/-- **The auth backend's reads** `bi` with the hook `P f` and the write token `T` in the mode `M`
(the auth plan's S5, `GetUser`; E2j, 2026-10-26, the rest), the admin side's (the apply thread's,
which holds the authority `authOwn M hs`): each answers from the latest state (`histLast`), and
keeps the token and the authority.
- `GetUser(name)`, `GetRole(name)` and `GetAllUsers()` are schema's read transaction: `ReadTx()`,
  `RLock()`, the read, `RUnlock()` (`schema/auth_users.go`, `auth_roles.go`), so the hook does
  not run and the caller keeps its critical-section contract (until E2j `GetUser` gave the hook's
  post `Post`, which a read transaction cannot produce: a bug of this contract, not of Go). The
  read transaction sees the latest state because the auth buckets' only writer is the apply
  thread, whose batch transactions write back at `Unlock` (D22 discharges it).
- `GetAllRoles()` is schema's batch transaction (`BatchTx()`, `Lock()`, `UnsafeGetAllRoles`,
  `Unlock()`: `LockInsideApply` runs the hook, so the hook's post `Post`): its read
  transaction's twin panics (`issues/etcd-auth-readtx-getallroles-panics.md`), the batch
  transaction's range of the roles' bucket does not. -/
def authBackendReads (bi : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    IProp GF :=
  iprop(□ (∀ (hs : List AuthState) (name : GoString),
      {{ T ∗ authOwn M hs }} (App (Val #(methods bi.ty go!"GetUser" bi.v)) (Val #name))
      {{ (u : Loc), RET #u; T ∗ authOwn M hs ∗
          ∃ sta : AuthState, ⌜histLast M hs sta⌝ ∗ userOut u sta name }}) ∗
    □ (∀ (hs : List AuthState) (name : GoString),
      {{ T ∗ authOwn M hs }} (App (Val #(methods bi.ty go!"GetRole" bi.v)) (Val #name))
      {{ (r : Loc), RET #r; T ∗ authOwn M hs ∗
          ∃ sta : AuthState, ⌜histLast M hs sta⌝ ∗ roleOut r sta name }}) ∗
    □ (∀ hs : List AuthState,
      {{ T ∗ authOwn M hs }} (App (Val #(methods bi.ty go!"GetAllUsers" bi.v)) (Val #()))
      {{ (s : GoSlice), RET #s; T ∗ authOwn M hs ∗
          ∃ sta : AuthState, ⌜histLast M hs sta⌝ ∗ usersOut s sta }}) ∗
    □ (∀ (hs : List AuthState) (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post ∗ T ∗ authOwn M hs }}
        (App (Val #(methods bi.ty go!"GetAllRoles" bi.v)) (Val #()))
      {{ (s : GoSlice), RET #s; Post ∗ T ∗ authOwn M hs ∗
          ∃ sta : AuthState, ⌜histLast M hs sta⌝ ∗ rolesOut s sta }}))

instance authBackendReads_persistent (bi : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) : Persistent (authBackendReads (GF := GF) bi M P f T) := by
  unfold authBackendReads; infer_instance

/-- **The auth backend's write side** `be` (an `AuthBackend`; a contract, as the lessor's
`leaseBackend`) with the hook `P f` and the write token `T` in the mode `M`: `BatchTx()` returns a
batch transaction (`authBatchTxOk`), `ForceCommit()` keeps the token (the real backend's commit
writes nothing back on its own: `NewAuthStore`'s axiom), and its reads (`authBackendReads`). -/
def authWBackendOk (be : GoInterface) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜be = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (tx : GoInterface), RET #tx; authBatchTxOk tx M P f T }}) ∗
    □ ({{ T }} (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #())) {{ RET #(); T }}) ∗
    authBackendReads bi M P f T)

instance authWBackendOk_persistent (be : GoInterface) (M : AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) : Persistent (authWBackendOk be M P f T) := by
  unfold authWBackendOk; infer_instance

/-- **The backend's batch transaction** `tx` as the backend states it (the auth plan's S4f): some
lock token of the backend's contract (`authBatchTxLkR`). -/
def authBatchTxOkR (tx : GoInterface) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗
    ∃ Lk : AuthState → IProp GF → IProp GF, authBatchTxLkR ti M P f T Lk)

instance authBatchTxOkR_persistent (tx : GoInterface) (M : AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) : Persistent (authBatchTxOkR tx M P f T) := by
  unfold authBatchTxOkR; infer_instance

/-- **The auth backend's write side as the backend states it** (the auth plan's S4f, 2026-10-25;
the provisional boundary D22 discharges, `notes/decisions.md`, "S4f of the auth plan"): as
`authWBackendOk`, with `BatchTx()` returning the backend's transaction (`authBatchTxOkR`, the
history's lock share under its lock); its reads (`authBackendReads`) as the store's view's. (Until
E2j this said `GetUser` was schema's batch transaction, `Lock()`, `UnsafeGetUser`, `Unlock()`; it
is the read transaction, `schema/auth_users.go`.) -/
def authWBackendOkR (be : GoInterface) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜be = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (tx : GoInterface), RET #tx; authBatchTxOkR tx M P f T }}) ∗
    □ ({{ T }} (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #())) {{ RET #(); T }}) ∗
    authBackendReads bi M P f T)

instance authWBackendOkR_persistent (be : GoInterface) (M : AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) : Persistent (authWBackendOkR be M P f T) := by
  unfold authWBackendOkR; infer_instance

/-- **The store's view of the backend's lock** (the auth plan's S4f): `Lock()` joins the lock's
share with the admin side's authority, `Unlock()` splits it off again. -/
theorem authBatchTxLk_of_R (ti : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) (Lk : AuthState → IProp GF → IProp GF) :
    authBatchTxLkR (GF := GF) ti M P f T Lk ⊢ authBatchTxLk ti M P f T Lk := by
  iintro #H
  iunfold authBatchTxLkR at H
  icases H with ⟨#HL, #HRd, #H1, #H2, #H3, #H4, #H5, #H6, #HU, #H7, #H8⟩
  iunfold authBatchTxLk
  isplitl []
  · iintro !> %hs %Pre %Q %Post %Φ !> ⟨Hcs, HT, Hown⟩ HΦ
    iapply HL $$ %Pre %Q %Post [$Hcs $HT]
    inext
    iintro ⟨%st, HLk, HI⟩
    ihave ⟨Hown, %Hl⟩ := authOwn_lockI_join M hs st $$ Hown HI
    iapply HΦ
    iexists st; iframe HLk Hown; ipureintro; exact Hl
  iframe #
  iintro !> %st %X %hs %Φ !> ⟨HLk, Hown, %Hl⟩ HΦ
  ihave ⟨Hown, HI⟩ := authOwnF_lockI_split M hs st Hl $$ Hown
  iapply HU $$ %st %X [$HLk $HI]
  inext
  iintro ⟨HX, HT⟩
  iapply HΦ
  iframe HX HT Hown

theorem authBatchTxOk_of_R (tx : GoInterface) (M : AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) : authBatchTxOkR (GF := GF) tx M P f T ⊢ authBatchTxOk tx M P f T := by
  iintro H
  iunfold authBatchTxOkR at H
  icases H with ⟨%ti, %Hti, %Lk, #H⟩
  iunfold authBatchTxOk
  iexists ti
  isplitr
  · ipureintro; exact Hti
  iexists Lk
  iapply authBatchTxLk_of_R $$ H

/-- **The store's view of the backend's write side** (the auth plan's S4f): its transactions
seen through `authBatchTxOk_of_R`. -/
theorem authWBackendOk_of_R (be : GoInterface) (M : AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) : authWBackendOkR (GF := GF) be M P f T ⊢ authWBackendOk be M P f T := by
  iintro H
  iunfold authWBackendOkR at H
  icases H with ⟨%bi, %Hbi, #HB, #HFC, #HGU⟩
  iunfold authWBackendOk
  iexists bi
  isplitr
  · ipureintro; exact Hbi
  iframe #
  iintro !> %Φ !> - HΦ
  iapply HB $$ []
  · itrivial
  inext
  iintro %tx Htx
  iapply HΦ
  iapply authBatchTxOk_of_R $$ Htx

/-- **The admin side's write resource** of the store `st` (what the apply package's write right
`RW` lends its writes, `apply/AuthDerive.lean`): the store's user's half of `be` (the other half
is `beMu`'s, `beP`; `Recover` takes both) with the backend's write side, the write token, and the
admin side's halves of `enabled` (`enabledHalf`) and of the permission cache (`cacheHalf`, the
auth plan's E2r). -/
def authWR (st : Loc) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) : IProp GF :=
  iprop((∃ be : AuthBackend, aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗ authWBackendOk be M P f T) ∗
    T ∗ enabledHalf st M ∗ cacheHalf st M)

/-- **The admin side's share of the token provider** of the store `st` in the mode `M` (the auth
plan's S5d, 2026-10-25): the store's provider with its contract at some admin resource `A`, and
`A`. The operations that call the provider's `enable`, `disable` or `invalidateUser` (`AuthEnable`,
`AuthDisable`, `Recover`, `UserDelete`, `UserChangePassword`) take and give it back; like the
authority `authOwn` it is the apply thread's (the store's only admin caller). -/
def tpAdmin (st : Loc) (M : AuthMode) : IProp GF :=
  iprop(∃ (tp : TokenProvider) (A : IProp GF), aF go!"tokenProvider" st ↦□ tp ∗
    tokenProviderOkA tp M A ∗ A)

/-- The revision the batch transaction holds after `commitRevision` at the pending state `sta`:
in `on γa` the model's (`bump`); in the other modes the atomic's value plus one, not tied to the
model. -/
def revAfter (M : AuthMode) (sta : AuthState) (rev : Nat) : Prop :=
  match M with
  | .on _ => rev = sta.revision + 1
  | _ => True

/-- The authority a reader may hold: none, or the admin side's at `hs` (`Revision`'s spec: with
it, the value read is the latest state's). -/
def authOwnOpt (M : AuthMode) : Option (List AuthState) → IProp GF
  | none => iprop(True)
  | some hs => authOwn M hs

theorem authOwnOpt_some (M : AuthMode) (hs : List AuthState) :
    authOwnOpt (GF := GF) M (some hs) = authOwn M hs := rfl

theorem authOwnOpt_none (M : AuthMode) : authOwnOpt (GF := GF) M none = iprop(True) := rfl

/-- With the authority, the atomic's value is the latest state's revision (`on γa`: the two
halves of the latest state's ghost variable agree). -/
theorem revCur_agree (M : AuthMode) (hs : List AuthState) (r : w64) :
    ⊢ authOwnF (GF := GF) M hs -∗ revCur M r -∗ authOwnF M hs ∗ revCur M r ∗
      ⌜∀ stl : AuthState, histLast M hs stl → M.isOn = true → M ≠ .any → uint.nat r = stl.revision⌝ := by
  cases M with
  | on γa =>
    simp only [authOwnF, revCur, histLast]
    iintro ⟨Hh, ⟨%stl, %Hl, Hc1⟩⟩ ⟨%stc, Hc2, %Hr⟩
    ihave %Heq := authCurHalf_agree γa stl stc $$ Hc1 Hc2
    subst Heq
    isplitl [Hh Hc1]
    · iframe Hh; iexists stl; iframe Hc1; ipureintro; exact Hl
    isplitl [Hc2]
    · iexists stl; iframe Hc2; ipureintro; exact Hr
    · ipureintro
      intro st' Hl' _ _
      rw [Hl] at Hl'; cases Hl'
      exact Hr
  | off =>
    simp only [authOwnF, revCur]
    iintro %H -
    isplitr
    · ipureintro; exact H
    · isplitr; itrivial; ipureintro; intro _ _ h; cases h
  | any =>
    simp only [authOwnF, revCur]
    iintro - -
    isplitr; itrivial; isplitr; itrivial; ipureintro; intro _ _ _ h; exact absurd rfl h

/-- With the admin side's authority (`revCur_agree`'s, between transactions), the atomic's value is the latest state's revision (`on γa`: the two
halves of the latest state's ghost variable agree). -/
theorem revCur_agree_own (M : AuthMode) (hs : List AuthState) (r : w64) :
    ⊢ authOwn (GF := GF) M hs -∗ revCur M r -∗ authOwn M hs ∗ revCur M r ∗
      ⌜∀ stl : AuthState, histLast M hs stl → M.isOn = true → M ≠ .any → uint.nat r = stl.revision⌝ := by
  cases M with
  | on γa =>
    simp only [authOwn, revCur, histLast]
    iintro ⟨Hh, ⟨%stl, %Hl, Hc1⟩⟩ ⟨%stc, Hc2, %Hr⟩
    ihave %Heq := authCurHalf_agree γa stl stc $$ Hc1 Hc2
    subst Heq
    isplitl [Hh Hc1]
    · iframe Hh; iexists stl; iframe Hc1; ipureintro; exact Hl
    isplitl [Hc2]
    · iexists stl; iframe Hc2; ipureintro; exact Hr
    · ipureintro
      intro st' Hl' _ _
      rw [Hl] at Hl'; cases Hl'
      exact Hr
  | off =>
    simp only [authOwn, revCur]
    iintro %H -
    isplitr
    · ipureintro; exact H
    · isplitr; itrivial; ipureintro; intro _ _ h; cases h
  | any =>
    simp only [authOwn, revCur]
    iintro - -
    isplitr; itrivial; isplitr; itrivial; ipureintro; intro _ _ _ h; exact absurd rfl h

/-- **The admin side appends `st'`** (the step's state) while the atomic is set to its
revision: in `on γa` both halves of the latest state's ghost variable move to `st'` and the
history grows (`st'` recorded, its revision the new value's verdict); in `off` the states stay
disabled; in `any` nothing. -/
theorem authOwnF_revCur_append (M : AuthMode) (hs : List AuthState) (st' : AuthState) (r r' : w64)
    (hk : M.isOn = true → M ≠ .any → permKeysOk st') (hoff : M = .off → st'.enabled = false)
    (hr' : M.isOn = true → M ≠ .any → uint.nat r' = st'.revision) :
    ⊢ authOwnF (GF := GF) M hs -∗ revCur M r -∗
      |==> (authOwnF M (hs ++ [st']) ∗ revCur M r' ∗ revisionVerdict M r') := by
  cases M with
  | on γa =>
    simp only [authOwnF, revCur, revisionVerdict]
    iintro ⟨Hh, ⟨%stl, %Hl, Hc1⟩⟩ ⟨%stc, Hc2, -⟩
    imod (authCurHalf_update γa stl stc st') $$ Hc1 Hc2 with ⟨Hc1, Hc2⟩
    imod (authHist_append γa hs st' (hk rfl (by intro h; cases h))) $$ Hh with Hh
    imod (authHist_stateAt_keep γa (hs ++ [st']) hs.length st'
      (by simp)) $$ Hh with ⟨Hh, #Hst⟩
    imodintro
    iframe Hh
    isplitl [Hc1]
    · iexists st'; iframe Hc1; ipureintro; simp
    isplitl [Hc2]
    · iexists st'; iframe Hc2; ipureintro; exact hr' rfl (by intro h; cases h)
    · iexists hs.length, st'; iframe Hst; ipureintro; exact hr' rfl (by intro h; cases h)
  | off =>
    simp only [authOwnF, revCur, revisionVerdict]
    iintro %H -
    imodintro
    isplitr
    · ipureintro
      refine ⟨by simp, ?_⟩
      intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact H.2 x hx
      · exact hoff rfl
    · isplitr <;> itrivial
  | any =>
    simp only [authOwnF, revCur, revisionVerdict]
    iintro - -
    imodintro
    isplitr; itrivial; isplitr; itrivial; itrivial

/-- The atomic set to the latest state's revision again (no append): the new value's verdict. -/
theorem authOwnF_revCur_keep (M : AuthMode) (hs : List AuthState) (stl : AuthState) (r r' : w64)
    (hl : histLast M hs stl) (hr' : M.isOn = true → M ≠ .any → uint.nat r' = stl.revision) :
    ⊢ authOwnF (GF := GF) M hs -∗ revCur M r -∗
      |==> (authOwnF M hs ∗ revCur M r' ∗ revisionVerdict M r') := by
  cases M with
  | on γa =>
    simp only [authOwnF, revCur, revisionVerdict, histLast] at hl ⊢
    iintro ⟨Hh, ⟨%stl', %Hl, Hc1⟩⟩ ⟨%stc, Hc2, -⟩
    rw [hl] at Hl; cases Hl
    ihave %Heq := authCurHalf_agree γa stl stc $$ Hc1 Hc2
    subst Heq
    have hi : hs[hs.length - 1]? = some stl := by
      cases hs with
      | nil => cases hl
      | cons x xs => rw [List.getLast?_eq_getElem?] at hl; exact hl
    imod (authHist_stateAt_keep γa hs (hs.length - 1) stl hi) $$ Hh with ⟨Hh, #Hst⟩
    imodintro
    iframe Hh
    isplitl [Hc1]
    · iexists stl; iframe Hc1; ipureintro; exact hl
    isplitl [Hc2]
    · iexists stl; iframe Hc2; ipureintro; exact hr' rfl (by intro h; cases h)
    · iexists hs.length - 1, stl; iframe Hst; ipureintro; exact hr' rfl (by intro h; cases h)
  | off =>
    simp only [authOwnF, revCur, revisionVerdict]
    iintro %H -
    imodintro
    isplitr
    · ipureintro; exact H
    · isplitr <;> itrivial
  | any =>
    simp only [authOwnF, revCur, revisionVerdict]
    iintro - -
    imodintro
    isplitr; itrivial; isplitr; itrivial; itrivial

/-- The authority has a latest state (`histLast`): in `off`, one of its states (all disabled). -/
theorem authOwnF_exists_last (M : AuthMode) (hs : List AuthState) :
    authOwnF (GF := GF) M hs ⊢ ⌜∃ st : AuthState, histLast M hs st⌝ := by
  cases M with
  | on γa =>
    simp only [authOwnF, histLast]
    iintro ⟨-, ⟨%st, %Hl, -⟩⟩
    ipureintro; exact ⟨st, Hl⟩
  | off =>
    simp only [authOwnF, histLast]
    iintro %H
    ipureintro
    obtain ⟨hne, hall⟩ := H
    cases hl : hs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hl) hne
    | some st => exact ⟨st, hall st (List.mem_of_getLast? hl)⟩
  | any =>
    simp only [authOwnF, histLast]
    iintro -; ipureintro; exact ⟨default, trivial⟩

/-- The latest state has valid permission keys (`on γa`: every recorded state has). -/
theorem authOwnF_last_permKeysOk (M : AuthMode) (hs : List AuthState) :
    authOwnF (GF := GF) M hs ⊢
      ⌜∀ st : AuthState, histLast M hs st → M.isOn = true → M ≠ .any → permKeysOk st⌝ := by
  cases M with
  | on γa =>
    simp only [authOwnF, histLast, authHist]
    iintro ⟨⟨-, %Hk⟩, -⟩
    ipureintro
    intro st hl _ _
    exact Hk st (List.mem_of_getLast? hl)
  | off => iintro -; ipureintro; intro _ _ h; cases h
  | any => iintro -; ipureintro; intro _ _ _ h; exact absurd rfl h

/-- The latest state is a state of the mode (`authSnap`: recorded in `on γa`). -/
theorem authSnapF_of_last (M : AuthMode) (hs : List AuthState) (st : AuthState)
    (hl : histLast M hs st) :
    authOwnF (GF := GF) M hs ⊢ |==> (authOwnF M hs ∗ authSnap M st) := by
  cases M with
  | on γa =>
    iintro Hown
    imod (authOwnF_last γa hs) $$ Hown with ⟨Hown, ⟨%st', %Hl', #Hst⟩⟩
    imodintro
    iframe Hown
    simp only [histLast] at hl
    rw [hl] at Hl'; cases Hl'
    simp only [authSnap]
    iexists hs.length - 1
    iexact Hst
  | off =>
    iintro Hown; imodintro; iframe Hown; simp only [authSnap]; ipureintro; exact hl
  | any =>
    iintro Hown; imodintro; iframe Hown; simp only [authSnap]; itrivial

/-- The admin side's latest state is a state of the mode, as `authSnapF_of_last`. -/
theorem authSnap_of_last (M : AuthMode) (hs : List AuthState) (st : AuthState)
    (hl : histLast M hs st) :
    authOwn (GF := GF) M hs ⊢ |==> (authOwn M hs ∗ authSnap M st) := by
  cases M with
  | on γa =>
    simp only [histLast] at hl
    have hi : hs[hs.length - 1]? = some st := by
      cases hs with
      | nil => cases hl
      | cons x xs => rw [List.getLast?_eq_getElem?] at hl; exact hl
    simp only [authOwn]
    iintro ⟨Hh, Hc⟩
    ihave #Hst := authHistHalf_stateAt γa hs (hs.length - 1) st hi $$ Hh
    imodintro
    iframe Hh Hc
    simp only [authSnap]
    iexists hs.length - 1
    iexact Hst
  | off =>
    iintro Hown; imodintro; iframe Hown; simp only [authSnap]; ipureintro; exact hl
  | any =>
    iintro Hown; imodintro; iframe Hown; simp only [authSnap]; itrivial

/-- After `commitRevision` from the pending state `x` (the latest state's flag and revision),
the transaction's state (the revision written, `revAfter`) is the latest of the history with
`bump x` appended. -/
theorem histLast_after (M : AuthMode) (hs : List AuthState) (x : AuthState) (rev : Nat)
    (hen : M = .off → x.enabled = false) (hrev : revAfter M x rev) :
    histLast M (hs ++ [bump x]) { x with revision := rev } := by
  cases M with
  | on γa =>
    simp only [histLast, revAfter] at hrev ⊢
    subst hrev
    simp [bump]
  | off => simp only [histLast]; exact hen rfl
  | any => trivial

theorem permsFit_rev (x : AuthState) (rev : Nat) (h : permsFit (bump x)) :
    permsFit { x with revision := rev } := h

theorem permKeysOk_rev (x : AuthState) (rev : Nat) (h : permKeysOk x) :
    permKeysOk { x with revision := rev } := h

/-- `UnsafeGetRole(name)` returned `nil`: the state has no such role. -/
theorem roleOut_null (st : AuthState) (name : GoString) :
    roleOut (GF := GF) null st name ⊢ ⌜st.roles !! name = none⌝ := by
  unfold roleOut
  cases h : st.roles !! name with
  | none => iintro -; ipureintro; rfl
  | some ps =>
    iintro ⟨%rr, -, Hr⟩
    iunfold ownRole at Hr
    icases Hr with ⟨%s1, %n, %kp, %pl, %uf, %sc, Hp, -⟩
    ihave %Hnn := typedPointsto_not_null $$ Hp
    exact absurd rfl Hnn

/-- `UnsafeGetRole(name)` returned a message: the state's role. -/
theorem roleOut_some (r : Loc) (st : AuthState) (name : GoString) (hnn : r ≠ null) :
    roleOut (GF := GF) r st name ⊢ ∃ (ps : Role) (rr : RoleRec),
      ⌜st.roles !! name = some ps ∧ rr.name = name ∧ rr.toRole = ps⌝ ∗ ownRole r rr := by
  unfold roleOut
  cases h : st.roles !! name with
  | none => iintro %Hn; exact absurd Hn hnn
  | some ps =>
    iintro ⟨%rr, %Hrr, Hr⟩
    iexists ps, rr
    iframe Hr
    ipureintro; exact ⟨rfl, Hrr.1, Hrr.2⟩

/-- **A state of the latest one's revision appended** (`AuthEnable`: the flag set, the revision
as stored): the atomic is unchanged, so the store's revision invariant is reopened only to move
its half of the latest state's ghost variable. -/
theorem authOwnF_append_same (st : Loc) (R : IProp GF) (M : AuthMode) (hs : List AuthState)
    (st0 x : AuthState) (hl : histLast M hs st0) (hrev : x.revision = st0.revision)
    (hk : M.isOn = true → M ≠ .any → permKeysOk x) (hoff : M = .off → x.enabled = false) :
    authInv (GF := GF) st R M ⊢ authOwnF M hs ={⊤}=∗ authOwnF M (hs ++ [x]) := by
  iintro #Hinv Hown
  iunfold authInv at Hinv
  icases Hinv with ⟨-, #Hrev, -⟩
  iinv Hrev with Hi Hclose
  iunfold revInv at Hi
  icases Hi with ⟨%r, >Hr, -, >Hc⟩
  ihave H := revCur_agree M hs r $$ Hown Hc
  icases H with ⟨Hown, Hc, %Hag⟩
  imod (authOwnF_revCur_append M hs x r r hk hoff (fun h1 h2 => by
    rw [hrev]; exact Hag st0 hl h1 h2)) $$ Hown Hc with ⟨Hown, Hc, #Hv⟩
  imod Hclose $$ [Hr Hc] with -
  · inext; iunfold revInv; iexists r; iframe Hr Hc; iexact Hv
  imodintro
  iexact Hown

/-- The admin side's authority has a latest state (`histLast`), as `authOwnF_exists_last`. -/
theorem authOwn_exists_last (M : AuthMode) (hs : List AuthState) :
    authOwn (GF := GF) M hs ⊢ ⌜∃ st : AuthState, histLast M hs st⌝ := by
  cases M with
  | on γa =>
    simp only [authOwn, histLast]
    iintro ⟨-, ⟨%st, %Hl, -⟩⟩
    ipureintro; exact ⟨st, Hl⟩
  | off =>
    simp only [authOwn, histLast]
    iintro %H
    ipureintro
    obtain ⟨hne, hall⟩ := H
    cases hl : hs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hl) hne
    | some st => exact ⟨st, hall st (List.mem_of_getLast? hl)⟩
  | any =>
    simp only [authOwn, histLast]
    iintro -; ipureintro; exact ⟨default, trivial⟩

/-- The admin side's latest state has valid permission keys, as `authOwnF_last_permKeysOk`. -/
theorem authOwn_last_permKeysOk (M : AuthMode) (hs : List AuthState) :
    authOwn (GF := GF) M hs ⊢
      ⌜∀ st : AuthState, histLast M hs st → M.isOn = true → M ≠ .any → permKeysOk st⌝ := by
  cases M with
  | on γa =>
    simp only [authOwn, histLast, authHistHalf]
    iintro ⟨⟨-, %Hk⟩, -⟩
    ipureintro
    intro st hl _ _
    exact Hk st (List.mem_of_getLast? hl)
  | off => iintro -; ipureintro; intro _ _ h; cases h
  | any => iintro -; ipureintro; intro _ _ _ h; exact absurd rfl h

/-- A state of the mode gives its flag's verdict. -/
theorem enabledVerdict_of_snap (M : AuthMode) (sta : AuthState) :
    authSnap (GF := GF) M sta ⊢ enabledVerdict M sta.enabled := by
  cases M with
  | on γa =>
    simp only [authSnap, enabledVerdict]
    iintro ⟨%i, #Hst⟩
    iexists i, sta; iframe Hst; ipureintro; rfl
  | off => simp only [authSnap, enabledVerdict]; iintro %H; ipureintro; exact H
  | any => simp only [enabledVerdict]; iintro -; itrivial

/-- A writer that did not write gives the caller's resources back. -/
theorem csContract_noWrite (P : IProp GF) (f : val) (Pre Q Post : IProp GF) :
    mvcc.csContract P f Pre Q Post ⊢ Post ∨ Pre := by
  unfold mvcc.csContract
  iintro ⟨HPre, -, -⟩
  iright; iexact HPre

/-- Every error variable of the model (`AuthErr`) holds an error (the package's facts). -/
theorem authErrVar_of_init (e : AuthErr) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      ∃ ei : GoInterfaceOk, globalAddr e.var ↦□ GoInterface.ok ei := by
  iintro #Hpkg
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#H1, #H2, #H3, #H4, #H5, -, -, #H6, #H7, #H8, #H9, #H10, #H11, #H12, #H13, #H14,
    #H15, #H16, #H17, #H18, -⟩
  cases e <;> simp only [AuthErr.var] <;>
    first
    | (iunfold authErrVar at H1; icases H1 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H2; icases H2 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H3; icases H3 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H4; icases H4 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H5; icases H5 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H6; icases H6 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H7; icases H7 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H8; icases H8 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H9; icases H9 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H10; icases H10 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H11; icases H11 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H12; icases H12 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H13; icases H13 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H14; icases H14 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H15; icases H15 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H16; icases H16 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H17; icases H17 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)
    | (iunfold authErrVar at H18; icases H18 with ⟨%x, #Hx, -⟩; iexists x; iexact Hx)

theorem authErrOf_intro (e : AuthErr) (ei : GoInterfaceOk) :
    globalAddr e.var ↦□ GoInterface.ok ei ⊢ authErrOf (GF := GF) e (GoInterface.ok ei) := by
  iintro #H
  iunfold authErrOf
  iexists ei
  iframe H
  ipureintro; rfl

/-- A reader slot of `enabledMu` (`IsAuthEnabled`) in the mode `M`. -/
def enabledRd (st : Loc) (M : AuthMode) : IProp GF :=
  sync.ownRWMutex (aF go!"enabledMu" st) (enabledP st M)

/-- A reader slot of `rangePermCacheMu` (`isRangeOpPermitted`). -/
def cacheRd (st : Loc) (M : AuthMode) : IProp GF :=
  sync.ownRWMutex (aF go!"rangePermCacheMu" st) (cacheP st M)

/-- A reader slot of `beMu` (`lockedReadTx`). -/
def beRd (st : Loc) (R : IProp GF) (M : AuthMode) : IProp GF :=
  sync.ownRWMutex (aF go!"beMu" st) (beP st R M)

/-- **A permission check's reader resource**: a slot of each lock and the backend's `R`. -/
def authRd (st : Loc) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(enabledRd st M ∗ cacheRd st M ∗ beRd st R M ∗ R)

/-- **What `Authenticate` returns** for `username` with the admin side's authority `hs`, in the
mode `M` (the auth plan's S5): an error and no response; or no error and a response holding a token
issued to `username` (`tokOk`), auth enabled at some recorded state, and the user present in the
latest state (`histLast`). (`Authenticate` does not check the password: the server's API layer
did, `CheckPassword`, before proposing the request.) -/
def authenticated (M : AuthMode) (hs : List AuthState) (username : GoString) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ (tok : GoString) (v : go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse),
      resp ↦ v ∗ ⌜v.Token' = tok⌝ ∗ tokOk M tok username ∗ enabledVerdict M true ∗
      ⌜∃ sta : AuthState, histLast M hs sta ∧ (sta.users.lookup username).isSome⌝))

/-- `err` is `nil` or one of the error variables the request side returns. -/
def authErrIs (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil⌝ ∨ ∃ (g : GoString) (e : GoInterfaceOk),
    ⌜g = ErrUserEmpty ∨ g = ErrUserNotFound ∨ g = ErrPermissionDenied ∨
      g = ErrAuthOldRevision ∨ g = ErrInvalidAuthToken⌝ ∗
    globalAddr g ↦□ GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝)

instance authErrIs_persistent (err : GoInterface) : Persistent (authErrIs (GF := GF) err) := by
  unfold authErrIs; infer_instance

/-- The permission types the request side passes (`Permission_READ`, `Permission_WRITE`). -/
def permTypOk (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) : Prop :=
  pt = W32 0 ∨ pt = W32 1

end defs

end auth
end EtcdGrove
end Perennial
