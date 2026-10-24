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

**The readers** (`authRd as R M`): `IsAuthEnabled` read-locks `enabledMu` and the permission checks
also `rangePermCacheMu` and `beMu`, each needing a reader slot (`sync.ownRWMutex`: Perennial bounds
an `RWMutex`'s readers), and the backend's read transaction needs `R`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Proof.go_etcd_io.etcd.server.v3.auth.Buckets
public import Proof.go_etcd_io.etcd.server.v3.auth.PermTree
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Link

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

/-- What `enabledMu` guards at `q` in the mode `M`: `enabled`, a recorded state's flag
(`enabledVerdict`: in `off` false, in `on γa` some recorded state's; the auth plan's S3). -/
def enabledP (st : Loc) (M : AuthMode) (q : Qp) : IProp GF :=
  iprop(∃ b : Bool, aF go!"enabled" st ↦{DFrac.own q} b ∗ enabledVerdict M b)

/-- The `*AuthInfo` `a` at `dq` holds `ai`: `none`, a `nil` pointer; `some info`, the message. -/
def authInfoAt (a : Loc) (dq : DFrac) (ai : Option AuthInfo) : IProp GF :=
  match ai with
  | none => iprop(⌜a = null⌝)
  | some info => iprop(a ↦{dq} info)

/-- What `rangePermCacheMu` guards at `q` in the mode `M`: the cache's map, `cacheOk`. -/
def cacheP (st : Loc) (M : AuthMode) (q : Qp) : IProp GF :=
  iprop(∃ (mp : GoMap) (Mp : GMap GoString Loc), aF go!"rangePermCache" st ↦{DFrac.own q} mp ∗
    mp ↦${DFrac.own q} Mp ∗ cacheOk M Mp)

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
`RUnlock()` turns back into `R`. (The auth plan's S1, 2026-10-23; until then: a token holding no
state, `UnsafeGetUser` returning any pointer.) -/
def authReadTxOk (tx : GoInterface) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗ ∃ Hs : AuthState → IProp GF,
    □ ({{ R }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnap M st }}) ∗
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

/-- **The token provider** `tp` (a `TokenProvider`, not nil; a contract): `info(ctx, token,
rev)` returns an auth info (`authInfoRO`) and a boolean. -/
def tokenProviderOk (tp : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tp = GoInterface.ok ti⌝ ∗
    □ (∀ (ctx : GoInterface) (token : GoString) (rev : w64),
      {{ True }}
        (App (App (App (Val #(methods ti.ty go!"info" ti.v)) (Val #ctx)) (Val #token)) (Val #rev))
      {{ (a : Loc) (ok : Bool), RET (PairV #a #ok); authInfoRO a }}))

instance tokenProviderOk_persistent (tp : GoInterface) :
    Persistent (tokenProviderOk (GF := GF) tp) := by
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

/-- The invariant of `revision` (an atomic) in the mode `M`: a recorded state's revision
(`revisionVerdict`; the auth plan's S3). -/
def revInv (st : Loc) (M : AuthMode) : IProp GF :=
  iprop(∃ r : w64, aF go!"revision" st ↦ r ∗ revisionVerdict M r)

/-- **The auth store** at `as` (persistent), its backend's read resource `R`, its mode `M`: the
atomic `revision`'s invariant, the read-only `lg` (not nil) and `tokenProvider` with its contract,
and the guards of its three locks (`beMu`'s holds `be` with its contract in the mode). -/
def authInv (st : Loc) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(⌜st ≠ null⌝ ∗ inv (nroot.@"authRev") (revInv st M) ∗
    (∃ lg : Loc, aF go!"lg" st ↦□ lg ∗ ⌜lg ≠ null⌝) ∗
    sync.isRWMutexGuard (aF go!"beMu" st) (beP st R M) ∗
    (∃ tp : TokenProvider, aF go!"tokenProvider" st ↦□ tp ∗ tokenProviderOk tp) ∗
    sync.isRWMutexGuard (aF go!"enabledMu" st) (enabledP st M) ∗
    sync.isRWMutexGuard (aF go!"rangePermCacheMu" st) (cacheP st M))

instance authInv_persistent (st : Loc) (R : IProp GF) (M : AuthMode) :
    Persistent (authInv (GF := GF) st R M) := by
  unfold authInv; infer_instance

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
