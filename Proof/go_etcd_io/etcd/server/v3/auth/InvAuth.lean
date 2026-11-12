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
an `RWMutex`'s readers), and the backend's read transaction needs `R`. In `on γa` (R-D2,
2026-11-04) `beMu`'s slot comes with a ticket for the store's currency (`rdTicketM`), which an
invariant of the store holds (`curInv`): a reader lends a part of it to the read transaction
(`beCurM_lend`), and a holder of every ticket can abandon the store (`authRd_abandon`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Proof.go_etcd_io.etcd.server.v3.auth.Buckets
public import Proof.go_etcd_io.etcd.server.v3.auth.Steps
public import Proof.go_etcd_io.etcd.server.v3.auth.BkNames
public import Proof.go_etcd_io.etcd.server.v3.auth.Requests
public import Proof.go_etcd_io.etcd.server.v3.lease.MvccShapes
public import Proof.go_etcd_io.etcd.server.v3.auth.Tokens
public import Proof.go_etcd_io.etcd.server.v3.auth.PermTree
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Link
public import Proof.google_golang_org.grpc.metadata.Incoming
public import Spec.go_uber_org.zap.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section fields
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

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

/-- **The backend's parameters `P` serve the auth store** (strict M1, 2026-11-05: in place of the
real instance's `mvcc.KBReal.P`, which mvcc's API does not export; the auth buckets' rows of it): each
of schema's three auth buckets (`Auth`, `AuthUsers`, `AuthRoles`) in the backend's table, a hook's
bucket (the readers' view), not a safe-range bucket, tracked (`RB`, D22), none of its keys a hook's
own. -/
def authParams (P : backend.BParams) : Prop :=
  ∀ bi ∈ [mvcc.authBI, mvcc.authUsersBI, mvcc.authRolesBI],
    P.has bi ∧ P.HB bi.name = true ∧ P.SB bi.name = false ∧ P.RB bi.name = true ∧
      ∀ k, P.HK bi.name k = false

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- **A share `q` of the field `enabled`'s ghost variable at `b`** in the mode `M` (the auth plan's
E3h): in `on γa`, `ghostVar γa.fen q b`; otherwise nothing. The guard holds a half (`enabledP`), the
admin side a quarter (`flagAt`), the store's freshness a quarter (`revFresh`): a reader under the
lock and the freshness agree on the value, which is a state's no older than the published index. -/
def enG (M : AuthMode) (q : Qp) (b : Bool) : IProp GF :=
  match M with
  | .on γa => ghostVar γa.fen q b
  | _ => iprop(True)

instance enG_timeless (M : AuthMode) (q : Qp) (b : Bool) : Timeless (enG (GF := GF) M q b) := by
  unfold enG; cases M <;> infer_instance

theorem enG_split (M : AuthMode) (q1 q2 : Qp) (b : Bool) :
    enG (GF := GF) M (q1 + q2) b ⊣⊢ enG M q1 b ∗ enG M q2 b := by
  cases M with
  | on γa => exact (ghostVar_fractional γa.fen b).fractional q1 q2
  | off =>
    simp only [enG]
    constructor
    · iintro -; isplitl []; itrivial; itrivial
    · iintro -; itrivial
  | any =>
    simp only [enG]
    constructor
    · iintro -; isplitl []; itrivial; itrivial
    · iintro -; itrivial

theorem enG_agree (M : AuthMode) (q1 q2 : Qp) (b1 b2 : Bool) (hM : M.isOn = true) (hA : M ≠ .any) :
    enG (GF := GF) M q1 b1 ∗ enG M q2 b2 ⊢ ⌜b1 = b2⌝ := by
  cases M with
  | on γa =>
    simp only [enG]
    iintro ⟨H1, H2⟩
    iapply (ghostVar_agree γa.fen b1 q1 b2 q2) $$ H1 H2
  | off => cases hM
  | any => exact absurd rfl hA

/-- What `enabledMu` guards at `q` in the mode `M`: half of `enabled` (the other half is the
admin side's, `enabledHalf`: `UserDelete`, `UserRevokeRole` and `RoleDelete` read the flag
outside the lock, in the apply thread, which alone writes it, under the lock, with both halves;
S4), a recorded state's flag (`enabledVerdict`: in `off` false, in `on γa` some recorded state's;
the auth plan's S3). -/
def enabledP (st : Loc) (M : AuthMode) (q : Qp) : IProp GF :=
  iprop(∃ b : Bool, aF go!"enabled" st ↦{DFrac.own q.half} b ∗ enabledVerdict M b ∗ enG M q.half b)

/-- **The admin side's half of `enabled` at `b`** (the auth plan's E2r): the field at half, for
the apply thread's checks (`IsAuthEnabled.specL`: the guard's half agrees), with (E3h) a quarter of
its value's ghost variable (`enG`; the guard holds a half, the store's freshness the other
quarter, `revFresh`). -/
def flagAt (st : Loc) (M : AuthMode) (b : Bool) : IProp GF :=
  iprop(aF go!"enabled" st ↦{DFrac.own (1 : Qp).half} b ∗ enG M (1 : Qp).half.half b)

/-- **The admin side's half of `enabled`** (S4): the flag at half, with its verdict. -/
def enabledHalf (st : Loc) (M : AuthMode) : IProp GF :=
  iprop(∃ b : Bool, flagAt st M b ∗ enabledVerdict M b)

theorem enabledHalf_flagAt (st : Loc) (M : AuthMode) :
    enabledHalf (GF := GF) st M ⊢ ∃ b : Bool, flagAt st M b ∗ enabledVerdict M b := by
  unfold enabledHalf
  iintro ⟨%b, H, #Hv⟩
  iexists b; iframe H Hv

theorem flagAt_enabledHalf (st : Loc) (M : AuthMode) (b : Bool) :
    flagAt (GF := GF) st M b ∗ enabledVerdict M b ⊢ enabledHalf st M := by
  unfold enabledHalf
  iintro ⟨H, #Hv⟩
  iexists b; iframe H Hv

/-- The `*AuthInfo` `a` at `dq` holds `ai`: `none`, a `nil` pointer; `some info`, the message. -/
def authInfoAt (a : Loc) (dq : DFrac) (ai : Option AuthInfo) : IProp GF :=
  match ai with
  | none => iprop(⌜a = null⌝)
  | some info => iprop(a ↦{dq} info)

/-- **A cache map of the state `sta`** (persistent): its keys `sta`'s users, each entry the
user's permissions at `sta` (`cacheEntryIs`). -/
def cacheOf (sta : AuthState) (Mp : GMap GoString Loc) : IProp GF :=
  iprop(⌜∀ u, (Mp !! u).isSome ↔ (sta.users !! u).isSome⌝ ∗
    [∗map] u ↦ p ∈ Mp, ∃ Lr Lw, permsAt p Lr Lw ∗ ⌜cacheEntryIs sta u Lr Lw⌝)

set_option synthInstance.maxSize 512 in
instance cacheOf_persistent (sta : AuthState) (Mp : GMap GoString Loc) :
    Persistent (cacheOf (GF := GF) sta Mp) := by
  unfold cacheOf; infer_instance

/-- **A state's permissions by user** (the auth plan's E3h): for each user of the state, the
permissions its roles grant (`userPerms`); what a permission cache of the state holds
(`cacheOf_permView`), whatever the flag, the revision and the roles' other contents. -/
def permView (s : AuthState) : GoString → Option (List Perm) :=
  fun u => (s.users !! u).map (userPerms s)

theorem cacheEntryIs_permView (s s' : AuthState) (h : permView s = permView s') (u : GoString)
    (Lr Lw : List adt.Entry) : cacheEntryIs s u Lr Lw → cacheEntryIs s' u Lr Lw := by
  have hu := congrFun h u
  unfold permView at hu
  rintro ⟨roles, hr, h1, h2⟩
  rw [hr] at hu
  cases hr' : s'.users !! u with
  | none => rw [hr'] at hu; cases hu
  | some roles' =>
    rw [hr'] at hu
    simp only [Option.map_some, Option.some.injEq] at hu
    refine ⟨roles', hr', ?_, ?_⟩
    · rw [← hu]; exact h1
    · rw [← hu]; exact h2

theorem cacheOf_permView (s s' : AuthState) (h : permView s = permView s') (Mp : GMap GoString Loc) :
    cacheOf (GF := GF) s Mp ⊢ cacheOf s' Mp := by
  unfold cacheOf
  iintro ⟨%Hdom, #Hall⟩
  isplitr
  · ipureintro
    intro u
    rw [Hdom u]
    have hu := congrFun h u
    unfold permView at hu
    cases h1 : s.users !! u <;> cases h2 : s'.users !! u <;> simp_all
  iapply (BigSepM.bigSepM_mono (Φ := fun (u : GoString) (p : Loc) =>
      iprop(∃ Lr Lw, permsAt p Lr Lw ∗ ⌜cacheEntryIs s u Lr Lw⌝))) ?_ $$ Hall
  intro u p _
  iintro ⟨%Lr, %Lw, Hp, %He⟩
  iexists Lr, Lw
  iframe Hp
  ipureintro; exact cacheEntryIs_permView s s' h u Lr Lw He

/-- **A share `q` of the cache's ghost variable at the map `mp` of the state at the index `j`**
(the auth plan's E3h): in `on γa`, `ghostVar γa.fca q (mp, j)`; otherwise nothing. The guard holds
a half (`caGM`, with the map's model at that state), the admin side a quarter (`caA`), the store's
freshness a quarter (`revFresh`: the state at `j` has the permissions of a state no older than the
published index). -/
def caG (M : AuthMode) (q : Qp) (v : GoMap × Nat) : IProp GF :=
  match M with
  | .on γa => ghostVar γa.fca q v
  | _ => iprop(True)

instance caG_timeless (M : AuthMode) (q : Qp) (v : GoMap × Nat) : Timeless (caG (GF := GF) M q v) := by
  unfold caG; cases M <;> infer_instance

/-- **The guard's share of the cache's ghost variable for the map `mp` holding `Mp`**: in `on γa`,
the share at `(mp, j)`, the map the cache of the state recorded at `j`; otherwise nothing. -/
def caGM (M : AuthMode) (q : Qp) (mp : GoMap) (Mp : GMap GoString Loc) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (j : Nat) (sj : AuthState), ghostVar γa.fca q (mp, j) ∗ authStateAt γa j sj ∗
      cacheOf sj Mp)
  | _ => iprop(True)

theorem caGM_split (M : AuthMode) (q1 q2 : Qp) (mp : GoMap) (Mp : GMap GoString Loc) :
    caGM (GF := GF) M (q1 + q2) mp Mp ⊣⊢ caGM M q1 mp Mp ∗ caGM M q2 mp Mp := by
  cases M with
  | on γa =>
    simp only [caGM]
    constructor
    · iintro ⟨%j, %sj, H, #Hs, #Hc⟩
      icases ((ghostVar_fractional γa.fca (mp, j)).fractional q1 q2).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists j, sj; iframe H1 Hs Hc
      · iexists j, sj; iframe H2 Hs Hc
    · iintro ⟨⟨%j, %sj, H1, #Hs, #Hc⟩, ⟨%j', %sj', H2, -, -⟩⟩
      icombine H1 H2 gives %Heq
      obtain ⟨-, Heq⟩ := Heq
      cases Heq
      iexists j, sj
      iframe Hs Hc
      iapply ((ghostVar_fractional γa.fca (mp, j)).fractional q1 q2).2 $$ [$H1 $H2]
  | off =>
    simp only [caGM]
    constructor
    · iintro -; isplitl []; itrivial; itrivial
    · iintro -; itrivial
  | any =>
    simp only [caGM]
    constructor
    · iintro -; isplitl []; itrivial; itrivial
    · iintro -; itrivial

/-- **The admin side's quarter of the cache's ghost variable for the map `mp` of the state `sc`**:
in `on γa`, the quarter at `(mp, j)`, the state at `j` with `sc`'s permissions; otherwise
nothing. -/
def caA (M : AuthMode) (mp : GoMap) (sc : AuthState) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (j : Nat) (sj : AuthState), ghostVar γa.fca (1 : Qp).half.half (mp, j) ∗
      authStateAt γa j sj ∗ ⌜permView sj = permView sc⌝)
  | _ => iprop(True)

/-- `caA` holds for any state with the same permissions. -/
theorem caA_congr (M : AuthMode) (mp : GoMap) (sa sb : AuthState) (h : permView sa = permView sb) :
    caA (GF := GF) M mp sa ⊢ caA M mp sb := by
  cases M with
  | on γa =>
    simp only [caA]
    iintro ⟨%j, %sj, H, #Hs, %Hp⟩
    iexists j, sj; iframe H Hs; ipureintro; rw [Hp, h]
  | off => simp only [caA]; iintro -; itrivial
  | any => simp only [caA]; iintro -; itrivial

/-- What `rangePermCacheMu` guards at `q` in the mode `M`: half of the field `rangePermCache`
(the other half is the admin side's, `cacheHalf`: only the apply thread replaces the map,
`refreshRangePermCache`, under the lock, with both halves; the auth plan's E2r, 2026-10-26), the map
it points to, read-only (`refreshRangePermCache` builds a new map and never writes it again), its
model `cacheOk`, and (E3h) half of the cache's ghost variable at the map (`caGM`). -/
def cacheP (st : Loc) (M : AuthMode) (q : Qp) : IProp GF :=
  iprop(∃ (mp : GoMap) (Mp : GMap GoString Loc), aF go!"rangePermCache" st ↦{DFrac.own q.half} mp ∗
    mp ↦${DFrac.discard} Mp ∗ cacheOk M Mp ∗ caGM M q.half mp Mp)

/-- **The admin side's half of the cache at the state `sta`** (the auth plan's E2r): half of the
field `rangePermCache`, the map it points to (read-only) and the map's model, `sta`'s cache
(`cacheOf`); what `refreshRangePermCache` gives the apply thread back; with (E3h) a quarter of the
cache's ghost variable at the map (`caA`). -/
def cacheAt (st : Loc) (M : AuthMode) (sta : AuthState) : IProp GF :=
  iprop(∃ (mp : GoMap) (Mp : GMap GoString Loc),
    aF go!"rangePermCache" st ↦{DFrac.own (1 : Qp).half} mp ∗ mp ↦${DFrac.discard} Mp ∗ cacheOf sta Mp ∗
    caA M mp sta)

/-- **The admin side's half of the cache** in the mode `M` (the auth plan's E2r; in `authWR`): at
some state of the mode (`authSnap`). -/
def cacheHalf (st : Loc) (M : AuthMode) : IProp GF :=
  iprop(∃ sta : AuthState, cacheAt st M sta ∗ authSnap M sta)

theorem cacheHalf_of_at (st : Loc) (M : AuthMode) (sta : AuthState) :
    cacheAt (GF := GF) st M sta ⊢ authSnap M sta -∗ cacheHalf st M := by
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
buffer before the next read transaction begins); and, for a reader holding a lower bound `i` of the
history's published index (`authPubLbM`), a state no older than `i` (`authSnapFrom`; the auth
plan's E3g, 2026-10-27, the reads' freshness the user chose: a state is published only once its
batch is committed, so a real backend's read transaction begun afterwards sees it or a later one).
(The auth plan's S1, 2026-10-23; until then: a token holding no state, `UnsafeGetUser` returning
any pointer.) In `on γa`, for the backend `γc` (the auth-on snapshot plan's Freeze, 2026-11-03;
`notes/decisions.md`, "The auth-on snapshot install"): the readers' clause and the freshness clause
take a part of the backend's currency (`authCur γc q`, given back at `RLock`): a retired, released
backend's reads cannot begin (after its `Close` its read transaction dereferences a nil bolt
transaction), and a read begun before is safe, as Go's `Close` waits for the read transaction's
holders; the latest clause takes the write token with the history's half (`authWTok γc ∗
authHistHalf γa hs`): no batch of the apply thread's is open, so the read buffer holds what its last
batch committed. -/
def authReadTxOk (tx : GoInterface) (R : IProp GF) (M : AuthMode) (γc : AuthBkNames) : IProp GF :=
  match M with
  | .on γa => iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗ ∃ Hs : AuthState → IProp GF,
      □ (∀ q : Qp, {{ R ∗ authCur γc q }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
        {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnap (.on γa) st ∗ authCur γc q }}) ∗
      □ (∀ (i : Nat) (q : Qp),
        {{ R ∗ authPubLbM (.on γa) i ∗ authCur γc q }}
          (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
        {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnapFrom (.on γa) i st ∗ authCur γc q }}) ∗
      □ (∀ hs : List AuthState,
        {{ R ∗ authWTok γc ∗ authHistHalf γa hs }}
          (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
        {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnap (.on γa) st ∗ authWTok γc ∗
            authHistHalf γa hs ∗ ⌜hs.getLast? = some st⌝ }}) ∗
      authTxReads ti R Hs)
  | _ => iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗ ∃ Hs : AuthState → IProp GF,
    □ ({{ R }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnap M st }}) ∗
    □ (∀ hs : List AuthState,
      {{ R ∗ authOwn M hs }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnap M st ∗ authOwn M hs ∗ ⌜histLast M hs st⌝ }}) ∗
    □ (∀ i : Nat,
      {{ R ∗ authPubLbM M i }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
      {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnapFrom M i st }}) ∗
    authTxReads ti R Hs)

instance authReadTxOk_persistent (tx : GoInterface) (R : IProp GF) (M : AuthMode)
    (γc : AuthBkNames) : Persistent (authReadTxOk (GF := GF) tx R M γc) := by
  unfold authReadTxOk; cases M <;> infer_instance

/-- **The auth backend** `be` (an `AuthBackend`, not nil; a contract): `ReadTx()` returns a read
transaction (`authReadTxOk`) for `R` in the mode `M`, of the backend's names `γc`. -/
def authBackendOk (be : GoInterface) (R : IProp GF) (M : AuthMode) (γc : AuthBkNames) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜be = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (tx : GoInterface), RET #tx; authReadTxOk tx R M γc }}))

instance authBackendOk_persistent (be : GoInterface) (R : IProp GF) (M : AuthMode)
    (γc : AuthBkNames) : Persistent (authBackendOk (GF := GF) be R M γc) := by
  unfold authBackendOk; infer_instance

/-- **An auth info bound to the token `token`** in the mode `M` (persistent; the auth plan's S5):
not nil, its user (read-only) one the token was issued to (`tokOk`: in `on γa`, `tokIssued`). -/
def infoBound (M : AuthMode) (token : GoString) (a : Loc) : IProp GF :=
  iprop(⌜a ≠ null⌝ ∗ ∃ user : GoString, aiF go!"Username" a ↦□ user ∗ tokOk M token user)

instance infoBound_persistent (M : AuthMode) (token : GoString) (a : Loc) :
    Persistent (infoBound (GF := GF) M token a) := by
  unfold infoBound; infer_instance

/-- **The token a call's metadata carries** (`ctxTokenOf`'s, over the metadata itself: what a
metadata-indexed gRPC spec sees of the attempt; moved from `client/v3/InvKVConn.lean` in G2,
2026-10-30, so that the server's watch registration can name it). -/
def mdTokenOf (md : Option (GoString → Option (List GoString))) : Option GoString :=
  match md with
  | none => none
  | some md =>
    match md go!"token" with
    | some (v :: _) => some (strings.trimPrefix v go!"Bearer ")
    | some [] => none
    | none =>
      match md go!"authorization" with
      | some (v :: _) => some (strings.trimPrefix v go!"Bearer ")
      | _ => none

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

/-- A context's token is its incoming metadata's (moved from `client/v3/KVServiceOn.lean`, G2). -/
theorem ctxTokenOf_md (ctx : GoInterface) : ctxTokenOf ctx = mdTokenOf (metadata.incomingOf ctx) :=
  rfl

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
in; C1's A2, 2026-10-28: `Value` is promised at those two keys only, not "any key, unconstrained
but for those two", since `context.WithValue`'s trust-boundary axiom does not speak of a key of
one of the stored keys' types but a different value), and the caller holds the right to issue the token they make
(`freshOk M (simpleTok pre idx)`: a token is `<prefix>.<raft index>`, issued once; the simple
provider panics on a token issued twice, `assignSimpleTokenToUser`); the prefix one the provider
makes (`tokPrefixOk`, no space; 2026-10-30). -/
def authnCtx (M : AuthMode) (ctx : GoInterface) : IProp GF :=
  iprop(∃ (ci : GoInterfaceOk) (idx : w64) (pre : GoString), ⌜ctx = GoInterface.ok ci⌝ ∗
    □ (∀ x : AuthenticateParamIndex,
      {{ True }} (App (Val #(methods ci.ty go!"Value" ci.v))
        (Val #(interface.mkOk AuthenticateParamIndex.ty #x)))
      {{ (v : GoInterface), RET #v; ⌜v = interface.mkOk go.uint64 #idx⌝ }}) ∗
    □ (∀ x : AuthenticateParamSimpleTokenPrefix,
      {{ True }} (App (Val #(methods ci.ty go!"Value" ci.v))
        (Val #(interface.mkOk AuthenticateParamSimpleTokenPrefix.ty #x)))
      {{ (v : GoInterface), RET #v; ⌜v = interface.mkOk go.string #pre⌝ }}) ∗
    freshOk M (simpleTok pre idx) ∗ ⌜tokPrefixOk pre⌝)

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
  token was issued to `username` (`tokOk`), else the error is one of the package's (`authErrOf`,
  C1's A2: `Authenticate` returns it as its own); on an `Authenticate` context (`authnCtx`: its
  index and prefix, and the right to issue the token; S5b).
- `genTokenPrefix()` (appended, C1's A4, 2026-10-29) returns a prefix with no space (`tokPrefixOk`,
  2026-10-31) and no error (the simple provider's draws random letters,
  `tokenSimple.genTokenPrefix`'s trust-boundary axiom; the no-op and JWT providers' return `""`).
The simple provider meets it (`auth/TokenSimple.lean`, S5b-S5d) but for `info`'s context premise:
its `info` waits on the raft index its token names and on the context's `Done()`, which this
module (generic in the later credits, Perennial's contexts are not) cannot state; the JWT
provider's binding is its signature's, and it does not meet `assign`'s error clause (its
`ErrVerifyOnly` and its signing errors are not the package's variables): out of scope. -/
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
          (⌜err = GoInterface.nil⌝ ∗ tokOk M t user) ∨
            (⌜err ≠ GoInterface.nil⌝ ∗ ∃ e : AuthErr, authErrOf e err) }}) ∗
    □ ({{ True }} (App (Val #(methods ti.ty go!"genTokenPrefix" ti.v)) (Val #()))
      {{ (s : GoString) (err : GoInterface), RET (PairV #s #err);
          ⌜err = GoInterface.nil ∧ tokPrefixOk s⌝ }}))

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
          (⌜err = GoInterface.nil⌝ ∗ tokOk M t user) ∨
            (⌜err ≠ GoInterface.nil⌝ ∗ ∃ e : AuthErr, authErrOf e err) }}) ∗
    □ ({{ True }} (App (Val #(methods ti.ty go!"genTokenPrefix" ti.v)) (Val #()))
      {{ (s : GoString) (err : GoInterface), RET (PairV #s #err);
          ⌜err = GoInterface.nil ∧ tokPrefixOk s⌝ }}))

instance tokenProviderOk_persistent (tp : GoInterface) (M : AuthMode) :
    Persistent (tokenProviderOk (GF := GF) tp M) := by
  unfold tokenProviderOk; infer_instance

/-! ### The currency's invariant (R-D2, 2026-11-04)

The current backend's currency (`authCur γc`) is not in `beMu`'s resource (`beP`) but in an
invariant of the store, `curInv` (`notes/decisions.md`, "R-D2: the auth store's currency in an
invariant"): a reader in `lockedReadTx`, between `beMu.RLock()` and `RUnlock()`, deposits one of its
ticket's two tokens (`rdTicketM`, inside `beRd`) and half of `beP`'s piece of the backend's name, and
takes `curEps K` of the currency, which it lends to the read transaction's `RLock()`; it takes the
deposit back with the currency's return. `Recover`, under the write lock, holds all of `beP`'s piece,
so no deposit is in (`n = 0`) and the currency is whole; a holder of every ticket (the server's
abandoned store, `authRd_abandon`) finds no deposit either, takes the whole currency and leaves the
invariant abandoned (every token in, so no reader can enter; half the name in, so no `Recover`). -/

/-- The share of the currency a reader in its section holds, of `K` tokens in all. -/
def curEps (K : Nat) : Qp := (1 : Qp) / sync.posToQpZ ((K : Int) + 1)

/-- What the invariant holds of the currency while `n` readers are in their section. -/
def curFrac (K n : Nat) : Qp := QpMul (sync.posToQpZ ((K : Int) + 1 - (n : Int))) (curEps K)

theorem curFrac_val (K n : Nat) (h : n ≤ K) :
    (curFrac K n).val = (((K : Int) + 1 - (n : Int) : Int) : Rat) / (((K : Int) + 1 : Int) : Rat) := by
  simp only [curFrac, curEps, QpMul, Qp.val_div, Qp.val_one]
  rw [sync.posToQpZ_val _ (by omega), sync.posToQpZ_val _ (by omega)]
  rw [Rat.div_def, Rat.one_mul, Rat.div_def]

theorem curFrac_S (K n : Nat) (h : n + 1 ≤ K) : curFrac K n = curEps K + curFrac K (n + 1) := by
  rw [Qp.ext_iff, Qp.val_add, curFrac_val K n (by omega), curFrac_val K (n + 1) h]
  simp only [curEps, Qp.val_div, Qp.val_one]
  rw [sync.posToQpZ_val _ (by omega)]
  rw [Rat.div_def, Rat.div_def, Rat.div_def, ← Rat.add_mul]
  congr 1
  push_cast
  grind

theorem curFrac_0 (K : Nat) : curFrac K 0 = 1 := by
  rw [Qp.ext_iff, curFrac_val K 0 (Nat.zero_le _)]
  rw [show (K : Int) + 1 - ((0 : Nat) : Int) = (K : Int) + 1 by omega, Qp.val_one, Rat.div_def,
    Rat.mul_inv_cancel]
  exact_mod_cast (show (K : Int) + 1 ≠ 0 by omega)

/-- The invariant's namespace. -/
abbrev curN : Namespace := nroot.@"authCur"

/-- The piece of the backend's name a reader in its section deposits: half of `beP`'s at
`sync.rfrac` (`beCurM`). -/
abbrev rdDep : Qp := sync.rfrac.half.half.half

/-- **The store's currency** (mode `on γa`; R-D2, 2026-11-04): `K` tokens in all (the tickets'
authority, discarded: `authRdTotal`), `n` of them deposited by the readers in their section, each
with a piece of the backend's name (`rdDep`); the invariant's quarter of the current backend's name
`γc` (the apply thread holds a half, `authWHeld`, and `beP` a quarter); and either the currency
less the readers' `curEps K` each (live), or (abandoned) the apply thread's half of the name with
every token and no reader in. -/
def curInv (γa : AuthNames) : IProp GF :=
  iprop(∃ (K n : Nat) (γc : AuthBkNames), ownTokAuthDfrac γa.rdt DFrac.discard K ∗
    ownToks γa.rdt n ∗ ([∗list] _x ∈ List.replicate n (), authBkCur γa rdDep γc) ∗
    authBkCur γa (1 : Qp).half.half γc ∗
    (authCur γc (curFrac K n) ∨ (authBkCur γa (1 : Qp).half γc ∗ ownToks γa.rdt K ∗ ⌜n = 0⌝)))

instance curInv_timeless (γa : AuthNames) : Timeless (curInv (GF := GF) γa) := by
  unfold curInv authBkCur authCur; infer_instance

/-- The currency's invariant (persistent). -/
def authCurInv (γa : AuthNames) : IProp GF := inv curN (curInv γa)

instance authCurInv_persistent (γa : AuthNames) : Persistent (authCurInv (GF := GF) γa) := by
  unfold authCurInv; infer_instance

/-- `a + b` tokens out are at most the discarded authority's count. -/
theorem toks_bound (γ : GName) (K a b : Nat) :
    ⊢ ownTokAuthDfrac (GF := GF) γ DFrac.discard K -∗ ownToks γ a -∗ ownToks γ b -∗
      ⌜a + b ≤ K⌝ ∗ ownToks γ a ∗ ownToks γ b := by
  iintro #Ha H1 H2
  ihave H := ownToks_add_2 b a γ $$ [H1 H2]
  · iframe H1 H2
  icombine Ha H gives %h
  icases ownToks_add_1 b a γ $$ H with ⟨H1, H2⟩
  iframe H1 H2
  ipureintro; exact h

instance authBkCur_combine_gives (γa : AuthNames) (q1 q2 : Qp) (γ1 γ2 : AuthBkNames) :
    CombineSepGives (authBkCur (GF := GF) γa q1 γ1) (authBkCur γa q2 γ2)
      iprop(⌜q1 + q2 ≤ 1 ∧ γ1 = γ2⌝) := by
  unfold authBkCur; exact ghostVar_combine_gives γa.bk γ1 q1 γ2 q2

/-- The whole of the backend's name, set to other names. -/
theorem authBkCur_update (γa : AuthNames) (γ γ' : AuthBkNames) :
    ⊢ authBkCur (GF := GF) γa 1 γ ==∗ authBkCur γa 1 γ' := by
  unfold authBkCur; exact ghostVar_update γ' γa.bk γ

/-- A piece of the backend's name as two halves. -/
theorem authBkCur_split_half (γa : AuthNames) (q : Qp) (γc : AuthBkNames) :
    authBkCur (GF := GF) γa q γc ⊣⊢ authBkCur γa q.half γc ∗ authBkCur γa q.half γc := by
  unfold authBkCur; exact ghostVar_split_half γa.bk q γc

/-- The whole of the backend's name, of a half and two quarters. -/
theorem authBkCur_whole (γa : AuthNames) (γc : AuthBkNames) :
    authBkCur (GF := GF) γa (1 : Qp).half γc ∗ authBkCur γa (1 : Qp).half.half γc ∗
      authBkCur γa (1 : Qp).half.half γc ⊣⊢ authBkCur γa 1 γc := by
  unfold authBkCur
  constructor
  · iintro ⟨H1, H2, H3⟩
    ihave H23 := (ghostVar_split_half γa.bk (1 : Qp).half γc).2 $$ [H2 H3]
    · iframe H2 H3
    iapply (ghostVar_split_half γa.bk 1 γc).2 $$ [H1 H23]
    iframe H1 H23
  · iintro H
    icases (ghostVar_split_half γa.bk 1 γc).1 $$ H with ⟨H1, H2⟩
    icases (ghostVar_split_half γa.bk (1 : Qp).half γc).1 $$ H2 with ⟨H2, H3⟩
    iframe H1 H2 H3

/-- Nothing beside the whole of the backend's name. -/
theorem authBkCur_excess (γa : AuthNames) (q : Qp) (γ1 γ2 : AuthBkNames) :
    ⊢ authBkCur (GF := GF) γa 1 γ1 -∗ authBkCur γa q γ2 -∗ False := by
  unfold authBkCur
  iintro H1 H2
  ihave %h := ghostVar_valid_2 γa.bk γ1 1 γ2 q $$ H1 H2
  exfalso
  have h1 := h.1
  have h2 := q.2
  simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at h1
  grind

/-- **The current backend's share under `beMu` at `q`, in the mode `M`** (the auth-on snapshot
plan's Freeze, 2026-11-03): in `on γa`, the share of the current backend's names (`authBkCur`, at
a quarter of the fraction: the apply thread holds a half, `authWHeld`, the currency's invariant a
quarter) and the currency's invariant (`authCurInv`); nothing in the other modes. (R-D2,
2026-11-04: until then at half the fraction, with the backend's currency at `q`, which only
`Recover`'s write lock could collect whole; `notes/decisions.md`, "R-D2: the auth store's currency in
an invariant".) -/
def beCurM (M : AuthMode) (q : Qp) (γc : AuthBkNames) : IProp GF :=
  match M with
  | .on γa => iprop(authBkCur γa q.half.half γc ∗ authCurInv γa)
  | _ => iprop(True)

/-- **The currency a read transaction's `RLock()` takes, in the mode `M`** (R-D2): `authCur γc q` in
`on γa`, nothing otherwise. -/
def authCurM (M : AuthMode) (q : Qp) (γc : AuthBkNames) : IProp GF :=
  match M with
  | .on _ => authCur γc q
  | _ => iprop(True)

theorem beCurM_split (M : AuthMode) (q1 q2 : Qp) (γc : AuthBkNames) :
    beCurM (GF := GF) M (q1 + q2) γc ⊣⊢ beCurM M q1 γc ∗ beCurM M q2 γc := by
  cases M with
  | on γa =>
    simp only [beCurM, authBkCur]
    have hh : (q1 + q2).half.half = q1.half.half + q2.half.half := Subtype.ext (by grind)
    rw [hh]
    constructor
    · iintro ⟨Hb, #Hi⟩
      icases ((ghostVar_fractional γa.bk γc).fractional q1.half.half q2.half.half).1 $$ Hb
        with ⟨Hb1, Hb2⟩
      isplitl [Hb1]
      · iframe Hb1 Hi
      · iframe Hb2 Hi
    · iintro ⟨⟨Hb1, #Hi⟩, ⟨Hb2, -⟩⟩
      iframe Hi
      iapply ((ghostVar_fractional γa.bk γc).fractional q1.half.half q2.half.half).2 $$ [$Hb1 $Hb2]
  | off =>
    simp only [beCurM]
    constructor
    · iintro -; isplitl [] <;> itrivial
    · iintro -; itrivial
  | any =>
    simp only [beCurM]
    constructor
    · iintro -; isplitl [] <;> itrivial
    · iintro -; itrivial

/-- **The read contract's latest clause, in any mode**: for the apply thread (the authority
`authOwn` with its write token `authWHeldM`) and a share of `beMu`'s backend (`beCurM`, whose
names the token's agree with), the state read is the history's last. -/
theorem authReadTxOk_latest (tx : GoInterface) (R : IProp GF) (M : AuthMode) (γc : AuthBkNames) :
    authReadTxOk (GF := GF) tx R M γc ⊢ ∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗
      ∃ Hs : AuthState → IProp GF,
      □ (∀ (hs : List AuthState) (q : Qp) (γw : AuthBkNames),
        {{ R ∗ authOwn M hs ∗ authWHeldM M γw ∗ beCurM M q γc }}
          (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
        {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnap M st ∗ authOwn M hs ∗ authWHeldM M γw ∗
            beCurM M q γc ∗ ⌜histLast M hs st⌝ }}) ∗
      authTxReads ti R Hs := by
  cases M with
  | on γa =>
    simp only [authReadTxOk]
    iintro ⟨%ti, %h, %Hs, -, -, #H3, #Hr⟩
    iexists ti
    isplitr
    · ipureintro; exact h
    iexists Hs
    isplitr
    · iintro !> %hs %q %γw %Φ !> ⟨HR, Hown, Hw, Hc⟩ HΦ
      simp only [authOwn, authWHeldM, authWHeld, beCurM]
      icases Hown with ⟨Hhh, Hcur⟩
      icases Hw with ⟨HT, Hb'⟩
      icases Hc with ⟨Hb, #Hcu⟩
      ihave %h : ⌜γw = γc⌝ $$ [Hb Hb']
      · unfold authBkCur
        icombine Hb' Hb gives %h
        ipureintro; exact h.2
      subst h
      iapply H3 $$ %hs [HR HT Hhh]
      · iframe HR HT Hhh
      inext
      iintro ⟨%st, Hst, #Hsn, HT, Hhh, %Hl⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn Hhh Hcur Hb Hcu
      isplitl [HT Hb']
      · iframe HT Hb'
      ipureintro; exact Hl
    iexact Hr
  | off =>
    simp only [authReadTxOk]
    iintro ⟨%ti, %h, %Hs, -, #H2, -, #Hr⟩
    iexists ti
    isplitr
    · ipureintro; exact h
    iexists Hs
    isplitr
    · iintro !> %hs %q %γw %Φ !> ⟨HR, Hown, Hw, Hc⟩ HΦ
      iapply H2 $$ %hs [HR Hown]
      · iframe HR Hown
      inext
      iintro ⟨%st, Hst, #Hsn, Hown, %Hl⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn Hown Hw Hc
      ipureintro; exact Hl
    iexact Hr
  | any =>
    simp only [authReadTxOk]
    iintro ⟨%ti, %h, %Hs, -, #H2, -, #Hr⟩
    iexists ti
    isplitr
    · ipureintro; exact h
    iexists Hs
    isplitr
    · iintro !> %hs %q %γw %Φ !> ⟨HR, Hown, Hw, Hc⟩ HΦ
      iapply H2 $$ %hs [HR Hown]
      · iframe HR Hown
      inext
      iintro ⟨%st, Hst, #Hsn, Hown, %Hl⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn Hown Hw Hc
      ipureintro; exact Hl
    iexact Hr

/-- Two shares merge, at the first's names (in `on γa` the names agree). -/
theorem beCurM_merge (M : AuthMode) (q1 q2 : Qp) (γ1 γ2 : AuthBkNames) :
    beCurM (GF := GF) M q1 γ1 ∗ beCurM M q2 γ2 ⊢ beCurM M (q1 + q2) γ1 := by
  cases M with
  | on γa =>
    iintro ⟨H1, H2⟩
    ihave %h : ⌜γ1 = γ2⌝ $$ [H1 H2]
    · simp only [beCurM, authBkCur]
      icases H1 with ⟨Hb1, -⟩
      icases H2 with ⟨Hb2, -⟩
      icombine Hb1 Hb2 gives %h
      ipureintro; exact h.2
    subst h
    iapply (beCurM_split (.on γa) q1 q2 γ1).2 $$ [$H1 $H2]
  | off => simp only [beCurM]; iintro -; itrivial
  | any => simp only [beCurM]; iintro -; itrivial

/-- What `beMu` guards at `q`: the backend `be` at half the fraction, with its contract
(`Recover` replaces it under the write lock). (D22 receiver epochs, S7c, 2026-10-23: the other half
of `be` is the store's user's, the server's apply thread, `authBeOn`, which `Recover` takes with
the write lock; so the user's half names the backend the store's writes go to. Until then `beMu`
held all of it.) With the backend's names `γc` and, in `on γa`, its share of them (`beCurM`; the
auth-on snapshot plan's Freeze, 2026-11-03; R-D2, 2026-11-04: with the currency's invariant, not the
currency, which the invariant holds). -/
def beP (st : Loc) (R : IProp GF) (M : AuthMode) (q : Qp) : IProp GF :=
  iprop(∃ (be : AuthBackend) (γc : AuthBkNames), aF go!"be" st ↦{DFrac.own q.half} be ∗
    authBackendOk be R M γc ∗ beCurM M q γc)

/-- **The read contract's clauses for a reader, in any mode**: the readers' clause and the
freshness clause, each over `authCurM M q γc` (in `on γa`, the currency `authCur γc q` they take;
R-D2, 2026-11-04: until then over `beP`'s share `beCurM`, which held it). -/
theorem authReadTxOk_rd (tx : GoInterface) (R : IProp GF) (M : AuthMode) (γc : AuthBkNames) :
    authReadTxOk (GF := GF) tx R M γc ⊢ ∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗
      ∃ Hs : AuthState → IProp GF,
      □ (∀ q : Qp, {{ R ∗ authCurM M q γc }} (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
        {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnap M st ∗ authCurM M q γc }}) ∗
      □ (∀ (i : Nat) (q : Qp),
        {{ R ∗ authPubLbM M i ∗ authCurM M q γc }}
          (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
        {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnapFrom M i st ∗ authCurM M q γc }}) ∗
      authTxReads ti R Hs := by
  cases M with
  | on γa =>
    simp only [authReadTxOk, authCurM]
    iintro ⟨%ti, %h, %Hs, #H1, #H2, -, #Hr⟩
    iexists ti
    isplitr
    · ipureintro; exact h
    iexists Hs
    isplitr
    · iintro !> %q %Φ !> ⟨HR, Hc⟩ HΦ
      iapply H1 $$ %q [HR Hc]
      · iframe HR Hc
      inext
      iintro ⟨%st, Hst, #Hsn, Hc⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn Hc
    isplitr
    · iintro !> %i %q %Φ !> ⟨HR, #Hlb, Hc⟩ HΦ
      iapply H2 $$ %i %q [HR Hc]
      · iframe HR Hlb Hc
      inext
      iintro ⟨%st, Hst, #Hsn, Hc⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn Hc
    iexact Hr
  | off =>
    simp only [authReadTxOk, authCurM]
    iintro ⟨%ti, %h, %Hs, #H1, -, #H2, #Hr⟩
    iexists ti
    isplitr
    · ipureintro; exact h
    iexists Hs
    isplitr
    · iintro !> %q %Φ !> ⟨HR, -⟩ HΦ
      iapply H1 $$ HR
      inext
      iintro ⟨%st, Hst, #Hsn⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn
    isplitr
    · iintro !> %i %q %Φ !> ⟨HR, #Hlb, -⟩ HΦ
      iapply H2 $$ %i [HR]
      · iframe HR Hlb
      inext
      iintro ⟨%st, Hst, #Hsn⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn
    iexact Hr
  | any =>
    simp only [authReadTxOk, authCurM]
    iintro ⟨%ti, %h, %Hs, #H1, -, #H2, #Hr⟩
    iexists ti
    isplitr
    · ipureintro; exact h
    iexists Hs
    isplitr
    · iintro !> %q %Φ !> ⟨HR, -⟩ HΦ
      iapply H1 $$ HR
      inext
      iintro ⟨%st, Hst, #Hsn⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn
    isplitr
    · iintro !> %i %q %Φ !> ⟨HR, #Hlb, -⟩ HΦ
      iapply H2 $$ %i [HR]
      · iframe HR Hlb
      inext
      iintro ⟨%st, Hst, #Hsn⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn
    iexact Hr

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
  | .on γa => iprop(∃ st : AuthState, authCurHalf γa st ∗ ⌜uint.nat r = st.revision⌝ ∗
      ∃ hs : List AuthState, authHistRev γa hs ∗ capLb γa hs)
  | _ => iprop(True)

instance revCur_timeless (M : AuthMode) (r : w64) : Timeless (revCur (GF := GF) M r) := by
  unfold revCur authCurHalf; cases M <;> infer_instance

/-- **The store's freshness** in the mode `M` at the atomic's value `r` (the auth plan's E3h,
2026-10-27; `notes/decisions.md`, "E3h of the auth plan"): in `on γa`, the published index `p`'s
authority (`authPubQ`; a reader's lower bound `authPubLb γa i` is at most `p`), `p` an index of
the history, `r` the revision of a state recorded at an index at least `p`, a quarter of the field
`enabled`'s ghost variable (`enG`) at the flag of such a state, and a quarter of the cache's ghost
variable (`caG`) at a map of a state with the permissions of such a state (`permView`) (so a reader with the lower
bound `i` reads a revision and, under the locks, a flag and a cache no older than `i`'s); in the
other modes nothing. The authority at half (`authPubQ γa ½`; the auth-on snapshot plan's Freeze,
2026-11-03: the realization holds a quarter, the apply thread a quarter, `authPubTok`). -/
def revFresh (M : AuthMode) (r : w64) : IProp GF :=
  match M with
  | .on γa => iprop(∃ p : Nat, authPubQ γa (1 : Qp).half p ∗ (∃ sp : AuthState, authStateAt γa p sp) ∗
      (∃ (j : Nat) (s : AuthState), authStateAt γa j s ∗ ⌜p ≤ j ∧ uint.nat r = s.revision⌝) ∗
      (∃ b : Bool, ghostVar γa.fen (1 : Qp).half.half b ∗
        ∃ (j : Nat) (s : AuthState), authStateAt γa j s ∗ ⌜p ≤ j ∧ b = s.enabled⌝) ∗
      ∃ v : GoMap × Nat, ghostVar γa.fca (1 : Qp).half.half v ∗
        ∃ (s : AuthState) (j' : Nat) (s' : AuthState), authStateAt γa v.2 s ∗ authStateAt γa j' s' ∗
          ⌜p ≤ j' ∧ permView s = permView s'⌝)
  | _ => iprop(True)

instance revFresh_timeless (M : AuthMode) (r : w64) : Timeless (revFresh (GF := GF) M r) := by
  unfold revFresh authPubQ authStateAt; cases M <;> infer_instance

/-- The invariant of `revision` (an atomic) in the mode `M`: a recorded state's revision
(`revisionVerdict`; the auth plan's S3), the latest's (`revCur`; S4), and the store's freshness
(`revFresh`; E3h). -/
def revInv (st : Loc) (M : AuthMode) : IProp GF :=
  iprop(∃ r : w64, aF go!"revision" st ↦ r ∗ revisionVerdict M r ∗ revCur M r ∗ revFresh M r)

/-- **The auth store** at `as` (persistent), its backend's read resource `R`, its mode `M`: the
atomic `revision`'s invariant, the read-only `lg` (not nil) and `tokenProvider` with its contract,
and the guards of its three locks (`beMu`'s holds `be` with its contract in the mode). -/
def authInv (st : Loc) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(⌜st ≠ null⌝ ∗ inv (nroot.@"authRev") (revInv st M) ∗
    (∃ lg : Loc, aF go!"lg" st ↦□ lg ∗ zapLoggerOk lg) ∗
    sync.isRWMutexGuard (aF go!"beMu" st) (beP st R M) ∗
    (∃ tp : TokenProvider, aF go!"tokenProvider" st ↦□ tp ∗ tokenProviderOk tp M) ∗
    sync.isRWMutexGuard (aF go!"enabledMu" st) (enabledP st M) ∗
    sync.isRWMutexGuard (aF go!"rangePermCacheMu" st) (cacheP st M))

instance authInv_persistent (st : Loc) (R : IProp GF) (M : AuthMode) :
    Persistent (authInv (GF := GF) st R M) := by
  unfold authInv; infer_instance

/-- **Every recorded state is below the cap** (H5, 2026-10-29): the store's revision invariant keeps
a quarter of the history with the cap's lower bound at it (`revCur`), so a recorded state `s` at `i`
is the `i`-th of a lower bound of the cap. -/
theorem authStateAt_capped (st : Loc) (R : IProp GF) (γa : AuthNames) (i : Nat) (s : AuthState)
    (E : CoPset) (hE : ↑(nroot.@"authRev") ⊆ E) :
    authInv (GF := GF) st R (.on γa) ∗ authStateAt γa i s ={E}=∗
      ∃ C, capLb γa C ∗ ⌜C[i]? = some s⌝ := by
  iintro ⟨#Hinv, #Hs⟩
  iunfold authInv at Hinv
  icases Hinv with ⟨-, #Hrev, -⟩
  iinv Hrev with Hi Hclose
  iunfold revInv at Hi
  icases Hi with ⟨%r, >Hr, Hv, >Hc, Hf⟩
  iunfold revCur at Hc
  icases Hc with ⟨%stc, Hc, %Hrc, %hh, Hq, #Hcl⟩
  ihave %Hlk := authHistRev_lookup γa hh i s $$ Hq Hs
  imod Hclose $$ [Hr Hv Hc Hq Hf] with -
  · inext; iunfold revInv; iexists r; iframe Hr Hv Hf
    iunfold revCur; iexists stc; iframe Hc; isplitr
    · ipureintro; exact Hrc
    · iexists hh; iframe Hq Hcl
  imodintro
  iexists hh; iframe Hcl; ipureintro; exact Hlk

/-- **The admin side's history is below the cap** (H5): the authority's history `hs` is the revision
invariant's quarter's (`authHistRev`), which it keeps with the cap's lower bound at it (`revCur`). -/
theorem authOwn_capped (st : Loc) (R : IProp GF) (γa : AuthNames) (hs : List AuthState)
    (E : CoPset) (hE : ↑(nroot.@"authRev") ⊆ E) :
    authInv (GF := GF) st R (.on γa) ∗ authOwn (.on γa) hs ={E}=∗
      authOwn (.on γa) hs ∗ capLb γa hs := by
  iintro ⟨#Hinv, Ho⟩
  iunfold authOwn at Ho
  icases Ho with ⟨Hh, Hcur⟩
  iunfold authHistHalf at Hh
  icases Hh with ⟨Hh, %Hpk⟩
  iunfold authInv at Hinv
  icases Hinv with ⟨-, #Hrev, -⟩
  iinv Hrev with Hi Hclose
  iunfold revInv at Hi
  icases Hi with ⟨%r, >Hr, Hv, >Hc, Hf⟩
  iunfold revCur at Hc
  icases Hc with ⟨%stc, Hc, %Hrc, %hh, Hq, #Hcl⟩
  iunfold authHistRev at Hq
  ihave %Hag := monoListAuthOwn_agree γa.hist _ _ hs hh $$ Hh Hq
  obtain ⟨-, rfl⟩ := Hag
  imod Hclose $$ [Hr Hv Hc Hq Hf] with -
  · inext; iunfold revInv; iexists r; iframe Hr Hv Hf
    iunfold revCur; iexists stc; iframe Hc; isplitr
    · ipureintro; exact Hrc
    · iexists hs; iunfold authHistRev; iframe Hq Hcl
  imodintro
  iframe Hcl
  iunfold authOwn
  isplitl [Hh]
  · iunfold authHistHalf; iframe Hh; ipureintro; exact Hpk
  iexact Hcur

end defs

/-! The write side is at `HasLC.hasLC`: its critical-section contract is the API's
(`srvApi.csContractA`, over `mvcc.api.hookRun`; strict M1, 2026-11-05). -/
section wdefs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-! ## The write side (the auth plan's S4, 2026-10-24) -/

/-- **The batch transaction's lock token** `Lk st X`: the backend's auth buckets hold the state
`st` (pending: the transaction's writes change it), `X` is given back at `Unlock`. The batch
transaction `ti` (an `AuthBatchTx`; a contract, as the lessor's `leaseBatchTx`) with the hook `P
f` (the apply package's: `Lock()` is the backend's `LockInsideApply`, which runs the post-lock
hook, `srvApi.csContractA` over the API's `hookRun`), the write token `T` (the write-back the real backend's `Unlock` spends,
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
bound is fatal: `nonissues/etcd-auth-record-too-large-fatal.md`, the premise `authRecordsFit` of
`NewAuthStore`'s axiom, which the derivation of this contract from the real backend will take). -/
def authBatchTxLk (ti : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : GoFunc) (T : IProp GF)
    (Lk : AuthState → IProp GF → IProp GF) : IProp GF :=
  iprop(□ (∀ (hs : List AuthState) (Pre Q Post : IProp GF),
      {{ srvApi.csContractA P f Pre Q Post ∗ T ∗ authOwn M hs }}
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
    □ (∀ (st : AuthState) (X : IProp GF) (r : Loc) (rr : RoleRec) (ps : Role),
      {{ Lk st X ∗ ownRole r rr ∗ ⌜rr.name.length ≤ backend.maxKeySize ∧ rr.toRole.Perm ps⌝ }}
        (App (Val #(methods ti.ty go!"UnsafePutRole" ti.v)) (Val #r))
      {{ RET #(); Lk (putRole st rr.name ps) X ∗ ownRole r rr }}) ∗
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

instance authBatchTxLk_persistent (ti : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : GoFunc)
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
def authBatchTxLkR (ti : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : GoFunc) (T : IProp GF)
    (Lk : AuthState → IProp GF → IProp GF) : IProp GF :=
  iprop(□ (∀ (Pre Q Post : IProp GF),
      {{ srvApi.csContractA P f Pre Q Post ∗ T }}
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
    □ (∀ (st : AuthState) (X : IProp GF) (r : Loc) (rr : RoleRec) (ps : Role),
      {{ Lk st X ∗ ownRole r rr ∗ ⌜rr.name.length ≤ backend.maxKeySize ∧ rr.toRole.Perm ps⌝ }}
        (App (Val #(methods ti.ty go!"UnsafePutRole" ti.v)) (Val #r))
      {{ RET #(); Lk (putRole st rr.name ps) X ∗ ownRole r rr }}) ∗
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

instance authBatchTxLkR_persistent (ti : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : GoFunc)
    (T : IProp GF) (Lk : AuthState → IProp GF → IProp GF) :
    Persistent (authBatchTxLkR ti M P f T Lk) := by
  unfold authBatchTxLkR; infer_instance

/-- **The backend's batch transaction** `tx` (a contract): some lock token (`authBatchTxLk`). -/
def authBatchTxOk (tx : GoInterface) (M : AuthMode) (P : IProp GF) (f : GoFunc) (T : IProp GF) :
    IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗
    ∃ Lk : AuthState → IProp GF → IProp GF, authBatchTxLk ti M P f T Lk)

instance authBatchTxOk_persistent (tx : GoInterface) (M : AuthMode) (P : IProp GF) (f : GoFunc)
    (T : IProp GF) : Persistent (authBatchTxOk tx M P f T) := by
  unfold authBatchTxOk; infer_instance

/-- What `GetAllUsers()` returns of the state `st` (the auth plan's E2j): a slice of messages, one
per user of the state, each once (`userOut`, in no promised order; nil when there is none). -/
def usersOut (s : GoSlice) (st : AuthState) : IProp GF :=
  iprop(∃ (us : List Loc) (names : List GoString), s ↦* us ∗
    ⌜us.length = names.length ∧ names.Nodup ∧ ∀ n, n ∈ names ↔ (st.users.lookup n).isSome⌝ ∗
    [∗list] x ∈ us.zip names, userOut x.1 st x.2)

/-- **A role name `GetAllRoles()` lists** (auth-schema-fix F3, 2026-11-12, decided by
etcd-grove-81): schema's `unsafeGetAllRoles` ranges the roles' bucket over `[0x00, 0xff)`
(`schema/auth_roles.go:91`; `unsafeRange` keeps keys below the end), so it lists a role whose name
is non-empty and below `"\xff"`; a name starting with the byte `0xff` (never valid UTF-8, which
etcd's request strings are) is skipped (`nonissues/etcd-auth-getallroles-ff-names.md`). -/
def roleListed (n : GoString) : Prop := n ≠ [] ∧ go.GoStringLt n [W8 255]

/-- What `GetAllRoles()` returns of the state `st` (the auth plan's E2j): as `usersOut`, the
state's roles (`roleOut`) whose names it lists (`roleListed`; until auth-schema-fix F3 every role,
false of a role named `"\xff"`: S0's F3). -/
def rolesOut (s : GoSlice) (st : AuthState) : IProp GF :=
  iprop(∃ (rs : List Loc) (names : List GoString), s ↦* rs ∗
    ⌜rs.length = names.length ∧ names.Nodup ∧
      ∀ n, n ∈ names ↔ (st.roles.lookup n).isSome ∧ roleListed n⌝ ∗
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
  transaction's twin panics (`nonissues/etcd-auth-readtx-getallroles-panics.md`), the batch
  transaction's range of the roles' bucket does not. -/
def authBackendReads (bi : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : GoFunc) (T : IProp GF) :
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
      {{ srvApi.csContractA P f Pre Q Post ∗ T ∗ authOwn M hs }}
        (App (Val #(methods bi.ty go!"GetAllRoles" bi.v)) (Val #()))
      {{ (s : GoSlice), RET #s; Post ∗ T ∗ authOwn M hs ∗
          ∃ sta : AuthState, ⌜histLast M hs sta⌝ ∗ rolesOut s sta }}))

instance authBackendReads_persistent (bi : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : GoFunc)
    (T : IProp GF) : Persistent (authBackendReads (GF := GF) bi M P f T) := by
  unfold authBackendReads; infer_instance

/-- **The auth backend's write side** `be` (an `AuthBackend`; a contract, as the lessor's
`leaseBackend`) with the hook `P f` and the write token `T` in the mode `M`: `BatchTx()` returns a
batch transaction (`authBatchTxOk`), `ForceCommit()` keeps the token (the real backend's commit
writes nothing back on its own: `NewAuthStore`'s axiom), and its reads (`authBackendReads`). -/
def authWBackendOk (be : GoInterface) (M : AuthMode) (P : IProp GF) (f : GoFunc) (T : IProp GF) :
    IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜be = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (tx : GoInterface), RET #tx; authBatchTxOk tx M P f T }}) ∗
    □ ({{ T }} (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #())) {{ RET #(); T }}) ∗
    authBackendReads bi M P f T)

instance authWBackendOk_persistent (be : GoInterface) (M : AuthMode) (P : IProp GF) (f : GoFunc)
    (T : IProp GF) : Persistent (authWBackendOk be M P f T) := by
  unfold authWBackendOk; infer_instance

/-- **The backend's batch transaction** `tx` as the backend states it (the auth plan's S4f): some
lock token of the backend's contract (`authBatchTxLkR`). -/
def authBatchTxOkR (tx : GoInterface) (M : AuthMode) (P : IProp GF) (f : GoFunc) (T : IProp GF) :
    IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗
    ∃ Lk : AuthState → IProp GF → IProp GF, authBatchTxLkR ti M P f T Lk)

instance authBatchTxOkR_persistent (tx : GoInterface) (M : AuthMode) (P : IProp GF) (f : GoFunc)
    (T : IProp GF) : Persistent (authBatchTxOkR tx M P f T) := by
  unfold authBatchTxOkR; infer_instance

/-- **The auth backend's write side as the backend states it** (the auth plan's S4f, 2026-10-25;
the provisional boundary D22 discharges, `notes/decisions.md`, "S4f of the auth plan"): as
`authWBackendOk`, with `BatchTx()` returning the backend's transaction (`authBatchTxOkR`, the
history's lock share under its lock); its reads (`authBackendReads`) as the store's view's. (Until
E2j this said `GetUser` was schema's batch transaction, `Lock()`, `UnsafeGetUser`, `Unlock()`; it
is the read transaction, `schema/auth_users.go`.) -/
def authWBackendOkR (be : GoInterface) (M : AuthMode) (P : IProp GF) (f : GoFunc) (T : IProp GF) :
    IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜be = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (tx : GoInterface), RET #tx; authBatchTxOkR tx M P f T }}) ∗
    □ ({{ T }} (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #())) {{ RET #(); T }}) ∗
    authBackendReads bi M P f T)

instance authWBackendOkR_persistent (be : GoInterface) (M : AuthMode) (P : IProp GF) (f : GoFunc)
    (T : IProp GF) : Persistent (authWBackendOkR be M P f T) := by
  unfold authWBackendOkR; infer_instance

/-- **The store's view of the backend's lock** (the auth plan's S4f): `Lock()` joins the lock's
share with the admin side's authority, `Unlock()` splits it off again. -/
theorem authBatchTxLk_of_R (ti : GoInterfaceOk) (M : AuthMode) (P : IProp GF) (f : GoFunc)
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

theorem authBatchTxOk_of_R (tx : GoInterface) (M : AuthMode) (P : IProp GF) (f : GoFunc)
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
theorem authWBackendOk_of_R (be : GoInterface) (M : AuthMode) (P : IProp GF) (f : GoFunc)
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
def authWR (st : Loc) (M : AuthMode) (P : IProp GF) (f : GoFunc) (T : IProp GF) : IProp GF :=
  iprop((∃ be : AuthBackend, aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗ authWBackendOk be M P f T) ∗
    T ∗ enabledHalf st M ∗ cacheHalf st M)

/-- A writer that did not write gives the caller's resources back. -/
theorem csContract_noWrite (P : IProp GF) (f : GoFunc) (Pre Q Post : IProp GF) :
    srvApi.csContractA P f Pre Q Post ⊢ Post ∨ Pre := by
  unfold srvApi.csContractA
  iintro ⟨HPre, -, -⟩
  iright; iexact HPre

end wdefs

section defs2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

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
    iintro ⟨Hh, ⟨%stl, %Hl, Hc1⟩⟩ ⟨%stc, Hc2, %Hr, Hq⟩
    ihave %Heq := authCurHalf_agree γa stl stc $$ Hc1 Hc2
    subst Heq
    isplitl [Hh Hc1]
    · iframe Hh; iexists stl; iframe Hc1; ipureintro; exact Hl
    isplitl [Hc2 Hq]
    · iexists stl; iframe Hc2 Hq; ipureintro; exact Hr
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
    iintro ⟨Hh, ⟨%stl, %Hl, Hc1⟩⟩ ⟨%stc, Hc2, %Hr, Hq⟩
    ihave %Heq := authCurHalf_agree γa stl stc $$ Hc1 Hc2
    subst Heq
    isplitl [Hh Hc1]
    · iframe Hh; iexists stl; iframe Hc1; ipureintro; exact Hl
    isplitl [Hc2 Hq]
    · iexists stl; iframe Hc2 Hq; ipureintro; exact Hr
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
    ⊢ authOwnF (GF := GF) M hs -∗ revCur M r -∗ capNext M hs st' -∗
      |==> (authOwnF M (hs ++ [st']) ∗ revCur M r' ∗ revisionVerdict M r') := by
  cases M with
  | on γa =>
    simp only [authOwnF, revCur, revisionVerdict, capNext]
    iintro ⟨Hh, ⟨%stl, %Hl, Hc1⟩⟩ ⟨%stc, Hc2, -, %hh, Hq, -⟩ #Hcap
    ihave %Hhh := authHist_rev_agree γa hs hh $$ Hh Hq
    subst Hhh
    imod (authCurHalf_update γa stl stc st') $$ Hc1 Hc2 with ⟨Hc1, Hc2⟩
    imod (authHist_append γa hs st' (hk rfl (by intro h; cases h))) $$ [Hh Hq] with ⟨Hh, Hq⟩
    · iframe Hh Hq
    imod (authHist_stateAt_keep γa (hs ++ [st']) hs.length st'
      (by simp)) $$ Hh with ⟨Hh, #Hst⟩
    imodintro
    iframe Hh
    isplitl [Hc1]
    · iexists st'; iframe Hc1; ipureintro; simp
    isplitl [Hc2 Hq]
    · iexists st'; iframe Hc2; isplitr
      · ipureintro; exact hr' rfl (by intro h; cases h)
      · iexists hs ++ [st']; iframe Hq Hcap
    · iexists hs.length, st'; iframe Hst; ipureintro; exact hr' rfl (by intro h; cases h)
  | off =>
    simp only [authOwnF, revCur, revisionVerdict]
    iintro %H - -
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
    iintro - - -
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
    iintro ⟨Hh, ⟨%stl', %Hl, Hc1⟩⟩ ⟨%stc, Hc2, -, Hq⟩
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
    isplitl [Hc2 Hq]
    · iexists stl; iframe Hc2 Hq; ipureintro; exact hr' rfl (by intro h; cases h)
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

/-- The admin side's half keeps a recorded state of it. -/
theorem authHistHalf_stateAt_keep (γa : AuthNames) (hs : List AuthState) (i : Nat) (st : AuthState)
    (h : hs[i]? = some st) :
    authHistHalf (GF := GF) γa hs ⊢ authHistHalf γa hs ∗ authStateAt γa i st := by
  unfold authHistHalf authStateAt
  iintro ⟨H, %Hk⟩
  ihave #Hlb := monoListLbOwn_get γa.hist _ hs $$ H
  iframe H
  isplitr
  · ipureintro; exact Hk
  isplitl []
  · iapply (monoListIdxOwn_get i st h) $$ Hlb
  · ipureintro; exact Hk st (List.mem_of_getElem? h)

/-- The admin side's half, kept, with a recorded state's index in it. -/
theorem authHistHalf_lookup_keep (γa : AuthNames) (hs : List AuthState) (i : Nat) (st : AuthState) :
    authHistHalf (GF := GF) γa hs ∗ authStateAt γa i st ⊢ authHistHalf γa hs ∗ ⌜hs[i]? = some st⌝ :=
  (and_intro (by iintro ⟨H, -⟩; iexact H) (authHistHalf_lookup γa hs i st)).trans
    persistent_and_sep_mp

/-- **The admin side's pending authority** (the auth-on snapshot plan's candidate (ii), the Freeze
of 2026-11-03): the history's half at `hs ++ N` (the caught-up states recorded), the latest state's
half still at `hs`'s last (the atomic not yet stored). `N = []`: `authOwn (.on γa) hs`. -/
def authOwnP (γa : AuthNames) (hs N : List AuthState) : IProp GF :=
  iprop(authHistHalf γa (hs ++ N) ∗ ∃ st : AuthState, ⌜hs.getLast? = some st⌝ ∗ authCurHalf γa st)

/-- **The pending authority in every mode** (`Recover` and `setRevision`'s one spec each): in
`on γa`, `authOwnP`; in the other modes, the authority at `hs ++ N` (no ghost variable to lag). -/
def authOwnPM (M : AuthMode) (hs N : List AuthState) : IProp GF :=
  match M with
  | .on γa => authOwnP γa hs N
  | _ => authOwn M (hs ++ N)

/-- Nothing pending: the authority. -/
theorem authOwnPM_nil (M : AuthMode) (hs : List AuthState) :
    authOwnPM (GF := GF) M hs [] ⊣⊢ authOwn M hs := by
  cases M <;> simp only [authOwnPM, authOwnP, authOwn, List.append_nil] <;>
    (constructor <;> iintro H <;> iexact H)

/-- **The atomic set to the caught-up history's last revision** (`Recover`'s `setRevision`):
the latest state's halves move to the last of `hs ++ N`, the authority is no longer pending, and
the new value's verdict. -/
theorem authOwnPM_revCur_set (M : AuthMode) (hs N : List AuthState) (stl : AuthState) (r r' : w64)
    (hl : histLast M (hs ++ N) stl) (hr' : M.isOn = true → M ≠ .any → uint.nat r' = stl.revision) :
    ⊢ authOwnPM (GF := GF) M hs N -∗ revCur M r -∗
      |==> (authOwn M (hs ++ N) ∗ revCur M r' ∗ revisionVerdict M r') := by
  cases M with
  | on γa =>
    simp only [authOwnPM, authOwnP, authOwn, revCur, revisionVerdict, histLast] at hl ⊢
    iintro ⟨Hh, ⟨%st0, %Hl0, Hc1⟩⟩ ⟨%stc, Hc2, -, Hq⟩
    imod (authCurHalf_update γa st0 stc stl) $$ Hc1 Hc2 with ⟨Hc1, Hc2⟩
    have hi : (hs ++ N)[(hs ++ N).length - 1]? = some stl := by
      rw [List.getLast?_eq_getElem?] at hl; exact hl
    ihave ⟨Hh, #Hst⟩ := authHistHalf_stateAt_keep γa (hs ++ N) _ stl hi $$ Hh
    imodintro
    iframe Hh
    isplitl [Hc1]
    · iexists stl; iframe Hc1; ipureintro; exact hl
    isplitl [Hc2 Hq]
    · iexists stl; iframe Hc2 Hq; ipureintro; exact hr' rfl (by intro h; cases h)
    · iexists (hs ++ N).length - 1, stl; iframe Hst; ipureintro; exact hr' rfl (by intro h; cases h)
  | off =>
    simp only [authOwnPM, authOwn, revCur, revisionVerdict]
    iintro %H -
    imodintro
    isplitr
    · ipureintro; exact H
    · isplitr <;> itrivial
  | any =>
    simp only [authOwnPM, authOwn, revCur, revisionVerdict]
    iintro - -
    imodintro
    isplitr; itrivial; isplitr; itrivial; itrivial

/-- `authOwnF_revFresh` from the admin side's authority alone. -/
theorem authOwn_revFresh (M : AuthMode) (hs : List AuthState) (s : AuthState) (r r' : w64)
    (hl : ∀ γa, M = .on γa → hs.getLast? = some s)
    (hr' : M.isOn = true → M ≠ .any → uint.nat r' = s.revision) :
    ⊢ authOwn (GF := GF) M hs -∗ revFresh M r -∗ |==> (authOwn M hs ∗ revFresh M r') := by
  cases M with
  | on γa =>
    have hl := hl γa rfl
    simp only [authOwn, revFresh]
    iintro ⟨Hh, Hc⟩ ⟨%p, Hp, ⟨%sp, #Hsp⟩, -, Hen, Hca⟩
    ihave ⟨Hh, %Hlk⟩ := authHistHalf_lookup_keep γa hs p sp $$ [Hh]
    · iframe Hh Hsp
    have hi : hs[hs.length - 1]? = some s := by
      rw [List.getLast?_eq_getElem?] at hl; exact hl
    obtain ⟨hp, -⟩ := List.getElem?_eq_some_iff.1 Hlk
    ihave ⟨Hh, #Hst⟩ := authHistHalf_stateAt_keep γa hs (hs.length - 1) s hi $$ Hh
    imodintro
    isplitl [Hh Hc]
    · iframe Hh Hc
    iexists p
    iframe Hp
    isplitl []
    · iexists sp; iexact Hsp
    iframe Hen Hca
    iexists hs.length - 1, s
    iframe Hst
    ipureintro
    exact ⟨by omega, hr' rfl (by intro h; cases h)⟩
  | off =>
    simp only [revFresh]
    iintro H -
    imodintro
    isplitl [H]
    · iexact H
    · itrivial
  | any =>
    simp only [revFresh]
    iintro H -
    imodintro
    isplitl [H]
    · iexact H
    · itrivial

/-- What `Recover` takes besides the store's resources: in `on γa`, the new backend's write token
and whole currency and the apply thread's share of the old backend's name `γc₀`. -/
def recoverIn (M : AuthMode) (γc₀ γc : AuthBkNames) : IProp GF :=
  match M with
  | .on γa => iprop(authWTok γc ∗ authCur γc 1 ∗ authBkCur γa (1 : Qp).half γc₀)
  | _ => iprop(True)

/-- What `Recover` gives back: in `on γa`, the new backend's write token, the share of its name, and
the old backend's whole currency (for its release). -/
def recoverOut (M : AuthMode) (γc₀ γc : AuthBkNames) : IProp GF :=
  match M with
  | .on γa => iprop(authWTok γc ∗ authBkCur γa (1 : Qp).half γc ∗ authCur γc₀ 1)
  | _ => iprop(True)

/-- The read state's facts: in `on γa`, it is the caught-up history's last, `stI`, and fits the
cache; in the other modes nothing is appended (`N = []`) and every state of the mode fits. -/
def recoverFit (M : AuthMode) (hs N : List AuthState) (stI : AuthState) : IProp GF :=
  match M with
  | .on _ => iprop(⌜(hs ++ N).getLast? = some stI ∧ permsFit stI⌝)
  | M => iprop(⌜N = []⌝ ∗ □ (∀ s : AuthState, authSnap M s -∗ ⌜permsFit s⌝))

/-- **`Recover`'s swap of the current backend's names**: with `beMu`'s share of the old backend's
names (at the write lock, all of `beP`'s), the new backend's names become current (`beP`'s share
and the currency's invariant at the new names, with their whole currency) and the old backend's
whole currency is handed back. (R-D2, 2026-11-04: through the currency's invariant, in which no
reader is in, as `beP`'s whole share is here, and which is not abandoned, as the apply thread's half
of the name is here; until then a ghost update of `beP`'s share, which held the currency.) -/
theorem recover_swap (M : AuthMode) (γc₀ γc γ1 : AuthBkNames) :
    ⊢ recoverIn (GF := GF) M γc₀ γc -∗ beCurM M 1 γ1 ={⊤}=∗ (beCurM M 1 γc ∗ recoverOut M γc₀ γc) := by
  cases M with
  | on γa =>
    simp only [recoverIn, recoverOut, beCurM]
    iintro ⟨HT, Hcu, Hb0⟩ ⟨Hb1, #Hci⟩
    ihave #Hci' := Hci
    iunfold authCurInv at Hci'
    iinv Hci' with >Hi Hclose
    iunfold curInv at Hi
    icases Hi with ⟨%K, %n, %γ', #Hauth, Htoks, Hdeps, Hq, Hrest⟩
    icombine Hb0 Hb1 gives %h1_
    obtain ⟨-, h1⟩ := h1_
    subst h1
    icombine Hb0 Hq gives %h2_
    obtain ⟨-, h2⟩ := h2_
    subst h2
    ihave Hb := (authBkCur_whole γa γc₀).1 $$ [Hb0 Hb1 Hq]
    · iframe Hb0 Hb1 Hq
    icases Hrest with (Hcu0 | ⟨Hh, -, -⟩)
    · cases n with
      | succ m =>
        -- a reader's deposit beside the whole name: too much
        simp only [List.replicate]
        icases BigSepL.bigSepL_cons.1 $$ Hdeps with ⟨Hd, -⟩
        iexfalso
        iapply authBkCur_excess γa _ γc₀ γc₀ $$ Hb Hd
      | zero =>
        rw [curFrac_0]
        imod (authBkCur_update γa γc₀ γc) $$ Hb with Hb
        icases (authBkCur_whole γa γc).2 $$ Hb with ⟨Hb0, Hb1, Hq⟩
        imod Hclose $$ [Htoks Hq Hcu] with -
        · inext
          iunfold curInv
          iexists K, 0, γc
          iframe Hauth Htoks Hq
          isplitr
          · simp only [List.replicate]; iapply BigSepL.bigSepL_nil.2; itrivial
          ileft; rw [curFrac_0]; iexact Hcu
        imodintro
        iframe HT Hb0 Hcu0 Hb1 Hci
    · -- abandoned: its half of the name beside the whole: too much
      iexfalso
      iapply authBkCur_excess γa _ γc₀ γc₀ $$ Hb Hh
  | off =>
    simp only [recoverIn, recoverOut, beCurM]
    iintro - -; imodintro; isplitl [] <;> itrivial
  | any =>
    simp only [recoverIn, recoverOut, beCurM]
    iintro - -; imodintro; isplitl [] <;> itrivial

/-- **The read contract for `Recover`** (any mode): with the pending authority at `hs ++ N` and,
in `on γa`, the new backend's write token (in `recoverOut`), the state read is the last of
`hs ++ N`. -/
theorem authReadTxOk_recover (tx : GoInterface) (R : IProp GF) (M : AuthMode) (γc : AuthBkNames) :
    authReadTxOk (GF := GF) tx R M γc ⊢ ∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗
      ∃ Hs : AuthState → IProp GF,
      □ (∀ (hs N : List AuthState) (γc₀ : AuthBkNames),
        {{ R ∗ authOwnPM M hs N ∗ recoverOut M γc₀ γc }}
          (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
        {{ RET #(); ∃ st : AuthState, Hs st ∗ authSnap M st ∗ authOwnPM M hs N ∗
            recoverOut M γc₀ γc ∗ ⌜histLast M (hs ++ N) st⌝ }}) ∗
      authTxReads ti R Hs := by
  cases M with
  | on γa =>
    simp only [authReadTxOk, authOwnPM, authOwnP, recoverOut, histLast]
    iintro ⟨%ti, %h, %Hs, -, -, #H3, #Hr⟩
    iexists ti
    isplitr
    · ipureintro; exact h
    iexists Hs
    isplitr
    · iintro !> %hs %N %γc₀ %Φ !> ⟨HR, ⟨Hhh, Hcur⟩, ⟨HT, Hb, Hcu⟩⟩ HΦ
      iapply H3 $$ %(hs ++ N) [HR HT Hhh]
      · iframe HR HT Hhh
      inext
      iintro ⟨%st, Hst, #Hsn, HT, Hhh, %Hl⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn Hhh Hcur HT Hb Hcu
      ipureintro; exact Hl
    iexact Hr
  | off =>
    simp only [authReadTxOk, authOwnPM, recoverOut]
    iintro ⟨%ti, %h, %Hs, -, #H2, -, #Hr⟩
    iexists ti
    isplitr
    · ipureintro; exact h
    iexists Hs
    isplitr
    · iintro !> %hs %N %γc₀ %Φ !> ⟨HR, Hown, Hout⟩ HΦ
      iapply H2 $$ %(hs ++ N) [HR Hown]
      · iframe HR Hown
      inext
      iintro ⟨%st, Hst, #Hsn, Hown, %Hl⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn Hown Hout
      ipureintro; exact Hl
    iexact Hr
  | any =>
    simp only [authReadTxOk, authOwnPM, recoverOut]
    iintro ⟨%ti, %h, %Hs, -, #H2, -, #Hr⟩
    iexists ti
    isplitr
    · ipureintro; exact h
    iexists Hs
    isplitr
    · iintro !> %hs %N %γc₀ %Φ !> ⟨HR, Hown, Hout⟩ HΦ
      iapply H2 $$ %(hs ++ N) [HR Hown]
      · iframe HR Hown
      inext
      iintro ⟨%st, Hst, #Hsn, Hown, %Hl⟩
      iapply HΦ
      iexists st
      iframe Hst Hsn Hown Hout
      ipureintro; exact Hl
    iexact Hr

/-- **The freshness at the latest state's revision** (the auth plan's E3h): with the whole
authority at `hs` whose latest state `s` has the revision `r'`, the published index (an index of
`hs`) is at most `s`'s, so the atomic at `r'` is fresh. -/
theorem authOwnF_revFresh (M : AuthMode) (hs : List AuthState) (s : AuthState) (r r' : w64)
    (hl : ∀ γa, M = .on γa → hs.getLast? = some s)
    (hr' : M.isOn = true → M ≠ .any → uint.nat r' = s.revision) :
    ⊢ authOwnF (GF := GF) M hs -∗ revFresh M r -∗ |==> (authOwnF M hs ∗ revFresh M r') := by
  cases M with
  | on γa =>
    have hl := hl γa rfl
    simp only [authOwnF, revFresh]
    iintro ⟨Hh, Hc⟩ ⟨%p, Hp, ⟨%sp, #Hsp⟩, -, Hen, Hca⟩
    ihave ⟨Hh, %Hlk⟩ := authHist_lookup_keep γa hs p sp $$ [Hh]
    · iframe Hh Hsp
    have hi : hs[hs.length - 1]? = some s := by
      cases hs with
      | nil => cases hl
      | cons x xs => rw [List.getLast?_eq_getElem?] at hl; exact hl
    obtain ⟨hp, -⟩ := List.getElem?_eq_some_iff.1 Hlk
    imod (authHist_stateAt_keep γa hs (hs.length - 1) s hi) $$ Hh with ⟨Hh, #Hst⟩
    imodintro
    isplitl [Hh Hc]
    · iframe Hh Hc
    iexists p
    iframe Hp
    isplitl []
    · iexists sp; iexact Hsp
    iframe Hen Hca
    iexists hs.length - 1, s
    iframe Hst
    ipureintro
    exact ⟨by omega, hr' rfl (by intro h; cases h)⟩
  | off =>
    simp only [revFresh]
    iintro H -
    imodintro
    isplitl [H]
    · iexact H
    · itrivial
  | any =>
    simp only [revFresh]
    iintro H -
    imodintro
    isplitl [H]
    · iexact H
    · itrivial

/-- A share of a monotone list's authority keeps its lower bound (`auth_lb_op`). -/
theorem histAuth_keep_lb (γ : GName) (q : Qp) (l : List AuthState) :
    monoListAuthOwn (GF := GF) γ q l ⊢ monoListAuthOwn γ q l ∗ monoListLbOwn γ l := by
  unfold monoListAuthOwn monoListLbOwn
  have h := Iris.MonoList.auth_lb_op (DFrac.own q) (l.map encodeO)
  refine Iris.BI.BIBase.Entails.trans ?_ (own_op γ _ _).1
  rw [← h]

/-- **The admin side's latest state, recorded at the last index, and the published index below
it** (the auth plan's E3h): with the admin side's authority at `hs` and a recorded state at `p`,
the latest state is recorded at `hs.length - 1 ≥ p`. -/
theorem authOwn_lastAt (γa : AuthNames) (hs : List AuthState) (p : Nat) (sp : AuthState) :
    authOwn (GF := GF) (.on γa) hs ∗ authStateAt γa p sp ⊢
      authOwn (.on γa) hs ∗ ∃ stl : AuthState, ⌜hs.getLast? = some stl ∧ p ≤ hs.length - 1⌝ ∗
        authStateAt γa (hs.length - 1) stl := by
  simp only [authOwn]
  have key : authHistHalf (GF := GF) γa hs ∗ authStateAt γa p sp ⊢
      authHistHalf γa hs ∗ ⌜hs[p]? = some sp⌝ :=
    (and_intro (by iintro ⟨H, -⟩; iexact H) (authHistHalf_lookup γa hs p sp)).trans
      persistent_and_sep_mp
  iintro ⟨⟨Hh, ⟨%stl, %Hl, Hc⟩⟩, #Hsp⟩
  ihave ⟨Hh, %Hlk⟩ := key $$ [Hh]
  · iframe Hh Hsp
  iunfold authHistHalf at Hh
  icases Hh with ⟨Hh, %Hk⟩
  ihave ⟨Hh, #Hlb⟩ := histAuth_keep_lb γa.hist _ hs $$ Hh
  have hi : hs[hs.length - 1]? = some stl := by
    cases hs with
    | nil => cases Hl
    | cons x xs => rw [List.getLast?_eq_getElem?] at Hl; exact Hl
  obtain ⟨hp, -⟩ := List.getElem?_eq_some_iff.1 Hlk
  isplitl [Hh Hc]
  · iunfold authHistHalf; iframe Hh; isplitr
    · ipureintro; exact Hk
    · iexists stl; iframe Hc; ipureintro; exact Hl
  iexists stl
  isplitr
  · ipureintro; exact ⟨Hl, by omega⟩
  unfold authStateAt
  isplitl
  · iapply (monoListIdxOwn_get (hs.length - 1) stl hi) $$ Hlb
  · ipureintro; exact Hk stl (List.mem_of_getElem? hi)

/-- **The field `enabled`'s ghost variable set to the latest state's flag** (the auth plan's E3h):
the writer holding `enabledMu` (the guard's half) and the admin side's quarter, with the admin side's
authority at `hs` whose latest state has the flag `b'`, sets the ghost variable to `b'` (the store's
freshness's quarter too: the latest state is recorded at an index no below the published one). -/
theorem enG_update (st : Loc) (R : IProp GF) (M : AuthMode) (hs : List AuthState) (b b' : Bool)
    (hb : ∀ γa stl, M = .on γa → hs.getLast? = some stl → b' = stl.enabled) :
    authInv (GF := GF) st R M ⊢ authOwn M hs -∗ enG M (1 : Qp).half b -∗
      enG M (1 : Qp).half.half b ={⊤}=∗
      authOwn M hs ∗ enG M (1 : Qp).half b' ∗ enG M (1 : Qp).half.half b' := by
  cases M with
  | on γa =>
    iintro #Hinv Hown Hg Hq
    iunfold authInv at Hinv
    icases Hinv with ⟨-, #Hrev, -⟩
    iinv Hrev with Hi Hclose
    iunfold revInv at Hi
    icases Hi with ⟨%r, Hr, Hv, Hc, >Hf⟩
    iunfold revFresh at Hf
    icases Hf with ⟨%p, Hp, #Hsp, Hrv, ⟨%b0, Hq0, Hj⟩, Hcf⟩
    iunfold enG at Hg
    iunfold enG at Hq
    iunfold enG
    icombine Hg Hq0 gives %Hb0
    obtain ⟨-, Hb0⟩ := Hb0
    subst Hb0
    icases Hsp with ⟨%sp, #Hsp⟩
    ihave ⟨Hown, %stl, %Hl, #Hst⟩ := authOwn_lastAt γa hs p sp $$ [Hown]
    · iframe Hown Hsp
    have hq : (1 : Qp).half + ((1 : Qp).half.half + (1 : Qp).half.half) = 1 := by
      rw [Qp.half_add_half, Qp.half_add_half]
    ihave Hq2 := ((ghostVar_fractional γa.fen b).fractional (1 : Qp).half.half
      (1 : Qp).half.half).2 $$ [Hq Hq0]
    · iframe Hq Hq0
    imod (ghostVar_update_2 b' γa.fen b _ b _ hq) $$ Hg Hq2 with ⟨Hg, Hq2⟩
    icases ((ghostVar_fractional γa.fen b').fractional (1 : Qp).half.half
      (1 : Qp).half.half).1 $$ Hq2 with ⟨Hq, Hq0⟩
    imod Hclose $$ [Hr Hv Hc Hp Hrv Hq0 Hcf] with -
    · inext
      iunfold revInv
      iexists r
      iframe Hr Hv Hc
      iunfold revFresh
      iexists p
      iframe Hp Hrv Hcf
      isplitl []
      · iexists sp; iexact Hsp
      iexists b'
      iframe Hq0
      iexists hs.length - 1, stl
      iframe Hst
      ipureintro
      exact ⟨Hl.2, hb γa stl rfl Hl.1⟩
    imodintro
    iframe Hown Hg Hq
  | off =>
    simp only [enG]
    iintro - Hown - -
    imodintro
    iframe Hown
    isplitl []; itrivial; itrivial
  | any =>
    simp only [enG]
    iintro - Hown - -
    imodintro
    iframe Hown
    isplitl []; itrivial; itrivial

/-- **The cache's ghost variable set to a new map of the latest state** (the auth plan's E3h): the
writer holding `rangePermCacheMu` (the guard's half, at the old map) and the admin side's quarter,
with the whole authority at `hs` whose latest state is `sta`, sets the ghost variable to the new map
`mp'` of `sta` at its index (the store's freshness's quarter too). -/
theorem caG_update (st : Loc) (R : IProp GF) (M : AuthMode) (hs : List AuthState)
    (mp mp' : GoMap) (Mp Mp' : GMap GoString Loc) (sc sta : AuthState)
    (hl : ∀ γa, M = .on γa → hs.getLast? = some sta) :
    authInv (GF := GF) st R M ⊢ authOwn M hs -∗ caGM M (1 : Qp).half mp Mp -∗ caA M mp sc -∗
      cacheOf sta Mp' ={⊤}=∗
      authOwn M hs ∗ caGM M (1 : Qp).half mp' Mp' ∗ caA M mp' sta := by
  cases M with
  | on γa =>
    have hl := hl γa rfl
    iintro #Hinv Hown Hg Hq #Hof
    iunfold authInv at Hinv
    icases Hinv with ⟨-, #Hrev, -⟩
    iinv Hrev with Hi Hclose
    iunfold revInv at Hi
    icases Hi with ⟨%r, Hr, Hv, Hc, >Hf⟩
    iunfold revFresh at Hf
    icases Hf with ⟨%p, Hp, #Hsp, Hrv, Hen, %v0, Hq0, Hj⟩
    iunfold caGM at Hg
    icases Hg with ⟨%j1, %s1, Hg, -, -⟩
    iunfold caA at Hq
    icases Hq with ⟨%j2, %s2, Hq, -, -⟩
    icombine Hg Hq0 gives %H1
    obtain ⟨-, H1⟩ := H1
    subst H1
    icombine Hq Hq0 gives %H2
    obtain ⟨-, H2⟩ := H2
    cases H2
    icases Hsp with ⟨%sp, #Hsp⟩
    ihave ⟨Hown, %stl, %Hl, #Hst⟩ := authOwn_lastAt γa hs p sp $$ [Hown]
    · iframe Hown Hsp
    have hstl : stl = sta := by rw [hl] at Hl; exact (Option.some.inj Hl.1).symm
    subst hstl
    have hq : (1 : Qp).half + ((1 : Qp).half.half + (1 : Qp).half.half) = 1 := by
      rw [Qp.half_add_half, Qp.half_add_half]
    ihave Hq2 := ((ghostVar_fractional γa.fca (mp, j1)).fractional (1 : Qp).half.half
      (1 : Qp).half.half).2 $$ [Hq Hq0]
    · iframe Hq Hq0
    imod (ghostVar_update_2 (mp', hs.length - 1) γa.fca (mp, j1) _ (mp, j1) _ hq) $$ Hg Hq2
      with ⟨Hg, Hq2⟩
    icases ((ghostVar_fractional γa.fca (mp', hs.length - 1)).fractional (1 : Qp).half.half
      (1 : Qp).half.half).1 $$ Hq2 with ⟨Hq, Hq0⟩
    imod Hclose $$ [Hr Hv Hc Hp Hrv Hen Hq0] with -
    · inext
      iunfold revInv
      iexists r
      iframe Hr Hv Hc
      iunfold revFresh
      iexists p
      iframe Hp Hrv Hen
      isplitl []
      · iexists sp; iexact Hsp
      iexists (mp', hs.length - 1)
      iframe Hq0
      iexists stl, hs.length - 1, stl
      iframe Hst
      ipureintro
      exact ⟨Hl.2, rfl⟩
    imodintro
    iframe Hown
    isplitl [Hg]
    · iunfold caGM; iexists hs.length - 1, stl; iframe Hg Hst Hof
    · iunfold caA; iexists hs.length - 1, stl; iframe Hq Hst; ipureintro; rfl
  | off =>
    simp only [caGM, caA]
    iintro - Hown - - -
    imodintro
    iframe Hown
    isplitl []; itrivial; itrivial
  | any =>
    simp only [caGM, caA]
    iintro - Hown - - -
    imodintro
    iframe Hown
    isplitl []; itrivial; itrivial

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
      ⌜st.roles !! name = some ps ∧ rr.name = name ∧ rr.toRole.Perm ps⌝ ∗ ownRole r rr := by
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
    authInv (GF := GF) st R M ⊢ authOwnF M hs -∗ capNext M hs x ={⊤}=∗ authOwnF M (hs ++ [x]) := by
  iintro #Hinv Hown #Hcap
  iunfold authInv at Hinv
  icases Hinv with ⟨-, #Hrev, -⟩
  iinv Hrev with Hi Hclose
  iunfold revInv at Hi
  icases Hi with ⟨%r, >Hr, -, >Hc, >Hf⟩
  ihave H := revCur_agree M hs r $$ Hown Hc
  icases H with ⟨Hown, Hc, %Hag⟩
  imod (authOwnF_revCur_append M hs x r r hk hoff (fun h1 h2 => by
    rw [hrev]; exact Hag st0 hl h1 h2)) $$ Hown Hc Hcap with ⟨Hown, Hc, #Hv⟩
  imod Hclose $$ [Hr Hc Hf] with -
  · inext; iunfold revInv; iexists r; iframe Hr Hc Hf; iexact Hv
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

/-- **A reader's ticket for the store's currency, in the mode `M`** (R-D2, 2026-11-04): in `on γa`
two of the tickets' tokens (`γa.rdt`): one deposited in the currency's invariant while the reader is
in `lockedReadTx`'s section, one kept, so that the reader finds the invariant live when it comes
back (`beCurM_lend`); nothing in the other modes. -/
def rdTicketM (M : AuthMode) : IProp GF :=
  match M with
  | .on γa => ownToks γa.rdt 2
  | _ => iprop(True)

/-- A reader slot of `beMu` (`lockedReadTx`), with (R-D2, 2026-11-04) the reader's ticket for the
store's currency (`rdTicketM`). -/
def beRd (st : Loc) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(sync.ownRWMutex (aF go!"beMu" st) (beP st R M) ∗ rdTicketM M)

/-- **A permission check's reader resource**: a slot of each lock and the backend's `R`. -/
def authRd (st : Loc) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(enabledRd st M ∗ cacheRd st M ∗ beRd st R M ∗ R)

/-- **The tickets out of the store's construction** (persistent; R-D2, 2026-11-04): `N` readers'
tickets of two tokens each, all there is (the authority discarded at `2 * N`), and the currency's
invariant. -/
def authRdTotal (γa : AuthNames) (N : Nat) : IProp GF :=
  iprop(ownTokAuthDfrac γa.rdt DFrac.discard (2 * N) ∗ authCurInv γa)

instance authRdTotal_persistent (γa : AuthNames) (N : Nat) :
    Persistent (authRdTotal (GF := GF) γa N) := by
  unfold authRdTotal; infer_instance

/-- **A reader lends the currency to the read transaction** (R-D2, 2026-11-04): with `beP`'s share at
the read lock (`sync.rfrac`) and its ticket, a part of the current backend's currency
(`authCurM`), which given back returns both. In `on γa` through the currency's invariant: the reader
deposits a token and half of its piece of the name (its ticket bounds the readers in, so the part is
positive); it finds the invariant live then and on its return (the abandoned invariant holds every
token, and the reader keeps one), and on its return its deposit there (the currency is not whole). -/
theorem beCurM_lend (M : AuthMode) (γc : AuthBkNames) :
    ⊢ beCurM (GF := GF) M sync.rfrac γc -∗ rdTicketM M ={⊤}=∗ ∃ q : Qp, authCurM M q γc ∗
      (authCurM M q γc ={⊤}=∗ beCurM M sync.rfrac γc ∗ rdTicketM M) := by
  cases M with
  | on γa =>
    simp only [beCurM, rdTicketM, authCurM]
    iintro ⟨Hb, #Hci⟩ Ht
    ihave #Hci' := Hci
    iunfold authCurInv at Hci'
    iinv Hci' with >Hi Hclose
    iunfold curInv at Hi
    icases Hi with ⟨%K, %n, %γ', #Hauth, Htoks, Hdeps, Hq, Hrest⟩
    icases toks_bound γa.rdt K 2 n $$ Hauth Ht Htoks with ⟨%hle, Ht, Htoks⟩
    icases Hrest with (Hcu | ⟨-, Hab, -⟩)
    · icombine Hb Hq gives %hγ_
      obtain ⟨-, hγ⟩ := hγ_
      subst hγ
      -- the reader's part, `curEps K`, out; a token and half the name's piece in
      ihave Hcu : authCur γc (curEps K + curFrac K (n + 1)) $$ [Hcu]
      · rw [← curFrac_S K n (by omega)]; iexact Hcu
      unfold authCur
      icases (ghostVar_split γc.2.1 () (curEps K) (curFrac K (n + 1))) $$ Hcu with ⟨He, Hcu⟩
      ihave Ht : ownToks γa.rdt (1 + 1) $$ [Ht]
      · iexact Ht
      icases (ownToks_add_1 1 1 γa.rdt) $$ Ht with ⟨Ht1, Ht2⟩
      icases (authBkCur_split_half γa sync.rfrac.half.half γc).1 $$ Hb with ⟨Hbd, Hbk⟩
      ihave Htoks := ownToks_add_2 1 n γa.rdt $$ [Htoks Ht1]
      · iframe Htoks Ht1
      imod Hclose $$ [Htoks Hdeps Hbd Hq Hcu] with -
      · inext
        iunfold curInv
        iexists K, n + 1, γc
        iframe Hauth Htoks Hq
        isplitl [Hbd Hdeps]
        · simp only [List.replicate]
          iapply BigSepL.bigSepL_cons.2
          iframe Hbd Hdeps
        ileft; unfold authCur; iexact Hcu
      imodintro
      iexists (curEps K)
      iframe He
      -- the return
      iintro He
      iinv Hci' with >Hi Hclose
      all_goals try exact fun _ _ => CoPset.mem_full
      iunfold curInv at Hi
      icases Hi with ⟨%K', %n', %γ'', #Hauth', Htoks, Hdeps, Hq, Hrest⟩
      unfold authCur
      icombine Hauth Hauth' gives %hK_
      obtain ⟨-, hK⟩ := hK_
      subst hK
      icases toks_bound γa.rdt K 1 n' $$ Hauth Ht2 Htoks with ⟨%hle', Ht2, Htoks⟩
      icombine Hbk Hq gives %hγ_
      obtain ⟨-, hγ⟩ := hγ_
      subst hγ
      icases Hrest with (Hcu | ⟨-, Hab, -⟩)
      · cases n' with
        | zero =>
          -- no deposit: the whole currency there, beside the reader's part
          ihave %hv := ghostVar_valid_2 γc.2.1 () (curEps K) () (curFrac K 0) $$ He Hcu
          exfalso
          have h1 := hv.1
          rw [curFrac_0] at h1
          have h2 := (curEps K).2
          simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at h1
          grind
        | succ m =>
          simp only [List.replicate]
          icases BigSepL.bigSepL_cons.1 $$ Hdeps with ⟨Hbd, Hdeps⟩
          icases (ownToks_add_1 1 m γa.rdt) $$ Htoks with ⟨Htoks, Ht1⟩
          ihave Hcu : ghostVar γc.2.1 (curFrac K m) () $$ [He Hcu]
          · rw [curFrac_S K m (by omega)]
            iapply ((ghostVar_fractional γc.2.1 ()).fractional (curEps K) (curFrac K (m + 1))).2
            iframe He Hcu
          imod Hclose $$ [Htoks Hdeps Hq Hcu] with -
          · inext
            iunfold curInv
            iexists K, m, γc
            iframe Hauth Htoks Hdeps Hq
            ileft; unfold authCur; iexact Hcu
          imodintro
          iframe Hci
          isplitl [Hbd Hbk]
          · iapply (authBkCur_split_half γa sync.rfrac.half.half γc).2 $$ [Hbd Hbk]
            iframe Hbd Hbk
          iapply (ownToks_add_2 1 1 γa.rdt) $$ [Ht1 Ht2]
          iframe Ht1 Ht2
      · icases toks_bound γa.rdt K 1 K $$ Hauth Ht2 Hab with ⟨%hbad, -, -⟩
        exfalso; omega
    · icases toks_bound γa.rdt K 2 K $$ Hauth Ht Hab with ⟨%hbad, -, -⟩
      exfalso; omega
  | off =>
    simp only [beCurM, rdTicketM, authCurM]
    iintro - -
    imodintro
    iexists 1
    isplitr
    · itrivial
    iintro -
    imodintro
    isplitl [] <;> itrivial
  | any =>
    simp only [beCurM, rdTicketM, authCurM]
    iintro - -
    imodintro
    iexists 1
    isplitr
    · itrivial
    iintro -
    imodintro
    isplitl [] <;> itrivial

/-- **Every reader's ticket** (R-D2): `N` readers' resources hold `2 * N` tokens. -/
theorem authRds_toks (stp : Loc) (R : IProp GF) (γa : AuthNames) (N : Nat) :
    ([∗list] _x ∈ List.replicate N (), authRd (GF := GF) stp R (.on γa)) ⊢
      |==> ownToks γa.rdt (2 * N) := by
  induction N with
  | zero =>
    iintro -
    iapply ownToks_0
  | succ N ih =>
    simp only [List.replicate]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hr, H⟩
    iunfold authRd at Hr
    icases Hr with ⟨-, -, Hb, -⟩
    iunfold beRd at Hb
    icases Hb with ⟨-, Ht⟩
    simp only [rdTicketM]
    imod ih $$ H with H
    imodintro
    ihave H := ownToks_add_2 2 (2 * N) γa.rdt $$ [H Ht]
    · iframe H Ht
    rw [show 2 * (N + 1) = 2 * N + 2 by omega]
    iexact H

/-- **The store abandoned** (mode `on γa`; R-D2, 2026-11-04; `notes/decisions.md`, "R-D2: the auth
store's currency in an invariant"): with every reader's resource (all `N` tickets, so no reader is in
`lockedReadTx`'s section) and the apply thread's write side on the backend `T` (`authWHeld`, its
publication quarter), the backend's lifecycle gives the realization's share `K` back: the
currency's invariant gives the whole currency and is left abandoned (no reader enters it again, and
the store's `Recover` is impossible, the apply thread's half of the name kept there); `T` is
retired and released. -/
theorem authRd_abandon (stp : Loc) (R : IProp GF) (γa : AuthNames) (N : Nat) (T : AuthBkNames)
    (K : IProp GF) :
    ⊢ authRdTotal γa N -∗ ([∗list] _x ∈ List.replicate N (), authRd (GF := GF) stp R (.on γa)) -∗
      authWHeld γa T -∗ authPubTok γa -∗ authBkLife γa T K ={⊤}=∗ K := by
  iintro #Htot Hrds HW Hpt #Hlife
  imod (authRds_toks stp R γa N) $$ Hrds with Ht
  iunfold authRdTotal at Htot
  icases Htot with ⟨#Hauth0, #Hci⟩
  iunfold authWHeld at HW
  icases HW with ⟨HT, Hb⟩
  iunfold authCurInv at Hci
  iinv Hci with >Hi Hclose
  iunfold curInv at Hi
  icases Hi with ⟨%K', %n, %γ', #Hauth, Htoks, Hdeps, Hq, Hrest⟩
  icombine Hauth0 Hauth gives %hK_
  obtain ⟨-, hK⟩ := hK_
  subst hK
  icases toks_bound γa.rdt (2 * N) (2 * N) n $$ Hauth0 Ht Htoks with ⟨%hle, Ht, Htoks⟩
  have hn : n = 0 := by omega
  subst hn
  icombine Hb Hq gives %hγ_
  obtain ⟨-, hγ⟩ := hγ_
  subst hγ
  icases Hrest with (Hcu | ⟨Hh, -, -⟩)
  · rw [curFrac_0]
    imod Hclose $$ [Htoks Hdeps Hq Hb Ht] with -
    · inext
      iunfold curInv
      iexists (2 * N), 0, T
      iframe Hauth0 Htoks Hdeps Hq
      iright
      iframe Hb Ht
      ipureintro; rfl
    iunfold authBkLife at Hlife
    icases Hlife with ⟨#Hret, #Hrel, -⟩
    imod Hret $$ [HT Hpt] with ⟨-, Hretd, -⟩
    · iframe HT Hpt
    imod Hrel $$ [Hretd Hcu] with ⟨HK, -⟩
    · iframe Hretd Hcu
    imodintro
    iexact HK
  · -- abandoned already: the apply thread's half and the invariant's make the whole, beside its quarter
    iexfalso
    ihave Hw : authBkCur γa 1 T $$ [Hb Hh]
    · unfold authBkCur
      iapply (ghostVar_split_half γa.bk 1 T).2
      iframe Hb Hh
    iapply authBkCur_excess γa _ T T $$ Hw Hq

/-- **What `Authenticate` returns** for `username` with the admin side's authority `hs`, in the
mode `M` (the auth plan's S5): an error and no response; or no error and a response holding a token
issued to `username` (`tokOk`), auth enabled at some recorded state, and the user present in the
latest state (`histLast`). (`Authenticate` does not check the password: the server's API layer
did, `CheckPassword`, before proposing the request.) -/
def authenticated (M : AuthMode) (hs : List AuthState) (username : GoString) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ (tok : GoString) (v : go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse),
      resp ↦ v ∗ ⌜v.Token' = tok ∧ v.unknownFields' = slice.nil⌝ ∗ tokOk M tok username ∗ enabledVerdict M true ∗
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

end defs2

end auth
end EtcdGrove
end Perennial
