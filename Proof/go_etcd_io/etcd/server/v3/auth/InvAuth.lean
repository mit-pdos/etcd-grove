/-
The auth store's request side (`server/auth/store.go`, `range_perm_cache.go`; 2026-10-14, unit
P2): its locks, what they hold, and the contracts of the objects it calls through interfaces.
Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The auth store's request side (unit
P2)".

**The store** `as` (`authInv as R`, persistent):
- `revision`, an atomic (`Revision()` loads it; `commitRevision`/`setRevision`, the admin side,
  add to or store it): its points-to in an invariant of its own;
- `lg`, `tokenProvider`: read-only (written by `NewAuthStore`);
- `beMu` (an `RWMutex`, since the fork's d52eec43e, D22k (A)) guards the backend `be` with its
  contract (`beP`): `Recover` (names-only) writes it under the write lock, the permission checks
  read it under a read lock (`lockedReadTx`), so a check's read transaction is of the backend
  current when it was locked (the server closes a replaced backend only after `Recover`);
- `enabledMu` (an `RWMutex`) guards `enabled` (`enabledP`);
- `rangePermCacheMu` (an `RWMutex`) guards the permission cache `rangePermCache` (`cacheP`): a
  map from user name to a `*unifiedRangePermissions` whose two interval trees (`readPerms`,
  `writePerms`) are read-only once built (`refreshRangePermCache` replaces the map whole with
  freshly built trees).

**Contracts** (the store calls them through interfaces; not yet proved of the real objects):
- the backend `be` (`authBackendOk be R M`: schema's `authBackend` in the server): `ReadTx()`
  returns a transaction whose `RLock()` turns the caller's read resource `R` into the held token
  of a state `st` of the mode `M` (`authSnap`, `Buckets.lean`; the auth plan's S1, 2026-10-23:
  until then the token held no state), under which `UnsafeGetUser(name)`/`UnsafeGetRole(name)`
  return the state's user/role (`userOut`/`roleOut`), `UnsafeReadAuthEnabled()`/
  `UnsafeReadAuthRevision()` its flag and revision, and which `RUnlock()` turns back into `R` (the
  backend's own read transaction needs a reader slot, `backend.rdTok`, hence `R`); schema's
  `authReadTx` meets it over the buckets (`etcdserver/InvAuthBackend.lean`, `authBucketsAre`);
- the token provider (`tokenProviderOk`): `info(ctx, token, rev)` returns an auth info (nil, or
  one with read-only fields) and a boolean;
- each cached tree (`ivtQuery`): `Intersects` and `Contains` of a bytes-affine interval return,
  keeping the interval's slices (the tree's proof, `adt.ownIvt`, covers string-affine intervals
  only).

**The mode** `M` (`AuthMode`, `Model.lean`) of the store's contract: what the backend's states are
(`authSnap`); the request side's specs are proved for every mode (their verdicts are track S's).

**The readers** (`authRd as R M`): `IsAuthEnabled` read-locks `enabledMu` and the permission checks
also `rangePermCacheMu` and `beMu`, each needing a reader slot (`sync.ownRWMutex`: Perennial bounds
an `RWMutex`'s readers), and the backend's read transaction needs `R`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Proof.go_etcd_io.etcd.server.v3.auth.Buckets
public import Proof.go_etcd_io.etcd.pkg.v3.adt.BytesIvl

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

/-- An auth info `a`: `nil`, or one whose `Username` and `Revision` are read-only. -/
def authInfoRO (a : Loc) : IProp GF :=
  iprop(⌜a = null⌝ ∨ ∃ (user : GoString) (rev : w64), ⌜a ≠ null⌝ ∗
    aiF go!"Username" a ↦□ user ∗ aiF go!"Revision" a ↦□ rev)

instance authInfoRO_persistent (a : Loc) : Persistent (authInfoRO (GF := GF) a) := by
  unfold authInfoRO; infer_instance

/-- **A cached interval tree** `t` (an `adt.IntervalTree`, not nil; a contract): `Intersects` and
`Contains` of a bytes-affine interval return a boolean, keeping the interval's slices. -/
def ivtQuery (t : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜t = GoInterface.ok ti⌝ ∗
    □ (∀ (b e : GoSlice) (bs es : List w8) (db de : DFrac),
      {{ b ↦*{db} bs ∗ e ↦*{de} es }}
        (App (Val #(methods ti.ty go!"Intersects" ti.v)) (Val #(adt.bytesIvl b e)))
      {{ (r : Bool), RET #r; b ↦*{db} bs ∗ e ↦*{de} es }}) ∗
    □ (∀ (b e : GoSlice) (bs es : List w8) (db de : DFrac),
      {{ b ↦*{db} bs ∗ e ↦*{de} es }}
        (App (Val #(methods ti.ty go!"Contains" ti.v)) (Val #(adt.bytesIvl b e)))
      {{ (r : Bool), RET #r; b ↦*{db} bs ∗ e ↦*{de} es }}))

instance ivtQuery_persistent (t : GoInterface) : Persistent (ivtQuery (GF := GF) t) := by
  unfold ivtQuery; infer_instance

/-- **A cache entry** `p` (a `*unifiedRangePermissions`, not nil): its two trees, read-only. -/
def permsOk (p : Loc) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ ∃ r w : go_etcd_io.etcd.pkg.v3.adt.IntervalTree,
    upF go!"readPerms" p ↦□ r ∗ upF go!"writePerms" p ↦□ w ∗ ivtQuery r ∗ ivtQuery w)

instance permsOk_persistent (p : Loc) : Persistent (permsOk (GF := GF) p) := by
  unfold permsOk; infer_instance

/-- What `enabledMu` guards at `q`: `enabled`. -/
def enabledP (st : Loc) (q : Qp) : IProp GF :=
  iprop(∃ b : Bool, aF go!"enabled" st ↦{DFrac.own q} b)

/-- What `rangePermCacheMu` guards at `q`: the cache's map, every entry `permsOk`. -/
def cacheP (st : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (mp : GoMap) (M : GMap GoString Loc), aF go!"rangePermCache" st ↦{DFrac.own q} mp ∗
    mp ↦${DFrac.own q} M ∗ [∗map] _u ↦ p ∈ M, permsOk p)

/-- **The transaction's reads under the held token** `Hs st` of the state `st` (the shared part of
`authReadTxOk` and `authReadTxLocked`): `UnsafeGetUser(name)` and `UnsafeGetRole(name)` return
the state's user and role (`userOut`, `roleOut`: nil if none, else the message, owned),
`UnsafeReadAuthEnabled()` its flag, `UnsafeReadAuthRevision()` its revision, each keeping the
token, and `RUnlock()` turns the token back into `R`. -/
def authTxReads (ti : GoInterfaceOk) (R : IProp GF) (Hs : AuthState → IProp GF) : IProp GF :=
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

/-- The invariant of `revision` (an atomic). -/
def revInv (st : Loc) : IProp GF :=
  iprop(∃ r : w64, aF go!"revision" st ↦ r)

/-- **The auth store** at `as` (persistent), its backend's read resource `R`, its mode `M`: the
atomic `revision`'s invariant, the read-only `lg` (not nil) and `tokenProvider` with its contract,
and the guards of its three locks (`beMu`'s holds `be` with its contract in the mode). -/
def authInv (st : Loc) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(⌜st ≠ null⌝ ∗ inv (nroot.@"authRev") (revInv st) ∗
    (∃ lg : Loc, aF go!"lg" st ↦□ lg ∗ ⌜lg ≠ null⌝) ∗
    sync.isRWMutexGuard (aF go!"beMu" st) (beP st R M) ∗
    (∃ tp : TokenProvider, aF go!"tokenProvider" st ↦□ tp ∗ tokenProviderOk tp) ∗
    sync.isRWMutexGuard (aF go!"enabledMu" st) (enabledP st) ∗
    sync.isRWMutexGuard (aF go!"rangePermCacheMu" st) (cacheP st))

instance authInv_persistent (st : Loc) (R : IProp GF) (M : AuthMode) :
    Persistent (authInv (GF := GF) st R M) := by
  unfold authInv; infer_instance

/-- A reader slot of `enabledMu` (`IsAuthEnabled`). -/
def enabledRd (st : Loc) : IProp GF :=
  sync.ownRWMutex (aF go!"enabledMu" st) (enabledP st)

/-- A reader slot of `rangePermCacheMu` (`isRangeOpPermitted`). -/
def cacheRd (st : Loc) : IProp GF :=
  sync.ownRWMutex (aF go!"rangePermCacheMu" st) (cacheP st)

/-- A reader slot of `beMu` (`lockedReadTx`). -/
def beRd (st : Loc) (R : IProp GF) (M : AuthMode) : IProp GF :=
  sync.ownRWMutex (aF go!"beMu" st) (beP st R M)

/-- **A permission check's reader resource**: a slot of each lock and the backend's `R`. -/
def authRd (st : Loc) (R : IProp GF) (M : AuthMode) : IProp GF :=
  iprop(enabledRd st ∗ cacheRd st ∗ beRd st R M ∗ R)

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
