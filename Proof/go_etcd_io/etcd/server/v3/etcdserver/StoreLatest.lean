/-
**The server's auth rows with auth on** (the auth plan's E3l, 2026-10-27; `notes/decisions.md`,
"E3l of the auth plan"). Lean-first (no Rocq counterpart).

What the server keeps of its auth store's invariant for the apply thread, with auth on:

- **the checks at the latest state** (`authStoreLatestM`): the store meets `apply.isAuthStoreL`
  for its reader resource and the apply thread's family `auth.latestRes`
  (`apply.isAuthStoreL_of_authInv`); `NewAuthStore`'s construction gives it (`authStoreKit`'s
  post), the built part keeps it (`srvUberBase`);
- **the range check at a reader's lower bound** (`authStoreLbM`, E3s): with auth on, the store's
  `IsRangePermitted` with its verdict no older than any lower bound of the published index
  (`apply.isAuthStoreRangeLb_of_authInv`); from the same construction, kept beside the above;
- **publication** (`authPublishM`, E3t): with auth on, the apply thread raising the published index
  to its history's latest one (E3j's `authPublishT`, of the store's invariant), from the same
  construction, kept beside the above; what it gets, a published index whose recorded state is
  the latest one (`authPubAt`), is what the waiter's reply carries;
- **the admin steps' resource** (E3f's blocker 1, the user's decision 2026-10-27: a separate row).
  The store's half of its `be` field stays in the server's rest (`authBeOn stl bel`, in
  `srvObjsOn`, whose text and D22's `Recover` premise are unchanged) and an admin entry's
  application borrows it. The apply thread's resource (`authApplyResB`) holds, beside
  `authApplyResAt`'s, the backend's write contract at *every* schema auth backend on the server's
  backend `bel` (`authWBackendAt`; the persistent agreement: whichever `*authBackend` the rest's
  half names, its contract is the apply thread's) and the store's admin steps at the resource
  `adminW` (`apply.isAuthStepsX`, of the store's invariant through E3l's backend-keeping
  `X.specTB`); the server's row (`srvAuthApplyResB`) adds the equation of the backend names, the
  environment's write right lending `authBeOn stl bel` (`rwLens E.RW`). `adminW_of_beOn` and
  `beOn_of_adminW` turn the borrowed half into the admin steps' resource and back.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthStepsX
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthCheckTxnLb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthLeaseLb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthApplyRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBkHook

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The store's checks at the latest state, in the mode `M`** (the auth plan's E3l, 2026-10-27;
persistent): in the mode `on γa`, the store `st` (`auth.authIface stl`) meets `apply.isAuthStoreL`
for its reader resource `RD` and the apply thread's family `auth.latestResC stl (.on γa) γc` at
every backend's names `γc` (what the real store's invariant gives, `apply.isAuthStoreL_of_authInv`;
the family at the write token since the auth-on snapshot plan's Prove step); `True` in the other
modes. What the
server's apply thread's latest-state KV triples need of the store (`srvStoreLatest`, `UberOn`). -/
def authStoreLatestM (M : auth.AuthMode) (st : GoInterface) (RD : IProp GF) (stl : Loc) : IProp GF :=
  match M with
  | .on γa => iprop(□ ∀ γc : auth.AuthBkNames,
      apply.isAuthStoreL st RD (.on γa) (auth.latestResC stl (.on γa) γc))
  | _ => iprop(True)

/-- **The store's range check no older than a reader's lower bound, in the mode `M`** (the auth
plan's E3s, 2026-10-27; persistent): in the mode `on γa`, for every lower bound `n` of the published
index (`auth.authPubLbM`), the store's `IsRangePermitted` with its verdict at states no older than `n`
(`apply.isAuthStoreRangeLb`, of the store's invariant through E3j's `IsRangePermitted.specLb`) and
(the lease-src plan, 2026-11-02) the lease checks' methods at such states (`isAuthStoreLeaseLb`,
through the five `specLb`s, `isAuthStoreLeaseLb_of_authInv`); `True` in the other modes. What a
reader with auth on needs of the store (`Range.specOn`, the lease checks' `srvAuthLeaseLb`). -/
def authStoreLbM (M : auth.AuthMode) (st : GoInterface) (RD : IProp GF) : IProp GF :=
  match M with
  | .on γa => iprop(□ ∀ n : Nat, auth.authPubLbM (.on γa) n -∗
      apply.isAuthStoreRangeLb st RD (.on γa) n ∗ isAuthStoreLeaseLb st RD (.on γa) n)
  | _ => iprop(True)

instance authStoreLbM_persistent (M : auth.AuthMode) (st : GoInterface) (RD : IProp GF) :
    Persistent (authStoreLbM (GF := GF) M st RD) := by
  cases M <;> unfold authStoreLbM <;> infer_instance

instance authStoreLatestM_persistent (M : auth.AuthMode) (st : GoInterface) (RD : IProp GF)
    (stl : Loc) : Persistent (authStoreLatestM (GF := GF) M st RD stl) := by
  cases M <;> unfold authStoreLatestM <;> infer_instance

open Iris.ProofMode in
/-- `authStoreLbM`'s range check, with auth on. -/
theorem authStoreLbM_range (γa : auth.AuthNames) (st : GoInterface) (RD : IProp GF) :
    authStoreLbM (GF := GF) (.on γa) st RD ⊢
      □ ∀ n : Nat, auth.authPubLbM (.on γa) n -∗ apply.isAuthStoreRangeLb st RD (.on γa) n := by
  unfold authStoreLbM
  iintro #H !> %n #Hn
  ihave ⟨#HR, -⟩ := H $$ Hn
  iexact HR

open Iris.ProofMode in
/-- `authStoreLbM`'s lease checks, with auth on (the lease-src plan). -/
theorem authStoreLbM_lease (γa : auth.AuthNames) (st : GoInterface) (RD : IProp GF) :
    authStoreLbM (GF := GF) (.on γa) st RD ⊢
      □ ∀ n : Nat, auth.authPubLbM (.on γa) n -∗ isAuthStoreLeaseLb st RD (.on γa) n := by
  unfold authStoreLbM
  iintro #H !> %n #Hn
  ihave ⟨-, #HL⟩ := H $$ Hn
  iexact HL

/-- **The backend's write contract at every schema auth backend on the backend `bel`**
(persistent; E3l): any `*authBackend` `abl` whose `be` field is `bel` (and some logger) has the
contract. The persistent agreement of E3f's blocker 1: the rest's half of the store's `be` field
(`authBeOn stl bel`) names some such `abl`. -/
def authWBackendAt (bel : Loc) (M : auth.AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    IProp GF :=
  iprop(□ ∀ (abl lg : Loc),
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #bel : GoInterface) -∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg -∗
    auth.authWBackendOk (authBkIface abl) M P f T)

instance authWBackendAt_persistent (bel : Loc) (M : auth.AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) : Persistent (authWBackendAt (GF := GF) bel M P f T) := by
  unfold authWBackendAt; infer_instance

/-- **The store's backend `be` is a schema auth backend on `bel`** (persistent; E3l): what of
`authBeOn` is kept while its half of the field is lent. -/
def beOn (bel : Loc) (be : go_etcd_io.etcd.server.v3.auth.AuthBackend) : IProp GF :=
  iprop(∃ (abl lg : Loc), ⌜be = authBkIface abl ∧ lg ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #bel : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg)

instance beOn_persistent (bel : Loc) (be : go_etcd_io.etcd.server.v3.auth.AuthBackend) :
    Persistent (beOn (GF := GF) bel be) := by
  unfold beOn; infer_instance

/-- **The admin steps' resource of the server's store** (E3l): the store's half of its `be` field
with the backend's write contract there, the write token `T`, the field's backend a schema auth
backend on `bel` (`beOn`), and the provider's admin share. -/
def adminW (stl bel : Loc) (M : auth.AuthMode) (P : IProp GF) (f : val) (T : IProp GF) :
    IProp GF :=
  iprop((∃ be : go_etcd_io.etcd.server.v3.auth.AuthBackend,
      ((auth.aF go!"be" stl ↦{DFrac.own (1 : Qp).half} be ∗ auth.authWBackendOk be M P f T) ∗ T) ∗
      beOn bel be) ∗ auth.tpAdmin stl M)

/-- **The admin steps' resource at the current backend's names `γc`** (the auth-on snapshot plan's
Prove step, 2026-11-03): `adminW` at its write token `auth.authWTok γc`, with the apply thread's half
of the backend's name (`auth.authBkCur`), so that it lends the token with the name, `authWHeld`, to
the checks at the latest state (`ownFuT_lendC`) and takes it back. -/
def adminWC (stl bel : Loc) (γa : auth.AuthNames) (P : IProp GF) (f : val) (γc : auth.AuthBkNames) :
    IProp GF :=
  iprop(adminW stl bel (.on γa) P f (auth.authWTok γc) ∗ auth.authBkCur γa (1 : Qp).half γc)

/-- **The apply thread's reader ticket of the auth store, in the mode `M`** (P6.2): `RD` in the
mode `on`, `True` otherwise. -/
def authRdM (M : auth.AuthMode) (RD : IProp GF) : IProp GF :=
  match M with
  | .on _ => RD
  | _ => iprop(True)

/-- **The store's admin steps at every hook and backend** (persistent; the auth-on snapshot plan's
P6.2, 2026-11-03): what the store's construction gives from the admin steps' specs
(`isAuthStepsX_of_authInvTB`, for all `bel Pk f T`), so that an install can rebuild
`authApplyResB`'s hook facts at the new backend. -/
def authStepsAny (stl : Loc) (γa : auth.AuthNames) (RD : IProp GF) : IProp GF :=
  iprop(□ ∀ (bel : Loc) (Pk : IProp GF) (f : val) (T : IProp GF),
    apply.isAuthStepsX (auth.authIface stl) Pk f (.on γa) (auth.tieRes stl (.on γa))
      (adminW stl bel (.on γa) Pk f T) RD)

instance authStepsAny_persistent (stl : Loc) (γa : auth.AuthNames) (RD : IProp GF) :
    Persistent (authStepsAny (GF := GF) stl γa RD) := by
  unfold authStepsAny; infer_instance

/-- **What the apply thread's auth row keeps for a snapshot's install** (persistent; the auth-on
snapshot plan's P6.2, 2026-11-03): the current backend `d`'s lifecycle at the realization's open
share of `d` (`authOpenQ`: retiring and releasing it gives the share back, for the old backend's
close), the write contract at `d`'s frozen hook (`authWAtHook`), and the admin steps at any backend
(`authStepsAny`). -/
def authInstallPre (stl : Loc) (γa : auth.AuthNames) (T : auth.AuthBkNames) (d : mvcc.KBReal)
    (RD : IProp GF) : IProp GF :=
  iprop(auth.authBkLife γa T (backend.bOpen d.γB authOpenQ) ∗ authWAtHook γa d T ∗
    authStepsAny stl γa RD ∗ authBkLend γa T d)

instance authInstallPre_persistent (stl : Loc) (γa : auth.AuthNames) (T : auth.AuthBkNames)
    (d : mvcc.KBReal) (RD : IProp GF) : Persistent (authInstallPre (GF := GF) stl γa T d RD) := by
  unfold authInstallPre; infer_instance

/-- **The apply thread's auth resource with the admin steps' facts at the hook `Pk f`** (E3l;
the hook a parameter since E3n): `authApplyResAt`'s, with, in the mode `on γa`, the write contract
at every schema auth backend on the current backend `d` (`authWBackendAt`) and the store's admin
steps at `adminW` (`apply.isAuthStepsX`), both at the backend's post-lock hook `Pk f` (the server's:
the apply environment's `E.P`, `E.f`, `srvAuthApplyResB`); and (the auth-on snapshot plan's P6.2,
2026-11-03) what an install needs (`authInstallPre` at `d`) with the apply thread's reader ticket
`RD`, what the store's `Recover` reads the new backend with (N4). -/
def authApplyResB (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState) (d : mvcc.KBReal)
    (Pk : IProp GF) (f : val) (RD : IProp GF) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f0 : val) (T : auth.AuthBkNames)
      (be : GoInterface), auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗
      auth.authWBackendOk be (.on γa) P f0 (auth.authWTok T) ∗ auth.authWHeld γa T ∗
      (∃ K : IProp GF, auth.authBkLife γa T K) ∗ auth.authPubTok γa ∗
      auth.tpAdmin stl (.on γa) ∗
      ⌜hs.getLast? = some st⌝ ∗ authWBackendAt d.be (.on γa) Pk f (auth.authWTok T) ∗
      apply.isAuthStepsX (auth.authIface stl) Pk f (.on γa) (auth.tieRes stl (.on γa))
        (adminW stl d.be (.on γa) Pk f (auth.authWTok T)) RD ∗
      authInstallPre stl γa T d RD ∗ RD)
  | _ => iprop(True)

/-- **The admin steps' facts at whichever post-lock hook the server will freeze** (E3n; persistent):
for the real backend `d` with its frozen hook `f'` (not `nil`) at the batch lock `Pk'`, the write
contract at every schema auth backend on `d`'s backend and the store's admin steps there, at the
write token `T`. -/
def authStepsAtHook (stl : Loc) (d : mvcc.KBReal) (γa : auth.AuthNames) (T RD : IProp GF) : IProp GF :=
  iprop(□ ∀ (W' Pk' : IProp GF) (f' : GoFunc),
    backend.isBackend d.γB d.P W' Pk' d.be -∗ backend.plHookRO d.γB f' -∗ ⌜f' ≠ func.nil⌝ -∗
    authWBackendAt d.be (.on γa) Pk' #f' T ∗
      apply.isAuthStepsX (auth.authIface stl) Pk' #f' (.on γa) (auth.tieRes stl (.on γa))
        (adminW stl d.be (.on γa) Pk' #f' T) RD)

instance authStepsAtHook_persistent (stl : Loc) (d : mvcc.KBReal) (γa : auth.AuthNames) (T RD : IProp GF) :
    Persistent (authStepsAtHook (GF := GF) stl d γa T RD) := by
  unfold authStepsAtHook; infer_instance

/-- **The apply thread's auth resource before the hook is frozen** (E3n): `authApplyResB`'s with
its hook-dependent facts for every frozen hook (`authStepsAtHook`), what the store's construction
gives (`authStoreKit`'s post); `authApplyResB_of_pre` instantiates it at the server's hook. -/
def authApplyResPre (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState) (d : mvcc.KBReal)
    (RD : IProp GF) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f0 : val) (T : auth.AuthBkNames)
      (be : GoInterface), auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗
      auth.authWBackendOk be (.on γa) P f0 (auth.authWTok T) ∗ auth.authWHeld γa T ∗
      (∃ K : IProp GF, auth.authBkLife γa T K) ∗ auth.authPubTok γa ∗
      auth.tpAdmin stl (.on γa) ∗
      ⌜hs.getLast? = some st⌝ ∗ authStepsAtHook stl d γa (auth.authWTok T) RD ∗
      ghostMapAuth γa.fresh 1 (∅ : GMap GoString Unit) ∗ authInstallPre stl γa T d RD)
  | _ => iprop(True)

/-- **The rest resource lends the store's half of `be` at the same rest value** (E3n; persistent):
what the apply thread holds (`E.RO`, the rest buckets with the objects' backend parts) lends
`authBeOn stl bel` to an admin entry's application and takes it back, the rest buckets kept. -/
def roLendsAuthBe (RO : apply.RestM → IProp GF) (stl bel : Loc) : IProp GF :=
  iprop(□ ∀ r : apply.RestM, RO r -∗ authBeOn stl bel ∗ (authBeOn stl bel -∗ RO r))

instance roLendsAuthBe_persistent (RO : apply.RestM → IProp GF) (stl bel : Loc) :
    Persistent (roLendsAuthBe RO stl bel) := by
  unfold roLendsAuthBe; infer_instance

/-- **The server's row for its apply thread's auth resource** (E3l): the store its `authStore`
field holds, `authApplyResB` in the environment's mode on the environment's backend `d` (since the
auth-on snapshot plan's P6.2, 2026-11-03, the backend, `E.γ.kb`, in place of its location) at the
environment's hook (`E.P`, `E.f`), and the equation of the backend names: the environment's write
right lends the store's half of `be` on `d`, and (E3n) so does its rest resource, at the same rest
value. -/
def srvAuthApplyResB (s : Loc) (E : apply.AEnv GF) (st : auth.AuthState) : IProp GF :=
  iprop(∃ (stl : Loc) (d : mvcc.KBReal), ⌜E.γ.kb = some d⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer
      go!"authStore" s ↦□ (auth.authIface stl) ∗ authApplyResB E.authMode stl st d E.P E.f E.RD ∗
    rwLens E.RW (authBeOn stl d.be) ∗ roLendsAuthBe E.RO stl d.be)

/-- **Publication, in the mode `M`** (the auth plan's E3t, 2026-10-27; persistent): in the mode
`on γa`, for any non-empty history `hs` of the authority with the tie of the store `stl`'s flag and
cache halves to its latest state (`auth.tieRes`), raising the published index to the latest one,
`hs.length - 1` (E3j's `auth.authPublishT`, of the store's invariant: `authPublishM_of_authInv`);
`True` in the other modes. Since the auth-on snapshot plan's Prove step (2026-11-03), with the
current backend's lifecycle, write token and the apply thread's publication quarter
(`auth.authPubRes`): publication is on the backend the store reads. -/
def authPublishM (M : auth.AuthMode) (stl : Loc) : IProp GF :=
  match M with
  | .on γa => iprop(□ ∀ (hs : List auth.AuthState) (γc : auth.AuthBkNames) (K : IProp GF),
      ⌜hs ≠ []⌝ -∗ auth.authPubRes (.on γa) γc K -∗ auth.authOwn (.on γa) hs -∗
      auth.tieRes stl (.on γa) hs ={⊤}=∗ auth.authPubRes (.on γa) γc K ∗ auth.authOwn (.on γa) hs ∗
      auth.tieRes stl (.on γa) hs ∗ auth.authPubLb γa (hs.length - 1))
  | _ => iprop(True)

instance authPublishM_persistent (M : auth.AuthMode) (stl : Loc) :
    Persistent (authPublishM (GF := GF) M stl) := by
  cases M <;> unfold authPublishM <;> infer_instance

/-- **A published index whose recorded state is `st`, in the mode `M`** (E3t; persistent): in the
mode `on γa`, a lower bound `i` of the published index (`auth.authPubLb`) at which the history
records `st` (`auth.authStateAt`); `True` in the other modes. What the apply thread hands the waiter
with an entry's result (`st` the model's auth state after the entry): a reader holding it is checked
at states no older than that one (`Range.specOn`). -/
def authPubAt (M : auth.AuthMode) (st : auth.AuthState) : IProp GF :=
  match M with
  | .on γa => iprop(∃ i : Nat, auth.authPubLb γa i ∗ auth.authStateAt γa i st)
  | _ => iprop(True)

instance authPubAt_persistent (M : auth.AuthMode) (st : auth.AuthState) :
    Persistent (authPubAt (GF := GF) M st) := by
  cases M <;> unfold authPubAt <;> infer_instance

instance authPubAt_timeless (M : auth.AuthMode) (st : auth.AuthState) :
    Timeless (authPubAt (GF := GF) M st) := by
  cases M <;> unfold authPubAt <;> (try unfold auth.authPubLb auth.authStateAt) <;> infer_instance

/-- A published index's lower bound, forgetting its state. -/
theorem authPubLbM_of_pubAt (γa : auth.AuthNames) (st : auth.AuthState) :
    authPubAt (GF := GF) (.on γa) st ⊢ ∃ i : Nat, auth.authPubLbM (.on γa) i := by
  unfold authPubAt auth.authPubLbM
  iintro ⟨%i, #Hlb, -⟩
  iexists i
  iexact Hlb

end defs

section publish
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

open Iris.ProofMode

/-- **Publication from the store's invariant** (E3t): `auth.authPublishT` at the tie's flag and
cache halves. -/
theorem authPublishM_of_authInv (stl : Loc) (R : IProp GF) (γa : auth.AuthNames) :
    auth.authInv stl R (.on γa) ⊢ authPublishM (.on γa) stl := by
  iintro #Hinv
  unfold authPublishM
  iintro !> %hs %γc %K %hne HR Ho Ht
  iunfold auth.tieRes at Ht
  icases Ht with ⟨%b, %sc, Hfl, #Hev, Hca, #Hsn, %Htie⟩
  obtain ⟨stl', hl⟩ : ∃ x, hs.getLast? = some x := by
    cases h : hs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some x => exact ⟨x, rfl⟩
  imod auth.authPublishT stl R (.on γa) hs b sc stl' (fun _ _ => hl) Htie γc K $$ Hinv HR Ho Hfl Hca
    with ⟨HR, Ho, Hfl, Hca, #Hlb⟩
  imodintro
  iframe HR Ho
  isplitl [Hfl Hca]
  · iunfold auth.tieRes
    iexists b, sc
    iframe Hfl Hev Hca Hsn
    ipureintro; exact Htie
  iunfold auth.authPubLbM at Hlb
  iexact Hlb

omit auth_sem in
/-- A state recorded at `i` is the authority's history's `i`th. -/
theorem authOwn_stateAt_lookup (γa : auth.AuthNames) (hs : List auth.AuthState) (i : Nat)
    (st : auth.AuthState) :
    auth.authOwn (GF := GF) (.on γa) hs ∗ auth.authStateAt γa i st ⊢
      auth.authOwn (.on γa) hs ∗ ⌜hs[i]? = some st⌝ := by
  simp only [auth.authOwn]
  have key : auth.authHistHalf (GF := GF) γa hs ∗ auth.authStateAt γa i st ⊢
      auth.authHistHalf γa hs ∗ ⌜hs[i]? = some st⌝ :=
    (and_intro (by iintro ⟨H, -⟩; iexact H) (auth.authHistHalf_lookup γa hs i st)).trans
      persistent_and_sep_mp
  iintro ⟨⟨Hh, Hc⟩, #Hs⟩
  ihave ⟨Hh, %Hi⟩ := key $$ [Hh]
  · iframe Hh Hs
  iframe Hh Hc
  ipureintro; exact Hi

omit auth_sem in
/-- **Publishing the authority's latest state** (E3t): with the capability, a non-empty history's
latest state `st` gets a published index (`authPubAt`). -/
theorem authPubAt_publish (γa : auth.AuthNames) (stl : Loc) (hs : List auth.AuthState)
    (st : auth.AuthState) (hl : hs.getLast? = some st) (γc : auth.AuthBkNames) (K : IProp GF) :
    authPublishM (GF := GF) (.on γa) stl ⊢ auth.authPubRes (.on γa) γc K -∗ auth.authOwn (.on γa) hs -∗
      auth.tieRes stl (.on γa) hs ={⊤}=∗ auth.authPubRes (.on γa) γc K ∗ auth.authOwn (.on γa) hs ∗
      auth.tieRes stl (.on γa) hs ∗ authPubAt (.on γa) st := by
  iintro #Hp HR Ho Ht
  have hne : hs ≠ [] := by intro h; subst h; cases hl
  unfold authPublishM
  imod Hp $$ %hs %γc %K %hne HR Ho Ht with ⟨HR, Ho, Ht, #Hlb⟩
  ihave ⟨Ho, #Hsn⟩ := auth.authOwn_latestSnap (.on γa) hs $$ Ho
  unfold auth.latestSnap
  icases Hsn with ⟨%i, %st', %hl', #Hst⟩
  rw [hl] at hl'
  cases hl'
  ihave ⟨Ho, %Hi⟩ := authOwn_stateAt_lookup γa hs i st $$ [Ho Hst]
  · iframe Ho Hst
  have hi : i ≤ hs.length - 1 := by
    have := (List.getElem?_eq_some_iff.1 Hi).1
    omega
  ihave #Hlb' := auth.authPubLb_le γa i hi $$ Hlb
  imodintro
  iframe HR Ho Ht
  unfold authPubAt
  iexists i
  iframe Hlb' Hst

omit auth_sem in
/-- **The construction's apply resource publishes its latest state** (E3u): `authPubAt_publish` at
`authApplyResPre`, before the server's applied index's invariant is allocated. -/
theorem authApplyResPre_publish (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState)
    (d : mvcc.KBReal) (RD : IProp GF) :
    authPublishM (GF := GF) M stl ⊢ authApplyResPre M stl st d RD ={⊤}=∗
      authApplyResPre M stl st d RD ∗ authPubAt M st := by
  cases M with
  | on γa =>
    iintro #Hp H
    unfold authApplyResPre
    icases H with ⟨%hs, %P, %f0, %T, %be, Hfu, Ht, Hwb, HT, ⟨%K, #Hlife⟩, Hpt, Htp, %Hl, Hhk, Hfr⟩
    iunfold auth.authOwnFu at Hfu
    icases Hfu with ⟨Ho, Hfuel⟩
    iunfold auth.authWHeld at HT
    icases HT with ⟨Htok, Hbk⟩
    ihave HR := (auth.authPubRes_on γa T K).2 $$ [Htok Hpt]
    · iframe Hlife Htok Hpt
    imod authPubAt_publish γa stl hs st Hl T K $$ Hp HR Ho Ht with ⟨HR, Ho, Ht, #Hpa⟩
    icases (auth.authPubRes_on γa T K).1 $$ HR with ⟨-, Htok, Hpt⟩
    imodintro
    iframe Hpa
    iexists hs, P, f0, T, be
    iunfold auth.authOwnFu
    iframe Ho Hfuel Ht Hwb Hpt Htp Hhk Hfr
    isplitl [Htok Hbk]
    · iunfold auth.authWHeld; iframe Htok Hbk
    isplitr
    · iexists K; iexact Hlife
    ipureintro; exact Hl
  | _ =>
    iintro - H
    imodintro
    iframe H
    unfold authPubAt; itrivial

end publish

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode

/-- `authApplyResB` forgets its admin steps' facts into `authApplyResAt`. -/
theorem authApplyResAt_of_B (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState) (d : mvcc.KBReal)
    (Pk : IProp GF) (f : val) (RD : IProp GF) :
    authApplyResB (GF := GF) M stl st d Pk f RD ⊢ authApplyResAt M stl st := by
  cases M with
  | on γa =>
    unfold authApplyResB authApplyResAt
    iintro ⟨%hs, %P, %f0, %T, %be, Ho, HX, #Hw, HT, Hlife, Hpt, Htp, %Hl, -, -⟩
    iexists hs, P, f0, T, be
    iframe Ho HX Hw HT Hlife Hpt Htp
    ipureintro; exact Hl
  | off => unfold authApplyResB authApplyResAt; iintro -; itrivial
  | any => unfold authApplyResB authApplyResAt; iintro -; itrivial

/-- **The construction's auth resource at the server's frozen hook** (E3n): `authApplyResPre`
instantiated at a real backend `d` with its frozen hook `f` at the batch lock `Pk`, with (P6.2) a
reader ticket of the apply thread's, `RD` in the mode `on` (`authRdM`). -/
theorem authApplyResB_of_pre (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState)
    (d : mvcc.KBReal) (W Pk RD : IProp GF) (f : GoFunc) :
    authApplyResPre (GF := GF) M stl st d RD ∗ backend.isBackend d.γB d.P W Pk d.be ∗
      backend.plHookRO d.γB f ∗ ⌜f ≠ func.nil⌝ ∗ authRdM M RD ⊢
      authApplyResB M stl st d Pk #f RD ∗ authFreshInit M := by
  cases M with
  | on γa =>
    unfold authApplyResPre authApplyResB authFreshInit authRdM
    iintro ⟨⟨%hs, %P, %f0, %T, %be, Ho, HX, #Hw, HT, Hlife, Hpt, Htp, %Hl, #Hat, Hfr, #Hins⟩, #HB,
      #Hhk, %Hnn, HRD⟩
    iunfold authStepsAtHook at Hat
    ihave ⟨#Hwa, #Hst⟩ := Hat $$ %W %Pk %f HB Hhk []
    · ipureintro; exact Hnn
    iframe Hfr
    iexists hs, P, f0, T, be
    iframe Ho HX Hw HT Hlife Hpt Htp Hwa Hst Hins HRD
    ipureintro; exact Hl
  | off => unfold authApplyResPre authApplyResB authFreshInit; iintro -; isplit <;> itrivial
  | any => unfold authApplyResPre authApplyResB authFreshInit; iintro -; isplit <;> itrivial

/-- `authApplyResB` reads the backend `d` only through its location, names and parameters (P6.2). -/
theorem authApplyResB_kb_congr (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState)
    (d d' : mvcc.KBReal) (Pk : IProp GF) (f : val) (RD : IProp GF) (h1 : d'.be = d.be)
    (h2 : d'.γB = d.γB) (h3 : d'.P = d.P) :
    authApplyResB (GF := GF) M stl st d' Pk f RD = authApplyResB M stl st d Pk f RD := by
  cases M <;> simp only [authApplyResB, authInstallPre, authWAtHook, authBkLend, h1, h2, h3]

/-- A reader ticket gives the apply thread's in any mode (P6.2). -/
theorem authRdM_of (M : auth.AuthMode) (RD : IProp GF) : RD ⊢ authRdM M RD := by
  cases M with
  | on γa => unfold authRdM; iintro H; iexact H
  | off => unfold authRdM; iintro -; itrivial
  | any => unfold authRdM; iintro -; itrivial

/-- `srvAuthApplyResB` forgets into `srvAuthApplyResAt`. -/
theorem srvAuthApplyResAt_of_B (s : Loc) (E : apply.AEnv GF) (st : auth.AuthState) :
    srvAuthApplyResB (GF := GF) s E st ⊢ srvAuthApplyResAt s E st := by
  unfold srvAuthApplyResB srvAuthApplyResAt
  iintro ⟨%stl, %d, -, #Hf, H, -, -⟩
  iexists stl
  iframe Hf
  iapply authApplyResAt_of_B $$ H

/-- **The rest's half of the store's `be` field, as the admin steps' write resource** (E3l):
with the write contract at every schema auth backend on `bel` and the write token. -/
theorem adminW_of_beOn (stl bel : Loc) (M : auth.AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) :
    authBeOn (GF := GF) stl bel ∗ authWBackendAt bel M P f T ∗ T ⊢
      ∃ be : go_etcd_io.etcd.server.v3.auth.AuthBackend,
        ((auth.aF go!"be" stl ↦{DFrac.own (1 : Qp).half} be ∗ auth.authWBackendOk be M P f T) ∗ T) ∗
        beOn bel be := by
  iintro ⟨Hb, #Hall, HT⟩
  iunfold authBeOn at Hb
  icases Hb with ⟨%abl, %lg, %Hlg, Hbe, #Habbe, #Hablg⟩
  iexists (authBkIface abl)
  iunfold authWBackendAt at Hall
  ihave #Hok := Hall $$ %abl %lg Habbe Hablg
  iframe Hbe Hok HT
  iunfold beOn
  iexists abl, lg
  iframe Habbe Hablg
  ipureintro; exact ⟨rfl, Hlg⟩

/-- **The admin steps' write resource back as the rest's half** (E3l): the token stays. -/
theorem beOn_of_adminW (stl bel : Loc) (M : auth.AuthMode) (P : IProp GF) (f : val)
    (T : IProp GF) (be : go_etcd_io.etcd.server.v3.auth.AuthBackend) :
    ((auth.aF go!"be" stl ↦{DFrac.own (1 : Qp).half} be ∗ auth.authWBackendOk be M P f T) ∗ T) ∗
      beOn bel be ⊢ authBeOn (GF := GF) stl bel ∗ T := by
  iintro ⟨⟨⟨Hbe, -⟩, HT⟩, #Hon⟩
  iunfold beOn at Hon
  icases Hon with ⟨%abl, %lg, ⟨%Hab, %Hlg⟩, #Habbe, #Hablg⟩
  subst Hab
  iframe HT
  iunfold authBeOn
  iexists abl, lg
  iframe Hbe Habbe Hablg
  ipureintro; exact Hlg

/-- **The environment's write right lends the store's half on its backend** (E3l): of
`srvRestRWH`'s objects (`srvObjsOn`), as the server builds `E.RW`. -/
theorem rwLens_authBeOn (γB : backend.BNames) (al stl lp cl bel : Loc) :
    ⊢ rwLens (GF := GF) (srvRestRWH γB (srvObjsOn al stl lp cl bel)) (authBeOn stl bel) := by
  iunfold rwLens
  iintro !> HRW
  iunfold srvRestRWH at HRW
  icases HRW with ⟨Hrw, Hobj⟩
  iunfold srvObjsOn at Hobj
  icases Hobj with ⟨Hal, Hau, Hle, Hcl⟩
  iframe Hau
  iintro Hau
  iunfold srvRestRWH
  iframe Hrw
  iunfold srvObjsOn
  iframe Hal Hau Hle Hcl

/-- **The server's rest resource lends the store's half on its backend** (E3n): of
`srvRestOwnH`'s objects (`srvObjsOn`), as the server builds `E.RO`. -/
theorem roLends_authBeOn (M : auth.AuthMode) (γB : backend.BNames) (c al stl lp cl bel : Loc) :
    ⊢ roLendsAuthBe (GF := GF) (srvRestOwnH M γB c (srvObjsOn al stl lp cl bel)) stl bel := by
  iunfold roLendsAuthBe
  iintro !> %r HRO
  iunfold srvRestOwnH at HRO
  icases HRO with ⟨Hr, Hobj⟩
  iunfold srvObjsOn at Hobj
  icases Hobj with ⟨Hal, Hau, Hle, Hcl⟩
  iframe Hau
  iintro Hau
  iunfold srvRestOwnH
  iframe Hr
  iunfold srvObjsOn
  iframe Hal Hau Hle Hcl

/-- **The authority with the tie and the admin steps' resource lend the latest-state resource
with the write token** (the auth-on snapshot plan's Prove step, 2026-11-03): `auth.ownFuT_lend`'s
`latestRes`, with the token and the half of the name out of `adminWC`; the family the generic
apply layer's check is lent (`apply.uberAdmC`'s premise). -/
theorem ownFuT_lendC (stl bel : Loc) (γa : auth.AuthNames) (P : IProp GF) (f : val)
    (γc : auth.AuthBkNames) (hs : List auth.AuthState) :
    (auth.authOwnFu (GF := GF) γa hs ∗ auth.tieRes stl (.on γa) hs) ∗ adminWC stl bel γa P f γc ⊢
      auth.latestResC stl (.on γa) γc hs ∗
        (auth.latestResC stl (.on γa) γc hs -∗
          (auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs) ∗ adminWC stl bel γa P f γc) := by
  iintro ⟨Hown, Hw⟩
  ihave ⟨HL, Hback⟩ := auth.ownFuT_lend stl γa hs $$ Hown
  unfold adminWC adminW
  icases Hw with ⟨⟨⟨%be, ⟨⟨Hbe, #Hok⟩, HT⟩, #Hon⟩, Htp⟩, Hbk⟩
  isplitl [HL HT Hbk]
  · unfold auth.latestResC
    iframe HL
    simp only [auth.authWHeldM, auth.authWHeld]
    iframe HT Hbk
  iintro HL
  unfold auth.latestResC
  icases HL with ⟨HL, Hw⟩
  simp only [auth.authWHeldM, auth.authWHeld]
  icases Hw with ⟨HT, Hbk⟩
  ihave Ho := Hback $$ HL
  iframe Ho Hbk Htp
  iexists be
  iframe Hbe Hok HT Hon

/-- **The apply thread's auth row lends the auth buckets** (#7-on): in the mode `on`, its write
token and its half of the history, at the latest state `st`, borrow the auth buckets' part
(`authInstallPre`'s `authBkLend`), which hold `st`. -/
theorem srvAuthApplyResB_lend (s : Loc) (E : apply.AEnv GF) (st : auth.AuthState)
    (γa : auth.AuthNames) (hM : E.authMode = .on γa) :
    srvAuthApplyResB (GF := GF) s E st ⊢
      bkLendW E authBkts (authBucketsAt st) (srvAuthApplyResB s E st) := by
  iintro H
  unfold bkLendW
  iintro %d0 %hd0
  iunfold srvAuthApplyResB at H
  icases H with ⟨%stl, %d, %hd, #Hsf, Har, Hrw, Hro⟩
  rw [hd0] at hd
  obtain rfl := Option.some.inj hd
  rw [hM]
  simp only [authApplyResB]
  icases Har with ⟨%hs, %P, %f0, %T, %be, Hfu, Htie, Hwok, Hwh, Hlife, Hpub, Htp, %Hl, Hwat,
    Hsteps, #Hins, HRD⟩
  ihave #Hins' := Hins
  iunfold authInstallPre at Hins'
  icases Hins' with ⟨-, -, -, #Hlend⟩
  iunfold auth.authOwnFu at Hfu
  icases Hfu with ⟨Hown, Hfuel⟩
  simp only [auth.authOwn]
  icases Hown with ⟨Hhh, Hcur⟩
  iunfold auth.authWHeld at Hwh
  icases Hwh with ⟨Hwt, Hbc⟩
  iunfold authBkLend at Hlend
  imod Hlend $$ %hs %st %Hl Hwt Hhh with ⟨%r, Hp, %Hr, Hback⟩
  imodintro
  iexists r
  iframe Hp
  isplitr
  · ipureintro; exact Hr
  iintro Hp
  imod Hback $$ Hp with ⟨Hwt, Hhh⟩
  imodintro
  iunfold srvAuthApplyResB
  iexists stl, d0
  iframe Hsf Hrw Hro
  isplitr
  · ipureintro; exact hd0
  rw [hM]
  simp only [authApplyResB]
  iexists hs, P, f0, T, be
  iframe Htie Hwok Hlife Hpub Htp Hwat Hsteps Hins HRD
  isplitl [Hhh Hcur Hfuel]
  · iunfold auth.authOwnFu
    iframe Hfuel
    simp only [auth.authOwn]
    iframe Hhh Hcur
  isplitl [Hwt Hbc]
  · iunfold auth.authWHeld
    iframe Hwt Hbc
  ipureintro; exact Hl

end lemmas

end EtcdGrove
end Perennial
