/-
**Why a guard refused a request** (auth-guard-completeness G0/G2, 2026-11-14;
`notes/auth-guard-scope.md`, §1-2). Lean-first (no Rocq counterpart).

The guards' specs said one thing: a request that passes was permitted (`authedOutB`, `adminOutB`,
`AuthBound.lean`). This file states the converse in its reason form: a refused request names a
reason its class allows, each a fact about the request or about the auth state no older than what
the caller knew when it called (a lower bound `n` of the store's published index, `auth.authPubLbM`).
Every reason starts with a read of the enabled flag `true` at a state no older than `n`: in Go every
refusal of these checks follows an `IsAuthEnabled()` of `true` during the call (`store.go:916`,
`:1073`; `v3_server.go:1278`; `v3rpc/auth.go:192`). So a guard that refuses with auth disabled meets
none of them.

* the request side (`reqSideWhy`, common to every class): `ErrUserEmpty` when the context carries no
  token, or when the flag also read `false` at such a state (the flag changed since `n`: the disable
  race, `nonissues/etcd-auth-requireauthinfo-disable-race-user-empty.md`; `auth.noPrincipalFrom`);
  `ErrInvalidAuthToken` when the context carries a token (`auth.tokRefusedFrom`: only that; the token
  provider's contract says nothing of a token it refuses, and a live token may be refused, since the
  simple provider's keeper may delete it at any time in a model with no clock; token liveness is the
  Scope's G5);
* **authenticated** (`authedWhy`): no other reason;
* **admin** (`adminWhy`): also a principal bound to the request's token (`principalBound`) refused by
  `IsAdminPermitted` (`auth.adminRefusalFrom`, each error tied to its case: `ErrUserEmpty` for an
  unnamed principal, `ErrUserNotFound` for a user absent at a state no older than `n`,
  `ErrPermissionDenied` for one present there without the root role);
* **RBAC** (`permWhy`): also, for the principal the request side gave (`AuthInfo{}` exactly when it
  gave none), `isOpPermitted`'s errors tied to their cases (`ErrUserEmpty` for revision `0`,
  `ErrAuthOldRevision` for a revision below a state's no older than `n`, `ErrPermissionDenied` with a
  view of such states in which the check refuses, `auth.refusedV`).

With a frozen history (`auth.authFrozenFrom`: no admin change after `n`), enabled, and a context
carrying a token, the authenticated class's only reason left is `ErrInvalidAuthToken`
(`authed_served_of_frozen`), and so is the admin class's when every principal bound to the token is
root (`admin_served_of_frozen`). In the mode `any` every reason is `True`. In the mode `off` the
request side's is `False` (the flag never reads `true`); the admin check's is `True`, because the
off store's request side (`isReqAuth`, of `NewAuthStore`'s axiom) does not say that `AuthInfoFromCtx`
returns no error with auth off (a follow-up of D22, discharging that axiom by proof, would give it
without new trust).

The guards' outcomes with the reason (`authedOutC`, `adminOutC`) are what their specs state; a caller
that needs no reason drops it (`authedOutB_of_C`, `adminOutB_of_C`). TLS identities are out of scope
(D4): `ErrUserEmpty`'s reason is "no token", silent on a client certificate. A guard that never
returns meets every triple.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBound
public import Proof.go_etcd_io.etcd.server.v3.auth.FreshCheck

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The request side's reasons** for the error `err` of a request at `ctx`, seen with the lower
bound `n` (persistent): the flag read `true` at a state no older than `n`, and `ErrUserEmpty` with no
principal from the request side (`auth.noPrincipalFrom`) or `ErrInvalidAuthToken` for a token the
context carries (`auth.tokRefusedFrom`). -/
def reqSideWhy (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) : IProp GF :=
  iprop(auth.enabledVerdictFrom M n true ∗
    ((auth.authErrOf .userEmpty err ∗ auth.noPrincipalFrom M n ctx) ∨
     (auth.authErrOf .invalidAuthToken err ∗ auth.tokRefusedFrom M n ctx)))

instance reqSideWhy_persistent (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    Persistent (reqSideWhy (GF := GF) M n ctx err) := by
  unfold reqSideWhy; infer_instance

/-- **Why the authenticated-user check refused** (persistent): the request side's reasons only
(`False` with auth off); `True` in the mode `any`. -/
def authedWhy (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) : IProp GF :=
  match M with
  | .any => iprop(True)
  | _ => reqSideWhy M n ctx err

instance authedWhy_persistent (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    Persistent (authedWhy (GF := GF) M n ctx err) := by
  unfold authedWhy; cases M <;> infer_instance

/-- **Why the admin check refused** on the server `s` (persistent): with auth on, the request side's
reasons, or a principal bound to the request (`principalBound`) that `IsAdminPermitted` refused at
states no older than `n` (`auth.adminRefusalFrom`); `True` in the modes `off` (see the file header)
and `any`. -/
def adminWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) : IProp GF :=
  match M with
  | .on γa => iprop(reqSideWhy M n ctx err ∨
      ∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo, principalBound s M ctx (some info) ∗
        auth.adminRefusalFrom γa n (some info) err)
  | _ => iprop(True)

instance adminWhy_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    Persistent (adminWhy (GF := GF) s M n ctx err) := by
  unfold adminWhy; cases M <;> infer_instance

/-- **Why one permission check `(key, rangeEnd, op)` refused** the auth info `info` (persistent;
`isOpPermitted`, `store.go:862-899`): the request side's reasons, or, for the principal the request
side gave (`AuthInfo{}` exactly when it gave none, or one bound to the request), the flag read `true`
at a state no older than `n` and `ErrUserEmpty` for revision `0`, `ErrAuthOldRevision` for a revision
below a state's no older than `n`, or `ErrPermissionDenied` with a view of such states in which the
check refuses (`auth.refusedV`); `False` with auth off, `True` in the mode `any`. -/
def permWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : auth.PermType) :
    IProp GF :=
  match M with
  | .on γa => iprop(reqSideWhy M n ctx err ∨
      (((⌜info.Username' = (zeroValDef : GoString) ∧ info.Revision' = W64 0⌝ ∗
          auth.noPrincipalFrom M n ctx) ∨ principalBound s M ctx (some info)) ∗
        auth.enabledVerdictFrom M n true ∗
        ((auth.authErrOf .userEmpty err ∗ ⌜info.Revision' = W64 0⌝) ∨
         (auth.authErrOf .authOldRevision err ∗ ∃ (j : Nat) (st : auth.AuthState),
            auth.authStateAt γa j st ∗ ⌜n ≤ j ∧ uint.nat info.Revision' < st.revision⌝) ∨
         (auth.authErrOf .permissionDenied err ∗ ∃ v : auth.AuthView, auth.recordedVFrom γa n v ∗
            ⌜auth.refusedV v (auth.authInfoM info) key rangeEnd op⌝))))
  | .any => iprop(True)
  | .off => reqSideWhy M n ctx err

instance permWhy_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : auth.PermType) :
    Persistent (permWhy (GF := GF) s M n ctx err info key rangeEnd op) := by
  unfold permWhy; cases M <;> infer_instance

/-- **The authenticated-user check's outcome with its reason** (persistent): `authedOutB`, and on an
error the reason (`authedWhy`). -/
def authedOutC (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) : IProp GF :=
  iprop(authedOutB s M ctx err ∗ (∀ _ : err ≠ GoInterface.nil, authedWhy M n ctx err))

instance authedOutC_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    Persistent (authedOutC (GF := GF) s M n ctx err) := by
  unfold authedOutC; infer_instance

/-- **The admin check's outcome with its reason** (persistent): `adminOutB`, and on an error the
reason (`adminWhy`). -/
def adminOutC (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) : IProp GF :=
  iprop(adminOutB s M ctx err ∗ (∀ _ : err ≠ GoInterface.nil, adminWhy s M n ctx err))

instance adminOutC_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    Persistent (adminOutC (GF := GF) s M n ctx err) := by
  unfold adminOutC; infer_instance

/-- The reason dropped. -/
theorem authedOutB_of_C (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    authedOutC (GF := GF) s M n ctx err ⊢ authedOutB s M ctx err := by
  unfold authedOutC; iintro ⟨#H, -⟩; iexact H

/-- The reason dropped. -/
theorem adminOutB_of_C (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    adminOutC (GF := GF) s M n ctx err ⊢ adminOutB s M ctx err := by
  unfold adminOutC; iintro ⟨#H, -⟩; iexact H

/-- `authedOutC` gives `authedOut`. -/
theorem authedOut_of_C (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    authedOutC (GF := GF) s M n ctx err ⊢ authedOut M err :=
  (authedOutB_of_C s M n ctx err).trans (authedOut_of_authedOutB s M ctx err)

/-- `adminOutC` gives `adminOut`. -/
theorem adminOut_of_C (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    adminOutC (GF := GF) s M n ctx err ⊢ adminOut M err :=
  (adminOutB_of_C s M n ctx err).trans (adminOut_of_adminOutB s M ctx err)

/-! ### What the guards' proofs use -/

/-- The request side's reasons are the authenticated check's. -/
theorem authedWhy_of_reqSide (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    reqSideWhy (GF := GF) M n ctx err ⊢ authedWhy M n ctx err := by
  cases M with
  | off => unfold authedWhy; iintro #H; iexact H
  | any => unfold authedWhy; iintro -; itrivial
  | on γa => unfold authedWhy; iintro #H; iexact H

/-- The request side's reasons are the admin check's. -/
theorem adminWhy_of_reqSide (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    reqSideWhy (GF := GF) M n ctx err ⊢ adminWhy s M n ctx err := by
  cases M with
  | off => unfold adminWhy; iintro -; itrivial
  | any => unfold adminWhy; iintro -; itrivial
  | on γa => unfold adminWhy; iintro #H; ileft; iexact H

theorem adminWhy_off (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface)
    (h : M.isOn = false) : ⊢ adminWhy (GF := GF) s M n ctx err := by
  cases M with
  | off => unfold adminWhy; itrivial
  | any => cases h
  | on γa => cases h

/-- `IsAdminPermitted(nil)` refused a request the request side gave no principal: the request
side's `ErrUserEmpty` (the check's only error for `nil`), the check's own read of the flag `true`
kept. -/
theorem adminWhy_none (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface)
    (herr : err ≠ GoInterface.nil) :
    auth.noPrincipalFrom (GF := GF) M n ctx ⊢ auth.adminVerdictFromO M n none err -∗
      adminWhy s M n ctx err := by
  cases M with
  | off => unfold auth.adminVerdictFromO; iintro - %H; exact absurd H herr
  | any => unfold adminWhy; iintro - -; itrivial
  | on γa =>
    unfold auth.adminVerdictFromO adminWhy reqSideWhy auth.adminRefusalFrom
    iintro #Hnp ⟨-, #Hr⟩
    icases Hr $$ %herr with ⟨⟨%i, %sf, #Hsf, %Hi⟩, (⟨#Hue, -⟩ | ⟨%info, %Hs, -⟩)⟩
    · ileft
      isplitr
      · unfold auth.enabledVerdictFrom; iexists i, sf; iframe Hsf; ipureintro; exact ⟨Hi.1, Hi.2.symm⟩
      · ileft; iframe Hue Hnp
    · cases Hs.1

/-- `IsAdminPermitted(info)` refused a bound principal: the admin reason. -/
theorem adminWhy_some (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (herr : err ≠ GoInterface.nil) :
    principalBound (GF := GF) s M ctx (some info) ⊢ auth.adminVerdictFromO M n (some info) err -∗
      adminWhy s M n ctx err := by
  cases M with
  | off => unfold auth.adminVerdictFromO; iintro - %H; exact absurd H herr
  | any => unfold adminWhy; iintro - -; itrivial
  | on γa =>
    unfold auth.adminVerdictFromO adminWhy
    iintro #Hpb ⟨-, #Hr⟩
    ihave #Hr' := Hr $$ %herr
    iright; iexists info; iframe Hpb Hr'

/-- A pass of `IsAdminPermitted` read with a lower bound is the admin token. -/
theorem adminRes_of_verdictFromO (M : auth.AuthMode) (n : Nat)
    (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    auth.adminVerdictFromO (GF := GF) M n oinfo GoInterface.nil ⊢ adminRes M oinfo := by
  cases M with
  | off => unfold adminRes; iintro -; itrivial
  | any => unfold adminRes; iintro -; itrivial
  | on γa =>
    unfold auth.adminVerdictFromO adminRes
    iintro ⟨⟨%i, %st, #Hst, %Hp⟩, -⟩
    iexists i, st; iframe Hst; ipureintro; exact Hp.2 rfl

/-! ### The positive form: a frozen history leaves only a refused token -/

/-- With the history frozen at `st` from `n` on, auth enabled there, and a token in the context, the
authenticated check's only reason left is `ErrInvalidAuthToken`: it does not refuse with
`ErrUserEmpty`, nor with any other error. -/
theorem authed_served_of_frozen (γa : auth.AuthNames) (n : Nat) (st : auth.AuthState)
    (ctx err : GoInterface) (t : GoString) (hen : st.enabled = true)
    (htok : auth.ctxTokenOf ctx = some t) :
    auth.authFrozenFrom (GF := GF) γa n st ⊢ authedWhy (.on γa) n ctx err -∗
      auth.authErrOf .invalidAuthToken err := by
  unfold authedWhy reqSideWhy auth.noPrincipalFrom auth.authFrozenFrom
  iintro #Hfz ⟨-, (⟨-, (⟨-, %Hnone⟩ | #Hdis)⟩ | ⟨#Hit, -⟩)⟩
  · rw [htok] at Hnone; cases Hnone
  · unfold auth.enabledVerdictFrom
    icases Hdis with ⟨%j, %s', #Hs', %Hj⟩
    ihave %Heq := Hfz $$ %j %s' Hs'
    have h := Heq Hj.1
    subst h
    rw [hen] at Hj; cases Hj.2
  · iexact Hit

/-- With the history frozen at `st` from `n` on, auth enabled there, a token in the context, and every
principal bound to the request a named user with the root role at `st`, the admin check's only reason
left is `ErrInvalidAuthToken`. -/
theorem admin_served_of_frozen (s : Loc) (γa : auth.AuthNames) (n : Nat) (st : auth.AuthState)
    (ctx err : GoInterface) (t : GoString) (hen : st.enabled = true)
    (htok : auth.ctxTokenOf ctx = some t) :
    auth.authFrozenFrom (GF := GF) γa n st ⊢
      (□ ∀ info : go_etcd_io.etcd.server.v3.auth.AuthInfo, principalBound s (.on γa) ctx (some info) -∗
        ⌜info.Username' ≠ [] ∧ ∃ u, st.users !! info.Username' = some u ∧ auth.isRoot u⌝) -∗
      adminWhy s (.on γa) n ctx err -∗ auth.authErrOf .invalidAuthToken err := by
  iintro #Hfz #Hroot #H
  unfold adminWhy
  icases H with (#Hr | ⟨%info, #Hpb, #Href⟩)
  · iapply (authed_served_of_frozen γa n st ctx err t hen htok) $$ Hfz
    unfold authedWhy; iexact Hr
  · ihave %Hrt := Hroot $$ %info Hpb
    obtain ⟨hname, u0, hu0, hroot0⟩ := Hrt
    unfold auth.adminRefusalFrom auth.authFrozenFrom
    icases Href with ⟨-, (⟨-, %Hemp⟩ | ⟨%info', %Hi, (⟨-, %j, %su, #Hsu, %Hj⟩ | ⟨-, %j, %su, %u, #Hsu, %Hj⟩)⟩)⟩
    · exact absurd (Hemp info rfl) hname
    · obtain ⟨hi, -⟩ := Hi
      cases hi
      ihave %Heq := Hfz $$ %j %su Hsu
      have h := Heq Hj.1
      subst h
      rw [hu0] at Hj; cases Hj.2
    · obtain ⟨hi, -⟩ := Hi
      cases hi
      ihave %Heq := Hfz $$ %j %su Hsu
      have h := Heq Hj.1
      subst h
      rw [hu0] at Hj
      obtain ⟨-, hu, hnr⟩ := Hj
      cases hu
      exact absurd hroot0 hnr

end defs

section apart
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Two auth error variables of different messages are different errors** (the variables'
message cells, the auth package's facts: `errVarCells authErrMsgs`). -/
theorem authErrOf_apart (e e' : auth.AuthErr) (m m' : GoString)
    (he : (e.var, m) ∈ go_etcd_io.etcd.server.v3.auth.authErrMsgs)
    (he' : (e'.var, m') ∈ go_etcd_io.etcd.server.v3.auth.authErrMsgs) (hm : m ≠ m')
    (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      auth.authErrOf e err -∗ auth.authErrOf e' err -∗ False := by
  iintro #Hpkg #H1 #H2
  ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HVC⟩
  ihave #Hc1 := EtcdGrove.errVarCells_mem he $$ HVC
  ihave #Hc2 := EtcdGrove.errVarCells_mem he' $$ HVC
  ihave #Hap := EtcdGrove.errVarApart_of e.var e'.var m m' hm $$ Hc1 Hc2
  iunfold EtcdGrove.errVarApart at Hap
  icases Hap with ⟨%e1, %e2, #Hg1, #Hg2, %Hne⟩
  iunfold auth.authErrOf at H1
  icases H1 with ⟨%ei, #Hei, %Hei'⟩
  iunfold auth.authErrOf at H2
  icases H2 with ⟨%ej, #Hej, %Hej'⟩
  icombine Hg1 Hei gives %Heq1
  icombine Hg2 Hej gives %Heq2
  subst Hei'
  injection Hej' with Hij
  injection Heq1 with Heq1
  injection Heq2 with Heq2
  ipureintro
  exact Hne (by rw [Heq1, Heq2, Hij])

/-- An auth error variable's error is an `*errorString` whose cell holds one of the package's
messages. -/
theorem authErrVarIs_cell (err : GoInterface) (hne : err ≠ GoInterface.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢ authErrVarIs err -∗
      ∃ (x : Loc) (m : GoString),
        ⌜err = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x ∧
          m ∈ go_etcd_io.etcd.server.v3.auth.authErrMsgs.map Prod.snd⌝ ∗ EtcdGrove.errStrCell x m := by
  iintro #Hpkg #Ha
  iunfold authErrVarIs at Ha
  icases Ha with (%Hn | ⟨%g, %e, %Hg, #Hge, %He⟩)
  · exact absurd Hn hne
  obtain ⟨⟨g', m⟩, hmem, rfl⟩ := List.mem_map.1 Hg.1
  ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HVC⟩
  ihave #Hc := EtcdGrove.errVarCells_mem hmem $$ HVC
  iunfold EtcdGrove.errVarCell at Hc
  icases Hc with ⟨%x, #Hx, #Hcell⟩
  icombine Hge Hx gives %Heq
  iexists x, m
  iframe Hcell
  ipureintro
  refine ⟨?_, List.mem_map_of_mem (f := Prod.snd) hmem⟩
  rw [He]; exact Heq

/-- **The read path's errors are not auth error variables** (auth-guard-completeness G3, G0's check):
`readErrIs`'s (a context error, `ErrStopped`, `ErrLeaderChanged`, `ErrTimeout`) and `authErrVarIs`'s
are `errors.New` errors of different messages (or, for `DeadlineExceeded`, of another type). -/
theorem readErrIs_authErrVarIs (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors ⊢
      readErrIs err -∗ authErrVarIs err -∗ ⌜err = GoInterface.nil⌝ := by
  iintro ⟨#Hpa, #Hpe⟩ #Hr #Ha
  by_cases hne : err = GoInterface.nil
  · ipureintro; exact hne
  ihave ⟨%x, %m, ⟨%Hx, %Hm⟩, #Hcell⟩ := authErrVarIs_cell err hne $$ Hpa Ha
  have hm : ∀ m', m' ∉ go_etcd_io.etcd.server.v3.auth.authErrTexts → m ≠ m' := by
    intro m' h' heq; subst heq; apply h'
    rw [← go_etcd_io.etcd.server.v3.auth.authErrMsgs_snd]; exact Hm
  ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpe
  icases Hei with ⟨-, -, #HEC⟩
  -- the server's `errors.New` variable `X` of message `msg` is not `err`
  have hvar : ∀ (X msg : GoString),
      (X, msg) ∈ go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs →
      msg ∉ go_etcd_io.etcd.server.v3.auth.authErrTexts →
      (EtcdGrove.errVarCells (GF := GF) go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs ⊢
        globalAddr X ↦□ err -∗ EtcdGrove.errStrCell x m -∗ False) := by
    intro X msg hX hmsg
    iintro #HC #HX #Hc
    ihave #HcX := EtcdGrove.errVarCells_mem hX $$ HC
    iunfold EtcdGrove.errVarCell at HcX
    icases HcX with ⟨%y, #Hy, #Hcy⟩
    icombine HX Hy gives %Heq
    rw [Hx] at Heq
    injection Heq with Heq
    injection Heq with _ Hv
    have hxy : x = y := go.intoVal_inj (V := Loc) Hv
    subst hxy
    iunfold EtcdGrove.errStrCell at Hc Hcy
    icombine Hc Hcy gives %Hmm
    exact absurd Hmm (hm msg hmsg)
  iunfold readErrIs at Hr
  icases Hr with (%Hn | #Hc | #Hs | #Hl | #Ht)
  · ipureintro; exact Hn
  · iunfold context.isCtxErr at Hc
    icases Hc with (⟨-, %y, %hy, #Hs⟩ | ⟨-, %hv⟩)
    · rw [Hx] at hy
      injection hy with hy
      injection hy with _ Hv
      have hxy : x = y := go.intoVal_inj (V := Loc) Hv
      subst hxy
      iunfold EtcdGrove.errStrCell at Hcell
      icombine Hcell Hs gives %Hmm
      exact absurd Hmm (hm _ (by decide))
    · rw [Hx] at hv
      injection hv with hv
      injection hv with hty
      simp [context.deadlineExceededError.ty] at hty
  · iexfalso
    iapply (hvar go_etcd_io.etcd.server.v3.etcdserver.errors.ErrStopped go!"etcdserver: server stopped"
      (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; simp) (by decide)) $$ HEC Hs Hcell
  · iexfalso
    iapply (hvar go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLeaderChanged go!"etcdserver: leader changed"
      (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; simp) (by decide)) $$ HEC Hl Hcell
  · iexfalso
    iapply (hvar go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeout go!"etcdserver: request timed out"
      (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; simp) (by decide)) $$ HEC Ht Hcell

/-- **The authenticated-user check never refuses for permission**: `authedWhy`'s errors are
`ErrUserEmpty` and `ErrInvalidAuthToken`, apart from `ErrPermissionDenied` (what excludes 3.6.9's
admin-only `MemberList`, `TestZZGuardMemberList369Regression`). -/
theorem authedWhy_not_permissionDenied (γa : auth.AuthNames) (n : Nat) (ctx err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      authedWhy (.on γa) n ctx err -∗ auth.authErrOf .permissionDenied err -∗ False := by
  iintro #Hpkg #H #Hpd
  unfold authedWhy reqSideWhy
  icases H with ⟨-, (⟨#Hue, -⟩ | ⟨#Hit, -⟩)⟩
  · iapply (authErrOf_apart .userEmpty .permissionDenied go!"auth: user name is empty"
      go!"auth: permission denied"
      (by simp [auth.AuthErr.var, go_etcd_io.etcd.server.v3.auth.authErrMsgs])
      (by simp [auth.AuthErr.var, go_etcd_io.etcd.server.v3.auth.authErrMsgs])
      (by decide) err) $$ Hpkg Hue Hpd
  · iapply (authErrOf_apart .invalidAuthToken .permissionDenied go!"auth: invalid auth token"
      go!"auth: permission denied"
      (by simp [auth.AuthErr.var, go_etcd_io.etcd.server.v3.auth.authErrMsgs])
      (by simp [auth.AuthErr.var, go_etcd_io.etcd.server.v3.auth.authErrMsgs])
      (by decide) err) $$ Hpkg Hit Hpd

end apart

end EtcdGrove
end Perennial
