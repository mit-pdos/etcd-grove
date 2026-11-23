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
none of them. One exception (G4): `doSerialize`'s revision re-check (`oldRevWhy`) reads no flag, and
its auth info may come from the TLS fallback, which reads none either; its reason has the flag read
`true` only when the server's TLS fallback is off (otherwise `srvTLSId`:
`nonissues/etcd-auth-old-revision-auth-disabled.md`).

* the request side (`reqSideWhy`, common to every class): `ErrUserEmpty` when the context carries no
  token, or when the flag also read `false` at such a state (the flag changed since `n`; unordered:
  for `requireAuthInfo` a race with `AuthDisable`,
  `nonissues/etcd-auth-requireauthinfo-disable-race-user-empty.md`; for the admin check and the
  watch's `isWatchPermitted` a race with `AuthEnable`, `nonissues/etcd-admin-check-authenable-race.md`;
  `auth.noPrincipalFrom`);
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
  `ErrAuthOldRevision` for a non-zero revision below a state's no older than `n`,
  `ErrPermissionDenied` for a non-zero, current revision and a user absent, or not root and not
  covered, at such states).

With the authority's history frozen from `n` on (`auth.histFrozenFrom`), enabled, and a context
carrying a token, the authenticated class's only reason left is `ErrInvalidAuthToken`
(`authed_served_of_frozen`), and so is the admin class's when every principal bound to the token is
root (`admin_served_of_frozen`). In the mode `any` every reason is `True`. In the mode `off` the
request side's is `False` (the flag never reads `true`); the admin and RBAC checks' are `True`, because the
off store's request side (`isReqAuth`, of `NewAuthStore`'s axiom) does not say that `AuthInfoFromCtx`
returns no error with auth off (a follow-up of D22, discharging that axiom by proof, would give it
without new trust).

The guards' outcomes with the reason (`authedOutC`, `adminOutC`) are what their specs state; a caller
that needs no reason drops it (`authedOutB_of_C`, `adminOutB_of_C`). TLS identities are out of scope
(D4): `ErrUserEmpty`'s reason is "no token", silent on a client certificate; the one place they appear
is `oldRevWhy`'s `srvTLSId` alternative (the fallback enabled), which a server without client-certificate
auth excludes (`srvTLSId_false`). A guard that never
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
def reqSideWhy (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) : IProp GF :=
  iprop(auth.enabledVerdictFrom M n true ∗
    ((auth.authErrOf .userEmpty err ∗ auth.noPrincipalFrom M n tok) ∨
     (auth.authErrOf .invalidAuthToken err ∗ auth.tokRefusedFrom M n tok)))

instance reqSideWhy_persistent (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    Persistent (reqSideWhy (GF := GF) M n tok err) := by
  unfold reqSideWhy; infer_instance

/-- **Why the authenticated-user check refused** (persistent): the request side's reasons only
(`False` with auth off); `True` in the mode `any`. -/
def authedWhy (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) : IProp GF :=
  match M with
  | .any => iprop(True)
  | _ => reqSideWhy M n tok err

instance authedWhy_persistent (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    Persistent (authedWhy (GF := GF) M n tok err) := by
  unfold authedWhy; cases M <;> infer_instance

/-- **Why the admin check refused** on the server `s` (persistent): with auth on, the request side's
reasons, or a principal bound to the request (`principalBound`) that `IsAdminPermitted` refused at
states no older than `n` (`auth.adminRefusalFrom`); `True` in the modes `off` (see the file header)
and `any`. -/
def adminWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) : IProp GF :=
  match M with
  | .on γa => iprop(reqSideWhy M n tok err ∨
      ∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo, principalBound (srvTLSId s) M tok (some info) ∗
        auth.adminRefusalFrom γa n (some info) err)
  | _ => iprop(True)

instance adminWhy_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    Persistent (adminWhy (GF := GF) s M n tok err) := by
  unfold adminWhy; cases M <;> infer_instance

/-- **Why one permission check `(key, rangeEnd, op)` refused** the auth info `info` (persistent;
`isOpPermitted`, `store.go:862-899`): the request side's reasons, or, for the principal the request
side gave (`AuthInfo{}` exactly when it gave none, or one bound to the request), the flag read `true`
at a state no older than `n` and `ErrUserEmpty` for revision `0`; `ErrAuthOldRevision` for a non-zero
revision below a state's no older than `n`; or `ErrPermissionDenied` for a non-zero revision no lower
than the revision read (a state no older than `n`) and a user absent, or without the root role and not
covered, at such states (`auth.permRefusalFrom`, `store.go:869-899`). The anonymous principal's
`ErrUserEmpty` beside `auth.noPrincipalFrom`'s flag read `false` is the watch's race with `AuthEnable`
(`AuthInfoFromCtx` reads `false`, `isOpPermitted` `true`: a valid-token client refused,
`nonissues/etcd-admin-check-authenable-race.md`). `True` in the modes `off` (as
`adminWhy`: the off store's request side leaves `AuthInfoFromCtx`'s error free; a follow-up of D22)
and `any`. -/
def permWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : auth.PermType) :
    IProp GF :=
  match M with
  | .on γa => iprop(reqSideWhy M n tok err ∨
      (((⌜info.Username' = (zeroValDef : GoString) ∧ info.Revision' = W64 0⌝ ∗
          auth.noPrincipalFrom M n tok) ∨ principalBound (srvTLSId s) M tok (some info)) ∗
        auth.permRefusalFrom γa n info key rangeEnd op err))
  | _ => iprop(True)

instance permWhy_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : auth.PermType) :
    Persistent (permWhy (GF := GF) s M n tok err info key rangeEnd op) := by
  unfold permWhy; cases M <;> infer_instance

/-- **The authenticated-user check's outcome with its reason** (persistent): `authedOutB`, and on an
error the reason (`authedWhy`). -/
def authedOutC (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) : IProp GF :=
  iprop(authedOutB s M tok err ∗ (∀ _ : err ≠ GoInterface.nil, authedWhy M n tok err))

instance authedOutC_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    Persistent (authedOutC (GF := GF) s M n tok err) := by
  unfold authedOutC; infer_instance

/-- **The caller authenticated, relative to `n`** (persistent; auth-lease S4, Freeze §4.4/§10 T1/H1): auth
disabled at a state no older than `n`, or a principal bound to the request's token `tok` (`requireAuthInfo`'s
success: it returns `nil` only when the flag reads `false`, read after the caller's `n` was published, or when
the token names a principal). By the token (perheap's re-keying, Thaw 2, 2026-11-19; until then by the context). -/
def authedFrom (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) : IProp GF :=
  iprop(auth.enabledVerdictFrom M n false ∨
    ∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo, □ (⌜M.isOn = true⌝ → principalBound (srvTLSId s) M tok (some info)))

instance authedFrom_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) :
    Persistent (authedFrom (GF := GF) s M n tok) := by
  unfold authedFrom; infer_instance

/-- **The admin check's outcome with its reason** (persistent): `adminOutB`, and on an error the
reason (`adminWhy`). -/
def adminOutC (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) : IProp GF :=
  iprop(adminOutB s M tok err ∗ (∀ _ : err ≠ GoInterface.nil, adminWhy s M n tok err))

instance adminOutC_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    Persistent (adminOutC (GF := GF) s M n tok err) := by
  unfold adminOutC; infer_instance

/-- The reason dropped. -/
theorem authedOutB_of_C (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    authedOutC (GF := GF) s M n tok err ⊢ authedOutB s M tok err := by
  unfold authedOutC; iintro ⟨#H, -⟩; iexact H

/-- The reason dropped. -/
theorem adminOutB_of_C (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    adminOutC (GF := GF) s M n tok err ⊢ adminOutB s M tok err := by
  unfold adminOutC; iintro ⟨#H, -⟩; iexact H

/-- `authedOutC` gives `authedOut`. -/
theorem authedOut_of_C (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    authedOutC (GF := GF) s M n tok err ⊢ authedOut M err :=
  (authedOutB_of_C s M n tok err).trans (authedOut_of_authedOutB s M tok err)

/-- `adminOutC` gives `adminOut`. -/
theorem adminOut_of_C (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    adminOutC (GF := GF) s M n tok err ⊢ adminOut M err :=
  (adminOutB_of_C s M n tok err).trans (adminOut_of_adminOutB s M tok err)

/-! ### What the guards' proofs use -/

/-- The request side's reasons are the authenticated check's. -/
theorem authedWhy_of_reqSide (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    reqSideWhy (GF := GF) M n tok err ⊢ authedWhy M n tok err := by
  cases M with
  | off => unfold authedWhy; iintro #H; iexact H
  | any => unfold authedWhy; iintro -; itrivial
  | on γa => unfold authedWhy; iintro #H; iexact H

/-- The request side's reasons are the admin check's. -/
theorem adminWhy_of_reqSide (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    reqSideWhy (GF := GF) M n tok err ⊢ adminWhy s M n tok err := by
  cases M with
  | off => unfold adminWhy; iintro -; itrivial
  | any => unfold adminWhy; iintro -; itrivial
  | on γa => unfold adminWhy; iintro #H; ileft; iexact H

theorem adminWhy_off (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (h : M.isOn = false) : ⊢ adminWhy (GF := GF) s M n tok err := by
  cases M with
  | off => unfold adminWhy; itrivial
  | any => cases h
  | on γa => cases h

/-- `IsAdminPermitted(nil)` refused a request the request side gave no principal: the request
side's `ErrUserEmpty` (the check's only error for `nil`), the check's own read of the flag `true`
kept. -/
theorem adminWhy_none (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (herr : err ≠ GoInterface.nil) :
    auth.noPrincipalFrom (GF := GF) M n tok ⊢ auth.adminVerdictFromO M n none err -∗
      adminWhy s M n tok err := by
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
theorem adminWhy_some (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (herr : err ≠ GoInterface.nil) :
    principalBound (GF := GF) (srvTLSId s) M tok (some info) ⊢ auth.adminVerdictFromO M n (some info) err -∗
      adminWhy s M n tok err := by
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

/-- With the authority's history `hs` frozen at `st` from `n` on (`auth.histFrozenFrom`), auth enabled
there, and a token in the context, the authenticated check's only reason left is `ErrInvalidAuthToken`:
it does not refuse with `ErrUserEmpty`, nor with any other error. Stated over the authority as it
stands (`auth.authOwn`, given back), not over states recorded later. -/
theorem authed_served_of_frozen (γa : auth.AuthNames) (hs : List auth.AuthState) (n : Nat)
    (st : auth.AuthState) (tok : Option GoString) (err : GoInterface) (t : GoString) (hf : auth.histFrozenFrom hs n st)
    (hen : st.enabled = true) (htok : tok = some t) :
    auth.authOwn (GF := GF) (.on γa) hs ∗ authedWhy (.on γa) n tok err ⊢
      auth.authOwn (.on γa) hs ∗ auth.authErrOf .invalidAuthToken err := by
  unfold authedWhy reqSideWhy auth.noPrincipalFrom
  iintro ⟨Ho, -, (⟨-, (⟨-, %Hnone⟩ | #Hdis)⟩ | ⟨#Hit, -⟩)⟩
  · rw [htok] at Hnone; cases Hnone
  · unfold auth.enabledVerdictFrom
    icases Hdis with ⟨%j, %s', #Hs', %Hj⟩
    ihave ⟨Ho, %Heq⟩ := auth.authOwn_frozen γa hs n st j s' hf Hj.1 $$ [$Ho $Hs']
    subst Heq
    rw [hen] at Hj; cases Hj.2
  · iframe Ho Hit

/-- With the authority's history frozen at `st` from `n` on, auth enabled there, a token in the
context, and every principal bound to the request a named user with the root role at `st`, the admin
check's only reason left is `ErrInvalidAuthToken`. Under client-certificate TLS
(`ClientCertAuthEnabled`) the premise on bound principals is vacuous-making: `principalBound` then
holds of any auth info (`srvTLSId`; D4), so the premise says every user is root. -/
theorem admin_served_of_frozen (s : Loc) (γa : auth.AuthNames) (hs : List auth.AuthState) (n : Nat)
    (st : auth.AuthState) (tok : Option GoString) (err : GoInterface) (t : GoString) (hf : auth.histFrozenFrom hs n st)
    (hen : st.enabled = true) (htok : tok = some t) :
    (□ ∀ info : go_etcd_io.etcd.server.v3.auth.AuthInfo, principalBound (GF := GF) (srvTLSId s) (.on γa) tok (some info) -∗
        ⌜info.Username' ≠ [] ∧ ∃ u, st.users !! info.Username' = some u ∧ auth.isRoot u⌝) ∗
      auth.authOwn (.on γa) hs ∗ adminWhy s (.on γa) n tok err ⊢
      auth.authOwn (.on γa) hs ∗ auth.authErrOf .invalidAuthToken err := by
  iintro ⟨#Hroot, Ho, #H⟩
  unfold adminWhy
  icases H with (#Hr | ⟨%info, #Hpb, #Href⟩)
  · iapply (authed_served_of_frozen γa hs n st tok err t hf hen htok)
    iframe Ho; unfold authedWhy; iexact Hr
  · ihave %Hrt := Hroot $$ %info Hpb
    obtain ⟨hname, u0, hu0, hroot0⟩ := Hrt
    unfold auth.adminRefusalFrom
    icases Href with ⟨-, (⟨-, %Hemp⟩ | ⟨%info', %Hi, (⟨-, %j, %su, #Hsu, %Hj⟩ | ⟨-, %j, %su, %u, #Hsu, %Hj⟩)⟩)⟩
    · exact absurd (Hemp info rfl) hname
    · obtain ⟨hi, -⟩ := Hi
      cases hi
      ihave ⟨Ho, %Heq⟩ := auth.authOwn_frozen γa hs n st j su hf Hj.1 $$ [$Ho $Hsu]
      subst Heq
      rw [hu0] at Hj; cases Hj.2
    · obtain ⟨hi, -⟩ := Hi
      cases hi
      ihave ⟨Ho, %Heq⟩ := auth.authOwn_frozen γa hs n st j su hf Hj.1 $$ [$Ho $Hsu]
      subst Heq
      rw [hu0] at Hj
      obtain ⟨-, hu, hnr⟩ := Hj
      cases hu
      exact absurd hroot0 hnr

/-! ### What `isWatchPermitted`'s proof uses -/

theorem permWhy_of_reqSide (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : auth.PermType) :
    reqSideWhy (GF := GF) M n tok err ⊢ permWhy s M n tok err info key rangeEnd op := by
  cases M with
  | on γa => unfold permWhy; iintro #H; ileft; iexact H
  | _ => unfold permWhy; iintro -; itrivial

/-- The anonymous principal (`AuthInfo{}`, the request side gave none) refused. -/
theorem permWhy_anon (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : auth.PermType)
    (herr : err ≠ GoInterface.nil)
    (h0 : info.Username' = (zeroValDef : GoString) ∧ info.Revision' = W64 0) :
    auth.noPrincipalFrom (GF := GF) M n tok ⊢ auth.permRefusalM M n info key rangeEnd op err -∗
      permWhy s M n tok err info key rangeEnd op := by
  cases M with
  | on γa =>
    unfold permWhy auth.permRefusalM
    iintro #Hnp #Hr
    iright; isplitr
    · ileft; iframe Hnp; ipureintro; exact h0
    · iapply Hr; exact herr
  | _ => unfold permWhy; iintro - -; itrivial

/-- A principal bound to the request refused. -/
theorem permWhy_bound (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : auth.PermType)
    (herr : err ≠ GoInterface.nil) :
    principalBound (GF := GF) (srvTLSId s) M tok (some info) ⊢ auth.permRefusalM M n info key rangeEnd op err -∗
      permWhy s M n tok err info key rangeEnd op := by
  cases M with
  | on γa =>
    unfold permWhy auth.permRefusalM
    iintro #Hpb #Hr
    iright; isplitr
    · iright; iexact Hpb
    · iapply Hr; exact herr
  | _ => unfold permWhy; iintro - -; itrivial

theorem permWhy_off (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : auth.PermType)
    (h : M.isOn = false) : ⊢ permWhy (GF := GF) s M n tok err info key rangeEnd op := by
  cases M with
  | off => unfold permWhy; itrivial
  | any => cases h
  | on γa => cases h

/-! ### The serializable read path (auth-guard-completeness G4) -/

/-- **The auth info a check saw, as the request side gave it** (persistent; `permWhy`'s principal
part): the anonymous one (`AuthInfo{}`, `doSerialize`'s and `isWatchPermitted`'s stand-in when the
request side gave none, `auth.noPrincipalFrom`), or one bound to the request (`principalBound`). -/
def infoWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) : IProp GF :=
  iprop((⌜info.Username' = (zeroValDef : GoString) ∧ info.Revision' = W64 0⌝ ∗
      auth.noPrincipalFrom M n tok) ∨ principalBound (srvTLSId s) M tok (some info))

instance infoWhy_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    Persistent (infoWhy (GF := GF) s M n tok info) := by
  unfold infoWhy; infer_instance

/-- **Why `doSerialize`'s revision re-check refused** (persistent; `v3_server.go:1053`,
`if ai.Revision != 0 && ai.Revision != s.authStore.Revision()`): `ErrAuthOldRevision`, for an auth
info with a non-zero revision bound to the request (`principalBound`) that the request side gave
with the flag read `true` at a state no older than `n`, or with the server's TLS fallback enabled
(`srvTLSId`: only that it is enabled; the principal may still have come from a token, but if it came
from the fallback no flag was read: `nonissues/etcd-auth-old-revision-auth-disabled.md`), and a state no older
than `n` (`Revision()`'s read, after the read) whose revision is not the info's. -/
def oldRevWhy (s : Loc) (γa : auth.AuthNames) (n : Nat) (tok : Option GoString) (err : GoInterface) : IProp GF :=
  iprop(auth.authErrOf .authOldRevision err ∗ ∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo,
    ⌜uint.nat info.Revision' ≠ 0⌝ ∗ principalBound (srvTLSId s) (.on γa) tok (some info) ∗
    (auth.enabledVerdictFrom (.on γa) n true ∨ srvTLSId s) ∗
    ∃ (j : Nat) (sr : auth.AuthState), auth.authStateAt γa j sr ∗
      ⌜n ≤ j ∧ sr.revision ≠ uint.nat info.Revision'⌝)

instance oldRevWhy_persistent (s : Loc) (γa : auth.AuthNames) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    Persistent (oldRevWhy (GF := GF) s γa n tok err) := by
  unfold oldRevWhy; infer_instance

/-- **Why `doSerialize` refused** on the server `s`, its check's refusal being `R info err` for the
auth info `info` it passed (G4; `v3_server.go:1035-1057`): with auth on, the request side's reasons
(`reqSideWhy`), or the check's refusal of the auth info the request side gave (`infoWhy`), or its
own revision re-check (`oldRevWhy`); `True` in the modes `off` (the off store's request side leaves
`AuthInfoFromCtx`'s error free, as `adminWhy`) and `any`. -/
def serialWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (R : go_etcd_io.etcd.server.v3.auth.AuthInfo → GoInterface → IProp GF) : IProp GF :=
  match M with
  | .on γa => iprop(reqSideWhy M n tok err ∨ (∃ info, infoWhy s M n tok info ∗ R info err) ∨
      oldRevWhy s γa n tok err)
  | _ => iprop(True)

/-- `permRefusalFrom` at a later lower bound is one at an earlier. -/
theorem auth.permRefusalFrom_mono (γa : auth.AuthNames) (n n' : Nat) (h : n ≤ n')
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : auth.PermType)
    (err : GoInterface) :
    auth.permRefusalFrom (GF := GF) γa n' info key rangeEnd op err ⊢
      auth.permRefusalFrom γa n info key rangeEnd op err := by
  unfold auth.permRefusalFrom
  iintro ⟨⟨%i, %sf, #Hsf, %Hi⟩, H⟩
  isplitr
  · iexists i, sf; iframe Hsf; ipureintro; exact ⟨Nat.le_trans h Hi.1, Hi.2⟩
  icases H with (⟨#He, %Hr⟩ | ⟨#He, %j, %sr, #Hsr, %Hj⟩ |
    ⟨#He, %j, %ju, %jc, %sr, %su, %sc, #Hsr, #Hsu, #Hsc, %Hj⟩)
  · ileft; iframe He; ipureintro; exact Hr
  · iright; ileft; iframe He; iexists j, sr; iframe Hsr; ipureintro
    exact ⟨Nat.le_trans h Hj.1, Hj.2⟩
  · iright; iright; iframe He; iexists j, ju, jc, sr, su, sc; iframe Hsr Hsu Hsc; ipureintro
    exact ⟨Nat.le_trans h Hj.1, Nat.le_trans h Hj.2.1, Nat.le_trans h Hj.2.2.1, Hj.2.2.2⟩

/-- `permWhy` from the check's principal and its refusal at a later bound. -/
theorem permWhy_of_infoWhy (s : Loc) (γa : auth.AuthNames) (n n' : Nat) (h : n ≤ n')
    (tok : Option GoString) (err : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString)
    (op : auth.PermType) (herr : err ≠ GoInterface.nil) :
    infoWhy (GF := GF) s (.on γa) n tok info ⊢ auth.permRefusalM (.on γa) n' info key rangeEnd op err -∗
      permWhy s (.on γa) n tok err info key rangeEnd op := by
  unfold infoWhy permWhy auth.permRefusalM
  iintro #Hi #Hr
  ihave #Hr' := Hr $$ %herr
  iright
  isplitr
  · iexact Hi
  · iapply (auth.permRefusalFrom_mono γa n n' h) $$ Hr'

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
theorem authedWhy_not_permissionDenied (γa : auth.AuthNames) (n : Nat) (tok : Option GoString) (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      authedWhy (.on γa) n tok err -∗ auth.authErrOf .permissionDenied err -∗ False := by
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

/-- **An error variable whose message cell is not an auth message is not an auth error variable**
(the cells' messages: `readErrIs_authErrVarIs`'s argument, for any package's `errors.New` variable). -/
theorem errVarCell_authErrVarIs (X m : GoString) (err : GoInterface)
    (hm : m ∉ go_etcd_io.etcd.server.v3.auth.authErrTexts) (hne : err ≠ GoInterface.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      EtcdGrove.errVarCell X m -∗ globalAddr X ↦□ err -∗ authErrVarIs err -∗ False := by
  iintro #Hpa #HcX #HX #Ha
  ihave ⟨%x, %m', ⟨%Hx, %Hm⟩, #Hcell⟩ := authErrVarIs_cell err hne $$ Hpa Ha
  iunfold EtcdGrove.errVarCell at HcX
  icases HcX with ⟨%y, #Hy, #Hcy⟩
  icombine HX Hy gives %Heq
  rw [Hx] at Heq
  injection Heq with Heq
  injection Heq with _ Hv
  have hxy : x = y := go.intoVal_inj (V := Loc) Hv
  subst hxy
  iunfold EtcdGrove.errStrCell at Hcell Hcy
  icombine Hcell Hcy gives %Hmm
  exfalso; apply hm
  rw [← go_etcd_io.etcd.server.v3.auth.authErrMsgs_snd, ← Hmm]; exact Hm

end apart

end EtcdGrove
end Perennial
