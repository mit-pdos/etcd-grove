/-
**Why a guard refused a request** (auth-guard-completeness G0, 2026-11-14;
`notes/auth-guard-scope.md`, §1-2). Lean-first (no Rocq counterpart).

The guards' specs said one thing: a request that passes was permitted (`authedOutB`, `adminOutB`,
`AuthBound.lean`). This file states the converse in its reason form: a refused request names a
reason its class allows, each a fact about the request or about the auth state no older than what
the caller knew when it called (a lower bound `n` of the store's published index, `auth.authPubLbM`):

* the request side (`reqSideWhy`, common to every class): `ErrUserEmpty` when the context carries no
  token or auth was disabled at a state no older than `n` (the disable race,
  `nonissues/etcd-auth-requireauthinfo-disable-race-user-empty.md`; `auth.noPrincipalFrom`), and
  `ErrInvalidAuthToken` when the context carries a token (`auth.tokRefusedFrom`; until token
  liveness, the Scope's G5, only that there was one);
* **authenticated** (`authedWhy`): no other reason; every accepted token passes;
* **admin** (`adminWhy`): also a principal bound to the request's token (`principalBound`) that is
  absent, unnamed or not root at states no older than `n` (`auth.adminRefusedFrom`), with the check's
  error (`auth.adminErrOf`);
* **RBAC** (`permWhy`): also a view of states no older than `n` in which the permission check refuses
  (`auth.refusedV`), for the principal the request side gave (`AuthInfo{}` exactly when it gave
  none).

Each is `True` in the modes `off` and `any`. The guards' outcomes with the reason are `C` variants
of today's (`authedOutC`, `adminOutC`), so that a caller that needs no reason drops it
(`authedOutB_of_C`, `adminOutB_of_C`). TLS identities are out of scope (D4): `ErrUserEmpty`'s reason
is "no token", silent on a client certificate. A guard that never returns meets every triple.
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
bound `n` (persistent): `ErrUserEmpty` with no principal from the request side
(`auth.noPrincipalFrom`), or `ErrInvalidAuthToken` for a token the context carries
(`auth.tokRefusedFrom`). -/
def reqSideWhy (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) : IProp GF :=
  iprop((auth.authErrOf .userEmpty err ∗ auth.noPrincipalFrom M n ctx) ∨
    (auth.authErrOf .invalidAuthToken err ∗ auth.tokRefusedFrom M n ctx))

instance reqSideWhy_persistent (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    Persistent (reqSideWhy (GF := GF) M n ctx err) := by
  unfold reqSideWhy; infer_instance

/-- **Why the authenticated-user check refused** (persistent): with auth on, the request side's
reasons only. -/
def authedWhy (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) : IProp GF :=
  match M with
  | .on _ => reqSideWhy M n ctx err
  | _ => iprop(True)

instance authedWhy_persistent (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    Persistent (authedWhy (GF := GF) M n ctx err) := by
  unfold authedWhy; cases M <;> infer_instance

/-- **Why the admin check refused** on the server `s` (persistent): with auth on, the request side's
reasons, or a principal bound to the request (`principalBound`) refused at states no older than `n`
(`auth.adminRefusedFrom`) with one of the check's errors (`auth.adminErrOf`). -/
def adminWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) : IProp GF :=
  match M with
  | .on γa => iprop(reqSideWhy M n ctx err ∨
      ∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo, principalBound s M ctx (some info) ∗
        auth.adminRefusedFrom γa n (some (auth.authInfoM info)) ∗ auth.adminErrOf (some info) err)
  | _ => iprop(True)

instance adminWhy_persistent (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) :
    Persistent (adminWhy (GF := GF) s M n ctx err) := by
  unfold adminWhy; cases M <;> infer_instance

/-- **Why one permission check `(key, rangeEnd, op)` refused** the auth info `info` (persistent):
with auth on, the request side's reasons, or, for the principal the request side gave (`AuthInfo{}`
exactly when it gave none, or one bound to the request), a view of states no older than `n` in which
the check refuses (`auth.refusedV`). -/
def permWhy (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) (op : auth.PermType) :
    IProp GF :=
  match M with
  | .on γa => iprop(reqSideWhy M n ctx err ∨
      (((⌜info.Username' = (zeroValDef : GoString) ∧ info.Revision' = W64 0⌝ ∗
        auth.noPrincipalFrom M n ctx) ∨ principalBound s M ctx (some info)) ∗
        ∃ v : auth.AuthView, auth.recordedVFrom γa n v ∗
          ⌜auth.refusedV v (auth.authInfoM info) key rangeEnd op⌝))
  | _ => iprop(True)

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

/-- The request side's reasons are admin reasons. -/
theorem adminWhy_of_reqSide (s : Loc) (γa : auth.AuthNames) (n : Nat) (ctx err : GoInterface) :
    reqSideWhy (GF := GF) (.on γa) n ctx err ⊢ adminWhy s (.on γa) n ctx err := by
  unfold adminWhy; iintro #H; ileft; iexact H

/-! ### What the guards' proofs use -/

/-- The request side's reasons are the authenticated check's, in a mode that may refuse. -/
theorem authedWhy_of_reqSide (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface)
    (h : M.isOn = true) :
    reqSideWhy (GF := GF) M n ctx err ⊢ authedWhy M n ctx err := by
  cases M with
  | off => cases h
  | any => unfold authedWhy; iintro -; itrivial
  | on γa => unfold authedWhy; iintro #H; iexact H

/-- With auth off, any refusal has its reason (there is none to give). -/
theorem authedWhy_off (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface) (h : M.isOn = false) :
    ⊢ authedWhy (GF := GF) M n ctx err := by
  cases M with
  | off => unfold authedWhy; itrivial
  | any => cases h
  | on γa => cases h

/-- The request side's reasons are the admin check's, in a mode that may refuse. -/
theorem adminWhy_of_reqSide' (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface)
    (h : M.isOn = true) :
    reqSideWhy (GF := GF) M n ctx err ⊢ adminWhy s M n ctx err := by
  cases M with
  | off => cases h
  | any => unfold adminWhy; iintro -; itrivial
  | on γa => unfold adminWhy; iintro #H; ileft; iexact H

theorem adminWhy_off (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface)
    (h : M.isOn = false) : ⊢ adminWhy (GF := GF) s M n ctx err := by
  cases M with
  | off => unfold adminWhy; itrivial
  | any => cases h
  | on γa => cases h

/-- `IsAdminPermitted(nil)` refused a request the request side gave no principal: the request
side's `ErrUserEmpty` (the check's only error for `nil`). -/
theorem adminWhy_none (s : Loc) (M : auth.AuthMode) (n : Nat) (ctx err : GoInterface)
    (herr : err ≠ GoInterface.nil) :
    auth.noPrincipalFrom (GF := GF) M n ctx ⊢ auth.adminVerdictFromO M n none err -∗
      adminWhy s M n ctx err := by
  cases M with
  | off => unfold auth.adminVerdictFromO; iintro - %H; exact absurd H herr
  | any => unfold adminWhy; iintro - -; itrivial
  | on γa =>
    unfold auth.adminVerdictFromO adminWhy reqSideWhy
    iintro #Hnp ⟨-, #Hr⟩
    icases Hr $$ %herr with ⟨-, #He⟩
    unfold auth.adminErrOf
    icases He with (#Hue | ⟨%Hs, -⟩)
    · ileft; ileft; iframe Hue Hnp
    · cases Hs

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
    icases Hr $$ %herr with ⟨#Hrf, #He⟩
    iright; iexists info; iframe Hpb He; simp only [Option.map_some]; iexact Hrf

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

/-- `IsAdminPermitted`'s answer read with a lower bound is `nil` with auth off. -/
theorem adminVerdictFromO_off (M : auth.AuthMode) (n : Nat)
    (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) :
    auth.adminVerdictFromO (GF := GF) M n oinfo err ⊢ ⌜M = .off → err = GoInterface.nil⌝ := by
  cases M with
  | off => unfold auth.adminVerdictFromO; iintro %H; ipureintro; intro _; exact H
  | any => iintro -; ipureintro; intro h; cases h
  | on γa => iintro -; ipureintro; intro h; cases h

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

/-- **The authenticated-user check never refuses for permission**: `authedWhy`'s errors are
`ErrUserEmpty` and `ErrInvalidAuthToken`, apart from `ErrPermissionDenied` (what excludes 3.6.9's
admin-only `MemberList`, `TestZZGuardMemberList369Regression`). -/
theorem authedWhy_not_permissionDenied (γa : auth.AuthNames) (n : Nat) (ctx err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      authedWhy (.on γa) n ctx err -∗ auth.authErrOf .permissionDenied err -∗ False := by
  iintro #Hpkg #H #Hpd
  unfold authedWhy reqSideWhy
  icases H with (⟨#Hue, -⟩ | ⟨#Hit, -⟩)
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
