/-
**The API layer's auth guards** (the auth plan's A2, 2026-10-23; `notes/auth-plan.md`): what a
passing guard establishes, as the token the guarded inner call takes. Lean-first (no Rocq
counterpart).

The server's entry points guard their inner operation with one of two checks before calling it:
the **admin check** (`AuthAdmin.isPermitted`, `EtcdServer.checkMembershipOperationPermission`:
`AuthInfoFromCtx` then the store's `IsAdminPermitted`) or the **authenticated-user check**
(`AuthAdmin.requireAuthInfo`, `EtcdServer.requireAuthInfo`: with auth enabled, `AuthInfoFromCtx`
must return a non-`nil` auth info). A guard's spec states what its passing establishes, over the
auth store's contract in its mode `M` (`apply.isAuthStore … M`, `auth.AuthMode`): in `on γa`, a
recorded state of the history `γa` that passes; in `off` and `any`, nothing (`adminRes`,
`authedRes`, persistent). A guarded entry point's spec takes the inner operation's triple as a
contract whose precondition carries the token, so the inner call happens only after a passing
check, and with auth off always (`v3rpc/InvAuthAdmin.lean`, `EtcdServer__RemoveMember.lean`).

**The checks' outcomes** (`adminOut M err`, `authedOut M err`): an error the apply package's
facts describe (`applyErrIs`), and on `nil` the token (for some auth info, `nil` or not); the
authenticated-user check also never refuses with auth off (`M.isOn = false → err = nil`), and
refuses only with auth enabled at a recorded state (`enabledVerdict M true`). The admin check's
error may be `AuthInfoFromCtx`'s, which the request-side contract (`isReqAuth`) leaves free, so
its outcome says nothing of the mode.

**The server's auth fields** (`srvAuthAt s E`, persistent): the auth store `s.authStore` with
its request side (`isReqAuth`, `AuthInfoFromCtx`), the certificate flag `ClientCertAuthEnabled`,
and the store's contract (`apply.isAuthStore`); from the proposer's and the reader's views of the
server (`srvAuthAt_of_views`).

**A premise the contracts lacked** (`adminNilOk st RD M`, `srvAdminNilOk s E`; since the auth
plan's S3, 2026-10-23, derivable from the store's contract, `adminNilOk_of_isAuthStore`): the admin check
calls `IsAdminPermitted(authInfo)` with the `nil` auth info `AuthInfoFromCtx` returns when the
request carries none; the store's contract (`apply.isAuthStore`) and the real store's spec
(`auth.authStore.IsAdminPermitted.spec`) take a non-`nil` one (`a ↦{dq} info`). The real method
answers `nil` with auth disabled and `ErrUserEmpty` otherwise (`store.go`, `IsAdminPermitted`),
the verdict `adminVerdict M none err`; until the store's spec covers `nil` (track S), the admin
guards take that clause as a premise.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass

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

/-! ## The tokens -/

/-- **An admin check passed** for the auth info `ai` (`none`: a `nil` pointer) in the mode `M`
(persistent): in `on γa`, a recorded state at which `ai` is admin (`adminOk`: auth disabled, or a
non-empty user with the root role), `adminVerdict`'s first half at `nil`; nothing otherwise. -/
def adminRes (M : auth.AuthMode) (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    IProp GF :=
  match M with
  | .on γa => iprop(∃ (i : Nat) (st : auth.AuthState), auth.authStateAt γa i st ∗
      ⌜auth.adminOk st (ai.map auth.authInfoM)⌝)
  | _ => iprop(True)

instance adminRes_persistent (M : auth.AuthMode)
    (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    Persistent (adminRes (GF := GF) M ai) := by
  unfold adminRes; cases M <;> infer_instance

/-- A passed admin check's verdict is the token. -/
theorem adminRes_of_adminVerdict (M : auth.AuthMode)
    (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    auth.adminVerdict (GF := GF) M ai GoInterface.nil ⊢ adminRes M ai := by
  cases M
  · unfold adminRes; iintro -; itrivial
  · unfold adminRes; iintro -; itrivial
  · unfold auth.adminVerdict adminRes
    iintro ⟨⟨%i, %st, #Hst, %Hp⟩, -⟩
    iexists i, st
    iframe #
    ipureintro
    exact Hp rfl

/-- **An authenticated-user check passed** for the auth info `ai` in the mode `M` (persistent):
in `on γa`, auth disabled at a recorded state, or the request carried an auth info
(`ai = some _`); nothing otherwise. -/
def authedRes (M : auth.AuthMode) (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    IProp GF :=
  match M with
  | .on γa => iprop((∃ (i : Nat) (st : auth.AuthState), auth.authStateAt γa i st ∗
      ⌜st.enabled = false⌝) ∨ ⌜ai.isSome = true⌝)
  | _ => iprop(True)

instance authedRes_persistent (M : auth.AuthMode)
    (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    Persistent (authedRes (GF := GF) M ai) := by
  unfold authedRes; cases M <;> infer_instance

/-- Auth disabled (`IsAuthEnabled` answered `false`) passes the authenticated-user check. -/
theorem authedRes_of_disabled (M : auth.AuthMode)
    (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    auth.enabledVerdict (GF := GF) M false ⊢ authedRes M ai := by
  cases M
  · unfold authedRes; iintro -; itrivial
  · unfold authedRes; iintro -; itrivial
  · unfold auth.enabledVerdict authedRes
    iintro ⟨%i, %st, #Hst, %Hb⟩
    ileft
    iexists i, st
    iframe #
    ipureintro
    exact Hb.symm

/-- An auth info passes the authenticated-user check. -/
theorem authedRes_some (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    ⊢ authedRes (GF := GF) M (some info) := by
  cases M
  · unfold authedRes; itrivial
  · unfold authedRes; itrivial
  · unfold authedRes; iright; ipureintro; rfl

/-- `IsAuthEnabled` answers `true` only in a mode that may refuse. -/
theorem enabledVerdict_true_isOn (M : auth.AuthMode) :
    auth.enabledVerdict (GF := GF) M true ⊢ ⌜M.isOn = true⌝ := by
  cases M
  · unfold auth.enabledVerdict; iintro %H; cases H
  · iintro -; ipureintro; rfl
  · iintro -; ipureintro; rfl

/-! ## The checks' outcomes -/

/-- **An admin check's outcome** `err` in the mode `M`: an error the apply package's facts
describe, and on `nil` the token for some auth info. -/
def adminOut (M : auth.AuthMode) (err : GoInterface) : IProp GF :=
  iprop(applyErrIs err ∗
    (∀ _ : err = GoInterface.nil, ∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo,
      adminRes M ai))

instance adminOut_persistent (M : auth.AuthMode) (err : GoInterface) :
    Persistent (adminOut (GF := GF) M err) := by
  unfold adminOut; infer_instance

/-- **An authenticated-user check's outcome** `err` in the mode `M`: an error the apply package's
facts describe, never one with auth off, on `nil` the token for some auth info, and on an error
auth enabled at a recorded state. -/
def authedOut (M : auth.AuthMode) (err : GoInterface) : IProp GF :=
  iprop(applyErrIs err ∗ ⌜M.isOn = false → err = GoInterface.nil⌝ ∗
    (∀ _ : err = GoInterface.nil, ∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo,
      authedRes M ai) ∗
    (∀ _ : err ≠ GoInterface.nil, auth.enabledVerdict M true))

instance authedOut_persistent (M : auth.AuthMode) (err : GoInterface) :
    Persistent (authedOut (GF := GF) M err) := by
  unfold authedOut; infer_instance

/-! ## The server's auth fields -/

/-- **`IsAdminPermitted(nil)`** on the store `st` (persistent; the premise the file header
describes): the real method's answer, as `isAuthStore`'s clause for a non-`nil` auth info. -/
def adminNilOk (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ ({{ RD }} (App (Val #(methods ai.ty go!"IsAdminPermitted" ai.v)) (Val #(null : Loc)))
      {{ (err : GoInterface), RET #err; RD ∗ applyErrIs err ∗
          ⌜M.isOn = false → err = GoInterface.nil⌝ ∗ auth.adminVerdict M none err }}))

instance adminNilOk_persistent (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) :
    Persistent (adminNilOk st RD M) := by
  unfold adminNilOk; infer_instance

/-- **The server `s`'s auth fields** (persistent; see the file header). -/
def srvAuthAt (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ (st : GoInterface) (cca : Bool) (P : IProp GF) (f : val),
    structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st E.RD ∗
    □ (⌜E.authMode.isOn = true⌝ → isReqAuthBound st E.RD E.authMode) ∗
    srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗
    apply.isAuthStore st E.γ P f E.RD E.authMode E.RW)

instance srvAuthAt_persistent (s : Loc) (E : apply.AEnv GF) : Persistent (srvAuthAt s E) := by
  unfold srvAuthAt; infer_instance

/-- **`IsAdminPermitted(nil)` on the server `s`'s store** (persistent; the premise). -/
def srvAdminNilOk (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ st : GoInterface, structFieldRef EtcdServer go!"authStore" s ↦□ st ∗
    adminNilOk st E.RD E.authMode)

instance srvAdminNilOk_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvAdminNilOk s E) := by
  unfold srvAdminNilOk; infer_instance

/-- **The premise is the store's contract's last clause** (the auth plan's S3, 2026-10-23: the
real store's spec covers a `nil` auth info, `apply.isAuthStore` states it): `adminNilOk` and
`srvAdminNilOk` are derivable, and the guarded entry points' specs can drop them (a mechanical
follow-up). -/
theorem adminNilOk_of_isAuthStore (st : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF)
    (f : val) (RD : IProp GF) (M : auth.AuthMode) (RW : IProp GF) :
    apply.isAuthStore st γ P f RD M RW ⊢ adminNilOk st RD M := by
  iintro H
  iunfold apply.isAuthStore at H
  icases H with ⟨%ai, %Hai, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    #HNil⟩
  iunfold adminNilOk
  iexists ai
  iframe HNil
  ipureintro; exact Hai

theorem srvAdminNilOk_of_srvAuthAt (s : Loc) (E : apply.AEnv GF) :
    srvAuthAt s E ⊢ srvAdminNilOk s E := by
  iintro H
  iunfold srvAuthAt at H
  icases H with ⟨%st, %cca, %P, %f, #Has, -, -, -, #Hast⟩
  iunfold srvAdminNilOk
  iexists st
  iframe Has
  iapply adminNilOk_of_isAuthStore st E.γ P f E.RD E.authMode E.RW $$ Hast

/-- The server's auth fields, from the proposer's view (the store's request side, the flag) and
the reader's (the store's contract). -/
theorem srvAuthAt_of_views (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServerReq s E ρ ∗ isServerRead s E γr ⊢ srvAuthAt s E := by
  iintro ⟨#Hq, #Hr⟩
  iunfold isServerReq at Hq
  icases Hq with ⟨⟨%vq, Hq⟩, -⟩
  iunfold srvReqFieldsAt at Hq
  icases Hq with ⟨-, -, -, -, -, -, -, -, #Hcca, -, -, #Has, #Hreq, -, -, -, -, -, -, -, -, -, -, -⟩
  iunfold isServerRead at Hr
  icases Hr with ⟨%vr, Hr⟩
  iunfold srvReadFieldsAt at Hr
  icases Hr with ⟨-, -, -, -, -, -, -, -, #Has2, #Hast, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hrb⟩
  icombine Has Has2 gives %Heq
  ihave #Hreq' : isReqAuth vr.auth E.RD $$ []
  · rw [← Heq]; iexact Hreq
  iunfold srvAuthAt
  iexists vr.auth, vq.cca, E.P, E.f
  iframe #

/-! ## The member operations' callees (names only), as contracts

Stated as definitions: `wp_start` rewrites the first `methods` term of the goal with its
`MethodUnfold` instance, and a names-only method has none. -/

/-- **`s.mayRemoveMember(id)`** (the strict reconfiguration check) over the caller's `Pm`,
answering `Qm`. -/
def mayRemoveOk (s : Loc) (id : w64) (Pm : IProp GF) (Qm : GoInterface → IProp GF) : IProp GF :=
  iprop({{ Pm }} (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"mayRemoveMember"))
    (Val #id)) {{ (err : GoInterface), RET #err; Qm err }})

instance mayRemoveOk_persistent (s : Loc) (id : w64) (Pm : IProp GF)
    (Qm : GoInterface → IProp GF) : Persistent (mayRemoveOk s id Pm Qm) := by
  unfold mayRemoveOk; infer_instance

/-- **`s.configure(ctx, &cc)`** for the remove-node change of `id`, guarded: with the token
`adminRes` of the request's auth info, the check's passing `Qm nil` and the change (`cc ↦ ccv`,
its `Type` pointing at `ConfChangeRemoveNode`, its `NodeId` at `id`), over the caller's `Pin`,
answering `Qin`. -/
def configureRemoveOk (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (id : w64)
    (Pin : IProp GF) (Qm : GoInterface → IProp GF) (Qin : GoSlice → GoInterface → IProp GF) :
    IProp GF :=
  iprop(∀ (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) (cc tp np : Loc)
      (ccv : go_etcd_io.raft.v3.raftpb.ConfChange),
    {{ Pin ∗ E.RD ∗ adminRes E.authMode ai ∗ Qm GoInterface.nil ∗ cc ↦ ccv ∗
        ⌜ccv.Type' = tp ∧ ccv.NodeId' = np⌝ ∗
        tp ↦ (W32 1 : go_etcd_io.raft.v3.raftpb.ConfChangeType) ∗ np ↦ id }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"configure"))
        (Val #(GoInterface.ok ctx))) (Val #cc))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); E.RD ∗ Qin sl err }})

instance configureRemoveOk_persistent (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk)
    (id : w64) (Pin : IProp GF) (Qm : GoInterface → IProp GF)
    (Qin : GoSlice → GoInterface → IProp GF) :
    Persistent (configureRemoveOk s E ctx id Pin Qm Qin) := by
  unfold configureRemoveOk; infer_instance

/-! ## Facts the guards' proofs share -/

/-- An auth info's fields (`authInfoIs`) are its struct points-to, read-only
(`EtcdServer__doSerialize.lean`'s `authInfoIs_ptsto`). -/
theorem authInfoIs_pointsto (a : Loc) (user : GoString) (rev : w64) :
    authInfoIs (GF := GF) a user rev ⊢
      a ↦□ ({ Username' := user, Revision' := rev } : go_etcd_io.etcd.server.v3.auth.AuthInfo) := by
  iunfold authInfoIs
  iintro ⟨%Hn, #Hu, #Hr⟩
  rw [typedPointsto_unseal_eq a]
  isplitl
  · simp only [typedPointstoDef]
    iframe Hu Hr
  · ipureintro; exact Hn

/-- An `auth` error variable (`authErrVar`) in the apply package's shape (`errVarLeaf`;
`v3rpc/BaseWatch.lean`'s `errVarLeaf_of_authErrVar`, which the server package cannot import). -/
theorem errVarLeaf_authErrVar (g : GoString) :
    go_etcd_io.etcd.server.v3.auth.authErrVar (GF := GF) g ⊢ errVarLeaf g := by
  unfold go_etcd_io.etcd.server.v3.auth.authErrVar errVarLeaf errLeaf errMsgOk
  iintro ⟨%e, #He, %Hl, #Hm⟩
  iexists e
  iframe He Hm
  ipureintro; exact Hl

end defs

end EtcdGrove
end Perennial
