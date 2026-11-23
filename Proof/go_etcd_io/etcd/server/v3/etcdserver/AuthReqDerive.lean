/-
The server's auth-store request-side contract (`isReqAuth`) of the real auth store, from the auth
store's proofs (2026-10-14, unit P2; restated for the server's contract in unit A2). Lean-first
(no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` and
`apply/AuthDerive.lean`.

`isReqAuth st RD`'s `AuthInfoFromCtx` clause takes the caller's reader resource `RD`: the real
method calls `IsAuthEnabled`, which read-locks `enabledMu` (a reader slot: Perennial bounds an
`RWMutex`'s readers). `isReqAuth_of_authInv` derives it of the real store with
`RD := auth.authRd st R` (the apply package's `isAuthStore` reader resource, of which the method
uses the `enabledMu` slot, `auth.enabledRd st`), so that one resource serves both contracts. Its
`AuthInfoFromTLS` clause is the method's (at the trust boundary:
`auth.authStore.AuthInfoFromTLS.spec`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthnStore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthDerive
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthInfoFromCtx
public import Proof.go_etcd_io.etcd.server.v3.auth.FreshAdmin
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthInfoFromTLS
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__CheckPassword
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__GenTokenPrefix
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthSteps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The auth store's auth info is the request path's. -/
theorem authInfoRO_authInfoOpt (a : Loc) : auth.authInfoRO (GF := GF) a ⊢ authInfoOpt a := by
  iintro Ha
  iunfold auth.authInfoRO at Ha
  iunfold authInfoOpt
  icases Ha with (%Hn | ⟨%user, %rev, %Hnn, #Hu, #Hr⟩)
  · ileft; ipureintro; exact Hn
  · iright; iexists user, rev
    iunfold authInfoIs
    iframe Hu Hr
    ipureintro; exact Hnn

/-- **The TLS fallback is on** at the server `s` (persistent): its config's
`ClientCertAuthEnabled` is `true`. -/
def srvTLSId (s : Loc) : IProp GF := iprop(srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ true)

instance srvTLSId_persistent (s : Loc) : Persistent (srvTLSId (GF := GF) s) := by
  unfold srvTLSId; infer_instance

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **An auth info is the caller's** (persistent; `infoBoundM`'s over the token: E3zb): its user
the empty one or the one the caller's token `tok` was issued to, or the TLS fact `T` (the server's
`srvTLSId s`: its TLS fallback is on; a parameter since O2, 2026-11-23, so that a service table can
state it without the server's heap). (Moved from `v3rpc/ServerKVOn.lean` in G2, 2026-10-30, for the
watch stream's vocabulary.) -/
def v3rpc.infoBoundT (T : IProp GF) (M : auth.AuthMode) (tok : Option GoString)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) : IProp GF :=
  iprop(⌜info.Username' = (zeroValDef : GoString)⌝ ∨
    ((∃ token : GoString, ⌜tok = some token⌝ ∗ auth.tokOk M token info.Username') ∨ T))

instance v3rpc.infoBoundT_persistent (T : IProp GF) [Persistent T] (M : auth.AuthMode) (tok : Option GoString)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    Persistent (v3rpc.infoBoundT (GF := GF) T M tok info) := by
  unfold v3rpc.infoBoundT; infer_instance

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


open Iris.ProofMode in
/-- The TLS fallback is off at a server whose config says so (a law for clients of `hdrBoundM`). -/
theorem srvTLSId_false (s : Loc) :
    srvTLSId (GF := GF) s ∗ srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ false ⊢ False := by
  unfold srvTLSId
  iintro ⟨#H1, #H2⟩
  icombine H1 H2 gives %h
  cases h

/-- **The server's auth info `a` for the request context `ctx` is bound** in the mode `M`
(persistent): bound to the context's own token (`auth.ctxBound`, which includes `nil`; the auth
plan's E2c), or the server's TLS fallback is on. -/
def ctxBoundOrTLS (s : Loc) (M : auth.AuthMode) (tok : Option GoString) (a : Loc) : IProp GF :=
  iprop(auth.ctxBound M tok a ∨ srvTLSId s)

instance ctxBoundOrTLS_persistent (s : Loc) (M : auth.AuthMode) (tok : Option GoString) (a : Loc) :
    Persistent (ctxBoundOrTLS (GF := GF) s M tok a) := by
  unfold ctxBoundOrTLS; infer_instance

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The server's `isReqAuth`, of the real store** at `st` (`auth.authInv st R`), with the
reader resource `auth.authRd st R` (its `enabledMu` slot is what `AuthInfoFromCtx` uses; see the
file header), once the token provider is ready (`auth.tpReady M`: the server's `start` fires it;
auth-schema-fix S1 option A, 2026-11-12). -/
theorem isReqAuth_of_authInv
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hTLS : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      □ (auth.tpReady M -∗ isReqAuth (auth.authIface st) (auth.authRd st R M)) := by
  iintro ⟨#Hpkg, #Hinv⟩ !> #Hrdy
  iunfold isReqAuth
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %ctx %Φ !> ⟨#Hlib, #Hda, Hrd⟩ HΦ
    ihave #Hdr := auth.ctxDoneRecv_of_ctxDoneAny ctx $$ Hda
    iunfold context.libCtxOk at Hlib
    icases Hlib with ⟨#Hinc, -, -, -⟩
    iunfold metadata.incomingCtxOk at Hinc
    icases Hinc with ⟨%md, #Hmd⟩
    iunfold auth.authRd at Hrd
    icases Hrd with ⟨Hen, Hca, HR⟩
    imod (authPubLbM_zero (GF := GF) M) with #Hlb0
    iapply (hCtx st R M 0 ctx (auth.mdTokenOf md)) $$ [Hen]
    · iframe; iframe #
      iintro !> %_
      iapply auth.ctxToken_of_ctxInMD ctx md $$ Hmd
    iintro !> %a %err ⟨Hen, #Ha, #Herr, -, -, -, -⟩
    iapply HΦ
    isplitl [Hen Hca HR]
    · iunfold auth.authRd; iframe
    isplitr
    · iapply authInfoRO_authInfoOpt a $$ Ha
    iapply EtcdGrove.apply.authErrIs_authApplyErrIs err $$ [$Hpkg $Herr]
  · iintro !> %ctx %Φ !> ⟨#Hlib, -⟩ HΦ
    iunfold context.libCtxOk at Hlib
    icases Hlib with ⟨#Hinc, -, #Hpeer, -⟩
    iapply (hTLS st R M ctx) $$ []
    · iframe #
    iintro !> %a #Ha
    iapply HΦ
    iapply authInfoRO_authInfoOpt a $$ Ha

/-- **The request side with the binding, of the real store** at `st` (`auth.authInv st R M`), once
the token provider is ready (`auth.tpReady M`). -/
theorem isReqAuthBound_of_authInv
    (hEnLb : auth.authStore.IsAuthEnabled.specLb (GF := GF))
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAdminLbO : auth.authStore.IsAdminPermitted.specLbO (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      □ (auth.tpReady M -∗ isReqAuthBound (auth.authIface st) (auth.authRd st R M) M) := by
  iintro ⟨#Hpkg, #Hinv⟩ !> #Hrdy
  iunfold isReqAuthBound
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  -- (auth-guard-completeness G1) the guards' calls at a lower bound
  isplitr
  · iintro !> %n %Φ !> ⟨#Hlb, Hrd⟩ HΦ
    iunfold auth.authRd at Hrd
    icases Hrd with ⟨Hen, Hca, HR⟩
    iapply (hEnLb st R M n) $$ [Hen]
    · iframe; iframe #
    iintro !> %b ⟨Hen, #Hv⟩
    iapply HΦ
    iframe Hv
    iunfold auth.authRd; iframe
  isplitr
  · iintro !> %n %ctx %tok %Φ !> ⟨#Hlb, -, #Htok, #Hda, Hrd⟩ HΦ
    ihave #Hdr := auth.ctxDoneRecv_of_ctxDoneAny ctx $$ Hda
    iunfold auth.authRd at Hrd
    icases Hrd with ⟨Hen, Hca, HR⟩
    iapply (hCtx st R M n ctx tok) $$ [Hen]
    · iframe; iframe #
    iintro !> %a %err ⟨Hen, #Ha, #Herr, #Hb, #Hz, #Hne, #Hnn⟩
    iapply HΦ
    isplitl [Hen Hca HR]
    · iunfold auth.authRd; iframe
    isplitr
    · iapply authInfoRO_authInfoOpt a $$ Ha
    isplitr
    · iapply EtcdGrove.apply.authErrIs_authApplyErrIs err $$ [$Hpkg $Herr]
    iframe Hb Hz Hne Hnn
  · iintro !> %n %a %oinfo %dq %Φ !> ⟨#Hlb, Ha, Hrd⟩ HΦ
    iapply (hAdminLbO st R M n a oinfo dq) $$ [Ha Hrd]
    · iframe; iframe #
    iintro !> %err ⟨Hrd, Ha, #Herr, #Hv⟩
    iapply HΦ
    iframe Hrd Ha Hv
    iapply EtcdGrove.apply.authErrIs_authApplyErrIs err $$ [$Hpkg $Herr]


/-! ### The bound request side's rows at a lower bound (auth-guard-completeness G2) -/

/-- `IsAuthEnabled`'s row: the flag at a state no older than the caller's lower bound. -/
theorem isReqAuthBound_enLb (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode)
    (ai : GoInterfaceOk) (hai : st = GoInterface.ok ai) :
    isReqAuthBound (GF := GF) st RD M ⊢
      □ (∀ n : Nat,
        {{ auth.authPubLbM M n ∗ RD }} (App (Val #(methods ai.ty go!"IsAuthEnabled" ai.v)) (Val #()))
        {{ (b : Bool), RET #b; RD ∗ auth.enabledVerdictFrom M n b }}) := by
  iunfold isReqAuthBound
  iintro ⟨%ai1, %Hai1, #H, -, -⟩
  have h1 : ai1 = ai := GoInterface.ok.inj (Hai1.symm.trans hai)
  subst h1
  iexact H

/-- `AuthInfoFromCtx`'s row: the request side's reasons at the caller's lower bound. -/
theorem isReqAuthBound_ctxLb (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode)
    (ai : GoInterfaceOk) (hai : st = GoInterface.ok ai) :
    isReqAuthBound (GF := GF) st RD M ⊢
      □ (∀ (n : Nat) (ctx : GoInterfaceOk) (tok : Option GoString),
        {{ auth.authPubLbM M n ∗ context.libCtxOk ctx ∗
            □ (⌜M.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗ auth.ctxDoneAny ctx ∗ RD }}
          (App (Val #(methods ai.ty go!"AuthInfoFromCtx" ai.v)) (Val #(GoInterface.ok ctx)))
        {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗
            authApplyErrIs err ∗ auth.ctxBound M tok a ∗
            (∀ _ : a = null ∧ err = GoInterface.nil, auth.noPrincipalFrom M n tok) ∗
            (∀ _ : err ≠ GoInterface.nil, auth.authErrOf .invalidAuthToken err ∗
              auth.enabledVerdictFrom M n true ∗ auth.tokRefusedFrom M n tok) ∗
            (∀ _ : a ≠ null, auth.enabledVerdictFrom M n true) }}) := by
  iunfold isReqAuthBound
  iintro ⟨%ai1, %Hai1, -, #H, -⟩
  have h1 : ai1 = ai := GoInterface.ok.inj (Hai1.symm.trans hai)
  subst h1
  iexact H

/-- `IsAdminPermitted`'s row: both halves of its verdict at the caller's lower bound. -/
theorem isReqAuthBound_adminLb (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode)
    (ai : GoInterfaceOk) (hai : st = GoInterface.ok ai) :
    isReqAuthBound (GF := GF) st RD M ⊢
      □ (∀ (n : Nat) (a : Loc) (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
        {{ auth.authPubLbM M n ∗ auth.authInfoAt a dq oinfo ∗ RD }}
          (App (Val #(methods ai.ty go!"IsAdminPermitted" ai.v)) (Val #a))
        {{ (err : GoInterface), RET #err; RD ∗ auth.authInfoAt a dq oinfo ∗ authApplyErrIs err ∗
            auth.adminVerdictFromO M n oinfo err }}) := by
  iunfold isReqAuthBound
  iintro ⟨%ai1, %Hai1, -, -, #H⟩
  have h1 : ai1 = ai := GoInterface.ok.inj (Hai1.symm.trans hai)
  subst h1
  iexact H

/-- **The store's `AuthInfoFromCtx` in the mode `M`, read with a lower bound `n`**
(auth-guard-completeness G1): the store's request side (`isReqAuth`), and with auth on, over the bound request
side's row at `n`, why it gave no principal (`auth.noPrincipalFrom`) or an error
(`ErrInvalidAuthToken`, for a token the context carries: `auth.tokRefusedFrom`). -/
theorem isReqAuth_ctxMLb (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) (ai : GoInterfaceOk)
    (hai : st = GoInterface.ok ai) (n : Nat) :
    isReqAuth (GF := GF) st RD ∗ □ (⌜M.isOn = true⌝ → isReqAuthBound st RD M) ∗
      □ auth.authPubLbM M n ⊢
      □ (∀ (ctx : GoInterfaceOk) (tok : Option GoString),
        {{ auth.ctxDoneAny ctx ∗ context.libCtxOk ctx ∗
            □ (⌜M.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗ RD }}
          (App (Val #(methods ai.ty go!"AuthInfoFromCtx" ai.v)) (Val #(GoInterface.ok ctx)))
        {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗
            authApplyErrIs err ∗ □ (⌜M.isOn = true⌝ → auth.ctxBound M tok a) ∗
            □ (⌜M.isOn = true⌝ → authErrVarIs err) ∗
            □ (⌜M.isOn = true⌝ → ∀ _ : a = null ∧ err = GoInterface.nil,
              auth.noPrincipalFrom M n tok) ∗
            □ (⌜M.isOn = true⌝ → ∀ _ : err ≠ GoInterface.nil,
              auth.authErrOf .invalidAuthToken err ∗ auth.enabledVerdictFrom M n true ∗
                auth.tokRefusedFrom M n tok) ∗
            □ (⌜M.isOn = true⌝ → ∀ _ : a ≠ null, auth.enabledVerdictFrom M n true) }}) := by
  iintro ⟨#Ha, #Hb, #Hlb⟩
  cases hon : M.isOn
  · iunfold isReqAuth at Ha
    icases Ha with ⟨%ai1, %Hai1, #H, -⟩
    have h1 : ai1 = ai := GoInterface.ok.inj (Hai1.symm.trans hai)
    subst h1
    iintro !> %ctx %tok %Φ !> ⟨#Hda, #Hlib, -, Hrd⟩ HΦ
    iapply H $$ %ctx [Hrd]
    · iframe; iframe #
    iintro !> %a %err ⟨HRD, Hai, Herr⟩
    iapply HΦ
    iframe HRD Hai Herr
    isplitl
    · iintro !> %h; cases h
    isplitl
    · iintro !> %h; cases h
    isplitl
    · iintro !> %h; cases h
    isplitl
    · iintro !> %h; cases h
    · iintro !> %h; cases h
  · ihave #Hb' : isReqAuthBound st RD M $$ []
    · iapply Hb; ipureintro; rfl
    ihave #H := isReqAuthBound_ctxLb st RD M ai hai $$ Hb'
    iintro !> %ctx %tok %Φ !> ⟨#Hda, #Hlib, #Htok, Hrd⟩ HΦ
    iapply H $$ %n %ctx %tok [Hrd]
    · iframe; iframe #
      iintro !> -; iapply Htok; ipureintro; rfl
    iintro !> %a %err ⟨HRD, Hai, #Herr, #Hbd, #Hz, #Hne, #Hnn⟩
    iapply HΦ
    iframe HRD Hai
    isplitr
    · iexact Herr
    iunfold authApplyErrIs at Herr
    icases Herr with ⟨-, #Hv⟩
    isplitl
    · iintro !> -; iexact Hbd
    isplitl
    · iintro !> -; iexact Hv
    isplitl
    · iintro !> -; iexact Hz
    isplitl
    · iintro !> -; iexact Hne
    · iintro !> -; iexact Hnn

/-- **The store's `IsAuthEnabled` in the mode `M`, read with a lower bound `n`**
(auth-guard-completeness G2): the store contract's verdict (`enabledVerdict`), and with auth on, over
the bound request side's row at `n`, the flag at a state no older than `n`. -/
theorem isAuthEnabled_ctxMLb (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode)
    (ai : GoInterfaceOk) (hai : st = GoInterface.ok ai) (n : Nat) :
    □ ({{ RD }} (App (Val #(methods ai.ty go!"IsAuthEnabled" ai.v)) (Val #()))
        {{ (b : Bool), RET #b; RD ∗ auth.enabledVerdict M b }}) ∗
      □ (⌜M.isOn = true⌝ → isReqAuthBound (GF := GF) st RD M) ∗ □ auth.authPubLbM M n ⊢
      □ ({{ RD }} (App (Val #(methods ai.ty go!"IsAuthEnabled" ai.v)) (Val #()))
        {{ (b : Bool), RET #b; RD ∗ auth.enabledVerdict M b ∗
            □ (⌜M.isOn = true⌝ → auth.enabledVerdictFrom M n b) }}) := by
  iintro ⟨#HEn, #Hb, #Hlb⟩
  rcases (Bool.eq_false_or_eq_true M.isOn).symm with hon | hon
  · iintro !> %Φ !> Hrd HΦ
    iapply HEn $$ Hrd
    iintro !> %b ⟨Hrd, #Hv⟩
    iapply HΦ
    iframe Hrd Hv
    iintro !> %h; rw [hon] at h; cases h
  · ihave #Hb' : isReqAuthBound st RD M $$ []
    · iapply Hb; ipureintro; exact hon
    ihave #H := isReqAuthBound_enLb st RD M ai hai $$ Hb'
    iintro !> %Φ !> Hrd HΦ
    iapply H $$ %n [Hrd]
    · iframe; iframe #
    iintro !> %b ⟨Hrd, #Hv⟩
    iapply HΦ
    iframe Hrd
    isplitr
    · iapply auth.enabledVerdictFrom_verdict M n b $$ Hv
    · iintro !> -; iexact Hv

/-- **The store's `Authenticate` side, of the real store** at `st` (`auth.authInv st R M`; C1's
A4): `CheckPassword` over the reader resource (its error one of the package's, `authErrOf`),
`GenTokenPrefix` (the provider's), `Revision`. -/
theorem authnStoreOk_of_authInv
    (hCP : auth.authStore.CheckPassword.spec (GF := GF) (hG := hG))
    (hGT : auth.authStore.GenTokenPrefix.spec (GF := GF) (hG := hG))
    (hRev : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      authnStoreOk (auth.authIface st) (auth.authRd st R M) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold authnStoreOk
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %name %pw %Φ !> Hrd HΦ
    iunfold auth.authRd at Hrd
    icases Hrd with ⟨Hen, Hca, Hbe, HR⟩
    iapply (hCP st R M name pw) $$ [Hen Hbe HR]
    · iframe; iframe #
    iintro !> %rev %err ⟨Hen, Hbe, HR, Hck⟩
    iapply HΦ
    isplitl [Hen Hca Hbe HR]
    · iunfold auth.authRd; iframe
    iunfold auth.passwordChecked at Hck
    icases Hck with (⟨-, %e, #He⟩ | ⟨%He, -⟩)
    · iapply EtcdGrove.apply.authErrOf_applyErrIs e err $$ [$Hpkg $He]
    · subst He; iapply applyErrIs_nil
  isplitr
  · iintro !> %Φ !> - HΦ
    iapply (hGT st R M) $$ []
    · iframe #
    iintro !> %s %err %H
    iapply HΦ; ipureintro; exact H
  · iintro !> %Φ !> - HΦ
    iapply (hRev st R M none) $$ []
    · iframe #; simp only [auth.authOwnOpt_none]; itrivial
    iintro !> %x -
    iapply HΦ; itrivial

section monoT
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-! ### O2: the TLS fact as a parameter (2026-11-23)

The client-facing auth vocabulary takes the TLS fallback as a parameter `T : IProp GF` (the server
passes `srvTLSId s`, a service table `⌜tls = true⌝`); `srvTLSId_iff` bridges the two at the server's
config, and each definition has a one-way monotonicity law in `T` (`…_mono`). -/

open Iris.ProofMode in
/-- **The TLS fallback is the config's flag** (O2's bridge): at a server whose config's
`ClientCertAuthEnabled` is `tls`, `srvTLSId s` holds exactly when `tls` is `true`. -/
theorem srvTLSId_iff (s : Loc) (tls : Bool) :
    srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ tls ⊢
      (srvTLSId (GF := GF) s ∗-∗ ⌜tls = true⌝) := by
  iintro #Hc
  isplit
  · iintro #H
    iunfold srvTLSId at H
    icombine H Hc gives %h
    ipureintro
    cases tls
    · cases h
    · rfl
  · iintro %h
    subst h
    unfold srvTLSId
    iexact Hc

open Iris.ProofMode in
/-- `infoBoundT` is monotone in the TLS fact. -/
theorem v3rpc.infoBoundT_mono (T1 T2 : IProp GF) (M : auth.AuthMode) (tok : Option GoString)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    iprop(□ (T1 -∗ T2)) ∗ v3rpc.infoBoundT T1 M tok info ⊢ v3rpc.infoBoundT T2 M tok info := by
  unfold v3rpc.infoBoundT
  iintro ⟨#HT, H⟩
  icases H with (H | (H | H))
  · ileft; iexact H
  · iright; ileft; iexact H
  · iright; iright; iapply HT $$ H

end monoT

end proof

end EtcdGrove
end Perennial
