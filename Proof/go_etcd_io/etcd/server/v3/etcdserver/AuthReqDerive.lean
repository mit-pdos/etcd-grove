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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthDerive
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthInfoFromTLS

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

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

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The server's `isReqAuth`, of the real store** at `st` (`auth.authInv st R`), with the
reader resource `auth.authRd st R` (its `enabledMu` slot is what `AuthInfoFromCtx` uses; see the
file header). -/
theorem isReqAuth_of_authInv
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hTLS : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      isReqAuth (auth.authIface st) (auth.authRd st R M) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold isReqAuth
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %ctx %cd %Φ !> ⟨-, Hrd⟩ HΦ
    iunfold auth.authRd at Hrd
    icases Hrd with ⟨Hen, Hca, HR⟩
    iapply (hCtx st R M (GoInterface.ok ctx)) $$ [Hen]
    · iframe; iframe #
    iintro !> %a %err ⟨Hen, #Ha, #Herr, -⟩
    iapply HΦ
    isplitl [Hen Hca HR]
    · iunfold auth.authRd; iframe
    isplitr
    · iapply authInfoRO_authInfoOpt a $$ Ha
    iapply EtcdGrove.apply.authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  · iintro !> %ctx %cd %Φ !> - HΦ
    iapply (hTLS st R M (GoInterface.ok ctx)) $$ []
    · iframe #
    iintro !> %a #Ha
    iapply HΦ
    iapply authInfoRO_authInfoOpt a $$ Ha

/-- **The request side with the token binding** (persistent; the auth plan's S5, 2026-10-24):
`isReqAuth`'s `AuthInfoFromCtx`, whose auth info is moreover bound to the context's own token in
the mode `M` (`auth.ctxBound`: the token `auth.ctxTokenOf ctx` its metadata carries, the auth plan's
E2c; in `on γa`, its user is one the token was issued to). Stated beside
`isReqAuth` (which the request path's and `NewAuthStore`'s statements name) rather than in it. -/
def isReqAuthBound (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      {{ mvcc.txnCtx ctx cd ∗ RD }}
        (App (Val #(methods ai.ty go!"AuthInfoFromCtx" ai.v)) (Val #(GoInterface.ok ctx)))
      {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗
          applyErrIs err ∗ auth.ctxBound M (GoInterface.ok ctx) a }}))

instance isReqAuthBound_persistent (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) :
    Persistent (isReqAuthBound (GF := GF) st RD M) := by
  unfold isReqAuthBound; infer_instance

/-- **The request side with the binding, of the real store** at `st` (`auth.authInv st R M`). -/
theorem isReqAuthBound_of_authInv
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ⊢
      isReqAuthBound (auth.authIface st) (auth.authRd st R M) M := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold isReqAuthBound
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  iintro !> %ctx %cd %Φ !> ⟨-, Hrd⟩ HΦ
  iunfold auth.authRd at Hrd
  icases Hrd with ⟨Hen, Hca, HR⟩
  iapply (hCtx st R M (GoInterface.ok ctx)) $$ [Hen]
  · iframe; iframe #
  iintro !> %a %err ⟨Hen, #Ha, #Herr, #Hb⟩
  iapply HΦ
  isplitl [Hen Hca HR]
  · iunfold auth.authRd; iframe
  isplitr
  · iapply authInfoRO_authInfoOpt a $$ Ha
  isplitr
  · iapply EtcdGrove.apply.authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  iexact Hb

/-- `isReqAuthBound` gives `isReqAuth`'s `AuthInfoFromCtx` clause (the binding dropped). -/
theorem isReqAuthBound_ctx (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) :
    isReqAuthBound (GF := GF) st RD M ⊢ ∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
      □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
        {{ mvcc.txnCtx ctx cd ∗ RD }}
          (App (Val #(methods ai.ty go!"AuthInfoFromCtx" ai.v)) (Val #(GoInterface.ok ctx)))
        {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗
            applyErrIs err }}) := by
  iunfold isReqAuthBound
  iintro ⟨%ai, %Hai, #H⟩
  iexists ai
  isplitr
  · ipureintro; exact Hai
  iintro !> %ctx %cd %Φ !> Hpre HΦ
  iapply H $$ %ctx %cd [$Hpre]
  iintro !> %a %err ⟨HRD, Ha, Herr, -⟩
  iapply HΦ
  iframe HRD Ha Herr

end proof

end EtcdGrove
end Perennial
