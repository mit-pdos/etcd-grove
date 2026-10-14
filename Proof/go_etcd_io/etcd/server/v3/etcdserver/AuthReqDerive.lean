/-
The server's auth-store request-side contract (`isReqAuth`) of the real auth store, from the auth
store's proofs (2026-10-14, unit P2). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` and `apply/AuthDerive.lean`.

`isReqAuth`'s `AuthInfoFromCtx` clause takes no resource, but the real method calls
`IsAuthEnabled`, which read-locks `enabledMu` (a reader slot: Perennial bounds an `RWMutex`'s
readers): not derivable as stated. `isReqAuthR st RD` is `isReqAuth` with the caller's reader
resource `RD` in that clause; `isReqAuthR_of_authInv` derives it of the real store with
`RD := auth.enabledRd st`. Its `AuthInfoFromTLS` clause is `isReqAuth`'s (the method is at the
trust boundary: `auth.authStore.AuthInfoFromTLS.spec`).
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

/-- **`isReqAuth` with a reader resource** `RD` for `AuthInfoFromCtx` (see the file header). -/
def isReqAuthR (st : GoInterface) (RD : IProp GF) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      {{ mvcc.txnCtx ctx cd ∗ RD }}
        (App (Val #(methods ai.ty go!"AuthInfoFromCtx" ai.v)) (Val #(GoInterface.ok ctx)))
      {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗
          applyErrIs err }}) ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      {{ mvcc.txnCtx ctx cd }}
        (App (Val #(methods ai.ty go!"AuthInfoFromTLS" ai.v)) (Val #(GoInterface.ok ctx)))
      {{ (a : Loc), RET #a; authInfoOpt a }}))

instance isReqAuthR_persistent (st : GoInterface) (RD : IProp GF) :
    Persistent (isReqAuthR st RD) := by
  unfold isReqAuthR; infer_instance

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
reader resource `auth.enabledRd st` for `AuthInfoFromCtx` (see the file header). -/
theorem isReqAuthR_of_authInv
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hTLS : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R ⊢
      isReqAuthR (auth.authIface st) (auth.enabledRd st) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold isReqAuthR
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %ctx %cd %Φ !> ⟨-, Hen⟩ HΦ
    iapply (hCtx st R (GoInterface.ok ctx)) $$ [Hen]
    · iframe; iframe #
    iintro !> %a %err ⟨Hen, #Ha, #Herr⟩
    iapply HΦ
    iframe
    isplitr
    · iapply authInfoRO_authInfoOpt a $$ Ha
    iapply EtcdGrove.apply.authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  · iintro !> %ctx %cd %Φ !> - HΦ
    iapply (hTLS st R (GoInterface.ok ctx)) $$ []
    · iframe #
    iintro !> %a #Ha
    iapply HΦ
    iapply authInfoRO_authInfoOpt a $$ Ha

end proof

end EtcdGrove
end Perennial
