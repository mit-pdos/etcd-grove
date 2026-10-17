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
`auth.authStore.AuthInfoFromTLS.spec`). Since PR etcd#22259 the method's spec asks of the
context that it answer `Value(ClientIPContextKey{})` (`auth.ctxClientIPOk`), which the clause's
`mvcc.txnCtx` does not say: assumed, `auth.ctxClientIPOk_of_txnCtx` (`ClientIPCtx.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthDerive
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthInfoFromTLS
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ClientIPCtx

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
    (st : Loc) (R : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R ⊢
      isReqAuth (auth.authIface st) (auth.authRd st R) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold isReqAuth
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %ctx %cd %Φ !> ⟨#Htc, Hrd⟩ HΦ
    ihave #Hip := auth.ctxClientIPOk_of_txnCtx ctx cd $$ Htc
    iunfold auth.authRd at Hrd
    icases Hrd with ⟨Hen, Hca, HR⟩
    iapply (hCtx st R (GoInterface.ok ctx)) $$ [Hen]
    · iframe; iframe #
    iintro !> %a %err ⟨Hen, #Ha, #Herr⟩
    iapply HΦ
    isplitl [Hen Hca HR]
    · iunfold auth.authRd; iframe
    isplitr
    · iapply authInfoRO_authInfoOpt a $$ Ha
    iapply EtcdGrove.apply.authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  · iintro !> %ctx %cd %Φ !> #Htc HΦ
    ihave #Hip := auth.ctxClientIPOk_of_txnCtx ctx cd $$ Htc
    iapply (hTLS st R (GoInterface.ok ctx)) $$ []
    · iframe #
    iintro !> %a #Ha
    iapply HΦ
    iapply authInfoRO_authInfoOpt a $$ Ha

end proof

end EtcdGrove
end Perennial
