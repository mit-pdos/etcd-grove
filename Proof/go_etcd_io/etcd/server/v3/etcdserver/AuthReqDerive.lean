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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthDerive
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthInfoFromCtx
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

/-- **An auth info is the caller's** (persistent; `infoBoundM`'s over the token: E3zb): its user
the empty one or the one the caller's token `tok` was issued to, or the server's TLS fallback is
on. (Moved from `v3rpc/ServerKVOn.lean` in G2, 2026-10-30, for the watch stream's vocabulary.) -/
def v3rpc.infoBoundT (s : Loc) (M : auth.AuthMode) (tok : Option GoString)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) : IProp GF :=
  iprop(⌜info.Username' = (zeroValDef : GoString)⌝ ∨
    ((∃ token : GoString, ⌜tok = some token⌝ ∗ auth.tokOk M token info.Username') ∨ srvTLSId s))

instance v3rpc.infoBoundT_persistent (s : Loc) (M : auth.AuthMode) (tok : Option GoString)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    Persistent (v3rpc.infoBoundT (GF := GF) s M tok info) := by
  unfold v3rpc.infoBoundT; infer_instance

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
def ctxBoundOrTLS (s : Loc) (M : auth.AuthMode) (ctx : GoInterface) (a : Loc) : IProp GF :=
  iprop(auth.ctxBound M ctx a ∨ srvTLSId s)

instance ctxBoundOrTLS_persistent (s : Loc) (M : auth.AuthMode) (ctx : GoInterface) (a : Loc) :
    Persistent (ctxBoundOrTLS (GF := GF) s M ctx a) := by
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

/-- **The store's `AuthInfoFromCtx` in the mode `M`**: `isReqAuth`'s, and with auth on, over the
bound request side (`isReqAuthBound`), the auth info bound to the context's token (`auth.ctxBound`). -/
theorem isReqAuth_ctxM (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) (ai : GoInterfaceOk)
    (hai : st = GoInterface.ok ai) :
    isReqAuth (GF := GF) st RD ∗ □ (⌜M.isOn = true⌝ → isReqAuthBound st RD M) ⊢
      □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
        {{ mvcc.txnCtx ctx cd ∗ RD }}
          (App (Val #(methods ai.ty go!"AuthInfoFromCtx" ai.v)) (Val #(GoInterface.ok ctx)))
        {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗
            applyErrIs err ∗ □ (⌜M.isOn = true⌝ → auth.ctxBound M (GoInterface.ok ctx) a) }}) := by
  iintro ⟨#Ha, #Hb⟩
  cases hon : M.isOn
  · iunfold isReqAuth at Ha
    icases Ha with ⟨%ai1, %Hai1, #H, -⟩
    have h1 : ai1 = ai := GoInterface.ok.inj (Hai1.symm.trans hai)
    subst h1
    iintro !> %ctx %cd %Φ !> Hpre HΦ
    iapply H $$ %ctx %cd [$Hpre]
    iintro !> %a %err ⟨HRD, Hai, Herr⟩
    iapply HΦ
    iframe HRD Hai Herr
    iintro !> %h
    cases h
  · ihave #Hb' : isReqAuthBound st RD M $$ []
    · iapply Hb; ipureintro; rfl
    iunfold isReqAuthBound at Hb'
    icases Hb' with ⟨%ai1, %Hai1, #H⟩
    have h1 : ai1 = ai := GoInterface.ok.inj (Hai1.symm.trans hai)
    subst h1
    iintro !> %ctx %cd %Φ !> Hpre HΦ
    iapply H $$ %ctx %cd [$Hpre]
    iintro !> %a %err ⟨HRD, Hai, Herr, #Hbd⟩
    iapply HΦ
    iframe HRD Hai Herr
    iintro !> -
    iexact Hbd

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

end proof

end EtcdGrove
end Perennial
