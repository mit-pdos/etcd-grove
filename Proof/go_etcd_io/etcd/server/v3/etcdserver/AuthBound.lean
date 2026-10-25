/-
**The token binding at the server's guards** (the auth plan's E1, 2026-10-24; `notes/decisions.md`,
"E1 of the auth plan"). Lean-first (no Rocq counterpart).

S5 stated the request side with the binding (`isReqAuthBound`, `AuthReqDerive.lean`: the auth info
`AuthInfoFromCtx` returns is `nil` or one bound to the request's token, `auth.ctxBound`) and derived
it of the real store (`isReqAuthBound_of_authInv`). The server's store comes from `NewAuthStore`'s
axiom, whose post names only the unbound `isReqAuth`, so the server cannot derive the binding of
its own store yet. This file states the guards' bound variants over the bound contract as a
premise (`srvAuthBound`), so that, once `NewAuthStore` is proved, the guards' principals are bound
without restating the guards again:

* `EtcdServer.AuthInfoFromCtx`'s auth info is bound to the request's token, or came from the
  client's TLS certificate (`AuthInfoFromTLS`, only with `ClientCertAuthEnabled`: the server falls
  back to it when the token path gives no auth info), `ctxBoundOrTLS`;
* `checkMembershipOperationPermission` (A2's admin guard of the member operations): on `nil`, the
  admin token of an auth info that is bound (`principalBound`), `adminOutB`.

TLS client certificates as identity are out of the plan's scope (D-AU6): the TLS path is the
disjunct the statement names, not a binding.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthReqDerive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkMembershipOperationPermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthStore
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__requireAuthInfo
@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The server `s`'s store has the bound request side** (persistent): its `authStore` field's
store satisfies `isReqAuthBound` in the server's auth mode. Of the real store once `NewAuthStore`
is proved (`isReqAuthBound_of_authInv`). -/
def srvAuthBound (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ st : GoInterface, structFieldRef EtcdServer go!"authStore" s ↦□ st ∗
    isReqAuthBound st E.RD E.authMode)

instance srvAuthBound_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvAuthBound s E) := by
  unfold srvAuthBound; infer_instance

/-- **The TLS fallback is on** at the server `s` (persistent): its config's
`ClientCertAuthEnabled` is `true`. -/
def srvTLSId (s : Loc) : IProp GF := iprop(srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ true)

instance srvTLSId_persistent (s : Loc) : Persistent (srvTLSId (GF := GF) s) := by
  unfold srvTLSId; infer_instance

/-- **The server's auth info `a` for the request context `ctx` is bound** in the mode `M`
(persistent): bound to the context's own token (`auth.ctxBound`, which includes `nil`; the auth
plan's E2c), or the server's TLS fallback is on. -/
def ctxBoundOrTLS (s : Loc) (M : auth.AuthMode) (ctx : GoInterface) (a : Loc) : IProp GF :=
  iprop(auth.ctxBound M ctx a ∨ srvTLSId s)

instance ctxBoundOrTLS_persistent (s : Loc) (M : auth.AuthMode) (ctx : GoInterface) (a : Loc) :
    Persistent (ctxBoundOrTLS (GF := GF) s M ctx a) := by
  unfold ctxBoundOrTLS; infer_instance

/-- **A checked principal of the request context `ctx` is bound** in the mode `M` (persistent):
`nil`, or the user to whom the context's own token was issued (`auth.ctxTokenOf ctx`, the auth
plan's E2c; `auth.tokOk`: in `on γa`, `tokIssued`), or the server's TLS fallback is on. -/
def principalBound (s : Loc) (M : auth.AuthMode) (ctx : GoInterface)
    (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) : IProp GF :=
  match ai with
  | none => iprop(True)
  | some info => iprop((∃ token : GoString, ⌜auth.ctxTokenOf ctx = some token⌝ ∗
      auth.tokOk M token info.Username') ∨ srvTLSId s)

instance principalBound_persistent (s : Loc) (M : auth.AuthMode) (ctx : GoInterface)
    (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    Persistent (principalBound (GF := GF) s M ctx ai) := by
  unfold principalBound; cases ai <;> infer_instance

/-- **An admin check's outcome with the binding**: `adminOut`, whose auth info is moreover
bound (`principalBound`). -/
def adminOutB (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) : IProp GF :=
  iprop(applyErrIs err ∗
    (∀ _ : err = GoInterface.nil, ∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo,
      adminRes M ai ∗ principalBound s M ctx ai))

instance adminOutB_persistent (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) :
    Persistent (adminOutB (GF := GF) s M ctx err) := by
  unfold adminOutB; infer_instance

/-- `adminOutB` gives `adminOut` (the binding dropped). -/
theorem adminOut_of_adminOutB (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) :
    adminOutB (GF := GF) s M ctx err ⊢ adminOut M err := by
  iunfold adminOutB
  iunfold adminOut
  iintro ⟨#He, #Hn⟩
  iframe #
  iintro %h
  icases Hn $$ %h with ⟨%ai, #Hr, -⟩
  iexists ai
  iexact Hr

instance authInfoIs_persistent' (a : Loc) (user : GoString) (rev : w64) :
    Persistent (authInfoIs (GF := GF) a user rev) := by
  unfold authInfoIs; infer_instance

/-- **An authenticated-user check's outcome with the binding**: `authedOut`, whose auth info is
moreover bound (`principalBound`). -/
def authedOutB (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) : IProp GF :=
  iprop(applyErrIs err ∗ ⌜M.isOn = false → err = GoInterface.nil⌝ ∗
    (∀ _ : err = GoInterface.nil, ∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo,
      authedRes M ai ∗ principalBound s M ctx ai) ∗
    (∀ _ : err ≠ GoInterface.nil, auth.enabledVerdict M true))

instance authedOutB_persistent (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) :
    Persistent (authedOutB (GF := GF) s M ctx err) := by
  unfold authedOutB; infer_instance

/-- `authedOutB` gives `authedOut` (the binding dropped). -/
theorem authedOut_of_authedOutB (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) :
    authedOutB (GF := GF) s M ctx err ⊢ authedOut M err := by
  iunfold authedOutB
  iunfold authedOut
  iintro ⟨#He, #Hoff, #Hn, #Hne⟩
  iframe #
  iintro %h
  icases Hn $$ %h with ⟨%ai, #Hr, -⟩
  iexists ai
  iexact Hr

/-- **A bound auth info's user** is bound: from `ctxBoundOrTLS` and the auth info's fields
(`authInfoIs`), the user's token (or the TLS fallback). -/
theorem principalBound_of_ctxBoundOrTLS (s : Loc) (M : auth.AuthMode) (ctx : GoInterface) (a : Loc)
    (user : GoString) (rev : w64) :
    ctxBoundOrTLS (GF := GF) s M ctx a ∗ authInfoIs a user rev ⊢
      principalBound s M ctx (some ({ Username' := user, Revision' := rev } :
        go_etcd_io.etcd.server.v3.auth.AuthInfo)) := by
  iunfold ctxBoundOrTLS
  iunfold principalBound
  iintro ⟨#Hb, #Hai⟩
  icases Hb with (#Hb | #Ht)
  · iunfold auth.ctxBound at Hb
    icases Hb with (%Hn | ⟨%token, %Htk, #Hib⟩)
    · iunfold authInfoIs at Hai
      icases Hai with ⟨%Hnn, -, -⟩
      exact absurd Hn Hnn
    · iunfold auth.infoBound at Hib
      icases Hib with ⟨-, %user', #Hu', #Htok⟩
      iunfold authInfoIs at Hai
      icases Hai with ⟨-, #Hu, -⟩
      icombine Hu Hu' gives %Heq
      ileft
      iexists token
      isplitr
      · ipureintro; exact Htk
      rw [Heq]
      iexact Htok
  · iright; iexact Ht

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`EtcdServer.AuthInfoFromCtx` with the binding**: `EtcdServer.AuthInfoFromCtx.spec`, over a
store with the bound request side too, whose auth info is moreover bound to the request's token or
came from the TLS fallback (`ctxBoundOrTLS`). -/
abbrev EtcdServer.AuthInfoFromCtx.boundSpec : Prop :=
  ∀ (s : Loc) (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) (cca : Bool)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st RD ∗
      isReqAuthBound st RD M ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ mvcc.txnCtx ctx cd ∗ RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"AuthInfoFromCtx"))
      (Val #(GoInterface.ok ctx)))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗ applyErrIs err ∗
      ctxBoundOrTLS s M (GoInterface.ok ctx) a }}

theorem EtcdServer.AuthInfoFromCtx_bound
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.AuthInfoFromCtx.boundSpec (GF := GF) (hG := hG) := by
  intro s st RD M cca ctx cd
  wp_start as ⟨#Hst, #Hauth, #Hbound, #Hcca, #Hctx, Hrd⟩
  ihave #Hauth' := Hauth
  iunfold isReqAuth at Hauth'
  icases Hauth' with ⟨%ai, %Hai, -, #HFromTLS⟩
  iunfold isReqAuthBound at Hbound
  icases Hbound with ⟨%ai2, %Hai2, #HFromCtx⟩
  have Hai2' : ai = ai2 := GoInterface.ok.inj (Hai.symm.trans Hai2)
  subst Hai2'
  wp_auto
  wp_apply hAS s st $$ []
  · iframe #
  subst Hai
  wp_auto
  wp_apply HFromCtx $$ %ctx %cd [Hrd] as %a %err ⟨Hrd, Ha, Herr, #Hb⟩
  · iframe; iframe #
  wp_if_destruct
  · cases err with
    | ok ei =>
      wp_auto
      iapply HΦ; iframe Hrd Ha Herr
      iunfold ctxBoundOrTLS; ileft; iexact Hb
    | nil =>
      wp_auto
      cases cca
      · wp_auto
        iapply HΦ; iframe Hrd; isplitr
        · iunfold authInfoOpt; ileft; ipureintro; rfl
        isplitr
        · iapply applyErrIs_nil
        iunfold ctxBoundOrTLS; ileft
        iunfold auth.ctxBound; ileft; ipureintro; rfl
      · wp_auto
        wp_apply hAS s _ $$ []
        · iframe #
        iintro -
        wp_auto
        wp_apply HFromTLS $$ %ctx %cd [] as %a' Ha'
        · iframe #
        iapply HΦ; iframe Hrd Ha'; isplitr
        · iapply applyErrIs_nil
        iunfold ctxBoundOrTLS
        iunfold srvTLSId; iright; iexact Hcca
  · iapply HΦ; iframe Hrd Ha Herr
    iunfold ctxBoundOrTLS; ileft; iexact Hb

/-- **`checkMembershipOperationPermission` with the binding** (A2's admin guard of the member
operations): its spec, over a server whose store has the bound request side too
(`srvAuthBound`), whose admin token's auth info is moreover bound (`adminOutB`). -/
abbrev EtcdServer.checkMembershipOperationPermission.boundSpec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ srvAuthBound s E ∗ srvAdminNilOk s E ∗ mvcc.txnCtx ctx cd ∗ E.RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!!
      go!"checkMembershipOperationPermission")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ adminOutB s E.authMode (GoInterface.ok ctx) err }}

theorem EtcdServer.checkMembershipOperationPermission_bound
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.checkMembershipOperationPermission.boundSpec (GF := GF) (hG := hG) := by
  intro s E ctx cd
  wp_start as ⟨#Hau, #Hbd, #Hnil, #Hctx, HRD⟩
  iunfold srvAuthAt at Hau
  icases Hau with ⟨%st, %cca, %P, %f, #Has, #Hreq, #Hcca, #Hast⟩
  iunfold srvAuthBound at Hbd
  icases Hbd with ⟨%st3, #Has3, #Hreqb⟩
  icombine Has Has3 gives %Heq3
  subst Heq3
  iunfold srvAdminNilOk at Hnil
  icases Hnil with ⟨%st2, #Has2, #Hnil⟩
  icombine Has Has2 gives %Heq
  subst Heq
  iunfold apply.isAuthStore at Hast
  icases Hast with ⟨%ai, %Hai, -, -, -, #HAdm, -⟩
  iunfold adminNilOk at Hnil
  icases Hnil with ⟨%ai2, %Hai2, #HAdmNil⟩
  have Hai2' : ai = ai2 := GoInterface.ok.inj (Hai.symm.trans Hai2)
  subst Hai2'
  subst Hai
  (try wp_auto)
  wp_apply (EtcdServer.AuthInfoFromCtx_bound hAS s (GoInterface.ok ai) E.RD E.authMode cca ctx cd)
    $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr, #Hb⟩
  · iframe #
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ
    iframe HRD
    iunfold adminOutB
    iframe #
    iintro %h; cases h
  · (try wp_auto)
    wp_apply (hAS s (GoInterface.ok ai))
    · iframe #
    (try wp_auto)
    iunfold authInfoOpt at Ha
    icases Ha with (%Han | ⟨%user, %rev, Hau⟩)
    · subst Han
      (try wp_auto)
      wp_apply HAdmNil $$ [$HRD] as %err2 ⟨HRD, #Herr2, %Hoff, #Hv⟩
      (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold adminOutB
      iframe #
      iintro %h
      subst h
      iexists none
      isplitl
      · iapply (adminRes_of_adminVerdict _ _) $$ Hv
      iunfold principalBound; itrivial
    · ihave #Hap := authInfoIs_pointsto a user rev $$ Hau
      ihave #Hpb := principalBound_of_ctxBoundOrTLS s E.authMode (GoInterface.ok ctx) a user rev $$ [$Hb $Hau]
      iunfold authInfoIs at Hau
      icases Hau with ⟨%Hann, -, -⟩
      (try wp_auto)
      wp_apply HAdm $$ [$Hap $HRD] as %err2 ⟨-, HRD, #Herr2, %Hoff, #Hv⟩
      (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold adminOutB
      iframe #
      iintro %h
      subst h
      iexists (some _)
      isplitl
      · iapply (adminRes_of_adminVerdict _ _) $$ Hv
      iexact Hpb

/-- **`requireAuthInfo` with the binding** (A2's authenticated-user guard of the server's entry
points): its spec, over a server whose store has the bound request side too, whose passed check's
auth info is moreover bound (`authedOutB`). -/
abbrev EtcdServer.requireAuthInfo.boundSpec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ srvAuthBound s E ∗ mvcc.txnCtx ctx cd ∗ E.RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"requireAuthInfo"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ authedOutB s E.authMode (GoInterface.ok ctx) err }}

theorem EtcdServer.requireAuthInfo_bound
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.requireAuthInfo.boundSpec (GF := GF) (hG := hG) := by
  intro s E ctx cd
  wp_start as ⟨#Hau, #Hbd, #Hctx, HRD⟩
  iunfold srvAuthAt at Hau
  icases Hau with ⟨%st, %cca, %P, %f, #Has, #Hreq, #Hcca, #Hast⟩
  iunfold srvAuthBound at Hbd
  icases Hbd with ⟨%st3, #Has3, #Hreqb⟩
  icombine Has Has3 gives %Heq3
  subst Heq3
  iunfold apply.isAuthStore at Hast
  icases Hast with ⟨%ai, %Hai, -, -, -, -, -, #HEn, -⟩
  subst Hai
  (try wp_auto)
  wp_apply HEn $$ [$HRD] as %b ⟨HRD, #Hb⟩
  (try wp_auto)
  cases b
  · (try wp_auto)
    iapply HΦ
    iframe HRD
    iunfold authedOutB
    isplitr
    · iapply applyErrIs_nil
    isplitr
    · ipureintro; intro _; rfl
    isplitr
    · iintro %_
      iexists none
      isplitl
      · iapply (authedRes_of_disabled E.authMode none) $$ Hb
      iunfold principalBound; itrivial
    · iintro %h; exact absurd rfl h
  · (try wp_auto)
    ihave %Hon := enabledVerdict_true_isOn E.authMode $$ Hb
    wp_apply (EtcdServer.AuthInfoFromCtx_bound hAS s (GoInterface.ok ai) E.RD E.authMode cca ctx cd)
      $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr, #Hbnd⟩
    · iframe #
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold authedOutB
      isplitr
      · iexact Herr
      isplitr
      · ipureintro; intro h; rw [h] at Hon; cases Hon
      isplitr
      · iintro %h; cases h
      · iintro %_; iexact Hb
    · (try wp_auto)
      iunfold authInfoOpt at Ha
      icases Ha with (%Han | ⟨%user, %rev, Hau⟩)
      · subst Han
        (try wp_auto)
        ihave #Hpauth : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
        · iPkgInit
        ihave #Hainit : go_etcd_io.etcd.server.v3.auth.authInit (GF := GF) $$ []
        · iapply isPkgInit_access $$ Hpauth
        icases Hainit with ⟨#HUE, -⟩
        ihave #HUEl := errVarLeaf_authErrVar _ $$ HUE
        ihave ⟨%eUE, #HeUE, #HaUE⟩ := errVarLeaf_get _ $$ HUEl
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold authedOutB
        isplitr
        · iexact HaUE
        isplitr
        · ipureintro; intro h; rw [h] at Hon; cases Hon
        isplitr
        · iintro %h; cases h
        · iintro %_; iexact Hb
      · ihave #Hpb := principalBound_of_ctxBoundOrTLS s E.authMode (GoInterface.ok ctx) a user rev $$ [$Hbnd $Hau]
        iunfold authInfoIs at Hau
        icases Hau with ⟨%Hann, -, -⟩
        (try wp_auto)
        rw [_root_.decide_eq_false Hann]
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold authedOutB
        isplitr
        · iapply applyErrIs_nil
        isplitr
        · ipureintro; intro _; rfl
        isplitr
        · iintro %_
          iexists (some { Username' := user, Revision' := rev })
          isplitl
          · iapply authedRes_some
          iexact Hpb
        · iintro %h; exact absurd rfl h

end proof

end EtcdGrove
end Perennial
