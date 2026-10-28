/-
**The token binding at the gRPC layer's admin guard** (the auth plan's E1, 2026-10-24;
`notes/decisions.md`, "E1 of the auth plan"). Lean-first (no Rocq counterpart).

`AuthAdmin.isPermitted` and `requireAuthInfo` (and the maintenance server's `requireAuthInfo` over
it; A2: the guards of the maintenance and cluster services' admin methods) is
the server's admin check over its `AuthInfoFromCtx`; its bound variant, over a server whose store
has the bound request side (`srvAuthBound`, `etcdserver/AuthBound.lean`), says moreover that the
admin token's (resp. the authenticated user's) auth info is bound (`adminOutB`, `authedOutB`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBound
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthAdmin__isPermitted
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthAdmin__requireAuthInfo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__requireAuthInfo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`AuthAdmin.isPermitted` with the binding**: its spec, over a server whose store has the
bound request side too, whose admin token's auth info is moreover bound (`adminOutB`). -/
abbrev v3rpc.AuthAdmin.isPermitted.boundSpec : Prop :=
  ∀ (aa s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.authAdminIs aa s E ∗ srvAuthBound s E ∗ srvAdminNilOk s E ∗ mvcc.txnCtx ctx cd ∗
      E.RD }}
    (App (Val (aa @!! go.GoType.PointerType v3rpc.AuthAdmin.ty @!! go!"isPermitted"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ adminOutB s E.authMode (GoInterface.ok ctx) err }}

theorem v3rpc.AuthAdmin.isPermitted_bound
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    v3rpc.AuthAdmin.isPermitted.boundSpec (GF := GF) (hG := hG) := by
  intro aa s E ctx cd
  wp_start as ⟨#Haa, #Hbd, #Hnil, #Hctx, HRD⟩
  iunfold v3rpc.authAdminIs at Haa
  icases Haa with ⟨%Hann, #Hag, #Hau⟩
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
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
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
      icases Hau with ⟨%Hann', -, -⟩
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

/-- **`AuthAdmin.requireAuthInfo` with the binding**: its spec, over a server whose store has the
bound request side too, whose passed check's auth info is moreover bound (`authedOutB`). -/
abbrev v3rpc.AuthAdmin.requireAuthInfo.boundSpec : Prop :=
  ∀ (aa s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.authAdminIs aa s E ∗ srvAuthBound s E ∗ mvcc.txnCtx ctx cd ∗ E.RD }}
    (App (Val (aa @!! go.GoType.PointerType v3rpc.AuthAdmin.ty @!! go!"requireAuthInfo"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ authedOutB s E.authMode (GoInterface.ok ctx) err }}

theorem v3rpc.AuthAdmin.requireAuthInfo_bound
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    v3rpc.AuthAdmin.requireAuthInfo.boundSpec (GF := GF) (hG := hG) := by
  intro aa s E ctx cd
  wp_start as ⟨#Haa, #Hbd, #Hctx, HRD⟩
  iunfold v3rpc.authAdminIs at Haa
  icases Haa with ⟨%Hann, #Hag, #Hau⟩
  iunfold srvAuthAt at Hau
  icases Hau with ⟨%st, %cca, %P, %f, #Has, #Hreq, #Hcca, #Hast⟩
  iunfold srvAuthBound at Hbd
  icases Hbd with ⟨%st3, #Has3, #Hreqb⟩
  icombine Has Has3 gives %Heq3
  subst Heq3
  iunfold apply.isAuthStore at Hast
  icases Hast with ⟨%ai, %Hai, -, -, -, -, -, #HEn, -⟩
  subst Hai
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (hAS s (GoInterface.ok ai))
  · iframe #
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
        icases Hau with ⟨%Hann', -, -⟩
        (try wp_auto)
        rw [_root_.decide_eq_false Hann']
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

/-- **The maintenance server's `requireAuthInfo` with the binding**: its spec over
`AuthAdmin.requireAuthInfo`'s bound variant. -/
abbrev v3rpc.authMaintenanceServer.requireAuthInfo.boundSpec : Prop :=
  ∀ (p ms aa s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.amsIs p ms aa ∗ v3rpc.authAdminIs aa s E ∗ srvAuthBound s E ∗ mvcc.txnCtx ctx cd ∗
      E.RD }}
    (App (Val (p @!! go.GoType.PointerType v3rpc.authMaintenanceServer.ty @!!
      go!"requireAuthInfo")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ authedOutB s E.authMode (GoInterface.ok ctx) err }}

theorem v3rpc.authMaintenanceServer.requireAuthInfo_bound
    (hP : v3rpc.AuthAdmin.requireAuthInfo.boundSpec (GF := GF) (hG := hG)) :
    v3rpc.authMaintenanceServer.requireAuthInfo.boundSpec (GF := GF) (hG := hG) := by
  intro p ms aa s E ctx cd
  wp_start as ⟨#Hams, #Haa, #Hbd, #Hctx, HRD⟩
  iunfold v3rpc.amsIs at Hams
  icases Hams with ⟨%Hpn, #Hms, #Haaf⟩
  (try wp_auto)
  wp_apply (hP aa s E ctx cd) $$ [$HRD] as %err ⟨HRD, #Hout⟩
  · iframe #
  (try wp_auto)
  iapply HΦ
  iframe HRD
  iexact Hout

end proof

end EtcdGrove
end Perennial
