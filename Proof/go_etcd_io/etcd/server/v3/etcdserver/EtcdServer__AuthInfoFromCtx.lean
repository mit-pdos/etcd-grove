/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__AuthInfoFromCtx.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- One proof for both modes: the store's `AuthInfoFromCtx` in the mode (`isReqAuth_ctxM`), its
auth info the binding's, or `nil` (bound, `auth.ctxBound`), or the TLS fallback's (`srvTLSId`). -/
theorem EtcdServer.AuthInfoFromCtx.wp_proof
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG) := by
  intro s st RD M cca ctx cd
  wp_start as ⟨#Hst, #Hauth, #Hbd, #Hcca, #Hctx, #Hlib, Hrd⟩
  -- (k8s 7f-4 item 7) a transaction's context or a stream handler's weak one: `Done()` either way
  ihave #Hda : auth.ctxDoneAny ctx $$ []
  · icases Hctx with (#Hctx | #Hctx)
    · iapply auth.ctxDoneAny_of_txnCtx ctx cd $$ Hctx
    · iapply auth.ctxDoneAny_of_srvCtxWeak ctx cd $$ Hctx
  ihave #Hauth' := Hauth
  iunfold isReqAuth at Hauth'
  icases Hauth' with ⟨%ai, %Hai, -, #HFromTLS⟩
  ihave #HFromCtx := isReqAuth_ctxM st RD M ai Hai $$ [$Hauth $Hbd]
  wp_auto
  wp_apply hAS s st $$ []
  · iframe #
  subst Hai
  wp_auto
  wp_apply HFromCtx $$ %ctx [Hrd] as %a %err ⟨Hrd, Ha, Herr, #Hb, #Hae⟩
  · iframe; iframe #
  wp_if_destruct
  · cases err with
    | ok ei =>
      wp_auto
      iapply HΦ; iframe Hrd Ha Herr Hae
      iintro !> %h
      iunfold ctxBoundOrTLS; ileft; iapply Hb; ipureintro; exact h
    | nil =>
      wp_auto
      cases cca
      · wp_auto
        iapply HΦ; iframe Hrd; isplitr
        · iunfold authInfoOpt; ileft; ipureintro; rfl
        isplitr
        · iapply authApplyErrIs_nil
        iframe Hae
        iintro !> -
        iunfold ctxBoundOrTLS; ileft
        iunfold auth.ctxBound; ileft; ipureintro; rfl
      · wp_auto
        wp_apply hAS s _ $$ []
        · iframe #
        iintro -
        wp_auto
        wp_apply HFromTLS $$ %ctx [] as %a' Ha'
        · iframe #
        iapply HΦ; iframe Hrd Ha'; isplitr
        · iapply authApplyErrIs_nil
        isplitr
        rotate_left
        · iintro !> -; iunfold authErrVarIs; ileft; ipureintro; rfl
        iintro !> -
        iunfold ctxBoundOrTLS
        iunfold srvTLSId; iright; iexact Hcca
  · iapply HΦ; iframe Hrd Ha Herr Hae
    iintro !> %h
    iunfold ctxBoundOrTLS; ileft; iapply Hb; ipureintro; exact h

/-- `specLb` (auth-guard-completeness G1): `wp_proof`'s, over the store's call at the lower bound
(`isReqAuth_ctxMLb`); the TLS fallback runs only after the store's `(nil, nil)`, whose reason it
keeps. -/
theorem EtcdServer.AuthInfoFromCtx.wp_proofLb
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.AuthInfoFromCtx.specLb (GF := GF) (hG := hG) := by
  intro s st RD M cca ctx cd n
  wp_start as ⟨#Hst, #Hauth, #Hbd, #Hcca, #Hctx, #Hlib, #Hlb, Hrd⟩
  ihave #Hda : auth.ctxDoneAny ctx $$ []
  · icases Hctx with (#Hctx | #Hctx)
    · iapply auth.ctxDoneAny_of_txnCtx ctx cd $$ Hctx
    · iapply auth.ctxDoneAny_of_srvCtxWeak ctx cd $$ Hctx
  ihave #Hauth' := Hauth
  iunfold isReqAuth at Hauth'
  icases Hauth' with ⟨%ai, %Hai, -, #HFromTLS⟩
  ihave #HFromCtx := isReqAuth_ctxMLb st RD M ai Hai n $$ [$Hauth $Hbd $Hlb]
  wp_auto
  wp_apply hAS s st $$ []
  · iframe #
  subst Hai
  wp_auto
  wp_apply HFromCtx $$ %ctx [Hrd] as %a %err ⟨Hrd, Ha, Herr, #Hb, #Hae, #Hz, #Hne⟩
  · iframe; iframe #
  wp_if_destruct
  · cases err with
    | ok ei =>
      wp_auto
      iapply HΦ; iframe Hrd Ha Herr Hae Hne
      isplitl
      · iintro !> %h
        iunfold ctxBoundOrTLS; ileft; iapply Hb; ipureintro; exact h
      · iintro !> %h %hz; cases hz.2
    | nil =>
      wp_auto
      cases cca
      · wp_auto
        iapply HΦ; iframe Hrd; isplitr
        · iunfold authInfoOpt; ileft; ipureintro; rfl
        isplitr
        · iapply authApplyErrIs_nil
        iframe Hae
        isplitl
        · iintro !> -
          iunfold ctxBoundOrTLS; ileft
          iunfold auth.ctxBound; ileft; ipureintro; rfl
        isplitl
        · iintro !> %h %_
          iapply Hz $$ %h
          exact ⟨rfl, rfl⟩
        · iintro !> %h %hne; exact absurd rfl hne
      · wp_auto
        wp_apply hAS s _ $$ []
        · iframe #
        iintro -
        wp_auto
        wp_apply HFromTLS $$ %ctx [] as %a' Ha'
        · iframe #
        iapply HΦ; iframe Hrd Ha'; isplitr
        · iapply authApplyErrIs_nil
        isplitr
        · iintro !> -
          iunfold ctxBoundOrTLS
          iunfold srvTLSId; iright; iexact Hcca
        isplitr
        · iintro !> -; iunfold authErrVarIs; ileft; ipureintro; rfl
        isplitl
        · iintro !> %h %_
          iapply Hz $$ %h
          exact ⟨rfl, rfl⟩
        · iintro !> %h %hne; exact absurd rfl hne
  · iapply HΦ; iframe Hrd Ha Herr Hae Hne
    isplitl
    · iintro !> %h
      iunfold ctxBoundOrTLS; ileft; iapply Hb; ipureintro; exact h
    · iintro !> %h %hz
      exact absurd hz.1 Hif

end proof

end EtcdGrove
end Perennial
