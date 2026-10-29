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
  wp_start as ⟨#Hst, #Hauth, #Hbd, #Hcca, #Hctx, Hrd⟩
  ihave #Hauth' := Hauth
  iunfold isReqAuth at Hauth'
  icases Hauth' with ⟨%ai, %Hai, -, #HFromTLS⟩
  ihave #HFromCtx := isReqAuth_ctxM st RD M ai Hai $$ [$Hauth $Hbd]
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
      iintro !> %h
      iunfold ctxBoundOrTLS; ileft; iapply Hb; ipureintro; exact h
    | nil =>
      wp_auto
      cases cca
      · wp_auto
        iapply HΦ; iframe Hrd; isplitr
        · iunfold authInfoOpt; ileft; ipureintro; rfl
        isplitr
        · iapply applyErrIs_nil
        iintro !> -
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
        iintro !> -
        iunfold ctxBoundOrTLS
        iunfold srvTLSId; iright; iexact Hcca
  · iapply HΦ; iframe Hrd Ha Herr
    iintro !> %h
    iunfold ctxBoundOrTLS; ileft; iapply Hb; ipureintro; exact h

end proof

end EtcdGrove
end Perennial
