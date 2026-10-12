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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.AuthInfoFromCtx.wp_proof
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG) := by
  intro s st cca ctx cd
  wp_start as ⟨#Hst, #Hauth, #Hcca, #Hctx⟩
  ihave #Hauth' := Hauth
  iunfold isReqAuth at Hauth'
  icases Hauth' with ⟨%ai, %Hai, #HFromCtx, #HFromTLS⟩
  wp_auto
  wp_apply hAS s st $$ []
  · iframe #
  subst Hai
  wp_auto
  wp_apply HFromCtx $$ %ctx %cd [] as %a %err Ha
  · iframe #
  wp_if_destruct
  · cases err with
    | ok ei =>
      wp_auto
      iapply HΦ; iexact Ha
    | nil =>
      wp_auto
      cases cca
      · wp_auto
        iapply HΦ; isplitr
        · iunfold authInfoOpt; ileft; ipureintro; rfl
        iapply applyErrIs_nil
      · wp_auto
        wp_apply hAS s _ $$ []
        · iframe #
        iintro -
        wp_auto
        wp_apply HFromTLS $$ %ctx %cd [] as %a' Ha'
        · iframe #
        iapply HΦ; iframe Ha'; iapply applyErrIs_nil
  · iapply HΦ; iexact Ha

end proof

end EtcdGrove
end Perennial
