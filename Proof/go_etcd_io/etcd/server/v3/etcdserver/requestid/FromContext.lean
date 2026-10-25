/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/requestid/FromContext.lean` (PR etcd#21401).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.requestid.FromContext
public import Spec.context.ValueRequestID

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.requestid.Assumptions]

theorem requestid.FromContext.wp_proof
    (hVal : context.ValueRequestID.spec (GF := GF) (hG := hG)) :
    requestid.FromContext.spec (GF := GF) (hG := hG) := by
  constructor
  · intro ctx o
    wp_start as #Hctx
    wp_auto
    wp_bind (App (Val #(methods ctx.ty go!"Value" ctx.v)) _)
    iunfold requestid.ctxReqIDIs at Hctx
    iapply Hctx
    inext
    iintro %v %Hv
    cases o with
    | some id =>
      subst Hv
      wp_auto
      iapply HΦ
      ipureintro; rfl
    | none =>
      subst Hv
      wp_auto
      iapply HΦ
      ipureintro; rfl
  · intro ctx cd
    wp_start as #Hctx
    wp_auto
    wp_apply (hVal ctx ⟨requestid.requestIDKey.ty, #(zero_val requestid.requestIDKey)⟩ cd rfl)
      $$ [] as %v %Hv
    · iexact Hctx
    rcases Hv with rfl | ⟨id, rfl⟩
    · wp_auto
      iapply HΦ
      itrivial
    · wp_auto
      iapply HΦ
      itrivial

end proof

end EtcdGrove
end Perennial
