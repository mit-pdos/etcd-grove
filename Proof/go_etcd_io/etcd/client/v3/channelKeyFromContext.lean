/-
Proof of `Spec/go_etcd_io/etcd/client/v3/channelKeyFromContext.lean` (PR #21765).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.channelKeyFromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem channelKeyFromContext.wp_proof :
    channelKeyFromContext.spec (GF := GF) (hG := hG) := by
  intro ctx o
  wp_start as #Hctx
  cases ctx with
  | nil =>
    iunfold clientv3.ctxChannelKeyIs at Hctx
    icases Hctx with %Ho
    subst Ho
    wp_auto
    iapply HΦ
    ipureintro; exact ⟨rfl, rfl⟩
  | ok c =>
    iunfold clientv3.ctxChannelKeyIs at Hctx
    wp_auto
    wp_bind (App (Val #(methods c.ty go!"Value" c.v)) (Val #clientv3.channelKeyVal))
    iapply Hctx
    inext
    iintro %v %Hv
    cases o with
    | none =>
      rcases Hv with rfl | ⟨ii, rfl, hty⟩
      · wp_auto
        iapply HΦ
        ipureintro; exact ⟨rfl, rfl⟩
      · wp_auto
        simp only [hty, ↓reduceIte, decide_false]
        wp_auto
        iapply HΦ
        ipureintro; exact ⟨rfl, rfl⟩
    | some k =>
      subst Hv
      wp_auto
      iapply HΦ
      ipureintro; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
