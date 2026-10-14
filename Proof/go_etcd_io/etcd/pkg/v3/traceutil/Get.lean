/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Get.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Get
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

theorem traceutil.Get.wp_proof
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG)) :
    traceutil.Get.spec (GF := GF) (hG := hG) := by
  intro ctx o
  wp_start as #Hctx
  wp_auto
  wp_bind (App (Val #(methods ctx.ty go!"Value" ctx.v)) _)
  iunfold traceutil.ctxTraceIs at Hctx
  iapply Hctx
  inext
  iintro %v %Hv
  cases o with
  | some t =>
    obtain ⟨Htn, rfl⟩ := Hv
    wp_auto
    rw [decide_eq_false Htn]
    wp_auto
    iapply HΦ
    iframe
    ipureintro; exact ⟨Htn, rfl⟩
  | none =>
    rcases Hv with rfl | ⟨ii, rfl, Hii⟩
    · wp_auto
      wp_apply hTODO as %t ⟨%Htn, Ht⟩
      iapply HΦ
      iframe
      ipureintro; exact Htn
    · wp_auto
      by_cases hty : ii.ty = go.GoType.PointerType traceutil.Trace.ty
      · have hv : ii.v = #(null : Loc) := by
          rcases Hii with h | h
          · exact absurd hty h
          · exact h
        simp only [hty, hv, ↓reduceIte, decide_true]
        wp_auto
        wp_apply hTODO as %t ⟨%Htn, Ht⟩
        iapply HΦ
        iframe
        ipureintro; exact Htn
      · simp only [hty, ↓reduceIte, decide_false]
        wp_auto
        wp_apply hTODO as %t ⟨%Htn, Ht⟩
        iapply HΦ
        iframe
        ipureintro; exact Htn

end proof

end EtcdGrove
end Perennial
