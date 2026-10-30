module
public import Spec.go_etcd_io.bbolt.panicked__Error

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem panicked.Error.wp_proof :
    panicked.Error.spec (GF := GF) (hG := hG) := by
  intro p
  rcases p with ⟨r⟩
  cases r with
  | nil =>
    wp_start as _
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Sprintf as %s _
    try wp_auto
    iapply HΦ; itrivial
  | ok ri =>
    by_cases Hc : go.typeSetContains ri.ty go.error = true
    · have He : panickedReasonOK (GF := GF) (interface.ok ri) = errorStringOK ri := by
        simp [panickedReasonOK, Hc]
      simp only
      rw [He]
      wp_start as #Herr
      wp_auto
      rw [Hc]
      try wp_auto
      wp_bind (App (Val #(methods ri.ty go!"Error" ri.v)) (Val #()))
      unfold errorStringOK
      iapply Herr
      inext
      iintro %s
      try wp_auto
      iapply HΦ; itrivial
    · simp only [Bool.not_eq_true] at Hc
      wp_start as _
      wp_auto
      rw [Hc]
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply fmt.wp_Sprintf as %s _
      try wp_auto
      iapply HΦ; itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
