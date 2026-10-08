import EtcdGrove.Btree.Spec.BTreeG__minItems

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode github_com.google.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

theorem BTreeG.minItems.wp_proof : BTreeG.minItems.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ t dq tv
  wp_start as Ht
  icases (Access.access (A := t.[BTreeG V, go!"degree"] ↦{dq} tv.degree')
      (A' := t.[BTreeG V, go!"degree"] ↦{dq} tv.degree') (P := t ↦{dq} tv)) $$ Ht
    with ⟨Hd, Hback⟩
  wp_auto
  ihave Ht := Hback $$ Hd
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
