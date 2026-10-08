import EtcdGrove.Btree.Spec.copyOnWriteContext__newNode
import EtcdGrove.Btree.Spec.FreeListG__newNode

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

theorem copyOnWriteContext.newNode.wp_proof
    (wp_FreeListG_newNode : FreeListG.newNode.spec (GF := GF) (hG := hG)) :
    copyOnWriteContext.newNode.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less
  wp_start as #Hcow
  unfold isCow
  icases Hcow with ⟨#Hc, #Hfl, #Hless⟩
  iStructNamed Hc
  wp_auto
  wp_apply (wp_FreeListG_newNode (V := V) (T := T) f) $$ [$Hfl] as %n Hn
  unfold freeNode
  icases Hn with ⟨%is, %cs, %cow, Hnf, Hsl1, Hcap1, Hsl2, Hcap2⟩
  unfold nodeFields
  icases Hnf with ⟨%Hnn, Hi, Hch, Hw⟩
  wp_auto
  iapply HΦ
  unfold nodeShallow nodeFields
  iexists is, cs
  simp only [List.map_nil]
  iframe
  ipureintro; exact Hnn

end proof

end Btree
end EtcdGrove
end Perennial
