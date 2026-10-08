import EtcdGrove.Btree.Spec.BTree__DescendRange
import EtcdGrove.Btree.Spec.BTreeG__DescendRange

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

theorem BTree.DescendRange.wp_proof (wp_BTreeG_DescendRange : BTreeG.DescendRange.spec (GF := GF) (hG := hG)) :
    BTree.DescendRange.spec (GF := GF) (hG := hG) := by
  intro K o t dq s lessOrEqual kle greaterThan kgt iterator I
  wp_start as ⟨H0, H1, H2, H3⟩
  wp_auto
  wp_apply (wp_BTreeG_DescendRange (V := GoInterface) (T := Item.ty) o t dq s lessOrEqual kle greaterThan kgt iterator I) $$ [$H0 $H1 $H2 $H3] as ⟨Hp0, Hp1⟩
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
