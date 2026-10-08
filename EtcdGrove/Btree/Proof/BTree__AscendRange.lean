import EtcdGrove.Btree.Spec.BTree__AscendRange
import EtcdGrove.Btree.Spec.BTreeG__AscendRange

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

theorem BTree.AscendRange.wp_proof (wp_BTreeG_AscendRange : BTreeG.AscendRange.spec (GF := GF) (hG := hG)) :
    BTree.AscendRange.spec (GF := GF) (hG := hG) := by
  intro K o t dq s greaterOrEqual kge lessThan klt iterator I
  wp_start as ⟨H0, H1, H2, H3⟩
  wp_auto
  wp_apply (wp_BTreeG_AscendRange (V := GoInterface) (T := Item.ty) o t dq s greaterOrEqual kge lessThan klt iterator I) $$ [$H0 $H1 $H2 $H3] as ⟨Hp0, Hp1⟩
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
