import EtcdGrove.Btree.Spec.BTree__AscendLessThan
import EtcdGrove.Btree.Spec.BTreeG__AscendLessThan

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

theorem BTree.AscendLessThan.wp_proof (wp_BTreeG_AscendLessThan : BTreeG.AscendLessThan.spec (GF := GF) (hG := hG)) :
    BTree.AscendLessThan.spec (GF := GF) (hG := hG) := by
  intro K o t dq s pivot kp iterator I
  wp_start as ⟨H0, H1, H2⟩
  wp_auto
  wp_apply (wp_BTreeG_AscendLessThan (V := GoInterface) (T := Item.ty) o t dq s pivot kp iterator I) $$ [$H0 $H1 $H2] as ⟨Hp0, Hp1⟩
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
