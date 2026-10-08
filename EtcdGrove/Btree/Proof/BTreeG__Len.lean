import EtcdGrove.Btree.Spec.BTreeG__Len
import EtcdGrove.Btree.Lemmas.Read

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

theorem BTreeG.Len.wp_proof : BTreeG.Len.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t dq s
  wp_start as Ht
  unfold ownBTree
  icases Ht with ⟨%tv, %f, %less, %d, Ht, #Hcow, %Hdeg, %Hlen, %Hsorted, #Hitems, Hroot⟩
  icases btree_fields $$ Ht with ⟨Hdg, Hln, Hrt, Hcw, Hback⟩
  wp_auto
  rw [Hlen]
  iapply HΦ
  iexists tv, f, less, d
  iframe Hcow Hitems Hroot
  isplitl [Hback Hdg Hln Hrt Hcw]
  · iapply Hback; iframe
  iframe %Hdeg %Hlen %Hsorted

end proof

end Btree
end EtcdGrove
end Perennial
