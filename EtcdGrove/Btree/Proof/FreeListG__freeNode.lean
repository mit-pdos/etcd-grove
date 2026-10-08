import EtcdGrove.Btree.Spec.FreeListG__freeNode
import EtcdGrove.Btree.Lemmas.Alloc

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

theorem FreeListG.freeNode.wp_proof : FreeListG.freeNode.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ f n
  wp_start as ⟨#Hfl, Hn⟩
  wp_auto
  unfold isFreeList
  wp_apply sync.Mutex.wp_Lock $$ [$Hfl] as ⟨Hlocked, HR⟩
  unfold freeListInv
  icases HR with ⟨%sl, %ns, Hfield, Hsl, Hcap, Hns⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_slice_literal (l := [n])
    isplitr
    · ipureintro; rfl
    iintro %zsl ⟨Hz, Hzcap⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hz] as %sl1 ⟨Hsl, Hcap, _⟩
    ihave Hns := bigSepL_push _ ns n $$ [Hns Hn]
    · iframe
    wp_apply sync.Mutex.wp_Unlock $$ [$Hfl $Hlocked Hfield Hsl Hcap Hns]
    · inext; iexists sl1, ns ++ [n]; iframe
    wp_end
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hfl $Hlocked Hfield Hsl Hcap Hns]
    · inext; iexists sl, ns; iframe
    wp_end

end proof

end Btree
end EtcdGrove
end Perennial
