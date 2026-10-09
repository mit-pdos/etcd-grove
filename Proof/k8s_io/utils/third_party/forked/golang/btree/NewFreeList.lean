module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.NewFreeList

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem NewFreeList.wp_proof : NewFreeList.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ size Hsize
  wp_start
  wp_auto
  wp_apply wp_slice_make3 (V := Loc) (W64 0) size ⟨by word, by word⟩ as %sl ⟨Hsl, Hcap, _⟩
  wp_alloc f as Hf
  iStructNamed Hf
  imod sync.init_Mutex (freeListInv (V := V) f) ⊤ (structFieldRef (FreeList V) go!"mu" f)
    $$ [mu] [freelist Hsl Hcap] with #Hmu
  · iexact mu
  · inext; unfold freeListInv; iexists sl, []; iframe
    simp; itrivial
  wp_auto
  iapply HΦ
  unfold isFreeList
  iexact Hmu
end proof

end btree
end EtcdGrove
end Perennial
