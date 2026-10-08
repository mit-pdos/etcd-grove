import EtcdGrove.Btree.Spec.items__insertAt

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

theorem items.insertAt.wp_proof : items.insertAt.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ s sl vs index item Hi0 Hi1
  wp_start as ⟨Hs, Hsl, Hcap⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_apply wp_slice_literal (l := [zero_val V])
  isplitr
  · ipureintro; rfl
  iintro %zsl ⟨Hz, Hzcap⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hz] as %sl1 ⟨Hsl, Hcap, _⟩
  sorry

end proof

end Btree
end EtcdGrove
end Perennial
