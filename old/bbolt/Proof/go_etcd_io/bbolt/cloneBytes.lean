module
public import Spec.go_etcd_io.bbolt.cloneBytes

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

theorem cloneBytes.wp_proof : cloneBytes.spec (GF := GF) (hG := hG) := by
  intro v bs dq
  wp_start as Hv
  ihave %Hl := ownSlice_len _ _ _ $$ Hv
  wp_auto
  wp_apply wp_slice_make2 (V := w8) $$ [] as %c ⟨Hc, Hcap⟩
  · ipureintro; word
  try wp_auto
  wp_apply wp_slice_copy c _ v bs dq $$ [Hc Hv] with %k ⟨%Hk, Hc, Hv⟩
  · iframe
  try wp_auto
  have e1 : List.take (List.replicate (sint.nat v.len) (zero_val w8)).length bs = bs := by
    rw [List.length_replicate, ← Hl.1]; exact List.take_of_length_le (Nat.le_refl _)
  have e2 : List.drop bs.length (List.replicate (sint.nat v.len) (zero_val w8)) = [] := by
    apply List.drop_eq_nil_of_le; rw [List.length_replicate, Hl.1]; exact Nat.le_refl _
  rw [e1, e2, List.append_nil]
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
