module
public import Spec.go_etcd_io.bbolt.internal.common.Pages__Less
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem Pages.Less.wp_proof : Pages.Less.spec (GF := GF) (hG := hG) := by
  intro s ps dq i j pi pj vi vj qi qj Hi Hj Hx Hy
  wp_start as ⟨Hs, Hpi, Hpj⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hi := (List.getElem?_eq_some_iff.1 Hx).1
  have hj := (List.getElem?_eq_some_iff.1 Hy).1
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi, by word⟩)]
  wp_apply wp_load_slice_index s (sint.Z i) ps dq pi Hi $$ [Hs] as Hs
  · iframe; ipureintro; exact Hx
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj, by word⟩)]
  wp_apply wp_load_slice_index s (sint.Z j) ps dq pj Hj $$ [Hs] as Hs
  · iframe; ipureintro; exact Hy
  try wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
