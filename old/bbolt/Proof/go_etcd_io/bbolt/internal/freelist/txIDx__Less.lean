module
public import Spec.go_etcd_io.bbolt.internal.freelist.txIDx__Less

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem txIDx.Less.wp_proof : txIDx.Less.spec (GF := GF) (hG := hG) := by
  intro t xs dq i j x y Hi Hj Hx Hy
  wp_start as Hs
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hi := (List.getElem?_eq_some_iff.1 Hx).1
  have hj := (List.getElem?_eq_some_iff.1 Hy).1
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi, by word⟩)]
  wp_apply wp_load_slice_index t (sint.Z i) xs dq x Hi $$ [Hs] as Hs
  · iframe; ipureintro; exact Hx
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj, by word⟩)]
  wp_apply wp_load_slice_index t (sint.Z j) xs dq y Hj $$ [Hs] as Hs
  · iframe; ipureintro; exact Hy
  try wp_auto
  iapply HΦ $$ Hs

end proof

end bbolt
end EtcdGrove
end Perennial
