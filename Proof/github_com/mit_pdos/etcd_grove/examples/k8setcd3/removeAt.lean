/-
Lean-first (no Rocq counterpart).

The proof of `removeAt`: the two subslices appended (as `linkv`'s).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.removeAt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem removeAt.wp_proof : removeAt.spec (GF := GF) (hG := hG) := by
  intro sl es dq i
  wp_start as ⟨Hs, %Hi⟩
  ihave %Hl := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  wp_auto
  wp_apply wp_slice_make3 (V := Input) (W64 0) sl.len ⟨by word, by word⟩
    as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  icases (ownSlice_slice i (i + W64 1) sl dq es ⟨Hi.1, by word, by word⟩).1 $$ Hs
    with ⟨H1, H2, H3⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, Hi.1, by word⟩)]
  wp_apply wp_slice_append $$ [$Ho $Hocap $H1] as %o1 ⟨Ho, Hocap, H1⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
  wp_apply wp_slice_append $$ [$Ho $Hocap $H3] as %o2 ⟨Ho, Hocap, H3⟩
  iapply HΦ
  ihave Hs := (ownSlice_slice i (i + W64 1) sl dq es ⟨Hi.1, by word, by word⟩).2 $$ [$H1 $H2 $H3]
  iframe
  rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.nil_append]
  unfold removeAtL
  iexact Ho

end proof

end k8setcd3
end EtcdGrove
end Perennial
