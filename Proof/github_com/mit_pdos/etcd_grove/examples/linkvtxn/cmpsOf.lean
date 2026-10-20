/-
Lean-first (no Rocq counterpart).

The proof of `cmpsOf`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.cmpsOf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem cmpsOf.wp_proof : cmpsOf.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := Cmp) (l := [])
  isplitr
  · ipureintro; rfl
  iintro %s0 ⟨H0, H0cap⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_slice_literal (l := [x.Cmp0'])
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨H1, _⟩
    wp_apply wp_slice_append $$ [$H0 $H0cap $H1] as %o' ⟨Ho, Hocap, -⟩
    iapply HΦ
    rw [show cmpsOfL x = [x.Cmp0'] by unfold cmpsOfL; rw [if_pos (by simpa using Hif)],
      List.nil_append]
    iframe
  · iapply HΦ
    rw [show cmpsOfL x = [] by unfold cmpsOfL; rw [if_neg (by simpa using Hif)]]
    iframe

end proof

end linkvtxn
end EtcdGrove
end Perennial
