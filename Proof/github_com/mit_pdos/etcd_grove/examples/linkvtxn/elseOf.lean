/-
Lean-first (no Rocq counterpart).

The proof of `elseOf`: one append per field the count covers.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.elseOf

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

theorem elseOfL_go (x : Input) : elseOfL x =
    (if sint.Z (W64 0) < sint.Z x.NElse' then [x.Else0'] else []) := by
  rw [show sint.Z (W64 0) = 0 by word]; rfl

theorem elseOf.wp_proof : elseOf.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := TOp) (l := [])
  isplitr
  · ipureintro; rfl
  iintro %s0 ⟨Ho, Hocap⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_slice_literal (l := [x.Else0'])
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨H1, _⟩
    wp_apply wp_slice_append $$ [$Ho $Hocap $H1] as %o1 ⟨Ho, Hocap, -⟩
    iapply HΦ
    simp only [elseOfL_go, *, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
      List.singleton_append]
    iframe
  · iapply HΦ
    simp only [elseOfL_go, *, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
      List.singleton_append]
    iframe

end proof

end linkvtxn
end EtcdGrove
end Perennial
