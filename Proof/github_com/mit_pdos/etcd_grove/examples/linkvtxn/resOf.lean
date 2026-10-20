/-
Lean-first (no Rocq counterpart).

The proof of `resOf`: one append per field the count covers.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.resOf

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

theorem resOfL_go (x : Output) : resOfL x =
    (if sint.Z (W64 0) < sint.Z x.NRes' then [x.Res0'] else []) ++
    (if sint.Z (W64 1) < sint.Z x.NRes' then [x.Res1'] else []) ++
    (if sint.Z (W64 2) < sint.Z x.NRes' then [x.Res2'] else []) := by
  rw [show sint.Z (W64 0) = 0 by word, show sint.Z (W64 1) = 1 by word, show sint.Z (W64 2) = 2 by word]; rfl

theorem resOf.wp_proof : resOf.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := TRes) (l := [])
  isplitr
  · ipureintro; rfl
  iintro %s0 ⟨Ho, Hocap⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_slice_literal (l := [x.Res0'])
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨H1, _⟩
    wp_apply wp_slice_append $$ [$Ho $Hocap $H1] as %o1 ⟨Ho, Hocap, -⟩
    wp_if_destruct
    · wp_apply wp_slice_literal (l := [x.Res1'])
      isplitr
      · ipureintro; rfl
      iintro %s2 ⟨H2, _⟩
      wp_apply wp_slice_append $$ [$Ho $Hocap $H2] as %o2 ⟨Ho, Hocap, -⟩
      wp_if_destruct
      · wp_apply wp_slice_literal (l := [x.Res2'])
        isplitr
        · ipureintro; rfl
        iintro %s3 ⟨H3, _⟩
        wp_apply wp_slice_append $$ [$Ho $Hocap $H3] as %o3 ⟨Ho, Hocap, -⟩
        iapply HΦ
        simp only [resOfL_go, *, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
          List.singleton_append]
        iframe
      · iapply HΦ
        simp only [resOfL_go, *, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
          List.singleton_append]
        iframe
    · wp_if_destruct
      · wp_apply wp_slice_literal (l := [x.Res2'])
        isplitr
        · ipureintro; rfl
        iintro %s3 ⟨H3, _⟩
        wp_apply wp_slice_append $$ [$Ho $Hocap $H3] as %o3 ⟨Ho, Hocap, -⟩
        iapply HΦ
        simp only [resOfL_go, *, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
          List.singleton_append]
        iframe
      · iapply HΦ
        simp only [resOfL_go, *, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
          List.singleton_append]
        iframe
  · wp_if_destruct
    · wp_apply wp_slice_literal (l := [x.Res1'])
      isplitr
      · ipureintro; rfl
      iintro %s2 ⟨H2, _⟩
      wp_apply wp_slice_append $$ [$Ho $Hocap $H2] as %o2 ⟨Ho, Hocap, -⟩
      wp_if_destruct
      · wp_apply wp_slice_literal (l := [x.Res2'])
        isplitr
        · ipureintro; rfl
        iintro %s3 ⟨H3, _⟩
        wp_apply wp_slice_append $$ [$Ho $Hocap $H3] as %o3 ⟨Ho, Hocap, -⟩
        iapply HΦ
        simp only [resOfL_go, *, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
          List.singleton_append]
        iframe
      · iapply HΦ
        simp only [resOfL_go, *, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
          List.singleton_append]
        iframe
    · wp_if_destruct
      · wp_apply wp_slice_literal (l := [x.Res2'])
        isplitr
        · ipureintro; rfl
        iintro %s3 ⟨H3, _⟩
        wp_apply wp_slice_append $$ [$Ho $Hocap $H3] as %o3 ⟨Ho, Hocap, -⟩
        iapply HΦ
        simp only [resOfL_go, *, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
          List.singleton_append]
        iframe
      · iapply HΦ
        simp only [resOfL_go, *, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
          List.singleton_append]
        iframe

end proof

end linkvtxn
end EtcdGrove
end Perennial
