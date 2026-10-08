import EtcdGrove.Btree.Spec.initialize

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

/-- `wp_sort_initialize` is `sort`'s `wp_initialize'`, which Perennial does not prove
(`Perennial/Proof/sort_proof/sort_init.lean` has only the `IsPkgInit` instance); it is
a hypothesis until Perennial has it. -/
theorem initialize.wp_proof
    (wp_sort_initialize : ∀ (get_is_pkg_init : GoString → IProp GF),
      GetIsPkgInitProp pkg_id.sort get_is_pkg_init →
      {{ ownInitializing get_is_pkg_init }}
        (App (Val _root_.Perennial.sort.initialize') (Val #()))
      {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.sort }}) :
    initialize.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoFunc) itemLess (LessFunc.ty Item.ty) as Hl
  wp_apply sync.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply strings.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hstrings⟩
  wp_apply wp_sort_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsort⟩
  wp_apply io.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply +noauto fmt.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hfmt⟩
  wp_pures
  wp_func_lits
  wp_store
  ipersist Hl
  wp_pures
  iframe Hown
  is_pkg_init_finish
  unfold isInit
  iexists _
  iframe Hl
  unfold isItemLessFn
  iintro !> %a %b %Ψ !> H
  wp_pures
  wp_alloc b_ptr as Hb
  wp_pures
  wp_alloc a_ptr as Ha
  wp_pures
  wp_load
  wp_pures
  wp_load
  wp_bind (App (App (Val (GoInstruction (MethodResolve _ _))) _) _)
  iapply wp_wand $$ H
  iintro %v Hv
  wp_pures
  iexact Hv

end proof

end Btree
end EtcdGrove
end Perennial
