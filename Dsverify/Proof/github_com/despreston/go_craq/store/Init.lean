/-
Package initialization of `github_com.despreston.go_craq.store`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`Base.lean`): its error variables (`ErrNotFound`, `ErrDirtyItem`, translated
`errors.New` calls) each hold `errors.New` of their message (`errors.newVar`). Its initializer
allocates them, initializes its imports and runs their translated initializers.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.store.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.errors.NewVar
public import Net.Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.despreston.go_craq.store.Assumptions]

namespace github_com.despreston.go_craq.store

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.despreston.go_craq.store get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrDirtyItem _ as HErrDirtyItem
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNotFound _ as HErrNotFound
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrNotFound))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrNotFound ⟨#SErrNotFound, #MErrNotFound⟩
  -- translated initializer of ErrDirtyItem))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrDirtyItem ⟨#SErrDirtyItem, #MErrDirtyItem⟩
  try wp_auto
  ipersist HErrNotFound
  ipersist HErrDirtyItem
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold _root_.Perennial.errors.newVar
  isplitr
  · iexists _; iframe HErrNotFound SErrNotFound MErrNotFound
  iexists _; iframe HErrDirtyItem SErrDirtyItem MErrDirtyItem

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.despreston.go_craq.store get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.despreston.go_craq.store

end init

end Perennial
