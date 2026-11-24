/-
Package initialization of `github_com.despreston.go_craq.node`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`Base.lean`): its error variables (`errNoSuccessor`, `errNoTail`, `errNotTail`, `errTailVersion`, translated
`errors.New` calls) each hold `errors.New` of their message (`errors.newVar`). Its initializer
allocates them, initializes its imports and runs their translated initializers.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.node.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.sync.Link
public import Dsverify.Proof.github_com.despreston.go_craq.store.Init
public import Dsverify.Proof.github_com.despreston.go_craq.transport.Init
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
variable [package_sem : _root_.Perennial.github_com.despreston.go_craq.node.Assumptions]

namespace github_com.despreston.go_craq.node

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.despreston.go_craq.node get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) errTailVersion _ as HerrTailVersion
  wp_apply wp_GlobalAlloc (V := GoInterface) errNotTail _ as HerrNotTail
  wp_apply wp_GlobalAlloc (V := GoInterface) errNoTail _ as HerrNoTail
  wp_apply wp_GlobalAlloc (V := GoInterface) errNoSuccessor _ as HerrNoSuccessor
  wp_apply (_root_.Perennial.github_com.despreston.go_craq.transport.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.github_com.despreston.go_craq.store.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.log _root_.Perennial.log.initialize'
      EtcdGrove.ExternalInit.log _root_.Perennial.log.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of errNoSuccessor))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrNoSuccessor ⟨#SerrNoSuccessor, #MerrNoSuccessor⟩
  -- translated initializer of errNoTail))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrNoTail ⟨#SerrNoTail, #MerrNoTail⟩
  -- translated initializer of errNotTail))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrNotTail ⟨#SerrNotTail, #MerrNotTail⟩
  -- translated initializer of errTailVersion))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrTailVersion ⟨#SerrTailVersion, #MerrTailVersion⟩
  try wp_auto
  ipersist HerrNoSuccessor
  ipersist HerrNoTail
  ipersist HerrNotTail
  ipersist HerrTailVersion
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold _root_.Perennial.errors.newVar
  isplitr
  · iexists _; iframe HerrNoSuccessor SerrNoSuccessor MerrNoSuccessor
  isplitr
  · iexists _; iframe HerrNoTail SerrNoTail MerrNoTail
  isplitr
  · iexists _; iframe HerrNotTail SerrNotTail MerrNotTail
  iexists _; iframe HerrTailVersion SerrTailVersion MerrTailVersion

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.despreston.go_craq.node get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.despreston.go_craq.node

end init

end Perennial
