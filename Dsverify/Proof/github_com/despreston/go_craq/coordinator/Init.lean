/-
Package initialization of `github_com.despreston.go_craq.coordinator`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`Base.lean`): its error variables (`ErrEmptyChain`, `errLastNode`, `errDisconnected`, `ErrVersions`, translated
`errors.New` calls) each hold `errors.New` of their message (`errors.newVar`). Its initializer
allocates them, initializes its imports and runs their translated initializers.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.coordinator.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
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
variable [package_sem : _root_.Perennial.github_com.despreston.go_craq.coordinator.Assumptions]

namespace github_com.despreston.go_craq.coordinator

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.despreston.go_craq.coordinator get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrVersions _ as HErrVersions
  wp_apply wp_GlobalAlloc (V := GoInterface) errDisconnected _ as HerrDisconnected
  wp_apply wp_GlobalAlloc (V := GoInterface) errLastNode _ as HerrLastNode
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrEmptyChain _ as HErrEmptyChain
  wp_apply (_root_.Perennial.github_com.despreston.go_craq.transport.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.log _root_.Perennial.log.initialize'
      EtcdGrove.ExternalInit.log _root_.Perennial.log.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrEmptyChain))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrEmptyChain ⟨#SErrEmptyChain, #MErrEmptyChain⟩
  -- translated initializer of errLastNode))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrLastNode ⟨#SerrLastNode, #MerrLastNode⟩
  -- translated initializer of errDisconnected))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrDisconnected ⟨#SerrDisconnected, #MerrDisconnected⟩
  -- translated initializer of ErrVersions))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrVersions ⟨#SErrVersions, #MErrVersions⟩
  try wp_auto
  ipersist HErrEmptyChain
  ipersist HerrLastNode
  ipersist HerrDisconnected
  ipersist HErrVersions
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold _root_.Perennial.errors.newVar
  isplitr
  · iexists _; iframe HErrEmptyChain SErrEmptyChain MErrEmptyChain
  isplitr
  · iexists _; iframe HerrLastNode SerrLastNode MerrLastNode
  isplitr
  · iexists _; iframe HerrDisconnected SerrDisconnected MerrDisconnected
  iexists _; iframe HErrVersions SErrVersions MErrVersions

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.despreston.go_craq.coordinator get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.despreston.go_craq.coordinator

end init

end Perennial
