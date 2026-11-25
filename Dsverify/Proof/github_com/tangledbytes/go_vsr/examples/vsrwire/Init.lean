/-
Package initialization of `github_com.tangledbytes.go_vsr.examples.vsrwire`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`events.frameDecoderSet`, `Base.lean`): the hook set for good. Its
initializer initializes its imports and runs its `init()`, which sets `events`' frame-decoder hook
to `decodeFrame` (`events.wp_SetFrameDecoder`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrwire.Base
public import Proof.encoding.json.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.events.Init
public import Proof.models_lab.jsoncodec.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.events.SetFrameDecoder
public import Proof.runtime.PkgInitExt

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
variable [package_sem : _root_.Perennial.github_com.tangledbytes.go_vsr.examples.vsrwire.Assumptions]

namespace github_com.tangledbytes.go_vsr.examples.vsrwire

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.tangledbytes.go_vsr.examples.vsrwire get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrwire }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply (_root_.Perennial.github_com.tangledbytes.go_vsr.pkg.events.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.models_lab.jsoncodec.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.encoding.json.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  wp_apply _root_.Perennial.github_com.tangledbytes.go_vsr.pkg.events.wp_SetFrameDecoder as #Hset
  try wp_auto
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.tangledbytes.go_vsr.examples.vsrwire get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrwire }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.tangledbytes.go_vsr.examples.vsrwire

end init

end Perennial
