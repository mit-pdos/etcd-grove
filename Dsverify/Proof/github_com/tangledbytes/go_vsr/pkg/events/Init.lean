/-
Package initialization of `github_com.tangledbytes.go_vsr.pkg.events`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`hookKnownFull`, `Base.lean`): the frame-decoder hook's lock, with its flag.
Its initializer allocates its variables (`ErrInvalidEventType`, an `errors.New` call;
`frameDecoderMu`, a new mutex guarding `frameDecoder`, `nil`, and the flag, unset) and
initializes its imports.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.events.Base
public import Dsverify.Proof.encoding.json.Init
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sync.Link
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.ipv4port.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.log.Init
public import Perennial.Ghost.MonoList
public import Perennial.Proof.errors.NewVar
public import Dsverify.Proof.runtime.PkgInitDsv

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
variable [_root_.Perennial.encoding.json.InitHyp GF]
variable [package_sem : _root_.Perennial.github_com.tangledbytes.go_vsr.pkg.events.Assumptions]

namespace github_com.tangledbytes.go_vsr.pkg.events

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.tangledbytes.go_vsr.pkg.events get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := Loc) frameDecoderMu _ as HframeDecoderMu
  wp_apply wp_GlobalAlloc (V := GoFunc) frameDecoder _ as HframeDecoder
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalidEventType _ as HErrInvalidEventType
  wp_apply (_root_.Perennial.github_com.tangledbytes.go_vsr.pkg.log.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.github_com.tangledbytes.go_vsr.pkg.ipv4port.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.Dsv.initLb_of_spec pkg_id.encoding.json _root_.Perennial.encoding.json.initialize'
      _root_.Perennial.encoding.json.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrInvalidEventType))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrInvalidEventType ⟨#_, #MErrInvalidEventType⟩
  -- translated initializer of frameDecoderMu))
  imod (mono_list_own_alloc (GF := GF) ([] : List Unit)) with ⟨%γh, Ha, -⟩
  imod _root_.Perennial.sync.init_Mutex (hookLockInvFull (GF := GF) γh) ⊤ _ $$ «$r0» [HframeDecoder Ha] with #Hmu
  · inext; iunfold hookLockInvFull; iexists _; iframe HframeDecoder; ileft; iframe Ha; ipureintro; rfl
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HframeDecoderMu with #HframeDecoderMu
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  iunfold hookKnownFull
  iexists γh
  iunfold hookState
  iexists _
  iframe HframeDecoderMu
  iexact Hmu

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.tangledbytes.go_vsr.pkg.events get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.tangledbytes.go_vsr.pkg.events

end init

end Perennial
