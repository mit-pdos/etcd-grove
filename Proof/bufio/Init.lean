/-
Package initialization of `bufio`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Proof.bufio.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.errors.NewVar
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
variable [package_sem : _root_.Perennial.bufio.Assumptions]

namespace bufio

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.bufio get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := _) ErrFinalToken _ as HErrFinalToken
  wp_apply wp_GlobalAlloc (V := _) ErrBadReadCount _ as HErrBadReadCount
  wp_apply wp_GlobalAlloc (V := _) ErrAdvanceTooFar _ as HErrAdvanceTooFar
  wp_apply wp_GlobalAlloc (V := _) ErrNegativeAdvance _ as HErrNegativeAdvance
  wp_apply wp_GlobalAlloc (V := _) ErrTooLong _ as HErrTooLong
  wp_apply wp_GlobalAlloc (V := _) errNegativeWrite _ as HerrNegativeWrite
  wp_apply wp_GlobalAlloc (V := _) errNegativeRead _ as HerrNegativeRead
  wp_apply wp_GlobalAlloc (V := _) ErrNegativeCount _ as HErrNegativeCount
  wp_apply wp_GlobalAlloc (V := _) ErrBufferFull _ as HErrBufferFull
  wp_apply wp_GlobalAlloc (V := _) ErrInvalidUnreadRune _ as HErrInvalidUnreadRune
  wp_apply wp_GlobalAlloc (V := _) ErrInvalidUnreadByte _ as HErrInvalidUnreadByte
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrInvalidUnreadByte))
  -- translated initializer of ErrInvalidUnreadRune))
  -- translated initializer of ErrBufferFull))
  -- translated initializer of ErrNegativeCount))
  -- translated initializer of errNegativeRead))
  -- translated initializer of errNegativeWrite))
  -- translated initializer of ErrTooLong))
  -- translated initializer of ErrNegativeAdvance))
  -- translated initializer of ErrAdvanceTooFar))
  -- translated initializer of ErrBadReadCount))
  -- translated initializer of ErrFinalToken))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x0 ⟨#_, #E0⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x1 ⟨#_, #E1⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x2 ⟨#_, #E2⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x3 ⟨#_, #E3⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x4 ⟨#_, #E4⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x5 ⟨#_, #E5⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x6 ⟨#_, #E6⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x7 ⟨#_, #E7⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x8 ⟨#_, #E8⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x9 ⟨#_, #E9⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x10 ⟨#_, #E10⟩
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.bufio get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end bufio

end init

end Perennial
