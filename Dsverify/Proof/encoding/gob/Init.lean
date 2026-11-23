/-
Package initialization of `encoding.gob`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the trusted
initializers of its variables (`X.init`, models in `TrustedCode/` that do nothing).
-/
module

public import Dsverify.Proof.encoding.gob.Base
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
variable [package_sem : _root_.Perennial.encoding.gob.Assumptions]

namespace encoding.gob

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.encoding.gob get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.encoding.gob }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_call  -- errBadUint: its trusted initializer does nothing
  wp_call  -- decArrayHelper: its trusted initializer does nothing
  wp_call  -- decSliceHelper: its trusted initializer does nothing
  wp_call  -- errBadType: its trusted initializer does nothing
  wp_call  -- errRange: its trusted initializer does nothing
  wp_call  -- decOpTable: its trusted initializer does nothing
  wp_call  -- maxIgnoreNestingDepth: its trusted initializer does nothing
  wp_call  -- emptyStructType: its trusted initializer does nothing
  wp_call  -- errBadCount: its trusted initializer does nothing
  wp_call  -- encArrayHelper: its trusted initializer does nothing
  wp_call  -- encSliceHelper: its trusted initializer does nothing
  wp_call  -- encBufferPool: its trusted initializer does nothing
  wp_call  -- encOpTable: its trusted initializer does nothing
  wp_call  -- spaceForLength: its trusted initializer does nothing
  wp_call  -- gobEncoderInterfaceType: its trusted initializer does nothing
  wp_call  -- gobDecoderInterfaceType: its trusted initializer does nothing
  wp_call  -- binaryMarshalerInterfaceType: its trusted initializer does nothing
  wp_call  -- binaryUnmarshalerInterfaceType: its trusted initializer does nothing
  wp_call  -- textMarshalerInterfaceType: its trusted initializer does nothing
  wp_call  -- textUnmarshalerInterfaceType: its trusted initializer does nothing
  wp_call  -- wireTypeType: its trusted initializer does nothing
  wp_call  -- types: its trusted initializer does nothing
  wp_call  -- idToTypeSlice: its trusted initializer does nothing
  wp_call  -- tBool: its trusted initializer does nothing
  wp_call  -- tInt: its trusted initializer does nothing
  wp_call  -- tUint: its trusted initializer does nothing
  wp_call  -- tFloat: its trusted initializer does nothing
  wp_call  -- tBytes: its trusted initializer does nothing
  wp_call  -- tString: its trusted initializer does nothing
  wp_call  -- tComplex: its trusted initializer does nothing
  wp_call  -- decIgnoreOpMap: its trusted initializer does nothing
  wp_call  -- tInterface: its trusted initializer does nothing
  wp_call  -- tReserved7: its trusted initializer does nothing
  wp_call  -- tReserved6: its trusted initializer does nothing
  wp_call  -- tReserved5: its trusted initializer does nothing
  wp_call  -- tReserved4: its trusted initializer does nothing
  wp_call  -- tReserved3: its trusted initializer does nothing
  wp_call  -- tReserved2: its trusted initializer does nothing
  wp_call  -- tReserved1: its trusted initializer does nothing
  wp_call  -- typeInfoMapInit: its trusted initializer does nothing
  wp_call  -- tWireType: its trusted initializer does nothing
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  -- the translated init.«1»
  wp_func_call
  wp_call
  try wp_auto
  -- the translated init.«2»
  wp_func_call
  wp_call
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.encoding.gob get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.encoding.gob }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end encoding.gob

end init

end Perennial
