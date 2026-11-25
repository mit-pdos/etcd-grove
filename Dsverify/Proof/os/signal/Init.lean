/-
Package initialization of `os.signal`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer allocates `handlers`, `watchSignalLoopOnce` and
`watchSignalLoop` (zero values), initializes its imports `os` and `sync`, and runs its `init`, which
stores the function value `loop` (not called) in `watchSignalLoop`.
-/
module

public import Dsverify.Proof.os.signal.Base
public import Perennial.Proof.sync.Link
public import Proof.os.Init
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
variable [package_sem : _root_.Perennial.os.signal.Assumptions]

namespace os.signal

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.os.signal get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.os.signal }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoFunc) watchSignalLoop _ as HwatchSignalLoop
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.Once) watchSignalLoopOnce _ as HwatchSignalLoopOnce
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.os.signal.«struct#c69a5a71») handlers _ as Hhandlers
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.os.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.os.signal get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.os.signal }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end os.signal

end init

end Perennial
