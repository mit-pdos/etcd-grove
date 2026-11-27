/-
Package initialization of `internal.runtime.sys`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True` (Perennial's `isPkgInit`). Its initializer allocates its variables and runs
their translated initializers (`intrinsics.go`: the array literals `deBruijn32tab` and `deBruijn64tab`;
`no_dit.go`, off arm64: `DITSupported = false`). (Until 2026-11-27 names-only, with the trust-boundary
axiom `opaqueInitsOk`.)
-/
module

public import Perennial.Proof.internal.runtime.sys.Base
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
variable [package_sem : _root_.Perennial.internal.runtime.sys.Assumptions]

namespace internal.runtime.sys

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.internal.runtime.sys get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.internal.runtime.sys }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := Bool) DITSupported _ as HDITSupported
  wp_apply wp_GlobalAlloc (V := GoArray w8 64) deBruijn64tab _ as HdeBruijn64tab
  wp_apply wp_GlobalAlloc (V := GoArray w8 32) deBruijn32tab _ as HdeBruijn32tab
  -- translated initializer of deBruijn32tab))
  -- translated initializer of deBruijn64tab))
  -- translated initializer of DITSupported))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.internal.runtime.sys get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.internal.runtime.sys }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end internal.runtime.sys

end init

end Perennial
