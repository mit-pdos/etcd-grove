/-
Package initialization of `go_uber_org.zap`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.go_uber_org.zap.zapcore.Init

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

section opaqueInits
namespace go_uber_org.zap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_uber_org.zap`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([errNoEncoderNameSpecified.init,
        _encoderNameToConstructor.init,
        _errArrayElemPool.init,
        _minTimeInt64.init,
        _maxTimeInt64.init,
        _globalL.init,
        _globalS.init,
        «_».init,
        _sinkRegistry.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end go_uber_org.zap
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_uber_org.zap.Assumptions]

namespace go_uber_org.zap

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_uber_org.zap get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply _root_.Perennial.go_uber_org.zap.zapcore.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk errNoEncoderNameSpecified.init (by mem_tac))
  wp_apply (opaqueInitsOk _encoderNameToConstructor.init (by mem_tac))
  wp_apply (opaqueInitsOk _errArrayElemPool.init (by mem_tac))
  wp_apply (opaqueInitsOk _minTimeInt64.init (by mem_tac))
  wp_apply (opaqueInitsOk _maxTimeInt64.init (by mem_tac))
  wp_apply (opaqueInitsOk _globalL.init (by mem_tac))
  wp_apply (opaqueInitsOk _globalS.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk _sinkRegistry.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish


end go_uber_org.zap

end init

end Perennial
