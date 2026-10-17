/-
Package initialization of `google_golang_org.protobuf.reflect.protoreflect`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

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
namespace google_golang_org.protobuf.reflect.protoreflect
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `google_golang_org.protobuf.reflect.protoreflect`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([nilType.init,
        boolType.init,
        int32Type.init,
        int64Type.init,
        uint32Type.init,
        uint64Type.init,
        float32Type.init,
        float64Type.init,
        stringType.init,
        bytesType.init,
        enumType.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end google_golang_org.protobuf.reflect.protoreflect
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.google_golang_org.protobuf.reflect.protoreflect.Assumptions]

namespace google_golang_org.protobuf.reflect.protoreflect

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.protobuf.reflect.protoreflect get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk nilType.init (by mem_tac))
  wp_apply (opaqueInitsOk boolType.init (by mem_tac))
  wp_apply (opaqueInitsOk int32Type.init (by mem_tac))
  wp_apply (opaqueInitsOk int64Type.init (by mem_tac))
  wp_apply (opaqueInitsOk uint32Type.init (by mem_tac))
  wp_apply (opaqueInitsOk uint64Type.init (by mem_tac))
  wp_apply (opaqueInitsOk float32Type.init (by mem_tac))
  wp_apply (opaqueInitsOk float64Type.init (by mem_tac))
  wp_apply (opaqueInitsOk stringType.init (by mem_tac))
  wp_apply (opaqueInitsOk bytesType.init (by mem_tac))
  wp_apply (opaqueInitsOk enumType.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish


end google_golang_org.protobuf.reflect.protoreflect

end init

end Perennial
