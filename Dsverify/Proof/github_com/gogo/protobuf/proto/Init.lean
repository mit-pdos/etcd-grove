/-
Package initialization of `github_com.gogo.protobuf.proto`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return.
-/
module

public import Dsverify.Proof.github_com.gogo.protobuf.proto.Base
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

section opaqueInits
namespace github_com.gogo.protobuf.proto
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `github_com.gogo.protobuf.proto`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([customType.init,
        errOverflow.init,
        ErrInternalBadWireType.init,
        discardInfoMap.init,
        durationType.init,
        errRepeatedHasNil.init,
        errOneofHasNil.init,
        ErrNil.init,
        ErrTooLarge.init,
        ErrMissingExtension.init,
        errNotExtendable.init,
        extProp.init,
        extensionMaps.init,
        errInvalidUTF8.init,
        defaults.init,
        int32PtrType.init,
        errNoMessageTypeID.init,
        «_».init,
        ptrSize.init,
        protoMessageType.init,
        marshalerType.init,
        propertiesMap.init,
        enumValueMaps.init,
        enumStringMaps.init,
        protoTypedNils.init,
        protoMapTypes.init,
        revProtoTypes.init,
        protoFiles.init,
        sizerType.init,
        protosizerType.init,
        marshalInfoMap.init,
        uint8SliceType.init,
        mergeInfoMap.init,
        unmarshalInfoMap.init,
        errInternalBadWireType.init,
        newline.init,
        spaces.init,
        endBraceNewline.init,
        backslashN.init,
        backslashR.init,
        backslashT.init,
        backslashDQ.init,
        backslashBS.init,
        posInf.init,
        negInf.init,
        nan.init,
        textMarshalerType.init,
        defaultTextMarshaler.init,
        compactTextMarshaler.init,
        errBadUTF8.init,
        timeType.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `github_com.gogo.protobuf.proto`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1», init.«2»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end github_com.gogo.protobuf.proto
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.gogo.protobuf.proto.Assumptions]

namespace github_com.gogo.protobuf.proto

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.gogo.protobuf.proto get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.gogo.protobuf.proto }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk customType.init (by mem_tac))
  wp_apply (opaqueInitsOk errOverflow.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrInternalBadWireType.init (by mem_tac))
  wp_apply (opaqueInitsOk discardInfoMap.init (by mem_tac))
  wp_apply (opaqueInitsOk durationType.init (by mem_tac))
  wp_apply (opaqueInitsOk errRepeatedHasNil.init (by mem_tac))
  wp_apply (opaqueInitsOk errOneofHasNil.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNil.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTooLarge.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMissingExtension.init (by mem_tac))
  wp_apply (opaqueInitsOk errNotExtendable.init (by mem_tac))
  wp_apply (opaqueInitsOk extProp.init (by mem_tac))
  wp_apply (opaqueInitsOk extensionMaps.init (by mem_tac))
  wp_apply (opaqueInitsOk errInvalidUTF8.init (by mem_tac))
  wp_apply (opaqueInitsOk defaults.init (by mem_tac))
  wp_apply (opaqueInitsOk int32PtrType.init (by mem_tac))
  wp_apply (opaqueInitsOk errNoMessageTypeID.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk ptrSize.init (by mem_tac))
  wp_apply (opaqueInitsOk protoMessageType.init (by mem_tac))
  wp_apply (opaqueInitsOk marshalerType.init (by mem_tac))
  wp_apply (opaqueInitsOk propertiesMap.init (by mem_tac))
  wp_apply (opaqueInitsOk enumValueMaps.init (by mem_tac))
  wp_apply (opaqueInitsOk enumStringMaps.init (by mem_tac))
  wp_apply (opaqueInitsOk protoTypedNils.init (by mem_tac))
  wp_apply (opaqueInitsOk protoMapTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk revProtoTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk protoFiles.init (by mem_tac))
  wp_apply (opaqueInitsOk sizerType.init (by mem_tac))
  wp_apply (opaqueInitsOk protosizerType.init (by mem_tac))
  wp_apply (opaqueInitsOk marshalInfoMap.init (by mem_tac))
  wp_apply (opaqueInitsOk uint8SliceType.init (by mem_tac))
  wp_apply (opaqueInitsOk mergeInfoMap.init (by mem_tac))
  wp_apply (opaqueInitsOk unmarshalInfoMap.init (by mem_tac))
  wp_apply (opaqueInitsOk errInternalBadWireType.init (by mem_tac))
  wp_apply (opaqueInitsOk newline.init (by mem_tac))
  wp_apply (opaqueInitsOk spaces.init (by mem_tac))
  wp_apply (opaqueInitsOk endBraceNewline.init (by mem_tac))
  wp_apply (opaqueInitsOk backslashN.init (by mem_tac))
  wp_apply (opaqueInitsOk backslashR.init (by mem_tac))
  wp_apply (opaqueInitsOk backslashT.init (by mem_tac))
  wp_apply (opaqueInitsOk backslashDQ.init (by mem_tac))
  wp_apply (opaqueInitsOk backslashBS.init (by mem_tac))
  wp_apply (opaqueInitsOk posInf.init (by mem_tac))
  wp_apply (opaqueInitsOk negInf.init (by mem_tac))
  wp_apply (opaqueInitsOk nan.init (by mem_tac))
  wp_apply (opaqueInitsOk textMarshalerType.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultTextMarshaler.init (by mem_tac))
  wp_apply (opaqueInitsOk compactTextMarshaler.init (by mem_tac))
  wp_apply (opaqueInitsOk errBadUTF8.init (by mem_tac))
  wp_apply (opaqueInitsOk timeType.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  wp_apply (initFuncsOk init.«1» (by mem_tac))
  wp_apply (initFuncsOk init.«2» (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.gogo.protobuf.proto get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.gogo.protobuf.proto }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.gogo.protobuf.proto

end init

end Perennial
