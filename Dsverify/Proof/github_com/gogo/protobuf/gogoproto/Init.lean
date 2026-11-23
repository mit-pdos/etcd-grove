/-
Package initialization of `github_com.gogo.protobuf.gogoproto`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return.
-/
module

public import Dsverify.Proof.github_com.gogo.protobuf.gogoproto.Base
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
namespace github_com.gogo.protobuf.gogoproto
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `github_com.gogo.protobuf.gogoproto`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([«_».init,
        «_».init,
        «_».init,
        E_GoprotoEnumPrefix.init,
        E_GoprotoEnumStringer.init,
        E_EnumStringer.init,
        E_EnumCustomname.init,
        E_Enumdecl.init,
        E_EnumvalueCustomname.init,
        E_GoprotoGettersAll.init,
        E_GoprotoEnumPrefixAll.init,
        E_GoprotoStringerAll.init,
        E_VerboseEqualAll.init,
        E_FaceAll.init,
        E_GostringAll.init,
        E_PopulateAll.init,
        E_StringerAll.init,
        E_OnlyoneAll.init,
        E_EqualAll.init,
        E_DescriptionAll.init,
        E_TestgenAll.init,
        E_BenchgenAll.init,
        E_MarshalerAll.init,
        E_UnmarshalerAll.init,
        E_StableMarshalerAll.init,
        E_SizerAll.init,
        E_GoprotoEnumStringerAll.init,
        E_EnumStringerAll.init,
        E_UnsafeMarshalerAll.init,
        E_UnsafeUnmarshalerAll.init,
        E_GoprotoExtensionsMapAll.init,
        E_GoprotoUnrecognizedAll.init,
        E_GogoprotoImport.init,
        E_ProtosizerAll.init,
        E_CompareAll.init,
        E_TypedeclAll.init,
        E_EnumdeclAll.init,
        E_GoprotoRegistration.init,
        E_MessagenameAll.init,
        E_GoprotoSizecacheAll.init,
        E_GoprotoUnkeyedAll.init,
        E_GoprotoGetters.init,
        E_GoprotoStringer.init,
        E_VerboseEqual.init,
        E_Face.init,
        E_Gostring.init,
        E_Populate.init,
        E_Stringer.init,
        E_Onlyone.init,
        E_Equal.init,
        E_Description.init,
        E_Testgen.init,
        E_Benchgen.init,
        E_Marshaler.init,
        E_Unmarshaler.init,
        E_StableMarshaler.init,
        E_Sizer.init,
        E_UnsafeMarshaler.init,
        E_UnsafeUnmarshaler.init,
        E_GoprotoExtensionsMap.init,
        E_GoprotoUnrecognized.init,
        E_Protosizer.init,
        E_Compare.init,
        E_Typedecl.init,
        E_Messagename.init,
        E_GoprotoSizecache.init,
        E_GoprotoUnkeyed.init,
        E_Nullable.init,
        E_Embed.init,
        E_Customtype.init,
        E_Customname.init,
        E_Jsontag.init,
        E_Moretags.init,
        E_Casttype.init,
        E_Castkey.init,
        E_Castvalue.init,
        E_Stdtime.init,
        E_Stdduration.init,
        E_Wktpointer.init,
        fileDescriptor_592445b5231bc2b9.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `github_com.gogo.protobuf.gogoproto`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end github_com.gogo.protobuf.gogoproto
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.gogo.protobuf.gogoproto.Assumptions]

namespace github_com.gogo.protobuf.gogoproto

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.gogo.protobuf.gogoproto get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.gogo.protobuf.gogoproto }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoEnumPrefix.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoEnumStringer.init (by mem_tac))
  wp_apply (opaqueInitsOk E_EnumStringer.init (by mem_tac))
  wp_apply (opaqueInitsOk E_EnumCustomname.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Enumdecl.init (by mem_tac))
  wp_apply (opaqueInitsOk E_EnumvalueCustomname.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoGettersAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoEnumPrefixAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoStringerAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_VerboseEqualAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_FaceAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GostringAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_PopulateAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_StringerAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_OnlyoneAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_EqualAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_DescriptionAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_TestgenAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_BenchgenAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_MarshalerAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_UnmarshalerAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_StableMarshalerAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_SizerAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoEnumStringerAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_EnumStringerAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_UnsafeMarshalerAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_UnsafeUnmarshalerAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoExtensionsMapAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoUnrecognizedAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GogoprotoImport.init (by mem_tac))
  wp_apply (opaqueInitsOk E_ProtosizerAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_CompareAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_TypedeclAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_EnumdeclAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoRegistration.init (by mem_tac))
  wp_apply (opaqueInitsOk E_MessagenameAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoSizecacheAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoUnkeyedAll.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoGetters.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoStringer.init (by mem_tac))
  wp_apply (opaqueInitsOk E_VerboseEqual.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Face.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Gostring.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Populate.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Stringer.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Onlyone.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Equal.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Description.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Testgen.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Benchgen.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Marshaler.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Unmarshaler.init (by mem_tac))
  wp_apply (opaqueInitsOk E_StableMarshaler.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Sizer.init (by mem_tac))
  wp_apply (opaqueInitsOk E_UnsafeMarshaler.init (by mem_tac))
  wp_apply (opaqueInitsOk E_UnsafeUnmarshaler.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoExtensionsMap.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoUnrecognized.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Protosizer.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Compare.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Typedecl.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Messagename.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoSizecache.init (by mem_tac))
  wp_apply (opaqueInitsOk E_GoprotoUnkeyed.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Nullable.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Embed.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Customtype.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Customname.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Jsontag.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Moretags.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Casttype.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Castkey.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Castvalue.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Stdtime.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Stdduration.init (by mem_tac))
  wp_apply (opaqueInitsOk E_Wktpointer.init (by mem_tac))
  wp_apply (opaqueInitsOk fileDescriptor_592445b5231bc2b9.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  wp_apply (initFuncsOk init.«1» (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.gogo.protobuf.gogoproto get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.gogo.protobuf.gogoproto }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.gogo.protobuf.gogoproto

end init

end Perennial
