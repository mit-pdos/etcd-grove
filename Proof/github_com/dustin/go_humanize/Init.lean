/-
Package initialization of `github_com.dustin.go_humanize`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
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

section opaqueInits
namespace github_com.dustin.go_humanize
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `github_com.dustin.go_humanize`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([bigIECExp.init,
        BigByte.init,
        BigKiByte.init,
        BigMiByte.init,
        BigGiByte.init,
        BigTiByte.init,
        BigPiByte.init,
        BigEiByte.init,
        BigZiByte.init,
        BigYiByte.init,
        BigRiByte.init,
        BigQiByte.init,
        bigSIExp.init,
        BigSIByte.init,
        BigKByte.init,
        BigMByte.init,
        BigGByte.init,
        BigTByte.init,
        BigPByte.init,
        BigEByte.init,
        BigZByte.init,
        BigYByte.init,
        BigRByte.init,
        BigQByte.init,
        bigBytesSizeTable.init,
        ten.init,
        bytesSizeTable.init,
        renderFloatPrecisionMultipliers.init,
        renderFloatPrecisionRounders.init,
        siPrefixTable.init,
        minSIExponent.init,
        siParseAliases.init,
        revSIPrefixTable.init,
        errInvalid.init,
        defaultMagnitudes.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `github_com.dustin.go_humanize`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end github_com.dustin.go_humanize
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.dustin.go_humanize.Assumptions]

namespace github_com.dustin.go_humanize

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.dustin.go_humanize get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.dustin.go_humanize }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk bigIECExp.init (by mem_tac))
  wp_apply (opaqueInitsOk BigByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigKiByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigMiByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigGiByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigTiByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigPiByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigEiByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigZiByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigYiByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigRiByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigQiByte.init (by mem_tac))
  wp_apply (opaqueInitsOk bigSIExp.init (by mem_tac))
  wp_apply (opaqueInitsOk BigSIByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigKByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigMByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigGByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigTByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigPByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigEByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigZByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigYByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigRByte.init (by mem_tac))
  wp_apply (opaqueInitsOk BigQByte.init (by mem_tac))
  wp_apply (opaqueInitsOk bigBytesSizeTable.init (by mem_tac))
  wp_apply (opaqueInitsOk ten.init (by mem_tac))
  wp_apply (opaqueInitsOk bytesSizeTable.init (by mem_tac))
  wp_apply (opaqueInitsOk renderFloatPrecisionMultipliers.init (by mem_tac))
  wp_apply (opaqueInitsOk renderFloatPrecisionRounders.init (by mem_tac))
  wp_apply (opaqueInitsOk siPrefixTable.init (by mem_tac))
  wp_apply (opaqueInitsOk minSIExponent.init (by mem_tac))
  wp_apply (opaqueInitsOk siParseAliases.init (by mem_tac))
  wp_apply (opaqueInitsOk revSIPrefixTable.init (by mem_tac))
  wp_apply (opaqueInitsOk errInvalid.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultMagnitudes.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.dustin.go_humanize get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.dustin.go_humanize }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.dustin.go_humanize

end init

end Perennial
