/-
Package initialization of `github_com.rs.zerolog`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.Base
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
namespace github_com.rs.zerolog
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `github_com.rs.zerolog`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([arrayPool.init,
        consoleBufPool.init,
        th.init,
        ch.init,
        «_».init,
        enc.init,
        eventPool.init,
        TimestampFieldName.init,
        LevelFieldName.init,
        LevelTraceValue.init,
        LevelDebugValue.init,
        LevelInfoValue.init,
        LevelWarnValue.init,
        LevelErrorValue.init,
        LevelFatalValue.init,
        LevelPanicValue.init,
        LevelFieldMarshalFunc.init,
        MessageFieldName.init,
        ErrorFieldName.init,
        CallerFieldName.init,
        CallerSkipFrameCount.init,
        CallerMarshalFunc.init,
        ErrorStackFieldName.init,
        ErrorMarshalFunc.init,
        InterfaceMarshalFunc.init,
        TimeFieldFormat.init,
        TimestampFunc.init,
        DurationFieldUnit.init,
        DurationFieldInteger.init,
        gLevel.init,
        disableSampling.init,
        Often.init,
        Sometimes.init,
        Rarely.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `github_com.rs.zerolog`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end github_com.rs.zerolog
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.rs.zerolog.Assumptions]

namespace github_com.rs.zerolog

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.rs.zerolog get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk arrayPool.init (by mem_tac))
  wp_apply (opaqueInitsOk consoleBufPool.init (by mem_tac))
  wp_apply (opaqueInitsOk th.init (by mem_tac))
  wp_apply (opaqueInitsOk ch.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk enc.init (by mem_tac))
  wp_apply (opaqueInitsOk eventPool.init (by mem_tac))
  wp_apply (opaqueInitsOk TimestampFieldName.init (by mem_tac))
  wp_apply (opaqueInitsOk LevelFieldName.init (by mem_tac))
  wp_apply (opaqueInitsOk LevelTraceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk LevelDebugValue.init (by mem_tac))
  wp_apply (opaqueInitsOk LevelInfoValue.init (by mem_tac))
  wp_apply (opaqueInitsOk LevelWarnValue.init (by mem_tac))
  wp_apply (opaqueInitsOk LevelErrorValue.init (by mem_tac))
  wp_apply (opaqueInitsOk LevelFatalValue.init (by mem_tac))
  wp_apply (opaqueInitsOk LevelPanicValue.init (by mem_tac))
  wp_apply (opaqueInitsOk LevelFieldMarshalFunc.init (by mem_tac))
  wp_apply (opaqueInitsOk MessageFieldName.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrorFieldName.init (by mem_tac))
  wp_apply (opaqueInitsOk CallerFieldName.init (by mem_tac))
  wp_apply (opaqueInitsOk CallerSkipFrameCount.init (by mem_tac))
  wp_apply (opaqueInitsOk CallerMarshalFunc.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrorStackFieldName.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrorMarshalFunc.init (by mem_tac))
  wp_apply (opaqueInitsOk InterfaceMarshalFunc.init (by mem_tac))
  wp_apply (opaqueInitsOk TimeFieldFormat.init (by mem_tac))
  wp_apply (opaqueInitsOk TimestampFunc.init (by mem_tac))
  wp_apply (opaqueInitsOk DurationFieldUnit.init (by mem_tac))
  wp_apply (opaqueInitsOk DurationFieldInteger.init (by mem_tac))
  wp_apply (opaqueInitsOk gLevel.init (by mem_tac))
  wp_apply (opaqueInitsOk disableSampling.init (by mem_tac))
  wp_apply (opaqueInitsOk Often.init (by mem_tac))
  wp_apply (opaqueInitsOk Sometimes.init (by mem_tac))
  wp_apply (opaqueInitsOk Rarely.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  wp_apply (initFuncsOk init.«1» (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.rs.zerolog get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.rs.zerolog

end init

end Perennial
