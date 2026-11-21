/-
Package initialization of `go_uber_org.zap`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact: `_minTimeInt64` and `_maxTimeInt64` hold fixed times (prove-srvloops2, 2026-11-21: `zap.Time`
compares with them; until then `True`). Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-initleft, 2026-11-21; until then the trust-boundary axiom
`opaqueInitsOk` covered them all): `errNoEncoderNameSpecified` (`errors.New`), the encoder constructors (a
map literal of two func literals), `_errArrayElemPool` (`pool.New`, proved), `_globalL = NewNop()`
(`zapcore.NewNopCore()`, `zapcore.AddSync(io.Discard)` over any writer, `zapcore.DefaultClock` from
zapcore's fact), `_globalS = _globalL.Sugar()` (a copy of the logger) and the interface assertion
`var _ internal.LeveledEnabler = AtomicLevel{}`, and (prove-srvloops2) `_minTimeInt64`/`_maxTimeInt64`
(`time.Unix`); `_sinkRegistry` (`newSinkRegistry`) stays untranslated, `opaqueInitsOk`.
-/
module

public import Proof.go_uber_org.zap.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.go_uber_org.zap.internal.Init
public import Proof.go_uber_org.zap.internal.pool.Init
public import Proof.go_uber_org.zap.zapcore.Init
public import Perennial.Proof.errors.NewVar

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_uber_org.zap`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([_sinkRegistry.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end go_uber_org.zap
end opaqueInits

section zapinit
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_uber_org.zap.Assumptions]

/-- (prove-initleft) `zapcore.AddSync(w)` returns, whatever the writer (a type switch: `w` itself if
it is a `WriteSyncer`, else `writerWrapper{w}`). -/
theorem EtcdGrove.zap_wp_AddSync_init (w : GoInterface) :
    {{ (True : IProp GF) }} (App (Val (@! _root_.Perennial.go_uber_org.zap.zapcore.AddSync)) (Val #w))
    {{ (r : GoInterface), RET #r; True }} := by
  wp_start
  wp_auto
  rcases w with wo | _
  · wp_auto
    cases hws : go.typeSetContains wo.ty _root_.Perennial.go_uber_org.zap.zapcore.WriteSyncer.ty
    all_goals (wp_auto; iapply HΦ; itrivial)
  · wp_auto
    iapply HΦ
    itrivial

/-- (prove-initleft) `zap.NewNop()` before zap's `isPkgInit`: a new `Logger` (its body: `NewNopCore()`,
`AddSync(io.Discard)`, `zapcore.DefaultClock`, from io's and zapcore's facts). -/
theorem EtcdGrove.zap_wp_NewNop_init :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.zapcore }}
      (App (Val (@! _root_.Perennial.go_uber_org.zap.NewNop)) (Val #()))
    {{ (l : Loc), RET #l; ∃ v : _root_.Perennial.go_uber_org.zap.Logger, l ↦ v }} := by
  wp_start
  ihave #IO : (_root_.Perennial.io.isInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iNamed IO
  icases HDiscard with ⟨%wd, #HDiscard⟩
  ihave #ZC : (iprop(∃ c : _root_.Perennial.go_uber_org.zap.zapcore.systemClock, typedPointsto (globalAddr
      _root_.Perennial.go_uber_org.zap.zapcore.DefaultClock) c DFrac.discard) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg2
  icases ZC with ⟨%dc, #HDC⟩
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_apply EtcdGrove.zap_wp_AddSync_init as %ws -
  try wp_auto
  iapply HΦ
  iexists _
  iframe

/-- (prove-initleft) `l.Sugar()` on a `Logger`: a copy of it (`clone`), its caller skip plus 2. -/
theorem EtcdGrove.zap_wp_Sugar_init (l : Loc) (v : _root_.Perennial.go_uber_org.zap.Logger) :
    {{ (l ↦ v : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType _root_.Perennial.go_uber_org.zap.Logger.ty @!! go!"Sugar")) (Val #()))
    {{ (s : Loc), RET #s; l ↦ v }} := by
  wp_start as Hl
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iapply HΦ
  iframe

end zapinit
end Perennial
