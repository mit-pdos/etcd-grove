/-
zap's logger vocabulary (sweep repairs 1, L1; `notes/axiom-review/zap-zero.md`): `zapLoggerOk l`,
a logger as zap's constructors build it, and `zapcore.zapEntry ce`, an entry `Logger.Check` returned
and not yet written. A logger is `zap.NewNop()`'s (`zap.nopLogger`, defined: `NewNop`'s spec is
proved over zap's code, prove-zap3, 2026-11-21) or another constructor's (`zap.loggerOther`, opaque:
the trust boundary, which `Logger.check`'s axiom covers); `zapEntry` is opaque, given only by
`Logger.check`. Lean-first.
-/
module

public import GeneratedProof.go_uber_org.zap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A logger value as `zap.NewNop()` builds it** (prove-zap3, 2026-11-21; zap v1.28.0
`logger.go`, `NewNop`: `&Logger{core: zapcore.NewNopCore(), errorOutput: zapcore.AddSync(io.Discard),
addStack: zapcore.FatalLevel + 1, clock: zapcore.DefaultClock}`): its core is zapcore's `nopCore` (whose
`Enabled` is `false`, whose `Check` returns its entry argument, whose `Write` returns `nil`), it is not
in development mode, adds no caller, and its terminal hooks are the defaults (`nil`: `WriteThenPanic`,
`WriteThenFatal`). -/
def zap.nopLoggerVal (v : go_uber_org.zap.Logger) : Prop :=
  (∃ w : val, v.core' = interface.mkOk go_uber_org.zap.zapcore.nopCore.ty w) ∧
  v.development' = false ∧ v.addCaller' = false ∧
  v.onPanic' = GoInterface.nil ∧ v.onFatal' = GoInterface.nil

/-- **`l` is a logger as `zap.NewNop()` builds it** (persistent; prove-zap3): the fields of a
`nopLoggerVal` (core a `nopCore`, not development, no caller, default terminal hooks), never written
afterwards. Stated over the fields (whose types need no package assumptions) rather than the struct.
One of `zap.loggerRaw`'s two cases, the one `NewNop`'s proof gives. -/
def zap.nopLogger (l : Loc) : IProp GF :=
  iprop((∃ w : val, l.[go_uber_org.zap.Logger, go!"core"] ↦□
      interface.mkOk go_uber_org.zap.zapcore.nopCore.ty w) ∗
    l.[go_uber_org.zap.Logger, go!"development"] ↦□ false ∗
    l.[go_uber_org.zap.Logger, go!"addCaller"] ↦□ false ∗
    l.[go_uber_org.zap.Logger, go!"onPanic"] ↦□ GoInterface.nil ∗
    l.[go_uber_org.zap.Logger, go!"onFatal"] ↦□ GoInterface.nil)

instance zap.nopLogger_persistent (l : Loc) : Persistent (zap.nopLogger (GF := GF) l) := by
  unfold zap.nopLogger; infer_instance

/-- **`l` is a zap logger other than `NewNop`'s** (opaque; the trust boundary). What it means: `l`
points to a `zap.Logger` struct as one of zap's other constructors leaves it (`zap.New`,
`NewProduction`, `NewDevelopment`, `NewExample`, `Config.Build`, and the derivations `Named`, `With`,
`WithOptions` with `AddCaller*`/`AddStacktrace`/`Development`), never written afterwards: its `core`
one of zap's own (`nopCore`, `ioCore` over a non-nil encoder, write syncer and level enabler, and
`multiCore`, `levelFilterCore`, `sampler` of such; not `Hooks`' `hooked` nor a user core), its
encoders, write syncers (the `errorOutput` too) and level enablers zap's own or ones whose methods
return without panicking, its `clock`, `errorOutput` and `addStack` non-nil, its terminal hooks the
defaults (`onFatal`/`onPanic` nil, `WriteThenNoop`, or `WriteThenFatal`/`WriteThenPanic`). Go check:
`examples/sweeprepairs/logger` (`ZapLoggerOk`). (Until 2026-11-21 all of `zap.loggerRaw`, which
covered `NewNop`'s loggers too.) -/
opaque zap.loggerOther (l : Loc) : IProp GF

/-- `zapLoggerOk`'s fact, raw: a logger as `zap.NewNop()` builds it (`zap.nopLogger`, defined), or as
zap's other constructors build it (`zap.loggerOther`, opaque). (Until 2026-11-21 opaque as a whole:
prove-zap3 split `NewNop`'s case out, so that `NewNop`'s spec is proved over the real code.) -/
def zap.loggerRaw (l : Loc) : IProp GF := iprop(zap.nopLogger l ∨ zap.loggerOther l)

/-- **`l` is a zap logger** (persistent; sweep repairs 1, L1): non-nil, and as a constructor
returns it (`zap.loggerRaw`). Given only by constructor specs (`zap.NewNop`), and carried from
there by `bootstrap`'s contract (`bootstrapContract`), the server's (`NewServer.spec`) and the
client's (`clientCfgOk`) preconditions. A zero `zap.Logger` (`&zap.Logger{}`: nil core and clock)
is not one: each logging method of it panics (`notes/axiom-review/zap-zero.md`). zap's loggers are
safe for concurrent use. Every logging method's spec requires it but `Logger.Panic`'s, which asks `l ≠ null`
(`zapLoggerOk_ne_null`; premise fixes 6). -/
def zapLoggerOk (l : Loc) : IProp GF := iprop(⌜l ≠ null⌝ ∗ □ zap.loggerRaw l)

instance zapLoggerOk_persistent (l : Loc) : Persistent (zapLoggerOk (GF := GF) l) := by
  unfold zapLoggerOk; infer_instance

theorem zapLoggerOk_ne_null (l : Loc) : zapLoggerOk (GF := GF) l ⊢ ⌜l ≠ null⌝ := by
  unfold zapLoggerOk; iintro ⟨%h, -⟩; ipureintro; exact h

/-- **`l` is nil or a zap logger** (persistent; premise fixes 6): what a Go function that checks
`lg != nil` before every use, or replaces nil by `zap.NewNop()`, needs of its logger
(`auth.NewAuthStore`, `backend.New`, `mvcc.NewStore`, `traceutil.EnsureTrace`). A zero
`zap.Logger` is neither. -/
def zapLoggerOrNil (l : Loc) : IProp GF := iprop(⌜l = null⌝ ∨ zapLoggerOk l)

instance zapLoggerOrNil_persistent (l : Loc) : Persistent (zapLoggerOrNil (GF := GF) l) := by
  unfold zapLoggerOrNil; infer_instance

theorem zapLoggerOk_orNil (l : Loc) : zapLoggerOk (GF := GF) l ⊢ zapLoggerOrNil l := by
  unfold zapLoggerOrNil; iintro H; iright; iexact H

theorem zapLoggerOrNil_null : ⊢ zapLoggerOrNil (GF := GF) null := by
  unfold zapLoggerOrNil; ileft; ipureintro; rfl

/-- A non-nil logger that is nil or a zap logger is a zap logger. -/
theorem zapLoggerOrNil_ok (l : Loc) (h : l ≠ null) : zapLoggerOrNil (GF := GF) l ⊢ zapLoggerOk l := by
  unfold zapLoggerOrNil; iintro (%h' | H)
  · exact absurd h' h
  · iexact H

/-- **An entry to write** (opaque, exclusive; sweep repairs 1, L1): `ce` is a
`*zapcore.CheckedEntry` that `Logger.Check` returned non-nil, at a level below `DPanicLevel`
(`Check.spec` admits only those), not yet written. `CheckedEntry.Write` consumes it: a second
`Write` of the same entry reports the re-use to the entry's `ErrorOutput`
(`zapcore/entry.go:251-263`), which this model does not cover; an entry built by hand may carry
any `ErrorOutput`, and an entry at `DPanicLevel` (under `Development()`) or `PanicLevel` panics in
its `Write`. Not persistent, not duplicable. -/
opaque zapcore.zapEntry (ce : Loc) : IProp GF

end defs

end EtcdGrove
end Perennial
