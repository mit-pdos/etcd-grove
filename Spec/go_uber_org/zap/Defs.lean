/-
zap's logger vocabulary (sweep repairs 1, L1; `notes/axiom-review/zap-zero.md`): `zapLoggerOk l`,
a logger as zap's constructors build it, and `zapcore.zapEntry ce`, an entry `Logger.Check` returned
and not yet written. The trust boundary (zap is names-only): both are opaque at the bottom, given
only by zap's constructor specs (`zap.NewNop`) and `Logger.Check`. Lean-first.
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

/-- `zapLoggerOk`'s fact, raw (opaque). What it means: `l` points to a `zap.Logger` struct as one of
zap's constructors leaves it (`zap.New`, `NewNop`, `NewProduction`, `NewDevelopment`, `NewExample`,
`Config.Build`, and the derivations `Named`, `With`, `WithOptions` with `AddCaller*`/`AddStacktrace`/
`Development`), never written afterwards: its `core` one of zap's own (`nopCore`, `ioCore` over a
non-nil encoder, write syncer and level enabler, and `multiCore`, `levelFilterCore`, `sampler` of
such; not `Hooks`' `hooked` nor a user core), its `clock`, `errorOutput` and `addStack` non-nil, its
terminal hooks the defaults (`onFatal`/`onPanic` nil, `WriteThenNoop`, or
`WriteThenFatal`/`WriteThenPanic`). Go check: `examples/sweeprepairs/logger` (`ZapLoggerOk`). -/
opaque zap.loggerRaw (l : Loc) : IProp GF

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
