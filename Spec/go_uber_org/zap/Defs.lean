/-
zap's logger vocabulary (sweep repairs 1, L1; `notes/axiom-review/zap-zero.md`): `zapLoggerOk l`,
a logger as `zap.NewNop()` builds it (`zap.nopLogger`: `NewNop`'s spec is proved over zap's code,
prove-zap3, 2026-11-21), and `zapcore.zapEntry ce`, an entry to write. Both defined (zap-z1, 2026-11-23;
until then the logger had an opaque case `zap.loggerOther` and `zapEntry` was opaque): `Logger.check` is
proved over zap's code; `CheckedEntry.Write` stays an axiom, now over a defined entry (a translator gap
blocks its proof, `Proof/go_uber_org/zap/zapcore/CheckedEntry__Write.lean`). Lean-first.
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
`WriteThenFatal`). (zap-z1, 2026-11-23: the core is the value `nopCore{}`, until then some value of type
`nopCore`, which a proof cannot call a method on.) -/
def zap.nopLoggerVal (v : go_uber_org.zap.Logger) : Prop :=
  v.core' = interface.mkOk go_uber_org.zap.zapcore.nopCore.ty #go_uber_org.zap.zapcore.nopCore.mk ∧
  v.development' = false ∧ v.addCaller' = false ∧
  v.onPanic' = GoInterface.nil ∧ v.onFatal' = GoInterface.nil

/-- **`l` is a logger as `zap.NewNop()` builds it** (persistent; prove-zap3): the fields of a
`nopLoggerVal` (core a `nopCore`, not development, no caller, default terminal hooks), never written
afterwards. Stated over the fields (whose types need no package assumptions) rather than the struct.
What `zapLoggerOk` holds of a logger. -/
def zap.nopLogger (l : Loc) : IProp GF :=
  iprop(l.[go_uber_org.zap.Logger, go!"core"] ↦□
      interface.mkOk go_uber_org.zap.zapcore.nopCore.ty #go_uber_org.zap.zapcore.nopCore.mk ∗
    l.[go_uber_org.zap.Logger, go!"development"] ↦□ false ∗
    l.[go_uber_org.zap.Logger, go!"addCaller"] ↦□ false ∗
    l.[go_uber_org.zap.Logger, go!"onPanic"] ↦□ GoInterface.nil ∗
    l.[go_uber_org.zap.Logger, go!"onFatal"] ↦□ GoInterface.nil)

instance zap.nopLogger_persistent (l : Loc) : Persistent (zap.nopLogger (GF := GF) l) := by
  unfold zap.nopLogger; infer_instance

/-- **`l` is a zap logger** (persistent; sweep repairs 1, L1): non-nil, and as `zap.NewNop()` returns
it (`zap.nopLogger`; zap-z1, 2026-11-23: until then also as zap's other constructors return it, an opaque
`zap.loggerOther` no spec produced, which kept `Logger.check` a trust-boundary axiom; a theorem about a
logger with a real core brings it back with the cores' specs, #40's Z3). Given only by constructor specs (`zap.NewNop`), and carried from
there by `bootstrap`'s contract (`bootstrapContract`), the server's (`NewServer.spec`) and the
client's (`clientCfgOk`) preconditions. A zero `zap.Logger` (`&zap.Logger{}`: nil core and clock)
is not one: each logging method of it panics (`notes/axiom-review/zap-zero.md`). zap's loggers are
safe for concurrent use. Every logging method's spec requires it but `Logger.Panic`'s, which asks `l ≠ null`
(`zapLoggerOk_ne_null`; premise fixes 6). -/
def zapLoggerOk (l : Loc) : IProp GF := iprop(⌜l ≠ null⌝ ∗ □ zap.nopLogger l)

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

/-- **An entry to write** (exclusive; sweep repairs 1, L1; defined, zap-z1, 2026-11-23: until then
opaque): `ce` points to a `*zapcore.CheckedEntry` that `Write` writes without effect -- not yet written
(`dirty` false), with no `before` hooks, no cores and no `after` hook; its `Entry` and `ErrorOutput` any.
`CheckedEntry.Write` consumes it (marks it written and returns it to zapcore's `_cePool`). A second `Write`
of the same entry reports the re-use to the entry's `ErrorOutput` (`zapcore/entry.go:251-263`), which this
excludes; so does an entry at `DPanicLevel` (under `Development()`) or `PanicLevel`, whose `after` hook
panics, and one with a core, whose `Write` this does not model. No spec produces one: `Logger.check` of a
`NewNop` logger returns `nil` below `DPanicLevel` (its core is disabled). Not persistent, not duplicable. -/
def zapcore.zapEntry (ce : Loc) : IProp GF :=
  iprop(∃ v : go_uber_org.zap.zapcore.CheckedEntry, ce ↦ v ∗
    ⌜v.dirty' = false ∧ v.after' = GoInterface.nil ∧ sint.Z v.before'.len = 0 ∧
      sint.Z v.cores'.len = 0⌝)

end defs

end EtcdGrove
end Perennial
