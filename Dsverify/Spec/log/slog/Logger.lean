/-
The specs of `log/slog` (the model `models/log/slog`, translated with its bodies into the part;
proved in `Dsverify/Proof/log/slog/Logger.lean`), the ones the vr kit calls (notes/dsv-vr.md):
`New`, the package variable `DiscardHandler`, `Logger.{Debug,Info,Warn,Error}` and the
package-level `Debug`.

**Narrowed to `DiscardHandler`**: `New(h)` panics in Go for `h = nil` (and, in the model, for any
handler other than `DiscardHandler`), so `New.spec` is stated at `dhV`, `DiscardHandler`'s value
(`Base.lean`), which `DiscardHandler.load_spec` returns; a logger (`isLogger l`) is one whose
handler is `dhV`, read-only for good. A `DiscardHandler` logger's methods return at once (its
`Enabled` is false), and so does the package-level `Debug` (the default logger's handler is
enabled from `LevelInfo` up; the model has no `SetDefault`, Go's own default is at `LevelInfo` too).

The logging calls take their arguments as `argOk` values (the lab's vocabulary,
`Harness/Proof/log/slog.lean`, lab master 915f964: `nil` or `fmt.ArgWf`, an error with some
message, or a value with neither a `String()` nor an `Error()` method): a premise the proofs do not
use (a discard handler formats nothing), kept as the vr proofs' call sites state it.
-/
module

public import Dsverify.Proof.log.slog.Base
public import Net.Proof.models_lab.Errors

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace log.slog

section nofmt
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- A value of a type with neither a `String()` nor an `Error()` method (the lab's
`replica.NoFmtArg`, over `fmt.Stringer` for the lab model's `stringer`). -/
def NoFmtArg (v : GoInterface) : Prop :=
  ∀ ii, v = interface.ok ii →
    go.typeSetContains ii.ty fmt.Stringer.ty = false ∧ go.typeSetContains ii.ty go.error = false

end nofmt

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A log argument (persistent): `nil` or `fmt.ArgWf`-ok, an error with some message
(`models_lab.errAny`, the lab's `net.rpc.errAny`), or a value without formatting methods. -/
def argOk (v : GoInterface) : IProp GF :=
  iprop(⌜∀ ii, v = interface.ok ii → fmt.ArgWf ii⌝ ∨ models_lab.errAny (GF := GF) v ∨ ⌜NoFmtArg v⌝)

instance argOk_persistent (v : GoInterface) : Persistent (argOk (GF := GF) v) := by
  unfold argOk; infer_instance

/-- The `*Logger` `l`, its handler `DiscardHandler`'s value for good (persistent). -/
def isLogger (l : Loc) : IProp GF :=
  iprop(structFieldRef log.slog.Logger go!"handler" l ↦□ dhV)

instance isLogger_persistent (l : Loc) : Persistent (isLogger (GF := GF) l) := by
  unfold isLogger; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : log.slog.Assumptions]

/-- `l.<meth>(msg, args...)` on a logger, its arguments log arguments (`argOk`). -/
abbrev Logger.method.spec (meth : GoString) : Prop :=
  ∀ (l : Loc) (msg : GoString) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog ∗ log.slog.isLogger l ∗ arg ↦*{dq} xs ∗
        [∗list] x ∈ xs, argOk (GF := GF) x }}
      (App (App (Val (l @!! go.GoType.PointerType log.slog.Logger.ty @!! meth)) (Val #msg))
        (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}

/-- `l.Debug(msg, args...)`. -/
abbrev Logger.Debug.spec : Prop := Logger.method.spec (GF := GF) (hG := hG) go!"Debug"
/-- `l.Info(msg, args...)`. -/
abbrev Logger.Info.spec : Prop := Logger.method.spec (GF := GF) (hG := hG) go!"Info"
/-- `l.Warn(msg, args...)`. -/
abbrev Logger.Warn.spec : Prop := Logger.method.spec (GF := GF) (hG := hG) go!"Warn"
/-- `l.Error(msg, args...)`. -/
abbrev Logger.Error.spec : Prop := Logger.method.spec (GF := GF) (hG := hG) go!"Error"

/-- `slog.New(DiscardHandler)` is a logger (Go's `New(nil)` panics: the spec is at `dhV`, the
handler the vr kit passes). -/
abbrev New.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog }}
    (App (Val (@! log.slog.New)) (Val #dhV))
  {{ (l : Loc), RET #l; isLogger l }}

/-- Reading the package variable `DiscardHandler`, `log/slog` initialized, returns `dhV`. -/
abbrev DiscardHandler.load_spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog }}
    (App (Val (GoInstruction (GoLoad log.slog.Handler.ty)))
      (Val #(globalAddr log.slog.DiscardHandler)))
  {{ (h : GoInterface), RET #h; ⌜h = dhV⌝ }}

/-- `slog.Debug(msg, args...)` (package-level, the default logger), its arguments `argOk`. -/
abbrev Debug.spec : Prop :=
  ∀ (msg : GoString) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog ∗ arg ↦*{dq} xs ∗
      [∗list] x ∈ xs, argOk (GF := GF) x }}
    (App (App (Val (@! log.slog.Debug)) (Val #msg)) (Val #arg))
  {{ RET #(); arg ↦*{dq} xs }}

end spec

end log.slog

end Perennial
