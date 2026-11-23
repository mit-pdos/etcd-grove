/-
The `log/slog` specs the replica's proof takes as hypotheses (notes/dsv-vr.md, "Hypotheses":
`log/slog` has no model here, so its specs are theorem arguments, never axioms or instances).
Stated over `Spec/sloglib.lean`'s `isLogger`. Also the kit's two (`examples/vsrnet/KitLib.lean`'s
`logger()`, `slog.New(slog.DiscardHandler)`): `New.spec`, `DiscardHandler.load_spec`. These are
all of the vr proof's `log/slog` hypotheses but `Debug.spec` (`Proof/network/LibHyps.lean`).

The lab's `Harness/Proof/log/slog.lean` (lab master 915f964) proved `Logger.{Debug,Info,Warn,Error}`
for arguments `fmt.ArgsWf` allows; its replica proof (`VsrProof/Proof/replica/Log.lean`, with
`VsrProof/Proof/network/Log.lean`) then stepped through the model's `touch` (a `fmt.Stringer`
type assertion, then an `error` one) to log other values: an error with some message (its
`Error()` called) and values of types with neither a `String()` nor an `Error()` method (nothing
called). Those steps read the lab model's code, which does not exist here; so the hypotheses
below are the lab's specs at the arguments the lab proved them for (`argOk`), what the lab's
`replica.wp_logMethod` gave. Names are the lab's.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.sloglib
public import Net.Proof.models_lab.Errors

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace log.slog

section nofmt
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

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

/-- **Hypothesis** (no `log/slog` model; the lab's `New.wp_DiscardHandler`, over any handler):
`slog.New(h)` is a logger. -/
abbrev New.spec : Prop :=
  ∀ (h : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog }}
    (App (Val (@! log.slog.New)) (Val #h))
  {{ (l : Loc), RET #l; isLogger l }}

/-- **Hypothesis** (no `log/slog` model): reading the package variable `DiscardHandler`, `log/slog`
initialized, returns (some handler; the lab's package state fixed its value). -/
abbrev DiscardHandler.load_spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog }}
    (App (Val (GoInstruction (GoLoad log.slog.Handler.ty)))
      (Val #(globalAddr log.slog.DiscardHandler)))
  {{ (h : GoInterface), RET #h; True }}

end spec

end log.slog

end Perennial
