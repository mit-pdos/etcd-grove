/-
`fmt.Errorf` of `pre ++ "%w"` over one error: the trust boundary (errorf-wrap, 2026-11-06). Go's
`Errorf` returns a `*fmt.wrapError` (`fmt/errors.go:46-49`), whose `Unwrap` gives the wrapped error
back, so that `errors.Is` sees it; Perennial's model of `Errorf` (`errors.New(format)`) does not
model `%w`, and a proof must not learn of Go's error a fact true only of the model's
(`notes/decisions.md`, "`fmt.Errorf` with `%w`: no fact from the model", superseded in part by H0).
The post is a disjunction, the model's error or Go's (etcd-grove-82's decision, 2026-11-06), so that
the spec is true of both and contradicts neither; the model's disjunct carries the model's own facts
(its `*errors.errorString`'s cell), Go's the facts of `*fmt.wrapError`. Since H0 (2026-11-18) a
theorem, proved from the model (`Proof/fmt/ErrorfWrap.lean`): the post's left disjunct is what the
model returns and the description conjunct is conditional on Go's `Unwrap` method. Attacked (as an
axiom): `notes/axiom-review/errorf-wrap.md`. Lean-first.
-/
module

public import Spec.fmt.Errorf
public import Spec.fmt.ErrorOk
public import Proof.errors.NewVarCell

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

/-- **Perennial's model of `fmt.Errorf`'s error, with message prefix `pre`** (`errors.New(format)`,
`format = pre ++ "%w"`): an `*errors.errorString` at `x` whose `s` field holds `pre ++ s` for good
(`errStrCell`: `errors.New` allocates it and nothing writes it again; H0, 2026-11-18) and whose
`Error()` always returns that string (stable: fromerror-stable needs it too; the model's `s` is
`"%w"`; N1a, 2026-11-06: the prefix is what both sides share). A fact of the model only, in the
model's disjunct of `fmt.errorfWrapIs`: no proof learns it of Go's error. -/
def fmt.modelErrIs (ii : GoInterfaceOk) (pre : GoString) : IProp GF :=
  iprop(∃ x : Loc, ⌜ii = ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩⌝ ∗
    ∃ s : GoString, errStrCell x (pre ++ s) ∗ □ ∀ Φ : val → IProp GF, ▷ Φ #(pre ++ s) -∗
      WP (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #())) {{ Φ }})

instance fmt.modelErrIs_persistent (ii : GoInterfaceOk) (pre : GoString) :
    Persistent (fmt.modelErrIs (GF := GF) ii pre) := by
  unfold fmt.modelErrIs; infer_instance

/-- **Go's `%w` error of `inner`**, with message prefix `pre` (a `*fmt.wrapError`, its type left
opaque): a pointer error; its method set has `Unwrap() error`, `Error() string` and no `Is`, `As`,
`GRPCStatus` or `Format` (`*wrapError` has `Error` and `Unwrap` only); `Error()` always returns one
string, `pre ++ s`
(`return e.msg`, formatted once); `Unwrap()` returns `inner` (`return e.err`). -/
def fmt.wrapErrIs (ii : GoInterfaceOk) (inner : GoInterface) (pre : GoString) : IProp GF :=
  iprop(⌜_root_.Perennial.errors.IsPointerError ii ∧
      methodSet ii.ty !! go!"Unwrap" = some (go.Signature [] false [go.error]) ∧
      methodSet ii.ty !! go!"As" ≠ some (go.Signature [go.any] false [go.bool]) ∧
      methodSet ii.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]) ∧
      methodSet ii.ty !! go!"GRPCStatus" = none ∧
      methodSet ii.ty !! go!"Format" = none ∧
      methodSet ii.ty !! go!"Error" = some noArgStringSig⌝ ∗
    (∃ s : GoString, □ ∀ Φ : val → IProp GF, ▷ Φ #(pre ++ s) -∗
      WP (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #())) {{ Φ }}) ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #inner -∗
      WP (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #())) {{ Φ }})

instance fmt.wrapErrIs_persistent (ii : GoInterfaceOk) (inner : GoInterface) (pre : GoString) :
    Persistent (fmt.wrapErrIs (GF := GF) ii inner pre) := by
  unfold fmt.wrapErrIs; infer_instance

/-- **`fmt.Errorf(pre ++ "%w", inner)`'s error**: the model's or Go's. -/
def fmt.errorfWrapIs (ii : GoInterfaceOk) (inner : GoInterface) (pre : GoString) : IProp GF :=
  iprop(fmt.modelErrIs ii pre ∨ fmt.wrapErrIs ii inner pre)

instance fmt.errorfWrapIs_persistent (ii : GoInterfaceOk) (inner : GoInterface) (pre : GoString) :
    Persistent (fmt.errorfWrapIs (GF := GF) ii inner pre) := by
  unfold fmt.errorfWrapIs; infer_instance

/-- **A chain of `%w` wraps**, outermost first (prefixes `pres`), from `err` down to `c`: each
level the model's error (which ends the chain) or Go's wrap of the next. -/
def fmt.wrapChain : List GoString → GoInterface → GoInterface → IProp GF
  | [], err, c => iprop(⌜err = c⌝)
  | pre :: ps, err, c => iprop(∃ ii : GoInterfaceOk, ⌜err = GoInterface.ok ii⌝ ∗
      (fmt.modelErrIs ii pre ∨ ∃ mid : GoInterface, fmt.wrapErrIs ii mid pre ∗ fmt.wrapChain ps mid c))

theorem fmt.wrapChain_nil (err c : GoInterface) :
    fmt.wrapChain (GF := GF) [] err c = iprop(⌜err = c⌝) := rfl

theorem fmt.wrapChain_cons (pre : GoString) (ps : List GoString) (err c : GoInterface) :
    fmt.wrapChain (GF := GF) (pre :: ps) err c = iprop(∃ ii : GoInterfaceOk, ⌜err = GoInterface.ok ii⌝ ∗
      (fmt.modelErrIs ii pre ∨ ∃ mid : GoInterface, fmt.wrapErrIs ii mid pre ∗ fmt.wrapChain ps mid c)) :=
  rfl

instance fmt.wrapChain_persistent (pres : List GoString) (err c : GoInterface) :
    Persistent (fmt.wrapChain (GF := GF) pres err c) := by
  induction pres generalizing err with
  | nil => unfold fmt.wrapChain; infer_instance
  | cons pre ps ih => unfold fmt.wrapChain; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Errorf(pre ++ "%w", inner)`**, where `pre` has no `%` and `inner` is a non-nil error `fmt`
formats by its `Error()` (`fmtErrorOk`: an `Error() string` method, which returns needing nothing,
and no `Format` method, which Go would call in its place; fmt soundness, 2026-11-18: until then only
`Error()`'s WP, which admitted a panicking or memory-writing `Format` and a non-`error` `inner`): the
model's error or Go's `*fmt.wrapError` (`fmt.errorfWrapIs`); if the error has
an `Unwrap() error` method (Go's `*fmt.wrapError` has, the model's `*errors.errorString` has not),
its gRPC description (`errDesc`) began with `pre` (errdesc stage 2b, 2026-11-21: that conjunct is gone with
the pure `errDesc`; the description is now the relation `descIs`, and `errorfWrap_descIs`,
`Proof/go_etcd_io/etcd/cache/v3/Base.lean`, proves of every `errorfWrapIs` error a description starting
with `pre`) (N1b, 2026-11-06: in Go the error has no
`GRPCStatus`, so `status.FromError` and the server's `FromContextError` take its `Error()`,
`pre ++ inner.Error()`; stated of the returned error only: as a law of every `errorfWrapIs` error it
would be inconsistent, an error whose `Error()` loops meeting it at every `pre`). The condition (H0,
2026-11-18) makes the conjunct vacuous of the model's error, whose `errDesc` the model does not
fix: unconditional, two programs `Errorf("A%w", e)` and `Errorf("B%w", e)` whose results the model
allocates at one address gave `"A" <+: errDesc v` and `"B" <+: errDesc v` of one value (F1,
`notes/perheap-scope.md` §5a). The arguments' slice comes back. Proved from Perennial's model
(`Proof/fmt/ErrorfWrap.lean`). -/
abbrev fmt.ErrorfWrap.spec : Prop :=
  ∀ (pre : GoString) (args_sl : GoSlice) (inner : GoInterfaceOk) (dq : DFrac),
  (W8 37 : w8) ∉ pre →
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} [GoInterface.ok inner] ∗
      fmtErrorOk (GoInterface.ok inner) }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #(pre ++ go!"%w"))) (Val #args_sl))
  {{ (err : GoInterfaceOk), RET #(GoInterface.ok err);
      args_sl ↦*{dq} [GoInterface.ok inner] ∗ fmt.errorfWrapIs err (GoInterface.ok inner) pre }}

end spec

end EtcdGrove
end Perennial
