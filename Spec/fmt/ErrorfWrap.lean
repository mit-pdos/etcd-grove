/-
`fmt.Errorf` of `pre ++ "%w"` over one error: the trust boundary (errorf-wrap, 2026-11-06). Go's
`Errorf` returns a `*fmt.wrapError` (`fmt/errors.go:46-49`), whose `Unwrap` gives the wrapped error
back, so that `errors.Is` sees it; Perennial's model of `Errorf` (`errors.New(format)`) does not
model `%w`, and a proof must not learn the error's type, `Is` behaviour or message from it
(`notes/decisions.md`, "`fmt.Errorf` with `%w`: no fact from the model"). The post is a disjunction,
the model's error or Go's (etcd-grove-82's decision, 2026-11-06), so that the spec is true of both
and contradicts neither. Attacked: `notes/axiom-review/errorf-wrap.md`. Lean-first.
-/
module

public import Spec.fmt.Errorf

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

/-- **Perennial's model of `fmt.Errorf`'s error** (`errors.New(format)`): an `*errors.errorString`
whose `Error()` returns. -/
def fmt.modelErrIs (ii : GoInterfaceOk) : IProp GF :=
  iprop(⌜∃ x : Loc, ii = ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ (∀ s : GoString, Φ #s) -∗
      WP (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #())) {{ Φ }})

instance fmt.modelErrIs_persistent (ii : GoInterfaceOk) :
    Persistent (fmt.modelErrIs (GF := GF) ii) := by
  unfold fmt.modelErrIs; infer_instance

/-- **Go's `%w` error of `inner`**, with message prefix `pre` (a `*fmt.wrapError`, its type left
opaque): a pointer error; its method set has `Unwrap() error` and no `Is`, `As` or `GRPCStatus`
(`*wrapError` has `Error` and `Unwrap` only); `Error()` always returns one string, `pre ++ s`
(`return e.msg`, formatted once); `Unwrap()` returns `inner` (`return e.err`). -/
def fmt.wrapErrIs (ii : GoInterfaceOk) (inner : GoInterface) (pre : GoString) : IProp GF :=
  iprop(⌜_root_.Perennial.errors.IsPointerError ii ∧
      methodSet ii.ty !! go!"Unwrap" = some (go.Signature [] false [go.error]) ∧
      methodSet ii.ty !! go!"As" ≠ some (go.Signature [go.any] false [go.bool]) ∧
      methodSet ii.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]) ∧
      methodSet ii.ty !! go!"GRPCStatus" = none⌝ ∗
    (∃ s : GoString, □ ∀ Φ : val → IProp GF, ▷ Φ #(pre ++ s) -∗
      WP (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #())) {{ Φ }}) ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #inner -∗
      WP (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #())) {{ Φ }})

instance fmt.wrapErrIs_persistent (ii : GoInterfaceOk) (inner : GoInterface) (pre : GoString) :
    Persistent (fmt.wrapErrIs (GF := GF) ii inner pre) := by
  unfold fmt.wrapErrIs; infer_instance

/-- **`fmt.Errorf(pre ++ "%w", inner)`'s error**: the model's or Go's. -/
def fmt.errorfWrapIs (ii : GoInterfaceOk) (inner : GoInterface) (pre : GoString) : IProp GF :=
  iprop(fmt.modelErrIs ii ∨ fmt.wrapErrIs ii inner pre)

instance fmt.errorfWrapIs_persistent (ii : GoInterfaceOk) (inner : GoInterface) (pre : GoString) :
    Persistent (fmt.errorfWrapIs (GF := GF) ii inner pre) := by
  unfold fmt.errorfWrapIs; infer_instance

/-- **A chain of `%w` wraps**, outermost first (prefixes `pres`), from `err` down to `c`: each
level the model's error (which ends the chain) or Go's wrap of the next. -/
def fmt.wrapChain : List GoString → GoInterface → GoInterface → IProp GF
  | [], err, c => iprop(⌜err = c⌝)
  | pre :: ps, err, c => iprop(∃ ii : GoInterfaceOk, ⌜err = GoInterface.ok ii⌝ ∗
      (fmt.modelErrIs ii ∨ ∃ mid : GoInterface, fmt.wrapErrIs ii mid pre ∗ fmt.wrapChain ps mid c))

theorem fmt.wrapChain_nil (err c : GoInterface) :
    fmt.wrapChain (GF := GF) [] err c = iprop(⌜err = c⌝) := rfl

theorem fmt.wrapChain_cons (pre : GoString) (ps : List GoString) (err c : GoInterface) :
    fmt.wrapChain (GF := GF) (pre :: ps) err c = iprop(∃ ii : GoInterfaceOk, ⌜err = GoInterface.ok ii⌝ ∗
      (fmt.modelErrIs ii ∨ ∃ mid : GoInterface, fmt.wrapErrIs ii mid pre ∗ fmt.wrapChain ps mid c)) :=
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

/-- **`fmt.Errorf(pre ++ "%w", inner)`**, where `pre` has no `%` and `inner` is a non-nil error whose
`Error()` returns: the model's error or Go's `*fmt.wrapError` (`fmt.errorfWrapIs`); the arguments'
slice comes back. -/
abbrev fmt.ErrorfWrap.spec : Prop :=
  ∀ (pre : GoString) (args_sl : GoSlice) (inner : GoInterfaceOk) (dq : DFrac),
  (W8 37 : w8) ∉ pre →
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} [GoInterface.ok inner] ∗
      fmt.stringMethodSpec inner go!"Error" }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #(pre ++ go!"%w"))) (Val #args_sl))
  {{ (err : GoInterfaceOk), RET #(GoInterface.ok err);
      args_sl ↦*{dq} [GoInterface.ok inner] ∗ fmt.errorfWrapIs err (GoInterface.ok inner) pre }}

end spec

end EtcdGrove
end Perennial
