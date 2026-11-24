/-
`ctxBg c` (persistent): the context `c` is `Background()` or a chain of `*valueCtx`s over it, each
with its three fields (`Context`, `key`, `val`) read-only, as `context.WithValue` builds them
(`context.WithValue.specPtr`, `Net/Spec/context/WithValuePtr.lean`). What net/http's `Serve` passes
`conn.serve` (`WithValue(Background(), ServerContextKey, s)`), and what `conn.serve` cancels
(`context.WithCancel.specValBg`, `Net/Spec/context/WithCancelValBg.lean`) after one more `WithValue`.
`ctxBgN n c`: the same, at most `n` `*valueCtx`s deep.
-/
module

public import Perennial.Proof.context.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace context

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : context.Assumptions]

/-- See the file header. -/
def ctxBgN : Nat → GoInterfaceOk → IProp GF
  | 0, c => iprop(⌜c = backgroundCtxVal⌝)
  | n + 1, c => iprop(⌜c = backgroundCtxVal⌝ ∨
      ∃ (q : Loc) (parent key : GoInterfaceOk) (v : GoInterface),
        ⌜c = interface.mk (go.GoType.PointerType context.valueCtx.ty) #q⌝ ∗
        structFieldRef context.valueCtx go!"Context" q ↦□ (interface.ok parent : GoInterface) ∗
        structFieldRef context.valueCtx go!"key" q ↦□ (interface.ok key : GoInterface) ∗
        structFieldRef context.valueCtx go!"val" q ↦□ v ∗ ctxBgN n parent)

instance ctxBgN_persistent (n : Nat) (c : GoInterfaceOk) : Persistent (ctxBgN (GF := GF) n c) := by
  induction n generalizing c with
  | zero => unfold ctxBgN; infer_instance
  | succ n ih => unfold ctxBgN; infer_instance

/-- See the file header. -/
def ctxBg (c : GoInterfaceOk) : IProp GF := iprop(∃ n, ctxBgN n c)

instance ctxBg_persistent (c : GoInterfaceOk) : Persistent (ctxBg (GF := GF) c) := by
  unfold ctxBg; infer_instance

end defs

end context
end Perennial
