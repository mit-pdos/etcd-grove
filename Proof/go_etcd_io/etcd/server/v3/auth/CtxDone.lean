/-
**A request context's `Done()`, as the auth store may select on it** (k8s 7f-4, T-e', decided by
etcd-grove-81, 2026-11-12). Lean-first.

The auth store's token check (`isValidSimpleToken`) selects on `ctx.Done()`, and Go evaluates every
channel operand of a `select` on entry, so `Done()` must return (a nil context panics there:
`notes/auth-validspec-false.md`). `auth.ctxDoneAny ctx` says that `Done()` returns, from any
goroutine, nil (a receive that never proceeds) or a context's Done channel (`isContextDone`, which
carries the receive spec). Both request-side contexts give it: a `txnCtx` (`doneNil` or `isContext`)
and a stream handler's weak context (`srvCtxWeak`, whose `Done()` clause is `isContext`'s); the laws
are beside those definitions' users (`InvRequest.lean`, `SrvCtxWeak.lean`). The auth stage S1 reuses
it for the token contract's `info` clause.
-/
module

public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section recv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A channel a receive may complete on with any outcome** (the index waiter's: etcd's
`wait.WaitTime`'s, closed once the index is applied; a context's Done channel): a receive's atomic
update for any postcondition that holds of every outcome. (Moved here from `TokenSimple.lean` by
auth-schema-fix S1, 2026-11-12, for `auth.ctxDoneRecv`.) -/
def auth.anyRecv (ch : Loc) : IProp GF :=
  iprop(∃ γ : ChanNames, isChan ch γ Unit ∗
    □ (∀ Φ : Unit → Bool → IProp GF, (∀ v ok, Φ v ok) -∗ recvAu γ Unit Φ))

instance auth.anyRecv_persistent (ch : Loc) : Persistent (auth.anyRecv (GF := GF) ch) := by
  unfold auth.anyRecv; infer_instance

/-- **`ctx.Done()` returns nil or a channel a receive may complete on with any outcome**
(persistent; generic in the later credits, as the auth store's invariant and the token provider's
contract are: the contract's `info` premise; auth-schema-fix S1, decided by etcd-grove-81,
2026-11-12). `auth.ctxDoneAny` (at `HasLC.hasLC`, over Perennial's contexts) gives it
(`auth.ctxDoneRecv_of_ctxDoneAny`). -/
def auth.ctxDoneRecv (ctx : GoInterfaceOk) : IProp GF :=
  iprop(□ {{ True }} (App (Val #(methods ctx.ty go!"Done" ctx.v)) (Val #()))
    {{ (ch : GoChan), RET #ch; ⌜ch = chan.nil⌝ ∨ auth.anyRecv ch }})

instance auth.ctxDoneRecv_persistent (ctx : GoInterfaceOk) :
    Persistent (auth.ctxDoneRecv (GF := GF) ctx) := by
  unfold auth.ctxDoneRecv; infer_instance

end recv

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- **`ctx.Done()` returns nil or a context's Done channel** (persistent; T-e'): from any goroutine,
`Done()` returns `nil` (receiving on it never proceeds) or a channel `ch` that is some context's
Done channel (`isContextDone s ch γch`, with its receive spec, `isContextDone_receive`). The binder's
distinctive name keys the axiom-tok gate's rule-7 entries (`etc/axiom-tok-allow.txt`) to it. -/
def auth.ctxDoneAny (ctx : GoInterfaceOk) : IProp GF :=
  iprop(□ {{ True }} (App (Val #(methods ctx.ty go!"Done" ctx.v)) (Val #()))
    {{ (ch : GoChan), RET #ch; ⌜ch = chan.nil⌝ ∨
        ∃ (sDoneAny : context.ContextDesc (IProp GF)) (γch : ChanNames),
          context.isContextDone sDoneAny ch γch }})

instance auth.ctxDoneAny_persistent (ctx : GoInterfaceOk) :
    Persistent (auth.ctxDoneAny (GF := GF) ctx) := by
  unfold auth.ctxDoneAny; infer_instance

/-- An `isContext` gives it (its `#HDone`). -/
theorem auth.ctxDoneAny_of_isContext (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) :
    context.isContext ctx s ⊢ auth.ctxDoneAny ctx := by
  iintro #H
  unfold auth.ctxDoneAny
  iintro !> %Φ !> - HΦ
  unfold context.isContext context.isContextDef
  icases H with ⟨-, #HDone, -⟩
  iapply HDone $$ []
  · itrivial
  iintro !> %ch %γch Hd
  iapply HΦ
  iright
  iexists s, γch
  iexact Hd

/-- **`ctxDoneAny` gives `ctxDoneRecv`**: a context's Done channel is a channel a receive may
complete on with any outcome (`isContextDone_is_chan`, `isContextDone_receive`). -/
theorem auth.ctxDoneRecv_of_ctxDoneAny (ctx : GoInterfaceOk) :
    auth.ctxDoneAny ctx ⊢ auth.ctxDoneRecv (GF := GF) ctx := by
  iintro #H
  unfold auth.ctxDoneRecv
  iintro !> %Φ !> - HΦ
  unfold auth.ctxDoneAny
  iapply H $$ []
  · itrivial
  iintro !> %ch Hch
  iapply HΦ
  icases Hch with (%Hnil | ⟨%s, %γch, #Hd⟩)
  · ileft; ipureintro; exact Hnil
  iright
  unfold auth.anyRecv
  iexists γch
  isplitr
  · iapply context.isContextDone_is_chan $$ Hd
  iintro !> %Ψ HΨ
  iapply context.isContextDone_receive _ _ _ _ $$ Hd
  iintro -
  iapply HΨ

end defs

end EtcdGrove
end Perennial
