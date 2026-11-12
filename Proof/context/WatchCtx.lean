/-
**A context the client's watch takes** (`watchCtx`; 2026-11-04, W1 of Q1 (b),
`notes/k8s-compactor-plan.md`, the user's approval of D1 (a)). Lean-first.

The client's watch reads two things of its caller's context (W0's survey):
- its `Done()` channel, in the `select`s of `Watch`, `serveSubstream`, `waitCancelSubstreams` and
  `sendCloseSubstream`;
- its `Err()`: while it may not be done (`waitCancelSubstreams`, `closeSubstream`), and once it is
  (`closeSubstream`, after `waitCancelSubstreams` saw `Done()` closed: the error is not `nil`).
Its gRPC stream runs under a context of its own, `WithCancel(&valCtx{ctx})` (an `isContext`). So the
watch's premise on the caller's context is `isContext`'s `Done()` triple (`"#HDone"`: a channel with
`isContextDone`) and its `Err()` triples (`"#HErr"`, Go's contract of `Err()`), without its `Value()`
or its `*cancelCtx` parent. Every `isContext` gives both (`watchCtx_of_isContext`). So does a context
outside Perennial's model whose `Done()` is one broadcast channel, such as k8s's
`wait.ContextForChannel(stop)` (`channelContext.Err`'s spec is of this form).

Since premise fixes 8 (D5, approved by etcd-grove-81) its outgoing metadata is grpc's
(`metadata.outgoingCtxOkC`, `"#HOut"`): `streamKeyFromCtx` reads it, and the stream context
`WithCancel(&valCtx{ctx})` reaches it through `valCtx`'s promoted `Value`.
-/
module

public import Perennial.Proof.context
public import Proof.context.LibKeysChain

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace context

open Iris Iris.BI Iris.ProofMode _root_.Perennial.context

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- **A context the client's watch takes** (persistent; see the file header). -/
abbrev watchCtx (c : GoInterfaceOk) (s : ContextDesc (IProp GF)) : IProp GF :=
  iprop(
  "#HDone" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ (ch : GoChan) (γch : ChanNames), isContextDone s ch γch -∗ Φ #ch) -∗
      WP (App (Val #(methods c.ty go!"Done" c.v)) (Val #())) {{ Φ }}) ∗
  "#HErr" ∷
    (∀ cl : Broadcast, □ (∀ Φ : val → IProp GF,
      (match cl with
       | .Done => ContextClosed s.Done_gn
       | _ => iprop(True)) -∗
      ▷ (∀ err : GoInterface,
          (match cl with
           | .Done => iprop(⌜err ≠ interface.nil⌝)
           | _ => if err = interface.nil then iprop(True)
                  else iprop(□ s.PDone ∗ ContextClosed s.Done_gn)) -∗
          (if err = interface.nil then iprop(True) else isCtxErr err) -∗
          Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }})) ∗
  "#HOut" ∷ metadata.outgoingCtxOkC c)

instance watchCtx_persistent (c : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    Persistent (watchCtx (GF := GF) c s) := by
  unfold watchCtx; infer_instance

/-- **Every model context with grpc's outgoing metadata is one the watch takes**: `isContext`'s
`Done()` and `Err()` triples. -/
theorem watchCtx_of_isContext (c : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    isContext (GF := GF) c s ∗ metadata.outgoingCtxOkC c ⊢ watchCtx c s := by
  iintro ⟨#H, #Ho⟩
  iunfold isContext at H
  iunfold isContextDef at H
  iNamed H
  unfold watchCtx
  isplitr
  · iexact HDone
  isplitr
  · iexact HErr
  · iexact Ho

/-- `watchCtx`'s outgoing-metadata clause. -/
theorem watchCtx_outgoingC (c : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    watchCtx (GF := GF) c s ⊢ metadata.outgoingCtxOkC c := by
  iintro #H
  unfold watchCtx
  iNamed H
  iexact HOut

end defs

end context
end EtcdGrove
end Perennial
