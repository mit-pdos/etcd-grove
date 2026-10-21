/-
The `node` API's context (stage R7a of the raft v3.7 retarget, D10 gap (2), 2026-10-16).

`node.Propose`, `node.ReadIndex`, `node.Step`, `node.ProposeConfChange`, `node.TransferLeadership`,
`node.ForgetLeader` and the `step*` chain take a `context.Context`, on whose `Done()` the
`select`s of `stepWithWaitOption` and `TransferLeadership` wait beside `n.done`. Until R7a they
were specified for `context.Background()` only (`Done()` is `nil`, so that case never fires); the
server passes a context with a timeout. The context is now any `nodeCtx ctx cd`:

* `doneNilCtx ctx`: `ctx.Done()` returns the `nil` channel (`Background()`, `TODO()`, and what
  `WithValue` derives from them); the shape of the server's `doneNil`
  (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/TxnRange.lean`, which raft cannot import); or
* `context.isContext ctx cd`: Perennial's context model (`Perennial/Proof/context/Base.lean`):
  `Done()` returns a channel of `isContextDone cd`, a receive from which returns once the context
  is done (`isContextDone_receive`: `□ cd.PDone ∗ ContextClosed cd.Done_gn`), after which
  `Err()` returns `context.Canceled` or `context.DeadlineExceeded` (Go's contract of
  `Context.Err`, this repository's trust-boundary spec `Spec/context/ErrDone.lean`,
  `context.ErrDone`, a callee of `stepWithWaitOption`; Perennial's `isContext` says only that
  it is a non-`nil` typed error, `"#HErr"` at `Broadcast.Done`).

What the error is (`nodeErr cd err`): `nil` (the message reached `run`), raft's package variable
`ErrStopped` (`errStopped err`: the value the read-only global holds, as `isInitialized` states
it; the `n.done` case, which the Stop premise keeps from firing), or the context's (`ctxErr cd
err`: `Canceled` or `DeadlineExceeded`, `ctxErrVal`, with the context done). `Propose`'s (through
`stepWait`, `stepWithWaitOption` with `wait`) can also be the proposal's own result, which `run`
sends on the result channel: `raft.Step`'s error for the proposal, `nil` or `ErrProposalDropped`
(`stepErr err`, `InvNode.lean`, what the result channel's handoff predicate `propP` promises;
stage R7c, 2026-10-16): `propErr cd err := nodeErr cd err ∨ stepErr err`.

`nodeCtx_background`: `context.Background()` is a `nodeCtx` for any descriptor (`bgCd` a
canonical one), so the register keeps calling with `Background()`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvNode
public import Spec.context.ErrDone
public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section ctx
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The context `ctx`'s `Done()` returns the `nil` channel: it is never canceled
(`context.Background()`'s, `nodeCtx_background`). The server's `doneNil`. -/
def doneNilCtx (ctx : GoInterfaceOk) : IProp GF :=
  iprop(□ {{ True }} (App (Val #(methods ctx.ty go!"Done" ctx.v)) (Val #()))
    {{ RET #chan.nil; True }})

instance doneNilCtx_persistent (ctx : GoInterfaceOk) : Persistent (doneNilCtx (GF := GF) ctx) := by
  unfold doneNilCtx; infer_instance

/-- **The `node` API's context** (see the file header): one whose `Done()` is `nil`, or an
`isContext` with the descriptor `cd`. -/
def nodeCtx (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(doneNilCtx ctx ∨ context.isContext ctx cd)

instance nodeCtx_persistent (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (nodeCtx (GF := GF) ctx cd) := by
  unfold nodeCtx; infer_instance

/-- A canonical descriptor for a context with a `nil` `Done()` (which no descriptor describes;
`nodeCtx` ignores it then): its Done proposition `False`. The server's `neverCd`. -/
def bgCd : context.ContextDesc (IProp GF) :=
  { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(False) }

/-- `context.Background()`'s `Done()` is `nil` (Perennial's `wp_background_Done`). -/
theorem doneNilCtx_background : ⊢ doneNilCtx (GF := GF) context.backgroundCtxVal := by
  iunfold doneNilCtx
  imodintro
  iapply context.wp_background_Done

/-- `context.Background()` is a `nodeCtx`, for any descriptor. -/
theorem nodeCtx_background (cd : context.ContextDesc (IProp GF)) :
    ⊢ nodeCtx (GF := GF) context.backgroundCtxVal cd := by
  iunfold nodeCtx
  ileft
  iapply doneNilCtx_background

/-- What a `nodeCtx`'s `Done()` returns: the `nil` channel, or a channel of the context's
`isContextDone` (with the context, for the `Err()` that follows a receive). -/
def nodeDone (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ch : GoChan) :
    IProp GF :=
  iprop(⌜ch = chan.nil⌝ ∨
    ((∃ γch : ChanNames, context.isContextDone cd ch γch) ∗ context.isContext ctx cd))

instance nodeDone_persistent (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (ch : GoChan) : Persistent (nodeDone (GF := GF) ctx cd ch) := by
  unfold nodeDone; infer_instance

/-- **`ctx.Done()`** of a `nodeCtx`. -/
theorem nodeCtx_Done (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    {{ nodeCtx (GF := GF) ctx cd }}
      (App (Val #(methods ctx.ty go!"Done" ctx.v)) (Val #()))
    {{ (ch : GoChan), RET #ch; nodeDone ctx cd ch }} := by
  iintro %Φ #Hctx HΦ
  unfold nodeCtx
  icases Hctx with (#Hdn | #Hctx)
  · iunfold doneNilCtx at Hdn
    iapply Hdn
    · itrivial
    inext
    iintro -
    iapply HΦ
    unfold nodeDone
    ileft
    ipureintro; rfl
  · ihave #Hctx' := Hctx
    iNamed Hctx'
    iapply HDone
    · itrivial
    inext
    iintro %ch %γch #Hd
    iapply HΦ
    unfold nodeDone
    iright
    isplitl []
    · iexists γch
      iexact Hd
    · iexact Hctx

/-- The value a done context's `Err()` returns (`context.ErrDone`'s postcondition,
`Spec/context/ErrDone.lean`): a typed error, the value of `context.Canceled` or of
`context.DeadlineExceeded`. -/
def ctxErrVal (err : GoInterface) : IProp GF :=
  iprop(⌜context.isTypedErr err⌝ ∗
    (globalAddr context.Canceled ↦□ err ∨ globalAddr context.DeadlineExceeded ↦□ err))

instance ctxErrVal_persistent (err : GoInterface) : Persistent (ctxErrVal (GF := GF) err) := by
  unfold ctxErrVal; infer_instance

/-- A typed error is not `nil`. -/
theorem ctxErrVal_ne_nil (err : GoInterface) : ctxErrVal (GF := GF) err ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold ctxErrVal
  iintro ⟨%Hty, -⟩
  ipureintro
  intro h
  subst h
  simp [context.isTypedErr] at Hty

/-- The error the context returns once done (see the file header): non-`nil`, `Canceled` or
`DeadlineExceeded` (`ctxErrVal`), with the context's Done proposition and `ContextClosed`. -/
def ctxErr (cd : context.ContextDesc (IProp GF)) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ interface.nil⌝ ∗ □ cd.PDone ∗ context.ContextClosed cd.Done_gn ∗ ctxErrVal err)

instance ctxErr_persistent (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    Persistent (ctxErr (GF := GF) cd err) := by
  unfold ctxErr; infer_instance

/-- `err` is raft's package variable `ErrStopped` (`node.go`), a read-only global the package
initializer sets to a non-`nil` error (`isInitialized`, `Base.lean`). -/
def errStopped (err : GoInterface) : IProp GF :=
  iprop((globalAddr ErrStopped ↦□ err : IProp GF) ∗ ⌜err ≠ interface.nil⌝)

instance errStopped_persistent (err : GoInterface) :
    Persistent (errStopped (GF := GF) err) := by
  unfold errStopped; infer_instance

/-- **The error of a `node` API call** that hands a message to `run` (see the file header):
`nil`, `ErrStopped`, or the context's. -/
def nodeErr (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ errStopped err ∨ ctxErr cd err)

instance nodeErr_persistent (cd : context.ContextDesc (IProp GF))
    (err : GoInterface) : Persistent (nodeErr (GF := GF) cd err) := by
  unfold nodeErr; infer_instance

theorem nodeErr_nil (cd : context.ContextDesc (IProp GF)) :
    ⊢ nodeErr (GF := GF) cd interface.nil := by
  unfold nodeErr
  ileft
  ipureintro; rfl

/-- **The error of a proposal that waits for its result** (`Propose`, `stepWait`,
`stepWithWaitOption` with `wait`; see the file header): `nodeErr`, or the result `run` sent,
`raft.Step`'s error for the proposal (`stepErr`, `InvNode.lean`: `nil` or
`ErrProposalDropped`). -/
def propErr (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    IProp GF :=
  iprop(nodeErr cd err ∨ stepErr err)

instance propErr_persistent (cd : context.ContextDesc (IProp GF))
    (err : GoInterface) : Persistent (propErr (GF := GF) cd err) := by
  unfold propErr; infer_instance

theorem propErr_of_nodeErr (cd : context.ContextDesc (IProp GF))
    (err : GoInterface) : nodeErr (GF := GF) cd err ⊢ propErr cd err := by
  unfold propErr
  iintro H
  ileft
  iexact H

theorem propErr_nil (cd : context.ContextDesc (IProp GF)) :
    ⊢ propErr (GF := GF) cd interface.nil := by
  iapply propErr_of_nodeErr
  iapply nodeErr_nil

/-- The proposal's own result (see the file header). -/
theorem propErr_of_stepErr (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    stepErr (GF := GF) err ⊢ propErr cd err := by
  unfold propErr
  iintro H
  iright
  iexact H

theorem nodeErr_ctx (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    ctxErr (GF := GF) cd err ⊢ nodeErr cd err := by
  unfold nodeErr
  iintro H
  iright; iright
  iexact H

/-- `stepWithWaitOption`'s error (`propErr` with `wait`, `nodeErr` otherwise): `nil`. -/
theorem waitErr_nil (cd : context.ContextDesc (IProp GF)) (wait : Bool) :
    ⊢ (if wait then propErr (GF := GF) cd interface.nil else nodeErr cd interface.nil) := by
  cases wait
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iapply nodeErr_nil
  · simp only [↓reduceIte]
    iapply propErr_nil

/-- `stepWithWaitOption`'s error: the context's. -/
theorem waitErr_ctx (cd : context.ContextDesc (IProp GF)) (err : GoInterface) (wait : Bool) :
    ctxErr (GF := GF) cd err ⊢ (if wait then propErr cd err else nodeErr cd err) := by
  iintro H
  cases wait
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iapply nodeErr_ctx $$ H
  · simp only [↓reduceIte]
    iapply propErr_of_nodeErr
    iapply nodeErr_ctx $$ H

/-- **`ctx.Err()`** of an `isContext` once a receive from its `Done()` returned
(`isContextDone_receive`): the context's error, `Canceled` or `DeadlineExceeded`, by the
trust-boundary spec `context.ErrDone` (a callee hypothesis; stage R7c, until then Perennial's
`"#HErr"` at `Broadcast.Done`, which names no value). -/
theorem isContext_Err_done (hED : context.ErrDone.spec (GF := GF) (hG := hG))
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ context.isContext (GF := GF) ctx cd ∗
        □ cd.PDone ∗ context.ContextClosed cd.Done_gn }}
      (App (Val #(methods ctx.ty go!"Err" ctx.v)) (Val #()))
    {{ (err : GoInterface), RET #err; ctxErr cd err }} := by
  iintro %Φ ⟨#Hpkg, #Hctx, #HPD, #HCC⟩ HΦ
  iapply hED ctx cd
  · iframe #
  inext
  iintro %err ⟨%Hty, #Hv⟩
  iapply HΦ
  ihave #Hval : ctxErrVal err $$ []
  · unfold ctxErrVal
    iframe Hv
    ipureintro; exact Hty
  ihave %Hne := ctxErrVal_ne_nil err $$ Hval
  unfold ctxErr
  iframe #
  ipureintro; exact Hne

/-- The `case <-ctx.Done():` clause of a blocking `select`, for what `nodeCtx_Done` returned: a
`nil` channel's clause never fires (`nilClausePre`), a context's fires once the context is done,
with its handler run on the closed channel's zero value (`isContextDone_receive`), the context
and its `Err()`'s premise in hand (`isContext_Err_done`). -/
theorem nodeDone_recv_clause (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (ch : GoChan) (body : Expr) (Φ : val → IProp GF) :
    ⊢ nodeDone (GF := GF) ctx cd ch -∗
      (context.isContext ctx cd ∗ □ cd.PDone ∗ context.ContextClosed cd.Done_gn -∗
        WP (App body (Val (PairV #(() : Unit) #false))) {{ Φ }}) -∗
      (chan.blockingClausePre
          (.CommClause (.RecvCase (go.GoType.StructType []) (Val #ch)) body) Φ ∨
        chan.nilClausePre (.CommClause (.RecvCase (go.GoType.StructType []) (Val #ch)) body)) := by
  iintro #Hd Hk
  unfold nodeDone
  icases Hd with (%Hnil | ⟨⟨%γch, #Hcd⟩, #Hctx⟩)
  · iright
    iapply chan.nilClausePre_recv Unit _ _ Hnil
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ Hcd
    iapply context.isContextDone_receive _ _ _ _ $$ Hcd
    iintro ⟨#HPD, #HCC⟩
    iapply Hk
    iframe #

end ctx

end EtcdGrove
end Perennial
