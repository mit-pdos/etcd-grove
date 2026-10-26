/-
**The concrete vocabulary of raft's signature** (2026-10-26, prototype; `Spec/go_etcd_io/raft/v3/Sig.lean`):
the facts about Go values its specs state -- the context a `node` call takes (`nodeCtx`) and the
errors it returns (`propErr`, `nodeErr`, `ctxErr`, `errStopped`, `errProposalDropped`,
`stepErr`). They speak of Go values only (package globals, `context`'s descriptors), not of raft's
ghost state, so the signature states them concretely. Moved here from `InvNode.lean` and
`InvNodeCtx.lean`; nothing here imports raft's `Proof/` tree.
-/
module

public import GeneratedProof.go_etcd_io.raft.v3
public import Spec.context.ErrDone
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI OFE CMRA Iris.ProofMode go_etcd_io.raft.v3

-- from Proof/go_etcd_io/raft/v3/InvNode.lean
section
open Iris Iris.BI OFE CMRA Iris.ProofMode go_etcd_io.raft.v3
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `err` is raft's package variable `ErrProposalDropped` (`raft.go`, an `errors.New` error),
a read-only global the package initializer sets to a non-`nil` error (`isInitialized`,
`Base.lean`); the shape of `errStopped` (`InvNodeCtx.lean`). -/
def errProposalDropped (err : GoInterface) : IProp GF :=
  iprop((globalAddr ErrProposalDropped ↦□ err : IProp GF) ∗ ⌜err ≠ interface.nil⌝)

instance errProposalDropped_persistent (err : GoInterface) :
    Persistent (errProposalDropped (GF := GF) err) := by
  unfold errProposalDropped; infer_instance

/-- **The error `run` answers a proposal with** (stage R7c, 2026-10-16): `raft.Step`'s for the
`MsgProp` (`raft__Step.lean`'s `"Herr"`), `nil` or `ErrProposalDropped` (`stepFollower`'s and
`stepCandidate`'s drop; `wp_rn_raft_Step_prop`), what the result channel's handoff promises
(`propP`) and `Propose` returns (`propErr`, `InvNodeCtx.lean`). -/
def stepErr (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ errProposalDropped err)

instance stepErr_persistent (err : GoInterface) : Persistent (stepErr (GF := GF) err) := by
  unfold stepErr; infer_instance

end

-- from Proof/go_etcd_io/raft/v3/InvNodeCtx.lean
section
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
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

/-- The value a done context's `Err()` returns (`context.ErrDone`'s postcondition,
`Spec/context/ErrDone.lean`): a typed error, the value of `context.Canceled` or of
`context.DeadlineExceeded`. -/
def ctxErrVal (err : GoInterface) : IProp GF :=
  iprop(⌜context.isTypedErr err⌝ ∗
    (globalAddr context.Canceled ↦□ err ∨ globalAddr context.DeadlineExceeded ↦□ err))

instance ctxErrVal_persistent (err : GoInterface) : Persistent (ctxErrVal (GF := GF) err) := by
  unfold ctxErrVal; infer_instance

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

end

end EtcdGrove
end Perennial
