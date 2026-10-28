/- Lean-first (no Rocq counterpart).

## `node.stepWithWaitOption(ctx, m, wait)` (node.go:508)

A message to `run`: a proposal on `propc`, with a result channel if `wait` (then waits for
the result), anything else on `recvc`. Until stage R7a specified for `context.Background()` (its
`Done()` is `nil`, so the `ctx` cases never fire); since (2026-10-16, D10 gap (2)) for any `nodeCtx ctx cd`
(`InvNodeCtx.lean`): a `case <-ctx.Done()` fires once the context is done, returning `ctx.Err()`
(`ctxErr`), in the second `select` abandoning the proposal's result channel (the handoff's consumer
token is dropped). The error is `nodeErr cd err` (`nil`, `ErrStopped`, the context's), or, with
`wait`, the proposal's result from `run` too (`propErr`). Specified for the two uses `Propose` and
`Step` make of it: `Propose`'s message (`propMsg`, with `wait`), and a message from the network
(`netP`).

raft v3.7 (2026-10-16, stage R5): `m` is a `*pb.Message` (`ml`), handed to `run` for good.
`Propose`'s message is `msgIn ml 1` of `propMsgM` with the one entry `propEntryM data` (D6: the
bytes; until then the Goose value `propMsg esl`, `m = propMsg esl`, with the entries' slice,
its capacity and the data slice). A message from the network is `netP` alone: its type, which
`netP` quantifies with the message's state, is not `MsgProp` by `NetMsgOk`
(`netStepTypes_ne_prop`; until then a separate conjunct `m.Type' ≠ MsgProp`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Perennial.Proof.context
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What `stepWithWaitOption` is called with (see the file header). -/
def stepArg (γ : NodeNames) (id : w64) (ml : Loc) (wait : Bool) : IProp GF :=
  iprop(netP γ id ml ∨
    (⌜wait = true⌝ ∗ ∃ data : List w8,
      msgIn ml (DFrac.own 1) ⟨propMsgM, [propEntryM data], none, [], []⟩ ∗
      propData γ.raft (propEntryM data) ∗ entTk γ.raft (propEntryM data)) ∨
    -- a proposal forwarded by a peer (2026-10-10)
    (⌜wait = false⌝ ∗ fwdP γ ml))

/-- See the file header. -/
abbrev node.stepWithWaitOption.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (ml : Loc) (wait : Bool)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗
      nodeCtx ctx cd ∗
      stepArg γ id ml wait }}
    (App (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"stepWithWaitOption"))
      (Val #(interface.ok ctx))) (Val #ml)) (Val #wait))
  {{ (err : GoInterface), RET #err; if wait then propErr cd err else nodeErr cd err }}

end spec

end EtcdGrove
end Perennial
