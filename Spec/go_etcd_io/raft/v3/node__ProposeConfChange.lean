/- `node.ProposeConfChange` (node.go), Lean-first (2026-10-13, reconfiguration stage D).

`ProposeConfChange(ctx, cc)` is `msg, err := confChangeToMsg(cc); if err != nil { return err };
return n.Step(ctx, msg)`: the proposal goes on `propc` as a forwarded one (no result channel),
and `run` steps it (`RawNode.ProposeConfChange`'s file header says what that does). The
entry's data is recorded as proposed (`isPropData`, through the node's proposed slices'
invariant, `node_read_register`), which makes the proposal a protocol message (`fwdP`).
Partial correctness: whether the change is appended or refused is not visible.
(2026-10-16, stage R7a, D10 gap (2)) The context is any `nodeCtx ctx cd` (`InvNodeCtx.lean`:
`Done()` nil, or Perennial's `isContext`), and the error `nodeErr cd err`: `nil`, raft's
`ErrStopped`, or the context's once its `Done()` fired (`ctxErr`).

raft v3.7 (2026-10-16, stage R5, D6): the entry holds the conf change's bytes, so no recording
(`isPropData`) is needed: the proposal is `fwdP` from `confChangeToMsg`'s owned message
(`msgIn ml 1`), `entData_cc`, `ccEntsOk_cc`.

etcd-io/raft#44 (2026-10-16): `return n.stepWait(ctx, msg)` instead of `n.Step(ctx, msg)`: the
proposal goes on `propc` with a result channel, and the call waits for `raft.Step`'s error for
it, as `Propose` does. The error is `propErr cd err` (`InvNodeCtx.lean`): `nodeErr cd err` as
before, or the proposal's result (`stepErr`: `nil` or `ErrProposalDropped`, which, since the PR,
a leader returns for a refused conf change, `Spec/go_etcd_io/raft/v3/stepLeader.lean`). Before
the PR: `nodeErr cd err` (the proposal's result never reached the caller).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev node.ProposeConfChange.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (c : GoInterface) (o : CCMsg) (dq : DFrac)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  -- (2026-10-15, stage N) a change the cluster admits
  CCAllowed γ.raft o →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      nodeCtx ctx cd ∗
      ownCCI c dq (some o) }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ProposeConfChange"))
      (Val #(interface.ok ctx))) (Val #c))
  {{ (err : GoInterface), RET #err; ownCCI c dq (some o) ∗ propErr cd err }}

end spec

end EtcdGrove
end Perennial
