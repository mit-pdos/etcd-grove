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
(`msgIn ml 1`), `ccEntsOk_cc`.

**Logically atomic (2026-10-27).** As `node.Propose`: the conf change's entry is a tracked
proposal, keyed by its type and bytes (`entKey`), and the caller hands in `ccPropArg γ.raft o` --
once `o` is marshaled to bytes `bs`, the key's registration (`propIs`) and an update `propAu1` for
it, which `ProposeConfChange` deposits before the proposal leaves the node (`cc_propose_ghost`),
its ticket travelling with the proposal; or nothing, if the entry is a filler (an empty
`ConfChangeV2`). The update fires at most once, when the entry commits, and never if a leader
refuses the change (an empty normal entry, a filler, is appended in its place and the ticket
dropped). Until 2026-10-27 a conf-change entry fired the standing `noopAu`, and the change had to
be one the cluster's policy admits (`CCAllowed`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Perennial.Proof.context

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

/-- See the file header. -/
abbrev node.ProposeConfChange.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (c : GoInterface) (o : ConfChangeIM) (dq : DFrac)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      nodeCtx ctx cd ∗
      ownConfChangeI c dq (some o) ∗
      -- (2026-10-27) the proposal tracked under its key (`ccPropArg`; until then
      -- `CCAllowed γ.raft o`, a change the cluster's policy admits)
      ccPropArg γ.raft o }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ProposeConfChange"))
      (Val #(interface.ok ctx))) (Val #c))
  {{ (err : GoInterface), RET #err; ownConfChangeI c dq (some o) ∗ nodeErr cd err }}

end spec

end EtcdGrove
end Perennial
