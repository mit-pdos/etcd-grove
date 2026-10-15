/- Lean-first (no Rocq counterpart).

## `newNode(rn)` (node.go:312)

The node struct over `rn`, with its fresh channels: every one unbuffered and idle but
`tickc`, buffered (capacity 128) and empty.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode

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

/-- The node struct's channels, fresh (see the file header). -/
def newNodeChans (nv : node) : IProp GF :=
  iprop(∃ (γp γr γc γcs γrd γa γt γd γs γst : ChanNames),
    isChan nv.propc' γp msgWithResult ∗ ownChan γp msgWithResult .Idle ∗
    isChan nv.recvc' γr raftpb.Message ∗ ownChan γr raftpb.Message .Idle ∗
    isChan nv.confc' γc raftpb.ConfChangeV2 ∗ ownChan γc raftpb.ConfChangeV2 .Idle ∗
    isChan nv.confstatec' γcs raftpb.ConfState ∗ ownChan γcs raftpb.ConfState .Idle ∗
    isChan nv.readyc' γrd Ready ∗ ownChan γrd Ready .Idle ∗
    isChan nv.advancec' γa Unit ∗ ownChan γa Unit .Idle ∗
    isChan nv.tickc' γt Unit ∗ ownChan γt Unit (.Buffered []) ∗
    isChan nv.done' γd Unit ∗ ownChan γd Unit .Idle ∗
    isChan nv.stop' γs Unit ∗ ownChan γs Unit .Idle ∗
    isChan nv.status' γst GoChan ∗ ownChan γst GoChan .Idle)

/-- See the file header. -/
abbrev newNode.spec : Prop :=
  ∀ (rn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions newNode [])) (Val #rn))
  {{ (nv : node), RET #nv; ⌜nv.rn' = rn⌝ ∗ newNodeChans nv }}

end spec

end EtcdGrove
end Perennial
