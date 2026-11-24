-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/RawNode__Ready.lean` (etc/copy-part.py; rerun it, do not edit).
/- Port of election_proof/proof_RawNode__Ready.v (857d09190).

The Rocq main proof is `Admitted` after its WIP script (it ends in `Show.` once the raft
struct is closed with empty queues). Here the script was ported and then finished (the
tail after the Rocq's `Show.` -- the postcondition: refolding `ownRawNode` at the new
state, the committed entries extending `delivered`, the messages' `isRaftMsg` -- is new,
built from the Rocq's own helper lemmas). Since 2026-10-09 the spec is client-facing.

Since 2026-10-10 the proof is split along the Go code, `Ready` being
`readyWithoutAccept` then `acceptReady` (which `node.go` calls apart, handing the `Ready`
to the application in between): the two halves are proved in
`RawNode__readyWithoutAccept.lean` and `RawNode__acceptReady.lean`, through the
intermediate predicate `ownRawNodeReady` (`InvRawnodeReady.lean`), and `Ready`'s proof
composes their specs.

Raft v3.7 (2026-10-16, stage R5): the same composition; the messages handed out at
`readyDq` (D8) and the hard state (`hsOpt`) pass through.

(#33 S4, P-raft-3) The proof is the strengthened triple's, `RawNode.Ready.wp_absProof`
(`RawNode__ReadyAbs.lean`, where this file's composition moved, over `ownRawNodeAt`); the old spec is
its corollary (`RawNode.Ready.spec_of_abs`, `RawNodeSpecOfAbs.lean`). One proof.
-/
module

public import KvNet.Spec.go_etcd_io.raft.v3.RawNode__Ready
public import KvNet.Proof.go_etcd_io.raft.v3.RawNode__ReadyAbs
public import KvNet.Proof.go_etcd_io.raft.v3.RawNodeSpecOfAbs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem RawNode.Ready.wp_proof
    (wp_RawNode_readyWithoutAccept : RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG))
    (wp_RawNode_acceptReady : RawNode.acceptReady.spec (GF := GF) (hG := hG)) :
    RawNode.Ready.spec (GF := GF) (hG := hG) :=
  RawNode.Ready.spec_of_abs (RawNode.Ready.wp_absProof wp_RawNode_readyWithoutAccept
    wp_RawNode_acceptReady)

end proof

end EtcdGrove
end Perennial
