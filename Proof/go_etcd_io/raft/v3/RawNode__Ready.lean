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
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Ready
public import Spec.go_etcd_io.raft.v3.RawNode__readyWithoutAccept
public import Spec.go_etcd_io.raft.v3.RawNode__acceptReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

theorem RawNode.Ready.wp_proof
    (wp_RawNode_readyWithoutAccept : RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG))
    (wp_RawNode_acceptReady : RawNode.acceptReady.spec (GF := GF) (hG := hG)) :
    RawNode.Ready.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs Hsteps0 Hunp0
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_RawNode_readyWithoutAccept γ rn id rs Hsteps0 Hunp0 $$ [$Hrn]
    as %rd %ce %es %ms H
  iNamed H
  wp_apply wp_RawNode_acceptReady γ rn id rs rd ce es ms $$ [$Hrn] as %steps H
  iNamed H
  iapply HΦ $$ %rd %ce %es %ms %steps
  iframe Hrn Hce Hcommitted Hents Hmsgs Hmsgs_cap Hmsgs_ok Happ
  ipureintro; exact ⟨Hmsgs_term, Hsnapz⟩

end proof

end EtcdGrove
end Perennial
