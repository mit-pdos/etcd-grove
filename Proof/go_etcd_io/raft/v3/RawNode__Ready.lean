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
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Ready
public import Spec.go_etcd_io.raft.v3.RawNode__readyWithoutAccept
public import Spec.go_etcd_io.raft.v3.RawNode__acceptReady
-- (2026-11-01, durability stage II (k)) *enter* (`raft_enter`)
import Proof.go_etcd_io.raft.v3.Protocol.Enter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem RawNode.Ready.wp_proof
    (wp_RawNode_readyWithoutAccept : RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG))
    (wp_RawNode_acceptReady : RawNode.acceptReady.spec (GF := GF) (hG := hG)) :
    RawNode.Ready.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs q g Hsteps0 Hunp0
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_RawNode_readyWithoutAccept γ rn id rs Hsteps0 Hunp0 $$ [$Hrn]
    as %rd %ce %es %ms %sts %h %L H
  iNamed H
  -- (2026-11-01, durability stage II (k)) the hand-out is the cut: the batch queued in `g`
  imod ownRawNodeReady_handout ⊤ γ rn id rs rd ce es ms L q g h CoPset.subseteq_top
    $$ Hhard Hlive Hfree Hrn
    with ⟨%W, %ss0, Hrn, Happ, #Hfrz, #Hdk, Hcr, -, -, Hlive, Hpb, #Hss0, %Hssn0, #Hmw, #Hml, -⟩
  wp_apply wp_RawNode_acceptReady γ rn id { rs with bw := W } rd ce es ms h L $$ [$Hrn $Hhard]
    as %steps %ss H
  iNamed H
  -- the soft state the node records is the cut's
  ihave %Hsseq := softStateIs_agree rd.SoftState' ss0 ss Hssn0 Hssn $$ [Hss0 Hss]
  · iframe Hss0 Hss
  subst Hsseq
  iapply HΦ $$ %rd %ce %es %ms %sts %h %steps %L %ss0 %W
  iframe Hss Hce Hcommitted Hents Hmsgs Hmsgs_cap Hmsgs_own Hcr Happ Hrs Hrs_ok Hhard Hhsw
    Hsnapz Hfrz Hdk Hlive
  isplitl [Hrn]
  · iExactEq Hrn; rfl
  isplitl [Hpb]
  · iintro %E %q' %HE ⟨Hd, Hl⟩
    imod raft_enter E γ id rs.dur q' g _ W HE $$ Hd Hl Hpb with ⟨Hd, Hl, Hf, #Hfr⟩
    imodintro
    iframe Hd Hl Hf Hfr
    iapply bigSepL_wand_pers (durFrags (GF := GF) γ id W) (fun q : QMsg => isRaftMsg γ id q.st) ms
      $$ Hmw Hfr
  isplitr
  · iexact Hml
  ipureintro; exact ⟨Hmsgs_term, Hpsn⟩

end proof

end EtcdGrove
end Perennial
