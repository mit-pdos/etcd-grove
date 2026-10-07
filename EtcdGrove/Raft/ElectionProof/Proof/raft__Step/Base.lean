/- Port of the part of election_proof/proof_raft__Step.v (and of
postulates_raft__Step.v) that the branch modules of `Proof/raft__Step/` share.

Rocq's `STEP_POSTULATES` (`postulates_raft__Step.v`) is the module type every branch
file of `proof_raft__Step_helpers/` is a functor over; here it is the structure
`raft.Step.Postulates`, which each branch lemma takes as its first argument.

Lean notes:
* Rocq's `step_post`, `ghost_step_recv`, `finish_branch` and `finish_branch0` are in
  `proof_raft__Step.v` itself, before the dispatch; here they are in this module so
  that the dispatch and the branch modules can share them: `stepPost` (as before, in
  `Perennial.EtcdGrove`), and `StepProof.ghost_step_recv`, `StepProof.finish_branch`,
  `StepProof.finish_branch0`.
* Rocq's `w32_ne` (`defs.v`) is the tactic macro `w32_ne` below.
* Everything below works at `HeapGS HasLC.hasLC GF` with `[AllG GF]`, as
  `raft.Step.spec` does.
* The branch modules put their lemmas in `namespace StepProof` (Rocq: one functor
  module per file, `StepMsgVoteGt` etc.); the names are unique across the modules, as
  they are in Rocq (all the functors are instantiated in one file).
-/
import EtcdGrove.Raft.ElectionProof.Spec.raft__Step
import EtcdGrove.Raft.ElectionProof.Spec.raft__hup
import EtcdGrove.Raft.ElectionProof.Spec.raft__becomeFollower
import EtcdGrove.Raft.ElectionProof.Spec.voteRespMsgType
import EtcdGrove.Raft.ElectionProof.Spec.raft__send
import EtcdGrove.Raft.ElectionProof.Spec.stepCandidate
import EtcdGrove.Raft.ElectionProof.Spec.stepFollower
import EtcdGrove.Raft.ElectionProof.Spec.stepLeader
import EtcdGrove.Raft.ElectionProof.Spec.traceReceiveMessage
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__lastEntryID
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__isUpToDate

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- Rocq `w32_ne`: two distinct message-type constants differ. -/
macro "w32_ne" : tactic =>
  `(tactic| (simp only [Perennial.EtcdGrove.MsgBeat, Perennial.EtcdGrove.MsgHup,
      Perennial.EtcdGrove.MsgProp, Perennial.EtcdGrove.MsgApp, Perennial.EtcdGrove.MsgAppResp,
      Perennial.EtcdGrove.MsgVote, Perennial.EtcdGrove.MsgVoteResp, Perennial.EtcdGrove.MsgSnap,
      Perennial.EtcdGrove.MsgHeartbeat, Perennial.EtcdGrove.MsgHeartbeatResp,
      Perennial.EtcdGrove.MsgPreVote, Perennial.EtcdGrove.MsgPreVoteResp,
      ne_eq]; word))

section base
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- Rocq `STEP_POSTULATES`: the callee specs the branches are proved from. -/
structure raft.Step.Postulates : Prop where
  hup : raft.hup.spec (GF := GF) (hG := hG)
  becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG)
  voteRespMsgType : voteRespMsgType.spec (GF := GF) (hG := hG)
  send : raft.send.spec (GF := GF) (hG := hG)
  stepCandidate : stepCandidate.spec (GF := GF) (hG := hG)
  /-- A `MsgVoteResp` falls through `Step`'s type switch to `r.step(m)`, which is any
  of the three depending on the role -- on `m.Term > r.Term` the term preamble has
  already run `becomeFollower`. -/
  stepFollower : stepFollower.spec (GF := GF) (hG := hG)
  stepLeader : stepLeader.spec (GF := GF) (hG := hG)
  traceReceiveMessage : traceReceiveMessage.spec (GF := GF) (hG := hG)
  lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG)
  isUpToDate : raftLog.isUpToDate.spec (GF := GF) (hG := hG)

/-- What `raft.Step.spec`'s postcondition hands to `Φ`: the continuation every dispatch
lemma below ends in. -/
def stepPost (γ : RaftElectionNames) (cfg : GSet w64) (r : Loc) (id : w64) (ps : PState)
    (m : raftpb.Message) (Φ : val → IProp GF) : IProp GF :=
  iprop(∀ (err : GoInterface) (s' : NState) (ps' : PState),
    ("Hphys" ∷ ownRaftPhys cfg r id s' ∗
     "Hghost" ∷ ownRaftGhost γ id ps' ∗
     "%Hrel" ∷ ⌜NStateRel s' ps'⌝ ∗
     "%Hrefines" ∷ ⌜∃ recv, Step cfg id ps recv ps'⌝ ∗
     "Herr" ∷ (⌜err = interface.nil⌝ ∨
               (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err))) -∗ Φ #err)

namespace StepProof

/-- The one ghost update of a branch: `recv` is the incoming message, some number of
times, and that message is `isMessage`. -/
theorem ghost_step_recv (γ : RaftElectionNames) (cfg : GSet w64) (id : w64)
    (ps ps' : PState) (a : Msg) (recv : List Msg)
    (Hcfg : γ.reCfg = cfg) (Hrecv : ∀ m' ∈ recv, m' = a) (Hstep : Step cfg id ps recv ps') :
    ⊢ isMessage (GF := GF) γ a -∗ ownRaftGhost γ id ps ={⊤}=∗ ownRaftGhost γ id ps' := by
  subst Hcfg
  iintro #Hm Hg
  ihave Hall : ([∗list] m ∈ recv, isMessage (GF := GF) γ m) $$ []
  · iapply (BigSepL.bigSepL_intro (P := iprop(□ isMessage (GF := GF) γ a))
      (fun k x hx => by
        rw [Hrecv x (List.mem_of_getElem? hx)]
        exact intuitionistically_elim))
    iexact Hm
  iapply ownRaftGhost_step γ id ps recv ps' Hstep $$ Hall Hg

/-- A branch's postcondition, delivered: the ghost step, then `Φ`. -/
theorem finish_branch (γ : RaftElectionNames) (cfg : GSet w64) (r : Loc) (id : w64)
    (s s' : NState) (m : raftpb.Message) (a : Msg) (recv : List Msg) (err : GoInterface)
    (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hwf' : NStateWf s') (Hrecv : ∀ m' ∈ recv, m' = a)
    (Hstep : Step cfg id (toPState s) recv (toPState s')) :
    ⊢ isMessage γ a -∗
      ownRaftGhost γ id (toPState s) -∗
      ownRaftPhys cfg r id s' -∗
      (⌜err = interface.nil⌝ ∨
        (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err)) -∗
      stepPost γ cfg r id (toPState s) m Φ -∗
      |={⊤}=> Φ #err := by
  iintro #Hm Hghost Hphys Herr HΦ
  imod ghost_step_recv γ cfg id _ _ a recv Hcfg Hrecv Hstep $$ Hm Hghost with Hghost
  imodintro
  unfold stepPost
  iapply HΦ $$ %err %s' %(toPState s')
  iframe Hphys Hghost Herr
  ipureintro
  exact ⟨⟨rfl, Hwf'⟩, ⟨recv, Hstep⟩⟩

/-- The same, for a branch that consumed nothing. -/
theorem finish_branch0 (γ : RaftElectionNames) (cfg : GSet w64) (r : Loc) (id : w64)
    (s s' : NState) (m : raftpb.Message) (err : GoInterface) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hwf' : NStateWf s')
    (Hstep : Step cfg id (toPState s) [] (toPState s')) :
    ⊢ ownRaftGhost γ id (toPState s) -∗
      ownRaftPhys cfg r id s' -∗
      (⌜err = interface.nil⌝ ∨
        (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err)) -∗
      stepPost γ cfg r id (toPState s) m Φ -∗
      |={⊤}=> Φ #err := by
  iintro Hghost Hphys Herr HΦ
  have Hst' : Step γ.reCfg id (toPState s) [] (toPState s') := by rw [Hcfg]; exact Hstep
  imod ownRaftGhost_step_0 γ id _ _ Hst' $$ Hghost with Hghost
  imodintro
  unfold stepPost
  iapply HΦ $$ %err %s' %(toPState s')
  iframe Hphys Hghost Herr
  ipureintro
  exact ⟨⟨rfl, Hwf'⟩, ⟨[], Hstep⟩⟩

end StepProof

end base

end EtcdGrove
end Perennial
