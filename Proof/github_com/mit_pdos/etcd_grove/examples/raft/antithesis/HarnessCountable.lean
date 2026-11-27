/-
Lean-first (no Rocq counterpart).

# The parity driver's ghost values are countable (#33 parity B1)

The run's invariant keeps each node's view (`AntSim.NodeView`, design §3.2) in a ghost variable,
which needs it countable: S4's instances (`HarnessInv.lean`'s, renamed `hc_*`, which they replace)
for the protocol state, and the parity `NodeView`'s new parts (`RState`, `DurW`, `MemRec`, `XMsg`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Rel
public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open go_etcd_io.raft.v3

section countable
variable [GooseExts]

instance hc_role_countable : Pos.Countable Role :=
  countableOfLeftInverse
    (fun r : Role => match r with | .follower => (0 : Nat) | .candidate => 1 | .leader => 2)
    (fun k => match k with | 1 => .candidate | 2 => .leader | _ => .follower)
    (fun r => by cases r <;> rfl)

instance hc_msgType_countable : Pos.Countable MsgType :=
  countableOfLeftInverse
    (fun t : MsgType => match t with
      | .vote => (0 : Nat) | .voteResp => 1 | .app => 2 | .appResp => 3 | .heartbeat => 4
      | .heartbeatResp => 5 | .propose => 6 | .snap => 7 | .preVote => 8 | .preVoteResp => 9
      | .readIndex => 10 | .readIndexResp => 11)
    (fun k => match k with
      | 1 => .voteResp | 2 => .app | 3 => .appResp | 4 => .heartbeat | 5 => .heartbeatResp
      | 6 => .propose | 7 => .snap | 8 => .preVote | 9 => .preVoteResp | 10 => .readIndex
      | 11 => .readIndexResp | _ => .vote)
    (fun t => by cases t <;> rfl)

instance hc_csLists_countable : Pos.Countable CSLists :=
  countableOfLeftInverse (fun c : CSLists => (c.voters, c.learners, c.outgoing, c.learnersNext))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

instance hc_pmsg_countable : Pos.Countable Msg :=
  countableOfLeftInverse
    (fun m : Msg => ((m.ty, m.src, m.dst, m.term, m.reject, m.index),
      (m.logterm, m.commit, m.rejecthint, m.entries, m.cl, m.al, m.ctx)))
    (fun p => ⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2,
      p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

instance hc_readStateM_countable : Pos.Countable ReadStateM :=
  countableOfLeftInverse (fun r : ReadStateM => (r.Index', r.RequestCtx')) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

instance hc_readReq_countable : Pos.Countable ReadReq :=
  countableOfLeftInverse (fun r : ReadReq => (r.index, r.src, r.ents)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (fun _ => rfl)

instance hc_readOnly_countable : Pos.Countable ReadOnly :=
  countableOfLeftInverse (fun r : ReadOnly => (r.pending, r.acks, r.confirmed))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

instance hc_rdState_countable : Pos.Countable RdState :=
  countableOfLeftInverse (fun r : RdState => (r.states, r.ro, r.pend)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (fun _ => rfl)

instance hc_pstate_countable : Pos.Countable PState :=
  countableOfLeftInverse
    (fun s : PState => ((s.term, s.vote, s.lead, s.role, s.votes, s.outbox),
      (s.base, s.log, s.commit, s.matched, s.rd)))
    (fun p => ⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2,
      p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩)
    (fun _ => rfl)

instance hc_rstate_countable : Pos.Countable RState :=
  countableOfLeftInverse
    (fun r : RState => (r.p, r.applied, r.pci, r.snap, r.cidx, r.cfg, r.fp))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩)
    (fun _ => rfl)

instance hc_durW_countable : Pos.Countable AntSim.DurW :=
  countableOfLeftInverse (fun w : AntSim.DurW => (w.term, w.vote, w.commit, w.log))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

instance hc_memRec_countable : Pos.Countable AntSim.MemRec :=
  countableOfLeftInverse
    (fun m : AntSim.MemRec => ((m.role, m.pre, m.term, m.vote), (m.commit, m.ents, m.snap, m.cause, m.byE)))
    (fun p => ⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩)
    (fun _ => rfl)

instance hc_xty_countable : Pos.Countable XTy :=
  countableOfLeftInverse (fun t : XTy => match t with | .transferLeader => (0 : Nat) | .timeoutNow => 1)
    (fun k => match k with | 1 => .timeoutNow | _ => .transferLeader) (fun t => by cases t <;> rfl)

instance hc_xmsg_countable : Pos.Countable XMsg :=
  countableOfLeftInverse (fun x : XMsg => (x.ty, x.src, x.dst, x.term))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

instance hc_nodeView_countable : Pos.Countable AntSim.NodeView :=
  countableOfLeftInverse
    (fun v : AntSim.NodeView =>
      ((v.r, v.delivered, v.dur, v.undo, v.made), (v.mems, v.conf, v.confAt, v.pre, v.reads),
       (v.alive, v.qs, v.pend, v.xpend, v.ce), (v.rpend, v.byE, v.cause, v.xcause, v.told)))
    (fun p =>
      { r := p.1.1, delivered := p.1.2.1, dur := p.1.2.2.1, undo := p.1.2.2.2.1, made := p.1.2.2.2.2,
        mems := p.2.1.1, conf := p.2.1.2.1, confAt := p.2.1.2.2.1, pre := p.2.1.2.2.2.1,
        reads := p.2.1.2.2.2.2,
        alive := p.2.2.1.1, qs := p.2.2.1.2.1, pend := p.2.2.1.2.2.1, xpend := p.2.2.1.2.2.2.1,
        ce := p.2.2.1.2.2.2.2,
        rpend := p.2.2.2.1, byE := p.2.2.2.2.1, cause := p.2.2.2.2.2.1, xcause := p.2.2.2.2.2.2.1,
        told := p.2.2.2.2.2.2.2 })
    (fun _ => rfl)

instance hc_input_countable :
    Pos.Countable github_com.mit_pdos.etcd_grove.examples.raft.antithesis.input :=
  countableOfLeftInverse
    (fun i : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.input =>
      (i.kind', i.msg', i.data', i.to', i.ok'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

end countable

end AntHarness
end EtcdGrove
end Perennial
