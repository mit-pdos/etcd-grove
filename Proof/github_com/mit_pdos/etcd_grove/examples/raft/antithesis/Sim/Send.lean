/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `send` (#33 S4, the invariant phase)

`antSim_send` (`Stmts.lean`): the next unreported message `q` of a node's `Ready` is reported
(`drain`, `evSend`) and taken (`Send`, B 510-593): after the `GC` steps due (`antSim_gc`), it is from
the node (or a forwarded proposal) to another server (`PendOk`), and by type (`notes/antithesis-rawnode-design.md`
§3.3): a vote request is the node's campaign's at its term (`CandPart`'s `VoteRequest`); a grant is
of the node's vote at its term (C3: the vote is in `votes`), and adds the grant fact; an append or a
heartbeat is the leader's at its term, `Sendable` from its log (`LeaderPart`, C3's commit facts,
`sendable_leader`); an acknowledgement answers the drain's `recv` (`pending[n]`, `Sendable` by C4)
and adds its ack fact, confirming the prefix it matched (log matching, `RaftLaws`) or at the commit
index (stale); a heartbeat response is at the node's term; a forwarded proposal is not checked.
The relation after it is `send_rel` (`SendRel.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.SendRel

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

section send
variable [GooseExts]

theorem isForwarded_prop : isForwarded go!"prop" = true := by decide
theorem isUnmodelled_prop : isUnmodelled go!"prop" = true := by decide

set_option hygiene false in
/-- `Step` of a `send` report evaluated, with the message's fields and the given facts. -/
local syntax "send_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| send_simp [$hs,*]) => `(tactic|
    (unfold State.step
     simp (config := { decide := true }) only [$hs,*, evSend, idx_name hc, State.bind, State.send, eok_bind,
       epure, pure_bind, ite_true, ite_false, need, Bool.false_eq_true, bne_self_eq_false, Option.isSome_none,
       Bool.or_false, Bool.false_and, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and, msgOf, Msg.from_,
       Msg.to_, Msg.typ, Msg.term_, Msg.index_, Msg.reject_, Msg.logTerm_, Msg.entries_, Msg.commit_,
       server_of hc n, hty, msgTypeStr, hsrv, hne, andM_true, andM_false, orM_true, orM_false, orM_ok_true,
       Bool.not_true, Bool.not_false, beq_self_eq_true, isReq, snapOk, reqFactIn, toAppendFact, voteFact,
       isForwarded_prop, isUnmodelled_prop, msgSeqHead]))

theorem orM_ok_true (b : Bool) : AntCheck.orM (.ok b) (.ok true) = .ok true := by cases b <;> rfl

theorem cons_bne_nil' {α : Type} [BEq α] (x : α) (l : List α) : ((x :: l) != []) = true := rfl
theorem cons_beq_nil' {α : Type} [BEq α] (x : α) (l : List α) : ((x :: l) == []) = false := rfl
theorem cons_get0 {α : Type} [Inhabited α] (x : α) (l : List α) : (x :: l)[0]! = x := rfl
theorem decide_lt_self (x : Int) : decide (x < x) = false := decide_eq_false (Int.lt_irrefl _)

variable {S : State} (n : Fin 3) (q : Msg) (b : Str) (hc : S.cfg = cfg3)
  (hsrv : S.cfg.server.has (nameOf q.dst) = true) (hne : (nameOf q.dst != nameOf (nodeId n)) = true)
include hc hsrv hne

theorem send_vote_eq (hty : q.ty = .vote) (hsrc : q.src = nodeId n)
    (hterm : S.currentTerm[n.val]! = uint.Z q.term)
    (hvf : S.msgs.contains (Fact.mk go!"vote" (nameOf (nodeId n)) [] (uint.Z q.term) (uint.Z q.index)
      (uint.Z q.logterm) 0) = true) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  send_simp [hsrc, beq_self_eq_true, orM_true, Bool.not_true, Bool.false_eq_true, ite_false, eok_bind,
    voteFact, need, Msg.term_, Msg.index_, Msg.logTerm_, Msg.from_, pure_bind, epure, hterm, hvf, andM_true]
  rfl

theorem send_voteRej_eq (hty : q.ty = .voteResp) (hsrc : q.src = nodeId n) (hrej : q.reject = true) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  send_simp [hsrc, beq_self_eq_true, orM_true, Bool.not_true, Bool.false_eq_true, ite_false, eok_bind, hrej]
  rfl

theorem send_grant_eq (hty : q.ty = .voteResp) (hsrc : q.src = nodeId n) (hrej : q.reject = false)
    (hv : S.votes.contains (VoteRec.mk (nameOf (nodeId n)) (uint.Z q.term) (nameOf q.dst)) = true) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val
      (lset.add S.msgs (Fact.mk go!"grant" (nameOf (nodeId n)) (nameOf q.dst) (uint.Z q.term) 0 0 0))
      S.confirmed)) := by
  send_simp [hsrc, beq_self_eq_true, orM_true, Bool.not_true, Bool.false_eq_true, ite_false, eok_bind, hrej,
    hv, Bool.true_or]
  rfl

theorem send_app_eq (hty : q.ty = .app) (hsrc : q.src = nodeId n)
    (hterm : S.currentTerm[n.val]! = uint.Z q.term) (hrole : S.role[n.val]! = leader)
    (hsd : S.sendable ⟨nameOf (nodeId n), nameOf q.dst, uint.Z q.term, uint.Z q.index, uint.Z q.logterm,
      logOf q.entries, uint.Z q.commit⟩ = .ok true) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  send_simp [hsrc, beq_self_eq_true, orM_true, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true, eok_bind, hterm, hrole, isReq, snapOk, reqFactIn, toAppendFact,
    need, Msg.typ, Msg.term_, Msg.index_, Msg.logTerm_, Msg.from_, Msg.to_, Msg.entries_, Msg.commit_,
    pure_bind, epure, hsd, andM_true, orM_false, Bool.true_or, Bool.or_true]
  rfl

theorem send_hb_eq (hty : q.ty = .heartbeat) (hsrc : q.src = nodeId n)
    (hterm : S.currentTerm[n.val]! = uint.Z q.term) (hrole : S.role[n.val]! = leader)
    (hsd : S.sendable ⟨nameOf (nodeId n), nameOf q.dst, uint.Z q.term, uint.Z q.index, uint.Z q.logterm,
      logOf q.entries, uint.Z q.commit⟩ = .ok true) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  send_simp [hsrc, beq_self_eq_true, orM_true, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true, eok_bind, hterm, hrole, isReq, snapOk, reqFactIn, toAppendFact,
    need, Msg.typ, Msg.term_, Msg.index_, Msg.logTerm_, Msg.from_, Msg.to_, Msg.entries_, Msg.commit_,
    pure_bind, epure, hsd, andM_true, orM_false, Bool.true_or, Bool.or_true]
  rfl

theorem send_hbresp_eq (hty : q.ty = .heartbeatResp) (hsrc : q.src = nodeId n)
    (hle : S.currentTerm[n.val]! ≤ uint.Z q.term) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  send_simp [hsrc, beq_self_eq_true, orM_true, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true, eok_bind, isReq, decide_eq_true hle]
  rfl

theorem send_prop_eq (hty : q.ty = .propose) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  send_simp [isForwarded, isUnmodelled, Bool.or_true, Bool.true_or,
    orM_ok_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, eok_bind, isReq, need, Msg.typ,
    pure_bind, epure]
  rfl

theorem send_appRespRej_eq (hty : q.ty = .appResp) (hsrc : q.src = nodeId n) (hrej : q.reject = true) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  send_simp [hsrc, beq_self_eq_true, orM_true, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true, eok_bind, isReq, hrej]
  rfl

/-- The append the drain's `recv` handled, as `Send` reads it (`ReqFactIn` of `pending[n]`). -/
def recvFact (m : Msg) (id : w64) : AppendFact :=
  ⟨nameOf m.src, nameOf id, uint.Z m.term, uint.Z m.index, uint.Z m.logterm, logOf m.entries, uint.Z m.commit⟩

/-- The last index of that append. -/
def recvLast (m : Msg) : Int := uint.Z m.index + ((logOf m.entries).length : Int)

/-- The confirmation an accepting acknowledgement leaves (B 568-570). -/
def ackConf (old : Confirmed) (t last : Int) : Confirmed :=
  ⟨t, if old.term == t then imax old.index last else last⟩

theorem send_appResp0_eq (hty : q.ty = .appResp) (hsrc : q.src = nodeId n) (hrej : q.reject = false) (m : Msg)
    (hpd : S.pending[n.val]! = [msgOf m (nodeId n)]) (hm : m.ty = .app)
    (hmt : S.currentTerm[n.val]! = uint.Z m.term) (hi : (uint.Z q.index == 0) = true) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  send_simp [hsrc, hrej, hpd, hm, hmt, cons_bne_nil', cons_beq_nil', cons_get0, decide_lt_self,
    decide_false, hi]
  rfl

theorem send_ack_eq (hty : q.ty = .appResp) (hsrc : q.src = nodeId n) (hrej : q.reject = false) (m : Msg)
    (hpd : S.pending[n.val]! = [msgOf m (nodeId n)]) (hm : m.ty = .app)
    (hmt : S.currentTerm[n.val]! = uint.Z m.term) (hi : (uint.Z q.index == 0) = false)
    (hsd : S.sendable (recvFact m (nodeId n)) = .ok true)
    (hqd : q.dst = m.src) (hqt : uint.Z q.term = uint.Z m.term)
    (hG : AntCheck.andM (.ok (uint.Z q.index == recvLast m))
      (AntCheck.andM (S.prevOk n.val (recvFact m (nodeId n)))
        (S.hasFirst n.val (recvFact m (nodeId n)) ((logOf m.entries).length : Int))) = .ok true) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val
      (lset.add S.msgs (ackFact (nameOf (nodeId n)) (nameOf m.src) (uint.Z m.term) (recvLast m)))
      (S.confirmed.set n.val (ackConf S.confirmed[n.val]! (uint.Z m.term) (recvLast m))))) := by
  rw [hqd] at hsrv hne
  unfold recvFact recvLast ackConf at *
  send_simp [hsrc, hrej, hpd, hm, hmt, cons_bne_nil', cons_beq_nil', cons_get0, decide_lt_self,
    decide_false, hi, hsd, hqd, hqt, hG]
  rfl

theorem send_stale_eq (hty : q.ty = .appResp) (hsrc : q.src = nodeId n) (hrej : q.reject = false) (m : Msg)
    (hpd : S.pending[n.val]! = [msgOf m (nodeId n)]) (hm : m.ty = .app)
    (hmt : S.currentTerm[n.val]! = uint.Z m.term) (hi : (uint.Z q.index == 0) = false)
    (hsd : S.sendable (recvFact m (nodeId n)) = .ok true)
    (hqd : q.dst = m.src) (hqt : uint.Z q.term = uint.Z m.term)
    (hG : AntCheck.andM (.ok (uint.Z q.index == recvLast m))
      (AntCheck.andM (S.prevOk n.val (recvFact m (nodeId n)))
        (S.hasFirst n.val (recvFact m (nodeId n)) ((logOf m.entries).length : Int))) = .ok false)
    (hst : uint.Z m.index < S.commitIndex[n.val]!) (hqi : uint.Z q.index = S.commitIndex[n.val]!) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val
      (lset.add S.msgs (ackFact (nameOf (nodeId n)) (nameOf m.src) (uint.Z m.term) S.commitIndex[n.val]!))
      S.confirmed)) := by
  rw [hqd] at hsrv hne
  unfold recvFact recvLast at *
  have h1 : decide (uint.Z m.index < S.commitIndex[n.val]!) = true := decide_eq_true hst
  have h2 : (uint.Z q.index == S.commitIndex[n.val]!) = true := by rw [hqi]; exact beq_self_eq_true _
  send_simp [hsrc, hrej, hpd, hm, hmt, cons_bne_nil', cons_beq_nil', cons_get0, decide_lt_self,
    decide_false, hi, hsd, hqd, hqt, hG, h1, h2]
  rfl

end send

end AntSim
end EtcdGrove
end Perennial
