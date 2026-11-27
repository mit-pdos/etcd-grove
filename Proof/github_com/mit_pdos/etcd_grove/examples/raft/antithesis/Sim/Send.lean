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

variable {R : RunCfg} {S : State} (n : Fin R.N) (q : Msg) (b : Str) (hc : S.cfg = R.cfg)
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

/-- A forwarded read request (B 700 `isForwarded`: any `From`; B 702 `isUnmodelled`) changes nothing. -/
theorem send_readIdx_eq (hty : q.ty = .readIndex) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  send_simp [isForwarded, isUnmodelled, Bool.or_true, Bool.true_or,
    orM_ok_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, eok_bind, isReq, need, Msg.typ,
    pure_bind, epure]
  rfl

/-- A read-index response (B 702 `isUnmodelled`) changes nothing. -/
theorem send_readResp_eq (hty : q.ty = .readIndexResp) (hsrc : q.src = nodeId n) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  send_simp [hsrc, beq_self_eq_true, orM_true, Bool.not_true, isUnmodelled, Bool.or_true, Bool.true_or,
    Bool.false_eq_true, ite_false, ite_true, eok_bind, isReq, need, Msg.typ, pure_bind, epure]
  all_goals rfl

/-- A pre-vote request or response (B 702 `isUnmodelled`) changes nothing. -/
theorem send_pre_eq (hty : q.ty = .preVote ∨ q.ty = .preVoteResp) (hsrc : q.src = nodeId n) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  rcases hty with hty | hty <;>
  send_simp [hsrc, beq_self_eq_true, orM_true, Bool.not_true, isUnmodelled, Bool.or_true, Bool.true_or,
    Bool.false_eq_true, ite_false, ite_true, eok_bind, isReq, need, Msg.typ, pure_bind, epure]
  all_goals rfl

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

/-- A stale `MsgApp`'s or `MsgHeartbeat`'s empty answer (`StaleEnd`, B 553-556: `pending[n]` a request
of a term below the node's; the answer at index `0` and the node's term) changes nothing. -/
theorem send_appRespStale_eq (hty : q.ty = .appResp) (hsrc : q.src = nodeId n) (hrej : q.reject = false)
    (m : Msg) (hpd : S.pending[n.val]! = [msgOf m (nodeId n)]) (hm : m.ty = .app ∨ m.ty = .heartbeat)
    (hlt : uint.Z m.term < S.currentTerm[n.val]!) (hi : (uint.Z q.index == 0) = true)
    (hqt : uint.Z q.term = S.currentTerm[n.val]!) :
    S.step (evSend (nodeId n) b q) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  rcases hm with hm | hm <;>
  send_simp [hsrc, hrej, hpd, hm, cons_bne_nil', cons_beq_nil', cons_get0, decide_eq_true hlt, hi, hqt]
  all_goals rfl

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

omit hc hsrv hne in
/-- `SendOk` of a `send` that adds no fact, any type in scope. -/
theorem SendOk.plainP {R : RunCfg} {dec : CCDec} {S : State} {n : Fin R.N} {q : Msg} (hsh : Shape R S)
    (hb : BindingOk R dec S)
    (hty : q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .app ∨ q.ty = .appResp ∨ q.ty = .heartbeat ∨
      q.ty = .heartbeatResp ∨ q.ty = .propose ∨ q.ty = .preVote ∨ q.ty = .preVoteResp ∨
      q.ty = .readIndexResp)
    (hsrc : q.src = nodeId n ∧ (PreTermKeep q ∨ uint.Z q.term ≤ S.currentTerm[n.val]!))
    (hpvo : PreVoterOk R q) (hdst : ∃ j : Fin R.N, q.dst = nodeId j)
    (hreq : (q.ty = .app ∨ q.ty = .heartbeat) → (toAppendFact (msgOf q q.dst) >>= S.sendable) = .ok true)
    (hvote : q.ty = .vote → ∃ f, voteFact (msgOf q q.dst) = .ok f ∧ f ∈ S.msgs)
    (hgrant : ¬ (q.ty = .voteResp ∧ q.reject = false))
    (hack : ¬ (q.ty = .appResp ∧ q.reject = false ∧ q.index ≠ W64 0))
    (hhb : q.ty = .heartbeat → ∀ j : Fin R.N, q.dst = nodeId j → S.currentTerm[j.val]! ≤ uint.Z q.term →
      ((S.confirmed[j.val]!).term = uint.Z q.term ∧ uint.Z q.commit ≤ (S.confirmed[j.val]!).index) ∨
        uint.Z q.commit ≤ S.commitIndex[j.val]!)
    (hlcm : (q.ty = .app ∨ q.ty = .heartbeat) → S.role[n.val]! ≠ follower →
      S.currentTerm[n.val]! = uint.Z q.term → uint.Z q.commit ≤ S.commitIndex[n.val]!) :
    SendOk R S n q S.msgs S.confirmed where
  sub := fun _ h => h
  new := fun _ h h' => absurd h h'
  clen := hsh.2.2.2.2.2.2.2.2.2.2.1
  cother := fun _ _ => rfl
  conf := hb.2.2.2.2.1 n
  acks := hb.2.2.2.2.2.1 n
  ty := by rcases hty with h | h | h | h | h | h | h | h | h | h <;> simp [h]
  src := fun _ => hsrc
  fwd := fun h => by
    rcases hty with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  pvo := hpvo
  dst := hdst
  req := hreq
  vote := hvote
  grant := fun h => absurd h hgrant
  ack := fun h => absurd h hack
  ackt := fun _ h h' => absurd h h'
  cmono := .inl rfl
  hb := hhb
  lcm := hlcm

omit hc hsrv hne in
/-- `SendOk` of a `send` that adds no fact. -/
theorem SendOk.plain {R : RunCfg} {dec : CCDec} {S : State} {n : Fin R.N} {q : Msg} (hsh : Shape R S)
    (hb : BindingOk R dec S)
    (hty : q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .app ∨ q.ty = .appResp ∨ q.ty = .heartbeat ∨
      q.ty = .heartbeatResp ∨ q.ty = .propose)
    (hsrc : q.src = nodeId n ∧ uint.Z q.term ≤ S.currentTerm[n.val]!) (hdst : ∃ j : Fin R.N, q.dst = nodeId j)
    (hreq : (q.ty = .app ∨ q.ty = .heartbeat) → (toAppendFact (msgOf q q.dst) >>= S.sendable) = .ok true)
    (hvote : q.ty = .vote → ∃ f, voteFact (msgOf q q.dst) = .ok f ∧ f ∈ S.msgs)
    (hgrant : ¬ (q.ty = .voteResp ∧ q.reject = false))
    (hack : ¬ (q.ty = .appResp ∧ q.reject = false ∧ q.index ≠ W64 0))
    (hhb : q.ty = .heartbeat → ∀ j : Fin R.N, q.dst = nodeId j → S.currentTerm[j.val]! ≤ uint.Z q.term →
      ((S.confirmed[j.val]!).term = uint.Z q.term ∧ uint.Z q.commit ≤ (S.confirmed[j.val]!).index) ∨
        uint.Z q.commit ≤ S.commitIndex[j.val]!)
    (hlcm : (q.ty = .app ∨ q.ty = .heartbeat) → S.role[n.val]! ≠ follower →
      S.currentTerm[n.val]! = uint.Z q.term → uint.Z q.commit ≤ S.commitIndex[n.val]!) :
    SendOk R S n q S.msgs S.confirmed :=
  SendOk.plainP hsh hb (by rcases hty with h | h | h | h | h | h | h <;> simp [h]) ⟨hsrc.1, .inr hsrc.2⟩
    (fun _ => by rcases hty with h | h | h | h | h | h | h <;> simp [h]) hdst hreq hvote hgrant hack hhb hlcm

omit hc hsrv hne in
/-- `SendOk` of a forwarded read request (any source, a node; term `0`; unmodelled). -/
theorem SendOk.readIdx {R : RunCfg} {dec : CCDec} {S : State} {n : Fin R.N} {q : Msg} (hsh : Shape R S)
    (hb : BindingOk R dec S) (hty : q.ty = .readIndex) (h0 : q.term = W64 0)
    (hsrc : ∃ i : Fin R.N, q.src = nodeId i) (hdst : ∃ j : Fin R.N, q.dst = nodeId j) :
    SendOk R S n q S.msgs S.confirmed where
  sub := fun _ h => h
  new := fun _ h h' => absurd h h'
  clen := hsh.2.2.2.2.2.2.2.2.2.2.1
  cother := fun _ _ => rfl
  conf := hb.2.2.2.2.1 n
  acks := hb.2.2.2.2.2.1 n
  ty := by simp [hty]
  src := fun h => absurd hty h
  fwd := fun _ => ⟨h0, hsrc⟩
  pvo := fun _ => ⟨fun h => (nomatch hty.symm.trans h), fun h => (nomatch hty.symm.trans h)⟩
  dst := hdst
  req := fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)
  vote := fun h => nomatch hty.symm.trans h
  grant := fun h => nomatch hty.symm.trans h.1
  ack := fun h => nomatch hty.symm.trans h.1
  ackt := fun _ h h' => absurd h h'
  cmono := .inl rfl
  hb := fun h => nomatch hty.symm.trans h
  lcm := fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)

omit hc hsrv hne in
/-- A leader's commit index as C3 has it, for `Sendable`'s `RecordedIn` of a request's commit `c` at
most it (B 109-112). -/
theorem commit_recorded {R : RunCfg} {dec : CCDec} {S : State} {n : Fin R.N} {lg : List EntryM} {c : Nat}
    (hb : BindingOk R dec S)
    (hlg : S.log[n.val]! = logOf lg) (hc : (c : Int) ≤ S.commitIndex[n.val]!) :
    c = 0 ∨ (c ≤ lg.length ∧ c ≤ S.chain.length ∧
      (∃ x ∈ S.termLen, x.1 ≤ S.currentTerm[n.val]! ∧ (c : Int) ≤ x.2) ∧
      S.chain.take c = (logOf lg).take c) := by
  obtain ⟨h1, h2⟩ := hb.2.2.1 n
  rcases hb.2.2.2.1 n with h0 | ⟨x, hx, hx1, hx2⟩
  · left; omega
  · right
    have hlen := congrArg List.length h2
    rw [hlg] at h2 hlen
    simp only [List.length_take, logOf_length] at hlen
    refine ⟨by omega, by omega, ⟨x, hx, hx1, by omega⟩, ?_⟩
    have e : c = min c (S.commitIndex[n.val]!).toNat := by omega
    rw [e, ← List.take_take, ← List.take_take, h2]


omit hc hsrv hne in
/-- **A leader's request is `Sendable`** under C1-C3: from its term, its log at `ledLog` (C2), the
previous entry an entry of its log, the entries its slice after it, the commit at most its own. -/
theorem leader_sendable {R : RunCfg} {dec : CCDec} {S : State} {n : Fin R.N} {v : NodeView}
    (hb : BindingOk R dec S) (hct : S.currentTerm[n.val]! = uint.Z v.ps.term)
    (hlg : S.log[n.val]! = logOf v.ps.log) (hcmt : S.commitIndex[n.val]! = uint.Z v.ps.commit)
    (hfull : v.r.full = v.ps.log) (hL : LeaderPart S n v) (hrole : v.ps.role = .leader) (dst : Str) {p pt c : w64} {es : List EntryM}
    (hpt : plogTermAt base0 v.ps.log p = some pt) (hes : (v.ps.log.drop (uint.nat p)).take es.length = es)
    (hcm : uint.Z c ≤ uint.Z v.ps.commit) :
    S.sendable ⟨nameOf (nodeId n), dst, uint.Z v.ps.term, uint.Z p, uint.Z pt, logOf es, uint.Z c⟩ = .ok true := by
  obtain ⟨l1, l2, -, -⟩ := hL hrole
  rw [hfull] at l2
  obtain ⟨hp, hptt⟩ := termAt_of_plog hpt
  have hpZ : ((uint.nat p : Nat) : Int) = uint.Z p := by word
  have hcZ : ((uint.nat c : Nat) : Int) = uint.Z c := by word
  have hrec := commit_recorded (c := uint.nat c) hb hlg (by rw [hcmt, hcZ]; exact hcm)
  rw [hct] at hrec
  have := sendable_leader (S := S) (dst := dst) (pt := uint.Z pt) l1 l2 (by rw [hpZ]; exact hptt)
    (by omega) hes hrec
  rw [hpZ, hcZ] at this
  exact this

end send

section ack
variable [GooseExts]

theorem andM_ok (a b : Bool) : AntCheck.andM (.ok a) (.ok b) = .ok (a && b) := by cases a <;> rfl

theorem termAt_pos {l : List Entry} {k : Int} (h1 : 0 < k) (h2 : k ≤ l.length) :
    termAt l k = (l[(k - 1).toNat]!).term := by
  unfold termAt; simp only [gt_iff_lt, h1, h2, and_self, ite_true]

theorem TermFn.mem_of_get {α : Type} {f : TermFn α} {t : Int} {x : α} (h : f.get t = .ok x) :
    (t, x) ∈ f := by
  unfold TermFn.get at h
  split at h
  · rename_i p hp
    have h1 := List.find?_some hp
    have h2 := List.mem_of_find?_eq_some hp
    obtain ⟨a, b⟩ := p
    simp only [beq_iff_eq] at h1
    cases h; subst h1; exact h2
  · cases h

/-- What an accepting acknowledgement's guard checks besides its index (B 571): `PrevOk` and
`HasFirst` of the handled append at the node, as conditions. -/
def AckGuard (S : State) (n : Nat) (m : Msg) (id : w64) : Prop :=
  ((recvFact m id).prevLogIndex = 0 ∨ ((recvFact m id).prevLogIndex ≤ (S.log[n]!).length ∧
      ((S.log[n]!)[((recvFact m id).prevLogIndex - 1).toNat]!).term = (recvFact m id).prevLogTerm)) ∧
    ∀ k < (logOf m.entries).length, HFAt S n (recvFact m id) k

instance (S : State) (n : Nat) (m : Msg) (id : w64) : Decidable (AckGuard S n m id) := by
  unfold AckGuard; infer_instance

/-- The guard of an accepting acknowledgement (B 571) evaluated. -/
theorem ack_guard_eq (S : State) (n : Nat) (m : Msg) (id : w64) (x : Int) :
    AntCheck.andM (.ok (x == recvLast m)) (AntCheck.andM (S.prevOk n (recvFact m id))
      (S.hasFirst n (recvFact m id) ((logOf m.entries).length : Int))) =
    .ok (decide (x = recvLast m ∧ AckGuard S n m id)) := by
  have h0 : 0 ≤ (recvFact m id).prevLogIndex := by unfold recvFact; simp only; word
  rw [prevOk_eq S n _ h0, hasFirst_eq S n _ h0 (logOf m.entries).length (Nat.le_refl _), andM_ok, andM_ok]
  congr 1
  unfold AckGuard
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]

/-- Log matching (`RaftLaws`' third law) at position `k` of two certified logs, in the binding's terms. -/
theorem match_logOf {G : RaftFacts} (hl : RaftLaws G) {L1 L2 : List EntryM} (h1 : L1 ∈ G.logs)
    (h2 : L2 ∈ G.logs) {k : Nat} (hk : 1 ≤ k) (hk1 : k ≤ L1.length) (hk2 : k ≤ L2.length)
    (ht : termAt (logOf L1) k = termAt (logOf L2) k) : (logOf L1).take k = (logOf L2).take k := by
  have he : L1[k - 1]? = some L1[k - 1] := List.getElem?_eq_getElem (by omega)
  have hf : L2[k - 1]? = some L2[k - 1] := List.getElem?_eq_getElem (by omega)
  have t1 := termAt_logOf he
  have t2 := termAt_logOf hf
  have e1 : (((k - 1 : Nat)) : Int) + 1 = (k : Int) := by omega
  rw [e1] at t1 t2
  have hef : (L1[k - 1]).Term' = (L2[k - 1]).Term' := uint_Z_inj.mp (by rw [← t1, ← t2, ht])
  have := hl.2.2.1 L1 h1 L2 h2 (k - 1) _ _ he hf hef
  rw [show k - 1 + 1 = k by omega] at this
  unfold logOf
  rw [← List.map_take, ← List.map_take, this]

/-- **The prefix an accepting acknowledgement confirms** (B 571-575): the node's log and the leader
log of the append's term agree up to its last index. Its last entry (or, with no entries, the
previous one) is at the same term in both: in the node's log by `PrevOk`/`HasFirst`, in the leader
log by the append's `Sendable` slice; log matching (`RaftLaws`) between the certified logs. -/
theorem ack_match {R : RunCfg} {S : State} {net : List Msg} {G : RaftFacts} (hl : RaftLaws G)
    (hgo : GlobalOk R S net G) {n : Fin R.N} {m : Msg} {l : List Entry} (hll : S.ledLog.get (uint.Z m.term) = .ok l)
    (hsd : S.sendable (recvFact m (nodeId n)) = .ok true) (hpos : 1 ≤ recvLast m)
    (hg : AckGuard S n.val m (nodeId n)) :
    recvLast m ≤ (S.log[n.val]!).length ∧ recvLast m ≤ l.length ∧
      (S.log[n.val]!).take (recvLast m).toNat = l.take (recvLast m).toNat := by
  obtain ⟨L1, hL1, hA⟩ := hgo.2.2.1 n
  obtain ⟨L2, hL2, hl2⟩ : ∃ L2 ∈ G.logs, l = logOf L2 := by
    rcases hgo.2.2.2.1 _ (TermFn.mem_of_get hll) with ⟨-, h⟩ | ⟨L2, hL2, hl2, -⟩
    · exact ⟨bootLog R, hgo.2.2.2.2.2.2.2.1, (Prod.mk.inj h).2⟩
    · exact ⟨L2, hL2, hl2⟩
  obtain ⟨l', hl', hlen, hpt, sub, hsub, heq⟩ := sendable_inv hsd
  obtain ⟨hpv, hhf⟩ := hg
  unfold recvFact at hl' hlen hpt hsub heq hpv hhf
  simp only at hl' hlen hpt hsub heq hpv hhf
  rw [hll] at hl'; cases hl'
  unfold recvLast at *
  rw [logOf_length] at hlen hsub hhf hpos ⊢
  have hP : 0 ≤ uint.Z m.index := by word
  unfold HFAt at hhf
  generalize hAdef : S.log[n.val]! = A at hA hpv hhf ⊢
  generalize hK : m.entries.length = K at hlen hsub hhf hpos heq ⊢
  have key : uint.Z m.index + (K : Int) ≤ A.length ∧
      termAt A (uint.Z m.index + K) = termAt l (uint.Z m.index + K) := by
    by_cases hK0 : K = 0
    · rw [hK0] at hpos ⊢
      have e : uint.Z m.index + ((0 : Nat) : Int) = uint.Z m.index := by omega
      rw [e] at hpos ⊢
      rcases hpv with h | ⟨h1, h2⟩
      · omega
      · exact ⟨h1, by rw [termAt_pos (by omega) h1, h2, hpt]⟩
    · obtain ⟨h1, h2⟩ := hhf (K - 1) (by omega)
      have e1 : uint.Z m.index + (((K - 1 : Nat) : Int) + 1) = uint.Z m.index + K := by omega
      rw [e1] at h1 h2
      refine ⟨h1, ?_⟩
      rw [termAt_pos (by omega) h1, h2, termAt_pos (by omega) hlen]
      obtain ⟨hl1, hl2⟩ := entriesEqual_true heq
      have hPn : ((uint.Z m.index).toNat : Int) = uint.Z m.index := by omega
      have hs := subSeq_nat l (uint.Z m.index).toNat K (by omega)
      rw [hPn, hsub] at hs
      cases hs
      have := hl2 (K - 1) (by rw [logOf_length]; omega)
      rw [this]
      have i1 : K - 1 < ((l.drop (uint.Z m.index).toNat).take K).length := by
        rw [List.length_take, List.length_drop]; omega
      rw [getElem!_pos ((l.drop (uint.Z m.index).toNat).take K) (K - 1) i1, getElem!_pos l (uint.Z m.index + (K : Int) - 1).toNat (by omega)]
      simp only [List.getElem_take, List.getElem_drop]
      congr 2
      omega
  obtain ⟨k1, k2⟩ := key
  refine ⟨k1, hlen, ?_⟩
  have hk : ((uint.Z m.index + (K : Int)).toNat : Int) = uint.Z m.index + K := by omega
  subst hA hl2
  rw [logOf_length] at k1 hlen
  rw [← hk] at k2
  exact match_logOf hl hL1 hL2 (by omega) (by omega) (by omega) k2

theorem ackConf_term (old : Confirmed) (t last : Int) : (ackConf old t last).term = t := rfl

theorem ackConf_ge (old : Confirmed) (t last : Int) :
    last ≤ (ackConf old t last).index ∧ (old.term = t → old.index ≤ (ackConf old t last).index) := by
  unfold ackConf imax
  by_cases h : old.term = t
  · simp only [h, beq_self_eq_true, ite_true]
    constructor <;> (try intro _) <;> split <;> omega
  · have hb : (old.term == t) = false := by simpa using h
    simp only [hb, Bool.false_eq_true, ite_false]
    exact ⟨Int.le_refl _, fun h' => absurd h' h⟩

theorem ack_ne_vote : go!"ack" ≠ go!"vote" := by decide
theorem grant_ne_vote : go!"grant" ≠ go!"vote" := by decide
theorem grant_ne_ack : go!"grant" ≠ go!"ack" := by decide

theorem cfg_has (R : RunCfg) (j : Fin R.N) : R.cfg.server.has (nameOf (nodeId j)) = true := by
  rw [R.server_eq]; exact server_has j

/-- `SendOk` of a grant: the grant fact added. -/
theorem SendOk.ofGrant {R : RunCfg} {dec : CCDec} {S : State} {n : Fin R.N} {q : Msg} (hsh : Shape R S)
    (hb : BindingOk R dec S)
    (hty : q.ty = .voteResp) (hsrc : q.src = nodeId n) (hterm : uint.Z q.term ≤ S.currentTerm[n.val]!)
    (j : Fin R.N) (hj : q.dst = nodeId j) :
    SendOk R S n q (lset.add S.msgs (Fact.mk go!"grant" (nameOf (nodeId n)) (nameOf q.dst) (uint.Z q.term) 0 0 0))
      S.confirmed where
  sub := fun _ h => mem_lset_add.mpr (.inl h)
  new := fun f hf hn => by
    rcases mem_lset_add.mp hf with h | h
    · exact absurd h hn
    · subst h; exact ⟨grant_ne_vote, rfl, j, by rw [hj]⟩
  clen := hsh.2.2.2.2.2.2.2.2.2.2.1
  cother := fun _ _ => rfl
  conf := hb.2.2.2.2.1 n
  acks := fun a ha ht hs hte => by
    rcases mem_lset_add.mp ha with h | h
    · exact hb.2.2.2.2.2.1 n a h ht hs hte
    · subst h; exact absurd ht grant_ne_ack
  ty := .inr (.inl hty)
  fwd := fun h => by rw [hty] at h; cases h
  src := fun _ => ⟨hsrc, .inr hterm⟩
  pvo := fun _ => by simp [hty]
  dst := ⟨j, hj⟩
  req := fun h => by rcases h with h | h <;> rw [hty] at h <;> cases h
  vote := fun h => by rw [hty] at h; cases h
  grant := fun _ => mem_lset_add.mpr (.inr (by rw [hsrc]))
  ack := fun h => by have h1 := h.1; rw [hty] at h1; cases h1
  ackt := fun a ha hn ht => by
    rcases mem_lset_add.mp ha with h | h
    · exact absurd h hn
    · subst h; exact absurd ht grant_ne_ack
  cmono := .inl rfl
  hb := fun h => by rw [hty] at h; cases h
  lcm := fun h => by rcases h with h | h <;> rw [hty] at h <;> cases h

/-- `SendOk` of a stale acknowledgement (B 577-580): an ack fact at the commit index added. -/
theorem SendOk.ofStale {R : RunCfg} {dec : CCDec} {S : State} {n : Fin R.N} {q m : Msg} (hsh : Shape R S)
    (hb : BindingOk R dec S)
    (hty : q.ty = .appResp) (hsrc : q.src = nodeId n) (hterm : uint.Z q.term ≤ S.currentTerm[n.val]!)
    (j : Fin R.N) (hj : q.dst = nodeId j) (hqd : q.dst = m.src) (hqt : uint.Z q.term = uint.Z m.term)
    (hqi : uint.Z q.index = S.commitIndex[n.val]!) :
    SendOk R S n q (lset.add S.msgs (ackFact (nameOf (nodeId n)) (nameOf m.src) (uint.Z m.term)
      S.commitIndex[n.val]!)) S.confirmed where
  sub := fun _ h => mem_lset_add.mpr (.inl h)
  new := fun f hf hn => by
    rcases mem_lset_add.mp hf with h | h
    · exact absurd h hn
    · subst h; exact ⟨ack_ne_vote, rfl, j, by rw [← hqd, hj]; rfl⟩
  clen := hsh.2.2.2.2.2.2.2.2.2.2.1
  cother := fun _ _ => rfl
  conf := hb.2.2.2.2.1 n
  acks := fun a ha ht hs hte => by
    rcases mem_lset_add.mp ha with h | h
    · exact hb.2.2.2.2.2.1 n a h ht hs hte
    · subst h; exact .inr (Int.le_refl _)
  ty := .inr (.inr (.inr (.inl hty)))
  fwd := fun h => by rw [hty] at h; cases h
  src := fun _ => ⟨hsrc, .inr hterm⟩
  pvo := fun _ => by simp [hty]
  dst := ⟨j, hj⟩
  req := fun h => by rcases h with h | h <;> rw [hty] at h <;> cases h
  vote := fun h => by rw [hty] at h; cases h
  grant := fun h => by have h1 := h.1; rw [hty] at h1; cases h1
  ack := fun _ => ⟨_, mem_lset_add.mpr (.inr rfl), rfl, by rw [hsrc]; rfl, by rw [hqd]; rfl,
    by rw [hqt]; rfl, by rw [hqi]; exact Int.le_refl _⟩
  ackt := fun a ha hn _ => by
    rcases mem_lset_add.mp ha with h | h
    · exact absurd h hn
    · subst h; show uint.Z m.term ≤ _; omega
  cmono := .inl rfl
  hb := fun h => by rw [hty] at h; cases h
  lcm := fun h => by rcases h with h | h <;> rw [hty] at h <;> cases h

/-- `SendOk` of an accepting acknowledgement (B 571-575): its ack fact added, the node's
confirmation moved to the prefix it matched (`ack_match`), above its acks at its term. -/
theorem SendOk.ofAck {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {G : RaftFacts} {n : Fin R.N}
    {q m : Msg} (hsh : Shape R S) (hb : BindingOk R dec S) (hl : RaftLaws G) (hgo : GlobalOk R S net G)
    (hty : q.ty = .appResp) (hsrc : q.src = nodeId n) (hct : S.currentTerm[n.val]! = uint.Z m.term)
    (j : Fin R.N) (hj : q.dst = nodeId j) (hqd : q.dst = m.src) (hqt : uint.Z q.term = uint.Z m.term)
    (hqi : uint.Z q.index = recvLast m) (hi : uint.Z q.index ≠ 0)
    (hsd : S.sendable (recvFact m (nodeId n)) = .ok true) (hg : AckGuard S n.val m (nodeId n)) :
    SendOk R S n q (lset.add S.msgs (ackFact (nameOf (nodeId n)) (nameOf m.src) (uint.Z m.term) (recvLast m)))
      (S.confirmed.set n.val (ackConf S.confirmed[n.val]! (uint.Z m.term) (recvLast m))) := by
  have hlen3 : S.confirmed.length = R.N := hsh.2.2.2.2.2.2.2.2.2.2.1
  have hCn : (S.confirmed.set n.val (ackConf S.confirmed[n.val]! (uint.Z m.term) (recvLast m)))[n.val]! =
      ackConf S.confirmed[n.val]! (uint.Z m.term) (recvLast m) :=
    get!_set_self _ (by rw [hlen3]; exact n.isLt)
  have hq0 : 0 ≤ uint.Z q.index := by word
  have hge := ackConf_ge S.confirmed[n.val]! (uint.Z m.term) (recvLast m)
  refine
   { sub := fun _ h => mem_lset_add.mpr (.inl h)
     new := ?_
     clen := by rw [List.length_set]; exact hlen3
     cother := fun k hk => get!_set_ne _ _ (fun h => hk (Fin.ext h))
     conf := ?_
     acks := ?_
     ty := .inr (.inr (.inr (.inl hty)))
     fwd := fun h => by rw [hty] at h; cases h
     src := fun _ => ⟨hsrc, .inr (by omega)⟩
     pvo := fun _ => by simp [hty]
     dst := ⟨j, hj⟩
     req := fun h => by rcases h with h | h <;> rw [hty] at h <;> cases h
     vote := fun h => by rw [hty] at h; cases h
     grant := fun h => by have h1 := h.1; rw [hty] at h1; cases h1
     ack := fun _ => ⟨_, mem_lset_add.mpr (.inr rfl), rfl, by rw [hsrc]; rfl, by rw [hqd]; rfl,
       by rw [hqt]; rfl, by rw [hqi]; exact Int.le_refl _⟩
     ackt := fun a ha hn _ => by
       rcases mem_lset_add.mp ha with h | h
       · exact absurd h hn
       · subst h; show uint.Z m.term ≤ _; omega
     cmono := ?_
     hb := fun h => by rw [hty] at h; cases h
     lcm := fun h => by rcases h with h | h <;> rw [hty] at h <;> cases h }
  · intro f hf hn
    rcases mem_lset_add.mp hf with h | h
    · exact absurd h hn
    · subst h; exact ⟨ack_ne_vote, rfl, j, by rw [← hqd, hj]; rfl⟩
  · intro l hll
    rw [hCn] at hll ⊢
    rw [ackConf_term] at hll
    obtain ⟨m1, m2, m3⟩ := ack_match hl hgo hll hsd (by omega) hg
    by_cases ht : (S.confirmed[n.val]!).term = uint.Z m.term
    · obtain ⟨o1, o2, o3⟩ := hb.2.2.2.2.1 n l (by rw [ht]; exact hll)
      have e : (ackConf S.confirmed[n.val]! (uint.Z m.term) (recvLast m)).index =
          imax (S.confirmed[n.val]!).index (recvLast m) := by
        unfold ackConf; simp only [ht, beq_self_eq_true, ite_true]
      rw [e]; unfold imax
      split
      · exact ⟨o1, o2, o3⟩
      · exact ⟨m1, m2, m3⟩
    · have e : (ackConf S.confirmed[n.val]! (uint.Z m.term) (recvLast m)).index = recvLast m := by
        have hb' : ((S.confirmed[n.val]!).term == uint.Z m.term) = false := by simpa using ht
        unfold ackConf; simp only [hb', Bool.false_eq_true, ite_false]
      rw [e]; exact ⟨m1, m2, m3⟩
  · intro a ha hty' hsa hta
    rw [hCn, ackConf_term]
    have hat : a.term = uint.Z m.term := hta.trans hct
    rcases mem_lset_add.mp ha with h | h
    · rcases hb.2.2.2.2.2.1 n a h hty' hsa hta with ⟨h1, h2⟩ | h2
      · exact .inl ⟨hat.symm, Int.le_trans h2 (hge.2 (h1.trans hat))⟩
      · exact .inr h2
    · subst h; exact .inl ⟨rfl, hge.1⟩
  · right
    rw [hCn, ackConf_term]
    obtain ⟨l, hll, -⟩ := sendable_inv hsd
    exact ⟨hct.symm, TermFn.has_of_get hll, hge.2⟩

/-- `PendOk`'s accepting acknowledgement passes the guard (B 571): its index the append's last, the
append's previous entry and entries terms of the node's log (no wrap: the index is a `w64`). -/
theorem accept_guard {R : RunCfg} {S : State} {n : Fin R.N} {v : NodeView} {q m : Msg}
    (hlg : S.log[n.val]! = logOf v.ps.log)
    (hqi : uint.Z q.index = uint.Z m.index + m.entries.length)
    (hpt : plogTermAt base0 v.ps.log m.index = some m.logterm)
    (hent : ∀ (k : Nat) (e : EntryM), m.entries[k]? = some e →
      plogTermAt base0 v.ps.log (m.index + W64 ((k : Int) + 1)) = some e.Term') :
    uint.Z q.index = recvLast m ∧ AckGuard S n.val m (nodeId n) := by
  have hlog := hlg
  refine ⟨by unfold recvLast; rw [logOf_length]; exact hqi, ?_, ?_⟩
  · unfold recvFact; simp only
    rw [hlog]
    obtain ⟨p1, p2⟩ := termAt_of_plog hpt
    by_cases h0 : uint.Z m.index = 0
    · exact .inl h0
    · right
      have hm0 : 0 ≤ uint.Z m.index := by word
      rw [logOf_length]
      refine ⟨p1, ?_⟩
      rw [termAt_pos (by omega) (by rw [logOf_length]; exact p1)] at p2
      exact p2
  · intro k hk
    rw [logOf_length] at hk
    have he : m.entries[k]? = some m.entries[k] := List.getElem?_eq_getElem hk
    obtain ⟨p1, p2⟩ := termAt_of_plog (hent k _ he)
    have hq : uint.Z q.index < 2 ^ 64 := by word
    have hm0 : 0 ≤ uint.Z m.index := by word
    have hw : uint.Z (m.index + W64 ((k : Int) + 1)) = uint.Z m.index + ((k : Int) + 1) := by
      have hk1 : uint.Z (W64 ((k : Int) + 1)) = (k : Int) + 1 := by word
      word
    rw [hw] at p1 p2
    unfold HFAt recvFact; simp only
    rw [hlog, logOf_length, logOf_getElem! he, entOf_term]
    refine ⟨p1, ?_⟩
    rw [termAt_pos (by omega) (by rw [logOf_length]; exact p1)] at p2
    exact p2

end ack

section main
variable [GooseExts]

/-- A pending message's shape (`MsgShape`): from the node (every `PendOk` case says so but a
forwarded read request's) to another node, an append's payload `AppOk`'s, a forwarded proposal or
read request at term `0`. -/
theorem pendOk_shape {N : Nat} {id : w64} {v : NodeView} {q : Msg} (h : PendOk N id v q)
    (hty : q.ty = .app ∨ q.ty = .appResp ∨ q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .heartbeat ∨
      q.ty = .heartbeatResp ∨ q.ty = .propose ∨ q.ty = .preVote ∨ q.ty = .preVoteResp ∨
      q.ty = .readIndex ∨ q.ty = .readIndexResp) : MsgShape q := by
  obtain ⟨hne, -, hc⟩ := h
  have key : (q.ty ≠ .readIndex → q.src = id) ∧ (q.ty = .app → AppPayloadOk q) ∧
      ((q.ty = .propose ∨ q.ty = .readIndex) → q.term = W64 0) := by
    cases hq : q.ty <;> simp only [hq] at hc
    case app =>
      obtain ⟨-, -, hs, -, -, -, -, -, -, hp⟩ := hc
      exact ⟨fun _ => hs, fun _ => hp, by simp⟩
    case heartbeat =>
      obtain ⟨-, ⟨-, hs, -⟩, -⟩ := hc
      exact ⟨fun _ => hs, by simp, by simp⟩
    case propose => exact ⟨fun _ => hc.1, by simp, fun _ => hc.2⟩
    case readIndex => exact ⟨fun h => absurd rfl h, by simp, fun _ => hc.1⟩
    case snap => exfalso; rw [hq] at hty; simp at hty
    all_goals exact ⟨fun _ => hc.1, by simp, by simp⟩
  exact ⟨key.2.1, fun hr e => hne (e.symm.trans (key.1 hr)), key.2.2⟩

/-- **`send`** (`drain`, B 510-593), for the runs a mask below `mskB1` admits (sync). -/
theorem antSim_send_in (msk : SimMask) (hmsk : msk ≤ mskB1) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (q : Msg)
      (rest : List Msg),
      InMask msk R net xnet →
      SimPre R dec S V net xnet evs G → R.md.async = false → (V n).pend = q :: rest → Told (V n) →
      MsgFacts G q → (q.ty = .readIndexResp → MsgNums (2 ^ 61) q) →
      SimStep R dec evs G (evSend (nodeId n) (V n).byE q)
        (setV V n { V n with pend := rest, undo := none, made := true }) (net ++ [q]) xnet := by
  intro R dec S V net xnet evs G n q rest hin ⟨hp, hs, hl, hgo⟩ hasync hpend htold hmf hnum
  obtain ⟨hmd, hbt, hpar, hspl, _, _⟩ := hin.b1 hmsk
  have hq7 : q.ty = .app ∨ q.ty = .appResp ∨ q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .heartbeat ∨
      q.ty = .heartbeatResp ∨ q.ty = .propose ∨ q.ty = .preVote ∨ q.ty = .preVoteResp ∨
      q.ty = .readIndex ∨ q.ty = .readIndexResp := by
    have := ((hs.2.2.2.2 n).facts.pendMask q (by rw [hpend]; exact List.mem_cons_self)).2.2
    rw [hmd] at this
    simp only [NetTy] at this
    rcases this with (h | h | h | h | h | h | ⟨-, h | h⟩ | ⟨-, h | h⟩ | ⟨h0, -⟩) | h
    all_goals first | (exact absurd h0 (by decide)) | simp [h]
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc R dec S V net xnet G hs hl hgo
  have hsync : ∀ k, (V k).dur = durOf (V k).r := fun k => ((hs1.2.2.2.2 k).sync hasync hbt hspl hpar).2.1
  have hdt : ∀ k, (V k).dur.term = (V k).ps.term := fun k => by rw [hsync k]; rfl
  suffices h : ∃ M C, S1.step (evSend (nodeId n) (V n).byE q) = .ok (some (sendS S1 n.val M C)) ∧
      SendOk R S1 n q M C by
    obtain ⟨M, C, hst, hok⟩ := h
    have hshape := pendOk_shape ((hs1.2.2.2.2 n).pend q (by rw [hpend]; exact List.mem_cons_self ..)) hq7
    obtain ⟨hs2, hgo2⟩ := send_rel hs1 hgo1 hpend hmf hok hshape hdt hnum
    exact ⟨_, Prefix.snoc hp hgc hst (violated_nil hs2.2.1.1 hl hgo2), hs2, hgo2⟩
  obtain ⟨hsh, hb, hnet, -, hno⟩ := hs1
  have hd := (hno n).disk
  have hmem := (hno n).mem
  have hL := (hno n).leader
  have hC := (hno n).cand
  have hT := (hno n).told
  have hca := (hno n).cause
  have hf := (hno n).facts
  have hfp : (V n).r.fp = [] := (hf.snap0 (by rw [hmd])).2.1
  have hb0 : (V n).ps.base = base0 := (hf.snap0 (by rw [hmd])).1
  have hfull : (V n).r.full = (V n).ps.log := by unfold RState.full; rw [hfp]; rfl
  have hdur := hsync n
  have hct : S1.currentTerm[n.val]! = uint.Z (V n).ps.term := by rw [hd.1, hdur]; rfl
  have hvt : S1.vote n.val = nameOf (V n).ps.vote := by rw [hd.2.1, hdur]; rfl
  have hlg : S1.log[n.val]! = logOf (V n).ps.log := by rw [hd.2.2.1, hdur]; unfold durOf; simp only [hfull]
  have hcmt : S1.commitIndex[n.val]! = uint.Z (V n).ps.commit := by rw [hd.2.2.2, hdur]; rfl
  have hlidx : LogIdx (V n).ps.log := by
    have := hf.logIdx; rw [hdur] at this; unfold durOf at this; simp only [hfull] at this; exact this
  obtain ⟨hne, ⟨j, hj⟩, hcase⟩ := (hno n).pend q (by rw [hpend]; exact List.mem_cons_self ..)
  have hc : S1.cfg = R.cfg := hsh.1
  have hsrv : S1.cfg.server.has (nameOf q.dst) = true := by rw [hc, hj]; exact cfg_has R j
  have hne' : (nameOf q.dst != nameOf (nodeId n)) = true := by
    rw [bne_iff_ne]; intro h; exact hne (nameOf_inj h)
  have hrl0 : (V n).ps.role = .leader → S1.role[n.val]! = leader := fun hr => by
    have hpf : (V n).pre = false := by
      cases h : (V n).pre
      · rfl
      · have := hf.preRole h; rw [hr] at this; cases this
    rw [hmem.1, hr]; rfl
  cases hty : q.ty <;> simp only [hty] at hcase
  case vote =>
    obtain ⟨h1, h2, h3, -, h5, h6⟩ := hcase
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h3]
    obtain ⟨-, hvr⟩ := hC h2
    have hidx := plogLast_idx hlidx
    have e : S1.voteRequest n.val (S1.currentTerm[n.val]!) = Fact.mk go!"vote" (nameOf (nodeId n)) []
        (uint.Z q.term) (uint.Z q.index) (uint.Z q.logterm) 0 := by
      unfold State.voteRequest State.lastTerm
      rw [server_of hc n, hterm, hlg, h5, h6, hb0, hidx.1, hidx.2, logOf_length]
    rw [e] at hvr
    have hvf := List.contains_iff_mem.mpr hvr
    exact ⟨_, _, send_vote_eq n q _ hc hsrv hne' hty h1 hterm hvf,
      SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inl hty) ⟨h1, by omega⟩ ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun _ => ⟨_, voteFact_msgOf q q.dst, by rw [h1]; exact hvr⟩)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h.1)⟩
  case voteResp =>
    obtain ⟨h1, h2, h3⟩ := hcase
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h2]
    cases hrej : q.reject
    · have hvd := h3 hrej
      have hvn : S1.vote n.val = nameOf q.dst := by rw [hvt, hvd]
      have hv0 := hb.2.2.2.2.2.2.2.2.2.2.1 n (by rw [hvn, hj]; exact nameOf_ne_nil j)
      rw [hvn, hterm] at hv0
      have hv := List.contains_iff_mem.mpr hv0
      exact ⟨_, _, send_grant_eq n q _ hc hsrv hne' hty h1 hrej hv,
        SendOk.ofGrant hsh hb hty h1 (by omega) j hj⟩
    · exact ⟨_, _, send_voteRej_eq n q _ hc hsrv hne' hty h1 hrej,
        SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inl hty)) ⟨h1, by omega⟩ ⟨j, hj⟩
          (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
          (fun h => nomatch hty.symm.trans h)
          (fun h => by rw [hrej] at h; exact absurd h.2 (by decide))
          (fun h => nomatch hty.symm.trans h.1)⟩
  case app =>
    obtain ⟨hrole, hok⟩ := hcase
    obtain ⟨-, h1, h2, -, hpt, hcm, -, hpre, hpay⟩ := hok
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h2]
    have hrl : S1.role[n.val]! = leader := hrl0 hrole
    rw [hb0] at hpt hpre
    have hes : ((V n).ps.log.drop (uint.nat q.index)).take q.entries.length = q.entries := by
      have hp2 := hpay.2
      have hw : uint.Z (q.index + W64 1) = uint.Z q.index + 1 := by word
      unfold plogFrom at hpre
      rw [hw, base0_index] at hpre
      have e : (uint.Z q.index + 1 - 0 - 1).toNat = uint.nat q.index := by word
      rw [e] at hpre
      exact (List.prefix_iff_eq_take.mp hpre).symm
    have hsd := leader_sendable hb hct hlg hcmt hfull hL hrole (nameOf q.dst) hpt hes hcm
    rw [← h2] at hsd
    exact ⟨_, _, send_app_eq n q _ hc hsrv hne' hty h1 hterm hrl hsd,
      SendOk.plain hsh hb (hlcm := fun _ _ _ => by rw [hcmt]; exact hcm) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inl hty))) ⟨h1, by omega⟩ ⟨j, hj⟩
        (fun _ => by rw [toAppendFact_msgOf, eok_bind, h1]; exact hsd)
        (fun h => nomatch hty.symm.trans h)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h.1)⟩
  case heartbeat =>
    obtain ⟨hrole, hok, hi0, hlt0, hen⟩ := hcase
    obtain ⟨-, h1, h2, -, hcm, hmt⟩ := hok
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h2]
    have hrl : S1.role[n.val]! = leader := hrl0 hrole
    have hhb : q.ty = .heartbeat → ∀ j' : Fin R.N, q.dst = nodeId j' →
        S1.currentTerm[j'.val]! ≤ uint.Z q.term →
        ((S1.confirmed[j'.val]!).term = uint.Z q.term ∧ uint.Z q.commit ≤ (S1.confirmed[j'.val]!).index) ∨
          uint.Z q.commit ≤ S1.commitIndex[j'.val]! := by
      intro _ j' hj' hle
      have hjn : j' ≠ n := fun e => hne (by rw [hj', e])
      obtain ⟨-, -, -, -, -, hb8, -, -, -, -, -, hb14, -, -, -, -, -⟩ := hb
      obtain ⟨-, -, -, l4, -⟩ := hL hrole
      have hc0 : 0 ≤ S1.commitIndex[j'.val]! := by rw [(hno j').disk.2.2.2]; word
      rw [hj'] at hmt
      rcases l4 j' hjn with h0 | ⟨a, ha, haty, hasrc, -, hat, hai⟩
      · right; rw [h0] at hmt; have : uint.Z (W64 0) = 0 := rfl; omega
      · have hqt : uint.Z q.term = uint.Z (V n).ps.term := by rw [h2]
        have hat' : a.term = S1.currentTerm[j'.val]! := by
          have := hb14 j' a ha haty hasrc
          omega
        rcases hb8 j' a ha haty hasrc hat' with ⟨c1, c2⟩ | c
        · left; exact ⟨by omega, by omega⟩
        · right; omega
    have hpt : plogTermAt base0 (V n).ps.log (W64 0) = some (W64 0) := by
      unfold plogTermAt; simp [base0]
    have hsd0 := leader_sendable (es := []) hb hct hlg hcmt hfull hL hrole (nameOf q.dst) hpt rfl hcm
    have hsd : S1.sendable ⟨nameOf (nodeId n), nameOf q.dst, uint.Z q.term, uint.Z q.index, uint.Z q.logterm,
        logOf q.entries, uint.Z q.commit⟩ = .ok true := by
      rw [hi0, hlt0, hen, h2]; exact hsd0
    exact ⟨_, _, send_hb_eq n q _ hc hsrv hne' hty h1 hterm hrl hsd,
      SendOk.plain hsh hb (hlcm := fun _ _ _ => by rw [hcmt]; exact hcm) (hhb := hhb) (.inr (.inr (.inr (.inr (.inl hty))))) ⟨h1, by omega⟩ ⟨j, hj⟩
        (fun _ => by rw [toAppendFact_msgOf, eok_bind, h1]; exact hsd)
        (fun h => nomatch hty.symm.trans h)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h.1)⟩
  case heartbeatResp =>
    obtain ⟨h1, h2⟩ := hcase
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, h2]
    exact ⟨_, _, send_hbresp_eq n q _ hc hsrv hne' hty h1 (by omega),
      SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inr (.inr (.inr (.inl hty)))))) ⟨h1, by omega⟩ ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun h => nomatch hty.symm.trans h)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h.1)⟩
  case propose =>
    obtain ⟨h1, h2⟩ := hcase
    have h0 : 0 ≤ uint.Z (V n).ps.term := by word
    have hz : uint.Z q.term = 0 := by rw [h2]; rfl
    exact ⟨_, _, send_prop_eq n q _ hc hsrv hne' hty,
      SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inr (.inr (.inr (.inr hty)))))) ⟨h1, by omega⟩ ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun h => nomatch hty.symm.trans h)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h.1)⟩
  case appResp =>
    obtain ⟨h1, hby, hcase⟩ := hcase
    have hreq : (q.ty = .app ∨ q.ty = .heartbeat) →
        (toAppendFact (msgOf q q.dst) >>= S1.sendable) = .ok true :=
      fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)
    rcases hcase with hcase | ⟨m, hcm, hmty, -, hlt, hqe⟩
    rotate_left
    · obtain ⟨m', hcm', hpd⟩ := (hT (htold hby)).resolve_right
        (fun ⟨x, hx, _⟩ => by rw [((hno n).xcause x hx).2] at hcm; cases hcm)
      rw [hcm] at hcm'; cases hcm'
      have hqt2 : q.term = (V n).ps.term := by rw [hqe]
      have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, hqt2]
      have hrej : q.reject = false := by rw [hqe]
      have hi' : (uint.Z q.index == 0) = true := by rw [hqe]; rfl
      have hlt' : uint.Z m.term < S1.currentTerm[n.val]! := by rw [hterm, hqt2]; exact hlt
      exact ⟨_, _, send_appRespStale_eq n q _ hc hsrv hne' hty h1 hrej m hpd hmty hlt' hi' hterm.symm,
        SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inr (.inl hty)))) ⟨h1, by omega⟩ ⟨j, hj⟩ hreq
          (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
          (fun h => h.2.2 (by rw [hqe]))⟩
    obtain ⟨m, hcm, hmty, hqd, hqt, hqt2, hacc⟩ := hcase
    have hterm : S1.currentTerm[n.val]! = uint.Z q.term := by rw [hct, hqt2]
    cases hrej : q.reject
    case true =>
      exact ⟨_, _, send_appRespRej_eq n q _ hc hsrv hne' hty h1 hrej,
        SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inr (.inl hty)))) ⟨h1, by omega⟩ ⟨j, hj⟩ hreq
          (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
          (fun h => by rw [hrej] at h; exact absurd h.2.1 (by decide))⟩
    case false =>
    obtain ⟨m', hcm', hpd⟩ := (hT (htold hby)).resolve_right (fun ⟨x, hx, _⟩ => by rw [((hno n).xcause x hx).2] at hcm; cases hcm)
    rw [hcm] at hcm'; cases hcm'
    have hqtZ : uint.Z q.term = uint.Z m.term := by rw [hqt]
    have hmt : S1.currentTerm[n.val]! = uint.Z m.term := by rw [hterm, hqtZ]
    by_cases hi : uint.Z q.index = 0
    · have hi' : (uint.Z q.index == 0) = true := by simpa using hi
      exact ⟨_, _, send_appResp0_eq n q _ hc hsrv hne' hty h1 hrej m hpd hmty hmt hi',
        SendOk.plain hsh hb (hlcm := fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h)) (hhb := fun h => nomatch hty.symm.trans h) (.inr (.inr (.inr (.inl hty)))) ⟨h1, by omega⟩ ⟨j, hj⟩ hreq
          (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
          (fun h => h.2.2 (by word))⟩
    · have hi' : (uint.Z q.index == 0) = false := by simpa using hi
      obtain ⟨hmn, hmd⟩ := hca m hcm
      obtain ⟨-, -, j', hj', hsd0⟩ := hnet.1 m hmn
      have hjn : j' = n := nodeId_inj (hj'.symm.trans hmd)
      rw [hjn] at hsd0
      obtain ⟨hsd1, -, -, -⟩ := hsd0 (by omega)
      have hsd : S1.sendable (recvFact m (nodeId n)) = .ok true := by
        have := hsd1 (.inl hmty); rw [toAppendFact_msgOf, eok_bind, hmd] at this; exact this
      have hG := ack_guard_eq S1 n.val m (nodeId n) (uint.Z q.index)
      by_cases hg : uint.Z q.index = recvLast m ∧ AckGuard S1 n.val m (nodeId n)
      · rw [decide_eq_true hg] at hG
        exact ⟨_, _, send_ack_eq n q _ hc hsrv hne' hty h1 hrej m hpd hmty hmt hi' hsd hqd hqtZ hG,
          SendOk.ofAck hsh hb hl hgo1 hty h1 hmt j hj hqd hqtZ hg.1 hi hsd hg.2⟩
      · rw [decide_eq_false hg] at hG
        rcases hacc hrej with ⟨a1, a2, a3⟩ | ⟨s1, s2⟩
        · exact absurd (accept_guard hlg a1 (by rw [← hb0]; exact a2) (fun k e h => by rw [← hb0]; exact a3 k e h)) hg
        · have hst : uint.Z m.index < S1.commitIndex[n.val]! := by rw [hcmt]; exact s1
          have hqi : uint.Z q.index = S1.commitIndex[n.val]! := by rw [hcmt, s2]
          exact ⟨_, _, send_stale_eq n q _ hc hsrv hne' hty h1 hrej m hpd hmty hmt hi' hsd hqd hqtZ hG hst hqi,
            SendOk.ofStale hsh hb hty h1 (by omega) j hj hqd hqtZ hqi⟩
  case preVote =>
    obtain ⟨h1, hvt⟩ := hcase
    exact ⟨_, _, send_pre_eq n q _ hc hsrv hne' (.inl hty) h1,
      SendOk.plainP hsh hb (by simp [hty]) ⟨h1, .inl (.inl hty)⟩
        (fun hcc => ⟨fun _ => by rw [h1]; rw [(hf.conf0 hcc).1, CfgM.voters_simple] at hvt; exact hvt,
          fun h => nomatch hty.symm.trans h⟩) ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h)
        (fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))⟩
  case preVoteResp =>
    obtain ⟨h1, hgr, hrjt⟩ := hcase
    have hsrc : PreTermKeep q ∨ uint.Z q.term ≤ S1.currentTerm[n.val]! := by
      cases hrej : q.reject
      · exact .inl (.inr ⟨hty, hrej⟩)
      · exact .inr (Int.le_of_eq (by rw [hct, hrjt hrej]))
    have hpvo : PreVoterOk R q := by
      refine fun hcc => ⟨fun h => (nomatch hty.symm.trans h), fun _ hrej => ?_⟩
      obtain ⟨m, hcm, hmty, hqd⟩ := hgr hrej
      obtain ⟨hmn, -⟩ := hca m hcm
      rw [hqd]; exact (hnet.2.2.2.2.2.1 m hmn hcc).1 hmty
    exact ⟨_, _, send_pre_eq n q _ hc hsrv hne' (.inr hty) h1,
      SendOk.plainP hsh hb (by simp [hty]) ⟨h1, hsrc⟩ hpvo ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h)
        (fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))⟩
  case readIndex =>
    obtain ⟨h0, i, hi⟩ := hcase
    exact ⟨_, _, send_readIdx_eq n q _ hc hsrv hne' hty, SendOk.readIdx hsh hb hty h0 ⟨i, hi⟩ ⟨j, hj⟩⟩
  case readIndexResp =>
    obtain ⟨h1, h2⟩ := hcase
    exact ⟨_, _, send_readResp_eq n q _ hc hsrv hne' hty h1,
      SendOk.plainP hsh hb (by simp [hty]) ⟨h1, .inr (Int.le_of_eq (by rw [hct, h2]))⟩
        (fun _ => ⟨fun h => (nomatch hty.symm.trans h), fun h => (nomatch hty.symm.trans h)⟩) ⟨j, hj⟩
        (fun h => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))
        (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h.1)
        (fun h => nomatch hty.symm.trans h.1) (fun h => nomatch hty.symm.trans h)
        (fun h _ _ => h.elim (fun h => nomatch hty.symm.trans h) (fun h => nomatch hty.symm.trans h))⟩
  all_goals (exfalso; rw [hty] at hq7; simp at hq7)

end main

end AntSim
end EtcdGrove
end Perennial
