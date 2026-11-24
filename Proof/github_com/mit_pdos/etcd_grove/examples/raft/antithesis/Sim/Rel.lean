/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the relation (#33 S3c step 5 / S4)

`AntSim S V net` (`notes/antithesis-rawnode-design.md` §3.2, C1-C4) relates the binding's state `S`
(the S3b transcription's `AntCheck.State`), each node's view `V n` (its protocol state between
inputs, or at its last `Ready` in a drain) and the messages sent so far `net`; `GlobalOk S net G`
(C5) says that what `S` and `net` hold is certified by raft's global facts `G` (`RaftFacts`: the
pure content of the persistent ghost facts `isLeader`, `isVote`, `logRecs`, `isCamp`,
`isCommitted`, `commitIn`, which the harness's invariant keeps and turns into a `RaftFacts`
satisfying `RaftLaws` before each report, `notes/antithesis-rawnode-design.md` §3.4). `Prefix cfg evs
S` (`notes/antithesis-s4-design.md` §3): the checker took `evs`, rejected none, found no violation,
and is at `S`; `Prefix.accepts` turns it into the closed statement's `Accepts`.

These are the statements' vocabulary (`Stmts.lean`); C2-C4 are as the design lists them and may be
strengthened by the invariant phase (the per-report proofs). §3.5 of the design note lists where
they differ from the sketch.

Pure: imports only raft's protocol model, `InputEnd`, and the transcription.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Abs
public import Proof.go_etcd_io.raft.v3.Protocol.InputEnd

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap

/-! ## The checker's prefix -/

/-- The checker from `init0 cfg` has taken `evs` (each with the `GC` steps due before it), rejected
none, found no violation, and is at `S` (`notes/antithesis-s4-design.md` §3). -/
def Prefix (cfg : AntCheck.Config) (evs : List AntCheck.Event) (S : AntCheck.State) : Prop :=
  ∃ c : AntCheck.Checker,
    ((AntCheck.init0 cfg).bind fun s => evs.foldlM (fun c ev => c.next ev) ({ state := s } : AntCheck.Checker))
      = .ok c ∧ c.done = false ∧ c.state = S

/-- **A prefix is accepted**: the stream so far is `ACCEPTED` (`Checker.finish` of a checker that
is not done). -/
theorem Prefix.accepts {cfg : AntCheck.Config} {evs : List AntCheck.Event} {S : AntCheck.State}
    (h : Prefix cfg evs S) : AntCheck.Accepts cfg evs := by
  obtain ⟨c, hc, hd, -⟩ := h
  refine ⟨c.finish, ?_, ?_⟩
  · unfold AntCheck.run
    cases h0 : AntCheck.init0 cfg with
    | error e => rw [h0] at hc; cases hc
    | ok s =>
      rw [h0] at hc
      change evs.foldlM (fun c ev => c.next ev) ({ state := s } : AntCheck.Checker) = .ok c at hc
      change (evs.foldlM (fun c ev => c.next ev) ({ state := s } : AntCheck.Checker) >>= fun c =>
        pure c.finish) = _
      rw [hc]; rfl
  · simp [AntCheck.Checker.finish, hd]

section rel
variable [GooseExts]

/-! ## A node's view -/

/-- What the relation knows of node `n` (the S4 invariant's view fragment, `γ.view`): its protocol
state `ps` and the committed entries it has handed out `delivered` (`RNState.delivered`), and, in a
drain after a `Ready` (§3.2's drain phase), what that `Ready` left: the self-addressed messages
`Advance` will step (`qs`), its messages not yet reported (`pend`, in the `Ready`'s order) and its
committed entries not yet reported (`ce`). `byE` and `cause` are the drain's (`drain(n, by)`, and the
message handled for `by = recv`); `told` says its `recv` was reported (`reportCause`), so that the
binding's `pending[n]` is that message. Between inputs `qs`, `pend`, `ce` are empty (`Idle`). -/
structure NodeView where
  ps : PState
  delivered : List EntryM
  qs : List Msg := []
  pend : List Msg := []
  ce : List EntryM := []
  byE : AntCheck.Str := []
  cause : Option Msg := none
  told : Bool := false

/-- Between inputs: nothing of a `Ready` left (`Advance` done, `HasReady` false). -/
def NodeView.Idle (v : NodeView) : Prop := v.qs = [] ∧ v.pend = [] ∧ v.ce = []

/-- A fresh node (`NewRawNode.emptyStartSpec`'s `pInit`): term 0, no vote, no leader, follower, no
tally, empty outbox, empty log from `base0`, commit 0, no `Match`. -/
def PInit (ps : PState) : Prop :=
  ps.term = W64 0 ∧ ps.vote = W64 0 ∧ ps.lead = W64 0 ∧ ps.role = .follower ∧ ps.votes = ∅ ∧
  ps.outbox = [] ∧ ps.base = base0 ∧ ps.log = [] ∧ ps.commit = W64 0 ∧ ps.matched = ∅

/-- The static configuration (`γ.reCfg`): voters `1, 2, 3`. -/
def voters3 : GSet w64 := GMap.listToSet [W64 1, W64 2, W64 3]

/-- A log from `base0` whose entries carry their positions as indices (`PlogWf base0`'s index part):
the binding's positions (`TermAt`, `SubSeq`, an `apply`'s `first`) are raft's indices. -/
def LogIdx (l : List EntryM) : Prop := ∀ (k : Nat) (e : EntryM), l[k]? = some e → uint.Z e.Index' = (k : Int) + 1

/-- The binding's per-server lists are those of `cfg3`'s three servers. -/
def Shape (S : AntCheck.State) : Prop :=
  S.cfg = cfg3 ∧ S.currentTerm.length = 3 ∧ S.voteTerm.length = 3 ∧ S.voteFor.length = 3 ∧
  S.log.length = 3 ∧ S.commitIndex.length = 3 ∧ S.role.length = 3 ∧ S.lastApplied.length = 3 ∧
  S.config.length = 3 ∧ S.confAt.length = 3 ∧ S.confirmed.length = 3 ∧ S.undo.length = 3 ∧
  S.pending.length = 3 ∧ S.queue.length = 3 ∧ S.reads.length = 3

/-- An ack fact `[type |-> "ack", src, dst, term |-> t, index |-> k']` with `k' ≥ k` is in `msgs`. -/
def AckIn (S : AntCheck.State) (src dst : AntCheck.Str) (t k : Int) : Prop :=
  ∃ a ∈ S.msgs, a.type = go!"ack" ∧ a.src = src ∧ a.dst = dst ∧ a.term = t ∧ k ≤ a.index

/-! ## C1-C2: the per-node part -/

/-- **C1, the node's durable part**: the binding's variables for `n` are the view's (every change of
term, vote, log, commit or role is in a `Ready` whose `ready` report the harness makes before its
write), its outbox empty (taken by the `Ready`), no snapshot, its log's indices its positions, the
initial configuration; what it
handed out (`delivered`, and in a drain `ce`) a prefix of its log within its commit. -/
def DurableIs (S : AntCheck.State) (n : Fin 3) (v : NodeView) : Prop :=
  S.currentTerm[n.val]! = uint.Z v.ps.term ∧ S.vote n.val = nameOf v.ps.vote ∧
  S.log[n.val]! = logOf v.ps.log ∧ S.commitIndex[n.val]! = uint.Z v.ps.commit ∧
  S.role[n.val]! = roleOf v.ps.role ∧ S.lastApplied[n.val]! = (v.delivered.length : Int) ∧
  v.ps.outbox = [] ∧ v.ps.base = base0 ∧ LogIdx v.ps.log ∧
  S.config[n.val]! = cfg3.initConf ∧ S.confAt[n.val]! = 0 ∧
  v.delivered ++ v.ce <+: v.ps.log ∧ (v.delivered ++ v.ce).length ≤ uint.nat v.ps.commit

/-- **A leader's confirmation** (for `LeaderPart`): a leader's `confirmed` is at its term and covers
its whole log. `CommitBeyondConfirmed` (B 435) reads it for a leader's commit made without a write
(`conf1` keeps `confirmed[n]` then); the win and each proposal's store set it to `{T, last}`
(`conf1`'s `stores` arm), and an accepting acknowledgement's `send` only raises its index at the
same term. -/
def LeaderConfOk (S : AntCheck.State) (n : Fin 3) (v : NodeView) : Prop :=
  (S.confirmed[n.val]!).term = uint.Z v.ps.term ∧ (v.ps.log.length : Int) ≤ (S.confirmed[n.val]!).index

/-- **C2, a leader's part**: it is in `leaders` at its term, `ledLog` at its term is its log; every
`Match` it holds is backed by acknowledgements in `msgs`: at any index of its term within a voter's
`Match` (what `cmt`'s `Acked` quorum needs, B 252; the node's own `Match` at its win, `reset`'s
`lastIndex`, is below every entry of its term), and for another voter at the `Match` itself (what a
heartbeat's commit `min(Match, committed)` needs, through C3's `confirmed`, B 435); its
`confirmed` at its term covering its log (`LeaderConfOk`). -/
def LeaderPart (S : AntCheck.State) (n : Fin 3) (v : NodeView) : Prop :=
  v.ps.role = .leader →
    S.leaders.contains { server := nameOf (nodeId n), term := uint.Z v.ps.term } ∧
    S.ledLog.get (uint.Z v.ps.term) = .ok (logOf v.ps.log) ∧
    (∀ (j : Fin 3) (k : w64), uint.Z k ≤ uint.Z (matchOf v.ps (nodeId j)) →
      plogTermAt base0 v.ps.log k = some v.ps.term →
      AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) (uint.Z v.ps.term) (uint.Z k)) ∧
    (∀ j : Fin 3, j ≠ n → matchOf v.ps (nodeId j) = W64 0 ∨
      AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) (uint.Z v.ps.term)
        (uint.Z (matchOf v.ps (nodeId j)))) ∧
    LeaderConfOk S n v

/-- **C2, a candidate's part**: its tally's grants are in the binding's `Granted(n)` (R 277: the
grant facts of its term sent to it, its own vote), and its campaign's vote request is in `msgs`
(`VoteRequest(n, currentTerm[n])`, R 217-219, recorded by the campaign's `ready`, B 418: what a
`send` of one of its requests checks, B 532). -/
def CandPart (S : AntCheck.State) (n : Fin 3) (v : NodeView) : Prop :=
  v.ps.role = .candidate →
    (∀ j : Fin 3, v.ps.votes !! nodeId j = some true → (S.granted n.val).has (nameOf (nodeId j))) ∧
    S.voteRequest n.val (S.currentTerm[n.val]!) ∈ S.msgs

/-- What raft says of a message of a `Ready` that the harness has not reported yet, at the view's
state (the `Ready`'s; `InputEnd` queues only at the state after the preamble, and the outbox was
empty at the input, C1). Each is what the binding's `Send` (B 510-593) checks: a vote request is the
campaign's (its fact recorded by the campaign's `ready`), a vote response is at the node's term (a grant for its vote), an
append or heartbeat is the leader's (`AppOk`: its commit at most the leader's, which `Sendable`
reads, not `AppSendOk`'s equal one, since an `Advance` stepping two self-messages may leave a first
batch with a stale commit; `HeartbeatOk`), an acknowledgement answers the
handled `MsgApp` (accepting: its last index, the log after the write matching it, B 571-575; stale:
the commit index, B 577-580), a heartbeat response is at the node's term; a forwarded proposal is
unchecked (B 524, 586), from the node at term `0` (`ProposeEnd`'s forward). A heartbeat
carries no index, term or entries (`sendHeartbeat`), which the binding's `Sendable` reads (B 120-124).
An acknowledgement is of a drain caused by a `recv` (`by = "recv"`, whose `pending[n]` it reads). -/
def PendOk (id : w64) (v : NodeView) (q : Msg) : Prop :=
  q.dst ≠ id ∧ (∃ j : Fin 3, q.dst = nodeId j) ∧
  match q.ty with
  | .vote => q.src = id ∧ v.ps.role = .candidate ∧ q.term = v.ps.term ∧ v.ps.vote = id ∧
      q.index = (plogLast base0 v.ps.log).index' ∧ q.logterm = (plogLast base0 v.ps.log).term'
  | .voteResp => q.src = id ∧ q.term = v.ps.term ∧ (q.reject = false → v.ps.vote = q.dst)
  | .app => v.ps.role = .leader ∧ AppOk id v.ps q
  | .heartbeat => v.ps.role = .leader ∧ HeartbeatOk id v.ps q ∧
      q.index = W64 0 ∧ q.logterm = W64 0 ∧ q.entries = []
  | .appResp => q.src = id ∧ v.byE = go!"recv" ∧ ∃ m, v.cause = some m ∧ m.ty = .app ∧ q.dst = m.src ∧
      q.term = m.term ∧ q.term = v.ps.term ∧
      (q.reject = false →
        (uint.Z q.index = uint.Z m.index + m.entries.length ∧
          plogTermAt base0 v.ps.log m.index = some m.logterm ∧
          ∀ (k : Nat) (e : EntryM), m.entries[k]? = some e →
            plogTermAt base0 v.ps.log (m.index + W64 ((k : Int) + 1)) = some e.Term') ∨
        (uint.Z m.index < uint.Z v.ps.commit ∧ q.index = v.ps.commit))
  | .heartbeatResp => q.src = id ∧ q.term = v.ps.term
  | .propose => q.src = id ∧ q.term = W64 0
  | _ => False

/-- The self-addressed messages `Advance` steps (`stepsOnAdvance`): a leader's self-acknowledgement,
its ack fact already recorded by the `ready` of its write (B 407), or a candidate's self-vote,
recorded by the campaign's (B 418). -/
def QsOk (S : AntCheck.State) (n : Fin 3) (v : NodeView) (q : Msg) : Prop :=
  q.src = nodeId n ∧ q.dst = nodeId n ∧ q.term = v.ps.term ∧ q.reject = false ∧
  ((q.ty = .appResp ∧
      AckIn S (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z v.ps.term) (uint.Z q.index)) ∨
   (q.ty = .voteResp ∧
      { voter := nameOf (nodeId n), term := uint.Z v.ps.term, cand := nameOf (nodeId n) } ∈ S.votes))

/-- **C1, the leader hint**: a node that does not lead does not name itself as leader (raft's
`LeadOk`): every step that sets `lead` to the node itself makes it leader, and a leader that steps
down resets `lead` (`becomeFollower`), or sets it to the sender of a message, never itself (D:
`m.src ≠ m.dst`). -/
def LeadOk (n : Fin 3) (v : NodeView) : Prop := v.ps.role ≠ .leader → v.ps.lead ≠ nodeId n

/-- C1, C2 and the drain's facts for node `n`: its pending messages (`PendOk`), its queued
self-messages (`QsOk`), once its drain's `recv` is reported, `pending[n]` (B 201), and the message
its drain handles was sent to it (an acknowledgement's `send` reads its `Sendable`, kept by C4);
the leader hint (`LeadOk`). -/
def NodeOk (S : AntCheck.State) (net : List Msg) (n : Fin 3) (v : NodeView) : Prop :=
  DurableIs S n v ∧ LeaderPart S n v ∧ CandPart S n v ∧
  (∀ q ∈ v.pend, PendOk (nodeId n) v q) ∧ (∀ q ∈ v.qs, QsOk S n v q) ∧
  (v.told = true → ∃ m, v.cause = some m ∧ S.pending[n.val]! = [msgOf m (nodeId n)]) ∧
  (∀ m, v.cause = some m → m ∈ net ∧ m.dst = nodeId n) ∧ LeadOk n v

/-! ## C3: the binding's own invariants -/

/-- **C3, the acks' terms**: every ack fact from node `i` is at most `currentTerm[i]`. Acks are
recorded only at the recorder's current term (`OnDisk`'s `t1`, B 407; a `send`'s `cm.term`, which
it checks is `currentTerm[n]`, B 571-580), and terms only grow. With `HbCommitOk`'s derivation at a
heartbeat's `send`, it makes a leader's ack fact from `j` at the leader's term be at `currentTerm[j]`
(C3's ack conjunct then applies). -/
def AckTermsOk (S : AntCheck.State) : Prop :=
  ∀ n : Fin 3, ∀ a ∈ S.msgs, a.type = go!"ack" → a.src = nameOf (nodeId n) →
    a.term ≤ S.currentTerm[n.val]!

/-- **C3, the vote's term**: `voteTerm[i] ≤ currentTerm[i]` (`OnDisk` sets `voteTerm` to the new
term `t1` only). So a term change that writes no vote leaves `Vote(n)` empty (`VoteOf`'s
`vt = t`, B 99), what `ready`'s `S'.vote n = []` needs. -/
def VoteTermOk (S : AntCheck.State) : Prop :=
  ∀ n : Fin 3, S.voteTerm[n.val]! ≤ S.currentTerm[n.val]!

/-- **C3, the confirmed records**: each `confirmed[j]` is at a term `j` has reached (`conf1` sets it at
`t1`; an accepting ack's `send` at `currentTerm[n]`, B 571-575), and either empty, at a term
`ledLog` has, or at a term every node has passed. At a win the leader's log enters `ledLog` at a
term `T` that was missing (`inMemory`'s check), and this excludes any `j` already confirmed at `T` with a
nonzero index (whose `confirmed[j]` would otherwise have to be a prefix of the new `ledLog[T]`,
C3's confirmed conjunct). `GC` removes from `ledLog` only terms every node has passed (`StaleLed`:
`Over`, `EffTerm ≤ currentTerm`, B 153, 709); a `ready` or a `send` confirms only at a term in
`ledLog` (`Sendable`, B 117-126, or the leader's own term). -/
def ConfirmedOk (S : AntCheck.State) : Prop :=
  ∀ j : Fin 3,
    ((S.confirmed[j.val]!).index = 0 ∨ S.ledLog.has (S.confirmed[j.val]!).term = true ∨
      ∀ i : Fin 3, (S.confirmed[j.val]!).term < S.currentTerm[i.val]!) ∧
    (S.confirmed[j.val]!).term ≤ S.currentTerm[j.val]!

/-- **C3**: facts about `S` alone, kept by every step and by `GC` (§3.2): no violation; no queued
write or read (default mode); an announced write never `made` (`undo`, B 349-359, only between a
`ready` and the next `send`/`apply`); `termLen` within `chain`; each node's commit within `chain`
and agreeing with it (`subSeq`'s domain, B 434, 600), recorded under a term it has reached
(`RecordedIn`, B 109-112, at a win and a request's commit); `confirmed` a prefix of its term's leader
log while that is kept; every ack of a node at its term within its `confirmed` or its commit (what
`CommitBeyondConfirmed`, B 435, needs); `ledLog`'s terms led; a node in `leaders` at its current term
only while it leads it; the grants' and acks' senders and receivers and the votes' voters servers
(`GC` looks them up, B 699-708: an evaluation error otherwise); a node's vote at its term in
`votes` (recorded by the write that made it, B 410: what a `send` of its grant checks, B 540);
the acks' terms (`AckTermsOk`), the votes' terms (`VoteTermOk`) and the `confirmed` records'
(`ConfirmedOk`) within the nodes' terms. -/
def BindingOk (S : AntCheck.State) : Prop :=
  S.viol = [] ∧
  (∀ n : Fin 3, S.queue[n.val]! = [] ∧ S.reads[n.val]! = []) ∧
  (∀ (n : Fin 3) (p : AntCheck.Pre), S.undo[n.val]! = some p → p.made = false) ∧
  (∀ p ∈ S.termLen, p.2 ≤ S.chain.length) ∧
  (∀ n : Fin 3, S.commitIndex[n.val]! ≤ S.chain.length ∧
    S.chain.take (S.commitIndex[n.val]!).toNat = (S.log[n.val]!).take (S.commitIndex[n.val]!).toNat) ∧
  (∀ n : Fin 3, S.commitIndex[n.val]! = 0 ∨
    ∃ p ∈ S.termLen, p.1 ≤ S.currentTerm[n.val]! ∧ S.commitIndex[n.val]! ≤ p.2) ∧
  (∀ n : Fin 3, ∀ l, S.ledLog.get (S.confirmed[n.val]!).term = .ok l →
    (S.confirmed[n.val]!).index ≤ (S.log[n.val]!).length ∧ (S.confirmed[n.val]!).index ≤ l.length ∧
    (S.log[n.val]!).take (S.confirmed[n.val]!).index.toNat = l.take (S.confirmed[n.val]!).index.toNat) ∧
  (∀ n : Fin 3, ∀ a ∈ S.msgs, a.type = go!"ack" → a.src = nameOf (nodeId n) →
    a.term = S.currentTerm[n.val]! →
    ((S.confirmed[n.val]!).term = a.term ∧ a.index ≤ (S.confirmed[n.val]!).index) ∨
      a.index ≤ S.commitIndex[n.val]!) ∧
  (∀ p ∈ S.ledLog, ∃ l ∈ S.leaders, l.term = p.1) ∧
  (∀ n : Fin 3, ∀ l ∈ S.leaders, l.server = nameOf (nodeId n) →
    l.term < S.currentTerm[n.val]! ∨
      (l.term = S.currentTerm[n.val]! ∧ S.role[n.val]! = AntCheck.leader)) ∧
  (∀ f ∈ S.msgs, f.type ≠ go!"vote" →
    (∃ i : Fin 3, f.src = nameOf (nodeId i)) ∧ ∃ j : Fin 3, f.dst = nameOf (nodeId j)) ∧
  (∀ v ∈ S.votes, ∃ i : Fin 3, v.voter = nameOf (nodeId i)) ∧
  (∀ n : Fin 3, S.vote n.val ≠ [] →
    { voter := nameOf (nodeId n), term := S.currentTerm[n.val]!, cand := S.vote n.val } ∈ S.votes) ∧
  AckTermsOk S ∧ VoteTermOk S ∧ ConfirmedOk S

/-! ## C4: the network -/

/-- **C4, a heartbeat's commit**: a heartbeat to `j` whose term `j` has not passed carries a commit
within `j`'s confirmation at its term, or within `j`'s commit. `CommitBeyondConfirmed` (B 435) reads
it when `j` commits on the heartbeat. `GC` can drop the leader's ack from `j` once `j` moves on
(`Garbage`, B 696-706), so the fact is recorded with the message: `antSim_send` establishes it from
`HeartbeatOk` (`commit ≤ Match[j]`), `LeaderPart`'s ack at `Match[j]`, `AckTermsOk` (that ack is at
`currentTerm[j]`) and C3's ack conjunct; it is kept since `confirmed[j]` moves only to a later term
or a larger index at its term (`ConfirmedOk`'s `term ≤ currentTerm[j]`) and commits only grow. -/
def HbCommitOk (S : AntCheck.State) (net : List Msg) : Prop :=
  ∀ m ∈ net, m.ty = .heartbeat → ∀ j : Fin 3, m.dst = nodeId j →
    S.currentTerm[j.val]! ≤ uint.Z m.term →
    ((S.confirmed[j.val]!).term = uint.Z m.term ∧ uint.Z m.commit ≤ (S.confirmed[j.val]!).index) ∨
      uint.Z m.commit ≤ S.commitIndex[j.val]!

/-- **C4, a message's shape**: an append carries a well-formed payload that does not wrap
(`AppPayloadOk`, what `RecvEnd` reads of a received `MsgApp`), no message is to its sender, and a
forwarded proposal is at term `0` (`ProposeEnd`'s forward). `send` keeps them from `PendOk`
(`AppOk`'s `AppPayloadOk` and `dst ≠ id`); with `Reach.input`'s `m.term ≠ 0`, a received message is
never a proposal. -/
def MsgShape (m : Msg) : Prop :=
  (m.ty = .app → AppPayloadOk m) ∧ m.src ≠ m.dst ∧ (m.ty = .propose → m.term = W64 0)

/-- Every message sent has `MsgShape`. -/
def NetShape (net : List Msg) : Prop := ∀ m ∈ net, MsgShape m

/-- **C4**: every message sent (`net`: every `send` so far, delivered, dropped or in flight) is
between two of the nodes, of a type in scope, of a term its sender has reached, and what the
binding checks at its receipt or of its answer was recorded by its sender's reports (B 546: the
`send` of a request checked `Sendable`; B 418, 540, 573: the facts of a vote request, a grant, an
ack) and is kept while its receiver has not passed its term (GC drops only what a term has
passed, B 696-709); a heartbeat's commit within its receiver's confirmation or commit
(`HbCommitOk`); every message's shape (`NetShape`). -/
def NetOk (S : AntCheck.State) (net : List Msg) : Prop :=
  (∀ m ∈ net,
    (m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose) ∧
    (∃ i : Fin 3, m.src = nodeId i ∧ uint.Z m.term ≤ S.currentTerm[i.val]!) ∧
    ∃ j : Fin 3, m.dst = nodeId j ∧
      (S.currentTerm[j.val]! ≤ uint.Z m.term →
        ((m.ty = .app ∨ m.ty = .heartbeat) →
          (AntCheck.toAppendFact (msgOf m m.dst) >>= S.sendable) = .ok true) ∧
        (m.ty = .vote → ∃ f, AntCheck.voteFact (msgOf m m.dst) = .ok f ∧ f ∈ S.msgs) ∧
        ((m.ty = .voteResp ∧ m.reject = false) →
          ({ type := go!"grant", src := nameOf m.src, dst := nameOf m.dst, term := uint.Z m.term } :
            AntCheck.Fact) ∈ S.msgs) ∧
        ((m.ty = .appResp ∧ m.reject = false ∧ m.index ≠ W64 0) →
          AckIn S (nameOf m.src) (nameOf m.dst) (uint.Z m.term) (uint.Z m.index)))) ∧
  HbCommitOk S net ∧ NetShape net

set_option linter.iris.dupNamespace false in
/-- **The refinement relation** (§3.2: C1-C4). -/
def AntSim (S : AntCheck.State) (V : Fin 3 → NodeView) (net : List Msg) : Prop :=
  Shape S ∧ BindingOk S ∧ NetOk S net ∧ ∀ n : Fin 3, NodeOk S net n (V n)

/-! ## C5: raft's global facts -/

/-- Raft's global facts, as pure data (the persistent ghost facts the harness's invariant keeps for
everything in `S`, §3.4): leaders (`isLeader γ j t`), votes (`isVote γ v t c`), certified logs
(`logRecs`, full logs from `base0`), each leader's log at its win (`isCamp`), the longest committed
log known (`isCommitted`), and the commits recorded in a term (`commitIn γ committed c x`: the first
`c` entries are committed by term `x`). -/
structure RaftFacts where
  leaders : List (w64 × w64)
  votes : List (w64 × w64 × w64)
  logs : List (List EntryM)
  camps : List (w64 × List EntryM)
  committed : List EntryM
  commits : List (w64 × Nat)

/-- What raft proves of its global facts (election safety `isLeader_unique`, one vote per term
`isVote_agree`, log matching `logRecs_agree`, leader completeness `commitIn_camp`): the laws a
`RaftFacts` the harness builds satisfies. -/
def RaftLaws (G : RaftFacts) : Prop :=
  (∀ a ∈ G.leaders, ∀ b ∈ G.leaders, a.2 = b.2 → a.1 = b.1) ∧
  (∀ a ∈ G.votes, ∀ b ∈ G.votes, a.1 = b.1 → a.2.1 = b.2.1 → a.2.2 = b.2.2) ∧
  (∀ a ∈ G.logs, ∀ b ∈ G.logs, ∀ (k : Nat) (e f : EntryM), a[k]? = some e → b[k]? = some f →
    e.Term' = f.Term' → a.take (k + 1) = b.take (k + 1)) ∧
  G.committed ∈ G.logs ∧
  (∀ p ∈ G.camps, p.2 ∈ G.logs) ∧
  (∀ x ∈ G.commits, x.2 ≤ G.committed.length ∧
    ∀ p ∈ G.camps, uint.Z x.1 < uint.Z p.1 → G.committed.take x.2 <+: p.2)

/-- **C5, `GlobalOk`**: everything `S` and `net` hold is certified by `G` -- its leaders and votes
are raft's, its logs (`log[·]`, `ledLog[·]`, each starting with its term's campaign log) certified,
`chain` a committed prefix, each `termLen` a commit recorded in its term, each append's entries a
slice of a certified log. With `RaftLaws G`: `ElectionSafety`, `OneVotePerTerm` (R 581-586), any two
logs `Matching` (B 132), and leader completeness for the terms after a commit's. -/
def GlobalOk (S : AntCheck.State) (net : List Msg) (G : RaftFacts) : Prop :=
  (∀ l ∈ S.leaders, ∃ j t, (j, t) ∈ G.leaders ∧ l.server = nameOf j ∧ l.term = uint.Z t) ∧
  (∀ v ∈ S.votes, ∃ a t c, (a, t, c) ∈ G.votes ∧
    v.voter = nameOf a ∧ v.term = uint.Z t ∧ v.cand = nameOf c) ∧
  (∀ n : Fin 3, ∃ l ∈ G.logs, S.log[n.val]! = logOf l) ∧
  (∀ p ∈ S.ledLog, ∃ l ∈ G.logs, p.2 = logOf l ∧
    ∃ t l0, uint.Z t = p.1 ∧ (t, l0) ∈ G.camps ∧ l0 <+: l) ∧
  (∃ c ≤ G.committed.length, S.chain = logOf (G.committed.take c)) ∧
  (∀ p ∈ S.termLen, 0 ≤ p.2 ∧ ∃ x, uint.Z x = p.1 ∧ (x, p.2.toNat) ∈ G.commits) ∧
  (∀ m ∈ net, m.ty = .app →
    ∃ l ∈ G.logs, (l.drop (uint.nat m.index)).take m.entries.length = m.entries)

/-- The raft facts a `ready` report needs of the node's new state `ps` (at node `id`), already in
`G` (the harness adds them from `rawNode`'s laws before the report, §3.4): its log certified, its
committed prefix the committed log's, its commit recorded in its term, its leadership raft's with
its campaign log, its vote raft's. -/
def ReadyFacts (G : RaftFacts) (id : w64) (ps : PState) : Prop :=
  ps.log ∈ G.logs ∧ uint.nat ps.commit ≤ G.committed.length ∧
  ps.log.take (uint.nat ps.commit) = G.committed.take (uint.nat ps.commit) ∧
  (ps.term, uint.nat ps.commit) ∈ G.commits ∧
  (ps.role = .leader → (id, ps.term) ∈ G.leaders ∧ ∃ l0, (ps.term, l0) ∈ G.camps ∧ l0 <+: ps.log) ∧
  (ps.vote ≠ W64 0 → (id, ps.term, ps.vote) ∈ G.votes)

/-- The raft facts a `send` report needs of its message (`isMessage`'s): an append's entries a slice
of a certified log, a grant raft's vote. -/
def MsgFacts (G : RaftFacts) (q : Msg) : Prop :=
  (q.ty = .app → ∃ l ∈ G.logs, (l.drop (uint.nat q.index)).take q.entries.length = q.entries) ∧
  ((q.ty = .voteResp ∧ q.reject = false) → (q.src, q.term, q.dst) ∈ G.votes)

end rel

end AntSim
end EtcdGrove
end Perennial
