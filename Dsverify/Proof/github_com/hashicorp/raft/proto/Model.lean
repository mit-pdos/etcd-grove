/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Model.lean (241f27e).
-/
/-
`proto` — the pure Raft protocol model the code is proved against (stage 1, redesign R1; see
`notes/redesign.md`).

The global protocol state `PState` is a pure value: every server's own state (`SState`: current
term, log, persisted vote, durable committed prefix, commit index) and the protocol's *history*
(the leader of each term with its log, the candidates' last entries at their elections, the votes
with the voter's log at the time, the acknowledgements, the recorded commits, the committed log
`C`). Each step of the code that changes the protocol state is one function `PState → PState`
below with its precondition (`…Pre`); `Invariant.lean` defines the inductive invariant `PInv`, and
`Steps.lean` proves that each step preserves it (and only grows the history: `σ ≼ σ'`).

Why a leader log per term (`llog T`): during its term the leader's log only grows, and every entry
of term `t` at index `k` anywhere equals `llog t` at `k`, with the same prefix (`LMok`, log matching
as one invariant per log). Messages need no state: an AppendEntries of term `T` is valid when its
previous entry and entries are a slice of (a prefix of) `llog T` (`AEok`), which stays true as
`llog T` grows.

Indexes are 1-based as in Raft: `ent L k = L[k-1]?`.
-/
module

public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-! ## Entries and logs -/

/-- A server id: the Go `ServerID`/`ServerAddress` bytes (`inproc.Addr(i)`). -/
abbrev SID : Type := List w8

/-- A log entry as the protocol sees it: its term, its `LogType` (as a number) and its data. -/
structure Entry where
  term : Nat
  kind : Nat
  data : List w8
deriving DecidableEq, Inhabited

/-- `LogCommand`, `LogNoop`, `LogBarrier`, `LogConfiguration` (log.go). -/
def kCommand : Nat := 0
def kNoop : Nat := 1
/-- `LogBarrier` (stage 2): `Raft.Barrier` sends one through `applyCh`; the leader appends it as any
command (`dispatchLogs`), the FSM goroutine skips it (`runFSM` applies only commands and
configurations). -/
def kBarrier : Nat := 4
def kConfig : Nat := 5

abbrev RLog : Type := List Entry

/-- The entry at Raft index `k` (1-based; index 0 has none). -/
def ent (L : RLog) (k : Nat) : Option Entry := if k = 0 then none else L[k - 1]?

/-- The term at Raft index `k` (0 if there is no entry). -/
def termAt (L : RLog) (k : Nat) : Nat :=
  match ent L k with
  | some e => e.term
  | none => 0

/-- The term of the last entry (0 for the empty log). -/
def lastTerm (L : RLog) : Nat := termAt L L.length

/-- Raft's up-to-date check: a candidate whose last entry is `(li, lt)` is at least as up to date
as the log `L`. -/
def upToDate (li lt : Nat) (L : RLog) : Prop :=
  lastTerm L < lt ∨ (lastTerm L = lt ∧ L.length ≤ li)

/-- `A` and `B` both have at least `k` entries and agree on indexes `1..k`. -/
def agree (A B : RLog) (k : Nat) : Prop :=
  k ≤ A.length ∧ k ≤ B.length ∧ A.take k = B.take k

/-! ## Configurations (stage 4) -/

/-- Index `k` of `L` holds a configuration entry. -/
def isCfgAt (L : RLog) (k : Nat) : Bool :=
  match ent L k with
  | some e => e.kind == kConfig
  | none => false

/-- The index of the last configuration entry of `L` (`0` if `L` has none): the largest `k ≤ |L|`
with `(ent L k).kind = kConfig`. A server's latest configuration (`configurations.latestIndex`)
is the last configuration entry of its log. -/
def lastCfgIdx (L : RLog) : Nat :=
  (List.range (L.length + 1)).foldl (fun acc k => if isCfgAt L k then k else acc) 0

/-- The voters of the configuration entry at index `p` of `L` (`[]` if there is no entry at `p`),
with `cv` decoding a configuration's data. -/
def cfgAtC (cv : List w8 → List SID) (L : RLog) (p : Nat) : List SID :=
  match ent L p with
  | some e => cv e.data
  | none => []

/-- The voters of the latest configuration of `L` (`[]` without one). -/
def cfgOfC (cv : List w8 → List SID) (L : RLog) : List SID := cfgAtC cv L (lastCfgIdx L)

/-- `Q` is a quorum of the voters `V`: distinct members of `V`, a strict majority. With `V = []`
no quorum exists. -/
def isQuorumOf (V Q : List SID) : Prop :=
  Q.Nodup ∧ (∀ j ∈ Q, j ∈ V) ∧ V.length < 2 * Q.length

/-- `A` and `B` differ by at most one server added or removed (the four changes of
`nextConfiguration`, read on the voters): as sets, `B = A ∪ {x}` or `A = B ∪ {x}` for some `x`.
It covers equal sets when `A ≠ []` (take `x ∈ A`); `adjV [] B` means `B = {x}` (review tier-2 3; so
`quorum_meet`'s equal-sets disjunct adds only `A = B = []`; kept, harmless). -/
def adjV (A B : List SID) : Prop :=
  ∃ x, (∀ y, y ∈ B ↔ y ∈ A ∨ y = x) ∨ (∀ y, y ∈ A ↔ y ∈ B ∨ y = x)

/-- Every quorum of `A` meets every quorum of `B`. -/
def cfgMeet (A B : List SID) : Prop :=
  ∀ Q1 Q2, isQuorumOf A Q1 → isQuorumOf B Q2 → ∃ j, j ∈ Q1 ∧ j ∈ Q2

/-- A configuration's voters are valid: some, distinct, each one of the servers `srvs`. -/
def cfgValid (srvs V : List SID) : Prop :=
  V ≠ [] ∧ V.Nodup ∧ ∀ j ∈ V, j ∈ srvs

/-! ## The state -/

/-- One server's own protocol state, owned by its main goroutine (the term is mirrored by the
`currentTerm` atomic, the log by the log store, `cidx` by the `commitIndex` atomic). -/
structure SState where
  /-- `currentTerm`. -/
  term : Nat
  /-- the log store's contents, index `k` at `log[k-1]`. -/
  log : RLog
  /-- the stable store's `LastVoteTerm` (0: never voted). -/
  vterm : Nat
  /-- the stable store's `LastVoteCand` (meaningful when `vterm > 0`). -/
  vcand : SID
  /-- a committed prefix of the log that can never be removed from it: `(k, T)` with
  `log[1..k] = llog T [1..k]` and a recorded commit of term `T` at `≥ k` (`k = 0`: none). -/
  dur : Nat × Nat
  /-- the value of the `commitIndex` atomic (`≤ dur.1`). -/
  cidx : Nat

/-- The global protocol state: the servers and the protocol's history. -/
structure PState where
  /-- (stage 4) the servers of the run (hr3: the six), each `inproc.Addr(i)`; every per-server
  clause ranges over them. Who votes is read from configurations in logs (`cfgOf`). -/
  srvs : List SID
  /-- (stage 4) the voters of an encoded configuration (a fixed parameter: the ghost layer fixes
  `cv d` = the voter IDs of the configuration whose encoding is `d`). -/
  cv : List w8 → List SID
  /-- the genesis entry: the bootstrap configuration at index 1, term 1, on every bootstrapped
  server (the voters `cv g.data`; the other servers start with the empty log). -/
  g : Entry
  /-- each server's own state. -/
  srv : SID → SState
  /-- `cand c T = some (li, lt)`: candidate `c` started its election of term `T` with last entry
  `(li, lt)` (the `RequestVote` it sends carries exactly these). -/
  cand : SID → Nat → Option (Nat × Nat)
  /-- `votes j T = some (c, L, early)`: `j` granted its vote of term `T` to `c`, with log `L` at the
  time; `early`: no leader of `T` existed then. -/
  votes : SID → Nat → Option (SID × RLog × Bool)
  /-- the leader of each term (at most one). -/
  leader : Nat → Option SID
  /-- the leader's log of each term: its log at the election, then grown by its own appends while
  its term lasts; `[]` for a term without a leader, `[g]` for term 1. -/
  llog : Nat → RLog
  /-- the length of `llog T` at the election. -/
  len0 : Nat → Nat
  /-- `acked j T m`: `j`, in term `T`, answered an AppendEntries of `T` with success when its log
  agreed with `llog T` on `1..m`. -/
  acked : SID → Nat → Nat → Prop
  /-- `commits T k p` (stage 4: with the configuration index `p`): the leader of `T` recorded the
  commit of `llog T [1..k]` by a quorum of the configuration entry at index `p` of `llog T`. -/
  commits : Nat → Nat → Nat → Prop
  /-- (stage 4) `ccfg T`: the index in `llog T` of the configuration the commitment of `T` counts
  (`commitment.setConfiguration`): the leader's latest, or its parent in the window between
  appending a configuration entry and installing it in the commitment. -/
  ccfg : Nat → Nat
  /-- `pubs T k` (stage 2): the leader of `T` published `k` as its commit index while leading `T`
  (leaderLoop's `commitCh` case: it learns `k` from its commitment and stores it with
  `setCommitIndex`; it then hands `1..k` to its FSM with `processLogs`). Every durable prefix is
  covered by a publication (`IPub`), which bounds what any FSM may have applied by what a leader
  published (the read bound, `Read.lean`). -/
  pubs : Nat → Nat → Prop
  /-- the committed log (grows only). -/
  C : RLog
  /-- bounds on terms and log lengths (paid for with time receipts in the ghost layer). -/
  maxT : Nat
  maxI : Nat

namespace PState

def term (σ : PState) (i : SID) : Nat := (σ.srv i).term
def log (σ : PState) (i : SID) : RLog := (σ.srv i).log

end PState

/-! ## Derived notions -/

/-- (stage 4) The voters of the configuration entry at `p` of `L`, decoded with `σ.cv`. -/
abbrev cfgAt (σ : PState) (L : RLog) (p : Nat) : List SID := cfgAtC σ.cv L p

/-- (stage 4) The voters of the latest configuration of `L`. -/
abbrev cfgOf (σ : PState) (L : RLog) : List SID := cfgOfC σ.cv L

/-- Log matching for one log: every entry of term `t` at `k` has `L[1..k] = llog t [1..k]`. -/
def LMok (σ : PState) (L : RLog) : Prop :=
  ∀ k, 1 ≤ k → k ≤ L.length → agree L (σ.llog (termAt L k)) k

/-- The leader of `T`'s log at its election lacks `llog Tc [1..k]`. -/
def lacks (σ : PState) (T k Tc : Nat) : Prop :=
  ¬ (k ≤ σ.len0 T ∧ agree (σ.llog T) (σ.llog Tc) k)

/-- `llog T [1..k]` is committed by the configuration entry at `p` of `llog T`: its last entry is
of term `T` and a quorum of that configuration acknowledged at least `k` entries in term `T`
(whether or not the leader learned it). -/
def committed (σ : PState) (T k p : Nat) : Prop :=
  σ.leader T ≠ none ∧ 1 ≤ k ∧ k ≤ (σ.llog T).length ∧ termAt (σ.llog T) k = T ∧
  ∃ e, ent (σ.llog T) p = some e ∧ e.kind = kConfig ∧
    ∃ Q, isQuorumOf (σ.cv e.data) Q ∧ ∀ j ∈ Q, ∃ m, k ≤ m ∧ σ.acked j T m

/-- (stage 4) The configuration index `p` is one the commitment of `T` may count with when `llog T`
had `q` entries: the latest configuration of `llog T [1..q]`, or its parent while the latest is
`T`'s own entry (the window between `appendConfigurationEntry`'s dispatch and its
`commitment.setConfiguration`). -/
def cfgAdmAt (σ : PState) (T q p : Nat) : Prop :=
  p = lastCfgIdx ((σ.llog T).take q) ∨
  (σ.len0 T < lastCfgIdx ((σ.llog T).take q) ∧
    p = lastCfgIdx ((σ.llog T).take (lastCfgIdx ((σ.llog T).take q) - 1)))

/-- (stage 4) A commitment of `llog T [1..k]` may count the configuration at `p`: admissible at some
length `q ≥ k` of `llog T`. -/
def cfgAdm (σ : PState) (T k p : Nat) : Prop :=
  ∃ q, k ≤ q ∧ q ≤ (σ.llog T).length ∧ cfgAdmAt σ T q p

/-- A valid AppendEntries request of term `T` with previous entry `(prev, pt)`, entries `ents`
(at indexes `prev+1 ..`) and leader commit index `lci`: sent by the leader of `T`, its previous
entry and entries a slice of `llog T`, and `lci` covered by a recorded commit (of a term `≤ T`)
whose log agrees with `llog T` up to `lci`, and (stage 2) by a publication of a term `≤ T` (the
leader sends its `commitIndex`, which it published). Stable as the history grows. -/
def AEok (σ : PState) (T prev pt : Nat) (ents : RLog) (lci : Nat) : Prop :=
  σ.leader T ≠ none ∧
  prev + ents.length ≤ (σ.llog T).length ∧
  (prev = 0 → pt = 0) ∧ (1 ≤ prev → termAt (σ.llog T) prev = pt) ∧
  ents = ((σ.llog T).drop prev).take ents.length ∧
  (lci = 0 ∨ ((∃ T' k' p', T' ≤ T ∧ lci ≤ k' ∧ σ.commits T' k' p' ∧ agree (σ.llog T) (σ.llog T') lci) ∧
    ∃ T'' k'', T'' ≤ T ∧ lci ≤ k'' ∧ σ.pubs T'' k''))

/-- The follower's previous-entry check passed. -/
def prevMatch (L : RLog) (prev pt : Nat) : Prop :=
  prev = 0 ∨ (prev ≤ L.length ∧ termAt L prev = pt)

/-- The first `j` entries of the request are already in the follower's log, with the same terms. -/
def matchedUpTo (L : RLog) (prev : Nat) (ents : RLog) (j : Nat) : Prop :=
  j ≤ ents.length ∧ ∀ j', j' < j → prev + 1 + j' ≤ L.length ∧ termAt L (prev + 1 + j') = termAt ents (j' + 1)

/-! ## Point updates -/

def upd {α : Type} (f : SID → α) (i : SID) (a : α) : SID → α :=
  fun j => if j = i then a else f j

def updT {α : Type} (f : Nat → α) (t : Nat) (a : α) : Nat → α :=
  fun u => if u = t then a else f u

def updST {α : Type} (f : SID → Nat → α) (i : SID) (t : Nat) (a : α) : SID → Nat → α :=
  fun j u => if j = i ∧ u = t then a else f j u

/-! ## The steps (each with its precondition) -/

/-! Stage 4: every step's server ranges over `srvs` (any of the servers, member of a configuration or
not). -/

/-- **setTerm**: `i` adopts term `t ≥` its own (the `currentTerm` atomic store in
`raftState.setCurrentTerm`). A term from a message is an existing one (`≤ maxT`). -/
def setTermPre (σ : PState) (i : SID) (t : Nat) : Prop :=
  i ∈ σ.srvs ∧ σ.term i ≤ t ∧ t ≤ σ.maxT

def setTerm (σ : PState) (i : SID) (t : Nat) : PState :=
  { σ with srv := upd σ.srv i { (σ.srv i) with term := t } }

/-- **newTerm**: `electSelf`'s `setCurrentTerm(term + 1)`: a new term (bumps `maxT`). -/
def newTermPre (σ : PState) (i : SID) : Prop := i ∈ σ.srvs

def newTerm (σ : PState) (i : SID) : PState :=
  { σ with srv := upd σ.srv i { (σ.srv i) with term := σ.term i + 1 },
           maxT := max σ.maxT (σ.term i + 1) }

/-- **recordCand**: right after `newTerm`, the candidate's last entry for its `RequestVote`.
(Stage 4: the new term is `≥ 1`, not `≥ 2`: a non-member at term 0, made candidate by a
`TimeoutNow`, starts an election of term 1 with the empty log; it is never elected, its
configuration being empty.) -/
def recordCandPre (σ : PState) (c : SID) : Prop :=
  c ∈ σ.srvs ∧ 1 ≤ σ.term c ∧ lastTerm (σ.log c) < σ.term c ∧ σ.cand c (σ.term c) = none

def recordCand (σ : PState) (c : SID) : PState :=
  { σ with cand := updST σ.cand c (σ.term c) (some ((σ.log c).length, lastTerm (σ.log c))) }

/-- **grantVote**: `j` (in term `T`, not yet voted in `T`) votes for `c`, whose request carried
`c`'s recorded last entry, which is at least as up to date as `j`'s log (`persistVote`). -/
def grantVotePre (σ : PState) (j c : SID) : Prop :=
  j ∈ σ.srvs ∧ (σ.srv j).vterm < σ.term j ∧
  ∃ li lt, σ.cand c (σ.term j) = some (li, lt) ∧ upToDate li lt (σ.log j)

def grantVote (σ : PState) (j c : SID) : PState :=
  let T := σ.term j
  { σ with votes := updST σ.votes j T (some (c, σ.log j, decide (σ.leader T = none))),
           srv := upd σ.srv j { (σ.srv j) with vterm := T, vcand := c } }

/-- **becomeLeader**: `c` won term `T = term c` with a quorum of votes of the latest configuration
of its log, its log unchanged since it recorded its last entry (`setState(Leader)` in
`runCandidate`). The commitment of `T` counts that configuration (`ccfg T`, `newCommitment` over
`configurations.latest`). (Review tier-2 2: no second branch for `c` already leading `T`; the code
wins an election once, and `gprot.becomeLeader_upd` takes the commitment's configuration at its
pre-election value `0`, which a leader's never is.) -/
def becomeLeaderPre (σ : PState) (c : SID) : Prop :=
  c ∈ σ.srvs ∧
  σ.cand c (σ.term c) = some ((σ.log c).length, lastTerm (σ.log c)) ∧
  ∃ Q, isQuorumOf (cfgOf σ (σ.log c)) Q ∧ ∀ j ∈ Q, ∃ L b, σ.votes j (σ.term c) = some (c, L, b)

def becomeLeader (σ : PState) (c : SID) : PState :=
  let T := σ.term c
  if σ.leader T = none then
    { σ with leader := updT σ.leader T (some c),
             llog := updT σ.llog T (σ.log c),
             len0 := updT σ.len0 T (σ.log c).length,
             ccfg := updT σ.ccfg T (lastCfgIdx (σ.log c)) }
  else σ

/-- **leaderAppend**: the leader of its current term appends its own entries (commands, no-ops or
barriers: `Apply`'s and `Barrier`'s futures, the leader's no-op) at the end of its log (`StoreLogs`
in `dispatchLogs`). -/
def leaderAppendPre (σ : PState) (i : SID) (es : RLog) : Prop :=
  i ∈ σ.srvs ∧ σ.leader (σ.term i) = some i ∧
  ∀ e ∈ es, e.term = σ.term i ∧ (e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kBarrier)

def leaderAppend (σ : PState) (i : SID) (es : RLog) : PState :=
  let T := σ.term i
  { σ with srv := upd σ.srv i { (σ.srv i) with log := σ.log i ++ es },
           llog := updT σ.llog T (σ.log i ++ es),
           maxI := max σ.maxI ((σ.log i).length + es.length) }

/-- **leaderAppendCfg** (stage 4): the leader of its current term appends a configuration entry
`e` (`appendConfigurationEntry`'s `dispatchLogs`): the new configuration's voters are valid and
adjacent to its latest configuration's (`nextConfiguration`: one server added, removed or changed
suffrage); the commitment counts its latest configuration (the previous change was installed);
and a commit of its own term covers its latest configuration's index
(`configurationChangeChIfStable`: the latest configuration is committed, and the leader has
committed an entry of its term). The commitment's configuration is not changed (the window until
`installCfg`). -/
def leaderAppendCfgPre (σ : PState) (i : SID) (e : Entry) : Prop :=
  i ∈ σ.srvs ∧ σ.leader (σ.term i) = some i ∧
  e.term = σ.term i ∧ e.kind = kConfig ∧ cfgValid σ.srvs (σ.cv e.data) ∧
  adjV (cfgOf σ (σ.log i)) (σ.cv e.data) ∧
  σ.ccfg (σ.term i) = lastCfgIdx (σ.log i) ∧
  ∃ k p, σ.commits (σ.term i) k p ∧ σ.len0 (σ.term i) < k ∧ lastCfgIdx (σ.log i) ≤ k

def leaderAppendCfg (σ : PState) (i : SID) (e : Entry) : PState := leaderAppend σ i [e]

/-- **installCfg** (stage 4): the leader of `T` installs its latest configuration in its commitment
(`commitment.setConfiguration` after `appendConfigurationEntry`'s dispatch). -/
def installCfgPre (σ : PState) (T : Nat) : Prop := σ.leader T ≠ none

def installCfg (σ : PState) (T : Nat) : PState :=
  { σ with ccfg := updT σ.ccfg T (lastCfgIdx (σ.llog T)) }

/-- **truncate**: a follower in term `T`, handling a valid AppendEntries of `T` whose previous entry
matched and whose first `j` entries are in its log, finds a different term at index
`c = prev + 1 + j` and deletes its log from `c` (`DeleteRange` in `appendEntries`). -/
def truncatePre (σ : PState) (i : SID) (prev pt : Nat) (ents : RLog) (lci j : Nat) : Prop :=
  i ∈ σ.srvs ∧ AEok σ (σ.term i) prev pt ents lci ∧
  prevMatch (σ.log i) prev pt ∧ matchedUpTo (σ.log i) prev ents j ∧ j < ents.length ∧
  prev + 1 + j ≤ (σ.log i).length ∧
  termAt (σ.log i) (prev + 1 + j) ≠ termAt ents (j + 1)

def truncate (σ : PState) (i : SID) (c : Nat) : PState :=
  { σ with srv := upd σ.srv i { (σ.srv i) with log := (σ.log i).take (c - 1) } }

/-- **followerStore**: then (or with no conflict) it stores the request's entries from the first
one past its log (`StoreLogs` in `appendEntries`). -/
def followerStorePre (σ : PState) (i : SID) (prev pt : Nat) (ents : RLog) (lci j : Nat) : Prop :=
  i ∈ σ.srvs ∧ AEok σ (σ.term i) prev pt ents lci ∧
  prevMatch (σ.log i) prev pt ∧ matchedUpTo (σ.log i) prev ents j ∧ j < ents.length ∧
  (σ.log i).length = prev + j

def followerStore (σ : PState) (i : SID) (es : RLog) : PState :=
  { σ with srv := upd σ.srv i { (σ.srv i) with log := σ.log i ++ es } }

/-- **ack**: `i`, in term `T`, answers an AppendEntries of `T` with success; its log agrees with
`llog T` on `1..k` (ghost; before the response is sent). -/
def ackPre (σ : PState) (i : SID) (k : Nat) : Prop :=
  i ∈ σ.srvs ∧ σ.leader (σ.term i) ≠ none ∧ agree (σ.log i) (σ.llog (σ.term i)) k

def ack (σ : PState) (i : SID) (T k : Nat) : PState :=
  { σ with acked := fun j u m => σ.acked j u m ∨ (j = i ∧ u = T ∧ m = k) }

/-- **commit**: the leader of `T` records the commit of `llog T [1..k]` (`commitment.recalculate`)
by a quorum of the configuration its commitment counts (`ccfg T`); the committed log grows to it. -/
def commitPre (σ : PState) (T k : Nat) : Prop := committed σ T k (σ.ccfg T)

def commit (σ : PState) (T k : Nat) : PState :=
  { σ with commits := fun u m p => σ.commits u m p ∨ (u = T ∧ m = k ∧ p = σ.ccfg T),
           C := if σ.C.length < k then (σ.llog T).take k else σ.C }

/-- **publish** (stage 2): the leader of `T` (its current term) publishes `k` as its commit index:
a recorded commit of `T` at `≥ k` (leaderLoop's `commitCh` case, ghost, before its
`setCommitIndex`; then `learnCommit` of `k`). -/
def publishPre (σ : PState) (i : SID) (k : Nat) : Prop :=
  i ∈ σ.srvs ∧ σ.leader (σ.term i) = some i ∧ ∃ k' p, k ≤ k' ∧ σ.commits (σ.term i) k' p

def publish (σ : PState) (T k : Nat) : PState :=
  { σ with pubs := fun u m => σ.pubs u m ∨ (u = T ∧ m = k) }

/-- **learnCommit**: `i` learns that its log's prefix `1..k` is committed: a recorded commit of a
term `T' ≤ term i` at `≥ k` whose leader log agrees with `i`'s log up to `k` (ghost, before
`setCommitIndex`), and (stage 2) `k` is covered by a publication of a term `≤ term i` (a follower
learns `k ≤` the leader's `LeaderCommitIndex`, which the leader published; the leader publishes
`k` first, `publish`). Keeps the larger durable prefix. -/
def learnCommitPre (σ : PState) (i : SID) (k T' : Nat) : Prop :=
  i ∈ σ.srvs ∧ T' ≤ σ.term i ∧
  (∃ k' p, k ≤ k' ∧ σ.commits T' k' p) ∧ agree (σ.log i) (σ.llog T') k ∧
  (∃ T'' k'', T'' ≤ σ.term i ∧ k ≤ k'' ∧ σ.pubs T'' k'')

def learnCommit (σ : PState) (i : SID) (k T' : Nat) : PState :=
  { σ with srv := upd σ.srv i { (σ.srv i) with dur := if (σ.srv i).dur.1 < k then (k, T') else (σ.srv i).dur } }

/-- **setCidx**: the `commitIndex` atomic store (`setCommitIndex`), at most the durable prefix. -/
def setCidxPre (σ : PState) (i : SID) (c : Nat) : Prop :=
  i ∈ σ.srvs ∧ c ≤ (σ.srv i).dur.1

def setCidx (σ : PState) (i : SID) (c : Nat) : PState :=
  { σ with srv := upd σ.srv i { (σ.srv i) with cidx := c } }

/-- **installDiscard** (stage 3): `installSnapshot`'s `DeleteRange(1, lastLogIdx)` on a follower `i`
whose log does not hold the snapshot's last entry `(s, st)` (`setLastLog(s, st)`). The request is
valid (fix `5894fa2`: the sender checked its term after opening the snapshot): it is the previous
entry and commit index of an AppendEntries of `i`'s term with no entries (`AEok σ T s st [] s`:
`llog T [s]` has term `st`, `s` is covered by a recorded commit of a term `T' ≤ T` agreeing with
`llog T` up to `s`, and by a publication of a term `≤ T`); the term's leader is another server. The
log becomes the committed prefix `llog T [1..s]` and the durable prefix `(s, T')`. (When the log holds
the entry, no new step: the install is a `learnCommit` of `s`.) -/
def installDiscardPre (σ : PState) (i : SID) (s st T' : Nat) : Prop :=
  i ∈ σ.srvs ∧ 1 ≤ s ∧ AEok σ (σ.term i) s st [] s ∧ ¬ prevMatch (σ.log i) s st ∧
  (∃ ℓ, ℓ ≠ i ∧ σ.leader (σ.term i) = some ℓ) ∧
  T' ≤ σ.term i ∧ (∃ k' p, s ≤ k' ∧ σ.commits T' k' p) ∧ agree (σ.llog (σ.term i)) (σ.llog T') s

def installDiscard (σ : PState) (i : SID) (s T' : Nat) : PState :=
  { σ with srv := upd σ.srv i { (σ.srv i) with log := (σ.llog (σ.term i)).take s, dur := (s, T') } }

/-! ## The initial state -/

/-- (stage 4) A server's initial state: a bootstrap voter (`i ∈ cv g.data`) has log `[g]` and term
1; any other server the empty log and term 0. -/
def initSrv (cv : List w8 → List SID) (g : Entry) (i : SID) : SState :=
  if i ∈ cv g.data then SState.mk 1 [g] 0 [] (0, 0) 0 else SState.mk 0 [] 0 [] (0, 0) 0

/-- The bootstrap voters (`cv g.data`) bootstrapped: log `[g]`, term 1; the other servers empty;
no vote; no leader, no history. -/
def init (srvs : List SID) (g : Entry) (cv : List w8 → List SID) : PState where
  srvs := srvs
  cv := cv
  g := g
  srv := initSrv cv g
  cand := fun _ _ => none
  votes := fun _ _ => none
  leader := fun _ => none
  llog := fun t => if t = 1 then [g] else []
  len0 := fun t => if t = 1 then 1 else 0
  acked := fun _ _ _ => False
  commits := fun _ _ _ => False
  ccfg := fun _ => 0
  pubs := fun _ _ => False
  C := []
  maxT := 1
  maxI := 1

/-! ## History order: what every step only grows

Every persistent fact the code holds about the protocol (a leader, a leader-log entry, a vote, an
acknowledgement, a recorded commit, the committed log, a lower bound on a term or on a durable
prefix, a publication) is stable under `≼`. (Review T1-3) A vote new in `σ'` recorded as early
(`grantVote` records `leader T = none`) is of a term without a leader in `σ` (transitive: a leader
of `σ` is one of `σ'`); `Read.snapOK_grows` needs it. -/
def Grows (σ σ' : PState) : Prop :=
  σ'.srvs = σ.srvs ∧ (σ'.g = σ.g ∧ σ'.cv = σ.cv) ∧
  (∀ T ℓ, σ.leader T = some ℓ → σ'.leader T = some ℓ) ∧
  (∀ T, σ.llog T <+: σ'.llog T ∧ (σ.leader T ≠ none ∨ T = 1 → σ'.len0 T = σ.len0 T)) ∧
  (∀ c T x, σ.cand c T = some x → σ'.cand c T = some x) ∧
  (∀ j T x, σ.votes j T = some x → σ'.votes j T = some x) ∧
  (∀ j T m, σ.acked j T m → σ'.acked j T m) ∧
  (∀ T k p, σ.commits T k p → σ'.commits T k p) ∧
  σ.C <+: σ'.C ∧
  (∀ i, σ.term i ≤ σ'.term i) ∧
  (∀ i, (σ.srv i).dur.1 ≤ (σ'.srv i).dur.1) ∧
  σ.maxT ≤ σ'.maxT ∧ σ.maxI ≤ σ'.maxI ∧
  (∀ T k, σ.pubs T k → σ'.pubs T k) ∧
  (∀ j T c L, σ'.votes j T = some (c, L, true) →
    σ.votes j T = some (c, L, true) ∨ σ.leader T = none)

/-- The frontier of what any FSM may have applied in `σ` (stage 2): the largest durable prefix of a
server (a server's FSM applies only entries of its durable prefix: `lastApplied ≤ dur`). -/
def maxDur (σ : PState) : Nat := (σ.srvs.map (fun i => (σ.srv i).dur.1)).foldr max 0

end proto
end github_com.hashicorp.raft
end Perennial
