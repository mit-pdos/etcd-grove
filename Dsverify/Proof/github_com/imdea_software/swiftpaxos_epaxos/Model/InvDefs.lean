/-
The vocabulary and the conjuncts of the protocol invariant `Inv` (split out of
`Epaxos/Model/Inv.lean`, which states the laws, so that the proofs in `Epaxos/Model/Proof/` can
import the definitions and `Inv.lean` can import the proofs; see `Inv.lean` for the overview).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Sys

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

/-! ## Vocabulary -/

/-- The signed value of a ballot/seq/deps entry. -/
abbrev zz (b : w32) : Int := sint.Z b

/-- The initial ballot of instance `x` (`isInitialBallot`: `ballot == replica`). -/
def initBal (x : InstId) : w32 := W32 x.q

/-- The owner of ballot `b` (`b mod N`). -/
def balOwner (b : w32) : Nat := (zz b % nR).toNat

def isPA (st : w8) : Prop := st = stPREACCEPTED ∨ st = stPREACCEPTED_EQ
def isCommitted (st : w8) : Prop := st = stCOMMITTED ∨ st = stEXECUTED

/-- `deps` covers `y`: `deps[y.q] = d` means every instance of row `y.q` up to `d`. -/
def covers (deps : List w32) (y : InstId) : Prop := (y.i : Int) ≤ zz (deps.getD y.q (W32 (-1)))

/-- Pointwise `≤` of deps (both of length `N`). -/
def depsLe (d d' : List w32) : Prop :=
  d.length = nR ∧ d'.length = nR ∧ ∀ q < nR, zz (d.getD q 0) ≤ zz (d'.getD q 0)

/-- Interference as the conflicts structures see it (`updateAttributes`: a non-GET depends on the
last op on the key, a GET on the last non-GET; NONE counts as a write; fix S1: a SCAN depends on
each row's last PUT, a PUT on each row's last SCAN, whatever their keys). -/
def interfereCode (a b : List WCmd) : Prop :=
  ∃ c ∈ a, ∃ c' ∈ b, (c.key = c'.key ∧ (c.op ≠ opGET ∨ c'.op ≠ opGET)) ∨
    (c.op = opSCAN ∧ c'.op = opPUT) ∨ (c.op = opPUT ∧ c'.op = opSCAN)

/-- Interference of executed commands (two commands on one key, neither NONE, one of them a
PUT; or a SCAN and a PUT of a key of its range): what execution consistency needs. On the run's
commands (no NONE among client commands, no wrapping range) it is `state.Conflict`; it leaves out
NONE, which executes nothing. The code orders a superset (`interfereCode`). (Stage 2, review
T2-5, check N1.) (Changed in the prove phase (p-modelexec): the ops other
than GET/PUT/NONE are not excluded any more — the model's proposals are arbitrary commands, and
the executor runs them; it implies `interfereCode` and excludes no-ops.) -/
def interfere (a b : List WCmd) : Prop :=
  ∃ c ∈ a, ∃ c' ∈ b, (c.key = c'.key ∧ (c.op = opPUT ∨ c'.op = opPUT) ∧
    c.op ≠ opNONE ∧ c'.op ≠ opNONE) ∨
    (c.op = opSCAN ∧ c'.op = opPUT ∧ c'.key ∈ rangeKeys c) ∨
    (c.op = opPUT ∧ c'.op = opSCAN ∧ c.key ∈ rangeKeys c')

/-- The value an instance record holds. -/
def instVal (w : InstRec) : Val := ⟨w.cmds.getD [], w.seq, w.deps⟩

/-- The instance a message is about. -/
def Msg.instOf : Msg → Option InstId
  | .prepare m => some ⟨toN m.replica, toN m.inst⟩
  | .prepareReply m => some ⟨toN m.replica, toN m.inst⟩
  | .preAccept m => some ⟨toN m.replica, toN m.inst⟩
  | .preAcceptReply m => some ⟨toN m.replica, toN m.inst⟩
  | .accept m => some ⟨toN m.replica, toN m.inst⟩
  | .acceptReply m => some ⟨toN m.replica, toN m.inst⟩
  | .commit m => some ⟨toN m.replica, toN m.inst⟩
  | .tryPreAccept m => some ⟨toN m.replica, toN m.inst⟩
  | .tryPreAcceptReply m => some ⟨toN m.replica, toN m.inst⟩
  | .beacon _ => none
  | .beaconReply _ => none

/-- The `(replica, instance)` fields of a message, as sent (`int32`s). -/
def Msg.rawId : Msg → Option (w32 × w32)
  | .prepare m => some (m.replica, m.inst)
  | .prepareReply m => some (m.replica, m.inst)
  | .preAccept m => some (m.replica, m.inst)
  | .preAcceptReply m => some (m.replica, m.inst)
  | .accept m => some (m.replica, m.inst)
  | .acceptReply m => some (m.replica, m.inst)
  | .commit m => some (m.replica, m.inst)
  | .tryPreAccept m => some (m.replica, m.inst)
  | .tryPreAcceptReply m => some (m.replica, m.inst)
  | .beacon _ => none
  | .beaconReply _ => none

/-- The deps arrays of a message the code indexes (`deps[q]`, `equal`): a PreAccept's, Accept's,
Commit's, PreAcceptReply's, and a PrepareReply's unless it reports NONE (then `inst.Deps` is the
default instance's `nil`). -/
def Msg.depsFields : Msg → List (List w32)
  | .prepareReply m => if m.status = stNONE then [] else [m.deps]
  | .preAccept m => [m.deps]
  | .preAcceptReply m => [m.deps]
  | .accept m => [m.deps]
  | .commit m => [m.deps]
  | _ => []

/-- A deps array the code can index and follow: `N` entries, each `-1` or an instance number in
range (`InstanceSpace[q][d]`, `d + 1 < MAX_INSTANCE`). -/
def depsOk (ds : List w32) : Prop :=
  ds.length = nR ∧ ∀ d ∈ ds, sint.Z d = -1 ∨ (0 ≤ sint.Z d ∧ toN d + 1 < MAX_INSTANCE)

/-- The conflicts-map record an event makes, if any: `x` for commands `c`. -/
def Event.recorded : Event → Option (InstId × List WCmd)
  | .record x c => some (x, c)
  | .attrsRec x c _ => some (x, c)
  | _ => none

/-- An input whose command's range is the model's (`rangeKeys (cmdOf inp) = scanKeys k n`: no
`int64` wrap-around; `kit.pre` gives it, S4). -/
def inpRangeOk : KvsInput (List w8) → Prop
  | .scan k n => k.toNat + n.toNat < 2 ^ 63
  | _ => True

/-- A client command of the run (`cmdOf` of an input meeting `kit.pre`, EpaxosNetSpec.lean): a GET
or a PUT of key 0 or 1 (a PUT's value non-empty and below `2^15` bytes), or a SCAN of 0 or 1 from
key 0 or 1 (its value the count's 8 bytes, S3). What the executor's no-panic and reply-length
facts rest on (S3, S5; review T1-3). -/
def OpCmdOk (c : WCmd) : Prop :=
  c.key.toNat < 2 ∧
  ((c.op = opGET ∧ c.val = []) ∨ (c.op = opPUT ∧ c.val ≠ [] ∧ c.val.length < 2 ^ 15) ∨
   (c.op = opSCAN ∧ ∃ n : w64, n.toNat < 2 ∧ c.val = u64Le n))

namespace Sys

/-- Replica `r` sent (or is sending) `m` (to anyone). -/
def sentBy (S : Sys) (r : Nat) (m : Msg) : Prop := ∃ to, m ∈ S.msgs r to

/-- Event `e` of replica `r` happened. -/
def ev (S : Sys) (r : Nat) (e : Event) : Prop := (r, e) ∈ S.hist

/-- Event `e` of `r` happened before event `e'` of `r'`. -/
def evBefore (S : Sys) (r : Nat) (e : Event) (r' : Nat) (e' : Event) : Prop :=
  ∃ p p' : Nat, p < p' ∧ S.hist[p]? = some (r, e) ∧ S.hist[p']? = some (r', e')

/-- Some replica committed `v` for `x`, or some Commit message carries `v` for `x`. -/
def committedVal (S : Sys) (x : InstId) (v : Val) : Prop :=
  (∃ r b, S.ev r (.commit x b v)) ∨
  (∃ fr to : Nat, ∃ m : Commit, Msg.commit m ∈ S.msgs fr to ∧ (Msg.commit m).instOf = some x ∧
    v = ⟨m.command, m.seq, m.deps⟩)

/-- Slow path: a majority voted ACCEPTED for `v` at ballot `b`. -/
def slowChosen (S : Sys) (x : InstId) (b : w32) (v : Val) : Prop :=
  ∃ Q : List Nat, Q.Nodup ∧ nR / 2 + 1 ≤ Q.length ∧
    ∀ r ∈ Q, r < nR ∧ S.ev r (.vote x b stACCEPTED v)

/-- Fast path's replies: `2F - 1` distinct replicas other than the leader pre-accepted `v` (the
leader's commands, identical attributes) at the initial ballot. -/
def fastReplies (S : Sys) (x : InstId) (v : Val) : Prop :=
  ∃ Q : List Nat, Q.Nodup ∧ 2 * fR - 1 ≤ Q.length ∧
    ∀ r ∈ Q, r < nR ∧ r ≠ x.q ∧ ∃ st, isPA st ∧ S.ev r (.vote x (initBal x) st v)

/-- The fast path can (still) commit `v`: its replies exist and the leader has not promised a
higher ballot (fix R-LEAD: then it never commits at its initial ballot), or it committed `v`
on the fast path (T2-5). -/
def fastLive (S : Sys) (x : InstId) (v : Val) : Prop :=
  fastReplies S x v ∧
    (((S.rep x.q).inst x).map (·.bal) = some (initBal x) ∨ S.ev x.q (.fastCommit x v))

/-- Replica `r` reported `m` (a `PrepareReply`) by event `e`: `e` is the send of `m` (to the
recovering replica, `handlePrepare`), or `r`'s own report at its recovery's start
(`startRecoveryForInstance`'s `PrepareReply` in `lb.prepareReplies`, `Event.selfReply`). -/
def prepReport (S : Sys) (r : Nat) (m : PrepareReply) (e : Event) : Prop :=
  S.ev r e ∧ ((∃ to, Msg.prepareReply m ∈ S.msgs r to ∧ e = .sent to (.prepareReply m)) ∨
    e = .selfReply m)

/-- Message `m` sent by `a` to `r` at position `n` was delivered (consumed by a handler of `r`). -/
def deliveredMsg (S : Sys) (a r : Nat) (m : Msg) : Prop :=
  ∃ n, (S.sent a r)[n]? = some m ∧ (a, r, n) ∈ S.delivered

/-- The edge `x → y` of the decided graph. -/
def dEdge (S : Sys) (x y : InstId) : Prop :=
  ∃ v, S.committedVal x v ∧ y.q < nR ∧ covers v.deps y

/-- The execution order inside a component (fix E2): `(seq, replica, instance)`. -/
def sccOrd (S : Sys) (x y : InstId) : Prop :=
  ∃ vx vy, S.committedVal x vx ∧ S.committedVal y vy ∧
    (zz vx.seq < zz vy.seq ∨ (vx.seq = vy.seq ∧ (x.q < y.q ∨ (x.q = y.q ∧ x.i ≤ y.i))))

/-- The abstract key-value state (`kvScan w8`'s): the replay of the global per-key sequences
(half of it is `epInv`'s `kvHalf`). -/
def kv (S : Sys) : w64 → Option (List w8) := fun k => lastPut (S.gexec k)

end Sys


/-! ## The conjuncts -/

/-- (wf) Well-formedness the code's indexing relies on (no panic, B11): each replica's `id`; an
instance record sits at its own id in a row `< N`, below `MAX_INSTANCE - 1` (R-CAP), with
followable deps (`depsOk`) once it left NONE, and so has its bookkeeping's deps once the
bookkeeping's status is not NONE; an own instance has its bookkeeping (`handleCommit`,
`handlePreAcceptReply` dereference `inst.lb`); a leader's `clientProposals` are its instance's
owners; `crtInstance` is `-1` or in range; the conflicts map points to existing instances
(`updateAttributes` reads `InstanceSpace[q][d].Seq`); every instance up to `ExecedUpTo[q]` is
executed; messages are between distinct replicas and delivered positions were sent; a pending
broadcast is not exhausted, reads distinct peers other than its replica, is about an instance with
bookkeeping, and is never pending during an executor pass. -/
def Inv.wf (S : Sys) : Prop :=
  (∀ r < nR, (S.rep r).id = r) ∧
  (∀ r < nR, ∀ x w, (S.rep r).inst x = some w →
    w.id = x ∧ x.q < nR ∧ x.i + 1 < MAX_INSTANCE ∧
    (w.status ≠ stNONE → depsOk w.deps) ∧
    (∀ lb, w.lb = some lb → lb.status ≠ stNONE → depsOk lb.deps) ∧
    (x.q = r → w.lb ≠ none) ∧
    (∀ lb ps, w.lb = some lb → lb.clientProposals = some ps → S.owner x = some ps)) ∧
  (∀ r < nR, ∀ q < nR,
    -1 ≤ zz ((S.rep r).crtInstance q) ∧ toN ((S.rep r).crtInstance q) + 1 < MAX_INSTANCE) ∧
  (∀ r < nR, ∀ q k p, (S.rep r).conflicts q k = some p →
    q < nR ∧ (0 ≤ zz p.last → (S.rep r).inst ⟨q, toN p.last⟩ ≠ none) ∧
    (0 ≤ zz p.lastWrite → (S.rep r).inst ⟨q, toN p.lastWrite⟩ ≠ none)) ∧
  (∀ r < nR, ∀ q < nR, ∀ n : Nat, (n : Int) ≤ zz ((S.rep r).execedUpTo q) →
    (S.rep r).executed ⟨q, n⟩) ∧
  (∀ fr to, S.msgs fr to ≠ [] → fr < nR ∧ to < nR ∧ fr ≠ to) ∧
  (∀ fr to n, (fr, to, n) ∈ S.delivered → n < (S.sent fr to).length) ∧
  (∀ r b, S.pending r = some b →
    r < nR ∧ S.execCur r = [] ∧ b.peers ≠ [] ∧ b.sent < b.need ∧ b.peers.Nodup ∧
    (∀ p ∈ b.peers, p < nR ∧ p ≠ r) ∧ ∃ w lb, (S.rep r).inst b.x = some w ∧ w.lb = some lb)

/-- (wf, B11 (1)) Message contents in range: the instance a message names is in range (the
handlers index `InstanceSpace[m.Replica][m.Instance]`), and the deps arrays the code indexes are
followable (`depsOk`). -/
def Inv.msgWf (S : Sys) : Prop :=
  ∀ fr to m, m ∈ S.msgs fr to →
    (∀ q n, m.rawId = some (q, n) →
      0 ≤ zz q ∧ zz q < nR ∧ 0 ≤ zz n ∧ toN n + 1 < MAX_INSTANCE) ∧
    (∀ ds ∈ m.depsFields, depsOk ds)

/-- (wf, B11 (2)) A reply reaches an instance with bookkeeping (`handlePrepareReply` dereferences
`inst.lb` before its `nil` test; `handlePreAcceptReply`, `handleAcceptReply` dereference `inst` and
`lb`). -/
def Inv.replyTargets (S : Sys) : Prop :=
  ∀ fr to m x, m ∈ S.msgs fr to → m.instOf = some x →
    ((∃ p, m = .prepareReply p) ∨ (∃ p, m = .preAcceptReply p) ∨ (∃ p, m = .acceptReply p)) →
    ∃ w lb, (S.rep to).inst x = some w ∧ w.lb = some lb

/-- (wf, B11 (3)) No TryPreAccept traffic (D2: the recovery never takes sub-case 4), so the
`hTryPreAccept*` handlers, and `deferMap`, are never reached. -/
def Inv.noTPA (S : Sys) : Prop :=
  ∀ fr to m, m ∈ S.msgs fr to →
    (∀ p, m ≠ .tryPreAccept p) ∧ (∀ p, m ≠ .tryPreAcceptReply p)

/-- (a1) Ballots: at every replica and instance, `bal ≥ vbal`; every vote of a replica is at a
ballot at most its current `bal` (ballots only grow). -/
def Inv.ballots (S : Sys) : Prop :=
  (∀ r < nR, ∀ x w, (S.rep r).inst x = some w → zz w.vbal ≤ zz w.bal) ∧
  (∀ r < nR, ∀ x b st v, S.ev r (.vote x b st v) →
    ∃ w, (S.rep r).inst x = some w ∧ zz b ≤ zz w.bal)

/-- (a2) Ballot ownership: a ballot `b` of `x` is made by its owner only, once: the initial
ballot by the leader (`handlePropose`), a recovery ballot `≥ N` by `b mod N` (fix R-BAL; it does
not wrap: fix B10's guard); every Prepare, PreAccept, Accept at `b` (and every Phase 1 / Accept
event at `b`) is by `b`'s maker, after it made `b`, with `LeaderId` its id. -/
def Inv.ballotOwner (S : Sys) : Prop :=
  (∀ r x b, S.ev r (.makeBallot x b) →
    ((zz b = x.q ∧ r = x.q) ∨ (nR ≤ zz b ∧ balOwner b = r)) ∧
    (S.hist.filter (· = (r, .makeBallot x b))).length = 1) ∧
  (∀ r x b v, S.ev r (.phase1 x b v) → S.evBefore r (.makeBallot x b) r (.phase1 x b v)) ∧
  (∀ r x b v, S.ev r (.accept x b v) → S.ev r (.makeBallot x b)) ∧
  (∀ r to (m : Prepare), Msg.prepare m ∈ S.msgs r to →
    m.leaderId = W32 r ∧ S.ev r (.makeBallot ⟨toN m.replica, toN m.inst⟩ m.ballot)) ∧
  (∀ r to (m : PreAccept), Msg.preAccept m ∈ S.msgs r to →
    m.leaderId = W32 r ∧
    S.ev r (.phase1 ⟨toN m.replica, toN m.inst⟩ m.ballot ⟨m.command, m.seq, m.deps⟩)) ∧
  (∀ r to (m : Accept), Msg.accept m ∈ S.msgs r to →
    m.leaderId = W32 r ∧
    S.ev r (.accept ⟨toN m.replica, toN m.inst⟩ m.ballot ⟨m.command, m.seq, m.deps⟩))

/-- (a3) One proposal per (instance, ballot): at most one Phase 1 at `b`; every Accept at `b`
carries one value; an Accept at the ballot of a Phase 1 carries its commands. -/
def Inv.oneProposal (S : Sys) : Prop :=
  (∀ r r' x b v v', S.ev r (.phase1 x b v) → S.ev r' (.phase1 x b v') → r = r' ∧ v = v' ∧
    (S.hist.filter (· = (r, .phase1 x b v))).length = 1) ∧
  (∀ r r' x b v v', S.ev r (.accept x b v) → S.ev r' (.accept x b v') → v = v') ∧
  (∀ r r' x b v v', S.ev r (.phase1 x b v) → S.ev r' (.accept x b v') → v'.cmds = v.cmds)

/-- (a4) A vote is for the ballot's proposal: a pre-accept vote at `b` is for the Phase 1 at `b`'s
commands (the initial ballot's Phase 1 is the leader's `handlePropose`); an accept vote at `b` for
the Accept at `b`. -/
def Inv.votesFollowProposals (S : Sys) : Prop :=
  (∀ r x b st v, S.ev r (.vote x b st v) → isPA st →
    ∃ ℓ v₀, S.ev ℓ (.phase1 x b v₀) ∧ v.cmds = v₀.cmds) ∧
  (∀ r x b v, S.ev r (.vote x b stACCEPTED v) → ∃ ℓ, S.ev ℓ (.accept x b v))

/-- (a5) Replies report votes.
* A `PrepareReply` of `r` (sent, or `r`'s own report at its recovery's start, `prepReport`)
  reports `r`'s last vote before it (status, `VBallot`, the whole value: T2-1, no deps escape), or
  the decided value if committed, or no vote at all (NONE); its `Ballot` is a promise: after it,
  `r` votes for `x` only at ballots `≥` it (Paxos phase 1).
* A `PreAcceptReply` of `a` to `r` answers `r`'s Phase 1 at its ballot; a pre-accepted one is
  `a`'s vote at that ballot (with its seq and deps), an accepted one reports `a`'s accept vote,
  a committed one the decided attributes.
* An `AcceptReply` of `a` at `b` to `r` (the leader of `b`; a rejected Accept gets no reply, fix
  R-AREP) follows `a`'s accept vote at `b`, or comes from `a` after it committed `x` and then no
  `PrepareReply` of `a` before it promised above `b` (B12 (3)). -/
def Inv.repliesReportVotes (S : Sys) : Prop :=
  (∀ r m e, S.prepReport r m e →
    let x : InstId := ⟨toN m.replica, toN m.inst⟩
    m.acceptorId = W32 r ∧
    ((isPA m.status ∨ m.status = stACCEPTED) →
      S.evBefore r (.vote x m.vballot m.status ⟨m.command, m.seq, m.deps⟩) r e) ∧
    (isCommitted m.status → S.committedVal x ⟨m.command, m.seq, m.deps⟩) ∧
    (m.status = stNONE → ∀ b st v, ¬ S.evBefore r (.vote x b st v) r e) ∧
    (∀ b st v, S.evBefore r e r (.vote x b st v) → zz m.ballot ≤ zz b)) ∧
  (∀ a r (m : PreAcceptReply), Msg.preAcceptReply m ∈ S.msgs a r →
    let x : InstId := ⟨toN m.replica, toN m.inst⟩
    (∃ v, S.ev r (.phase1 x m.ballot v)) ∧
    (isPA m.status → m.vballot = m.ballot ∧
      ∃ v, S.ev a (.vote x m.ballot m.status v) ∧ v.seq = m.seq ∧ v.deps = m.deps) ∧
    (m.status = stACCEPTED →
      ∃ v, S.ev a (.vote x m.vballot stACCEPTED v) ∧ v.seq = m.seq ∧ v.deps = m.deps) ∧
    (isCommitted m.status → ∃ v, S.committedVal x v ∧ v.seq = m.seq ∧ v.deps = m.deps)) ∧
  (∀ a r (m : AcceptReply), Msg.acceptReply m ∈ S.msgs a r →
    let x : InstId := ⟨toN m.replica, toN m.inst⟩
    (∃ v, S.evBefore a (.vote x m.ballot stACCEPTED v) a (.sent r (.acceptReply m))) ∨
    ((∃ b v, S.evBefore a (.commit x b v) a (.sent r (.acceptReply m))) ∧
      ∀ m' e', S.prepReport a m' e' → (Msg.prepareReply m').instOf = some x →
        S.evBefore a e' a (.sent r (.acceptReply m)) → zz m'.ballot ≤ zz m.ballot))

/-- (a6, B12 (2)) A `PrepareReply` reports the highest vote before it (Paxos phase 1 picks the
reply with the highest `VBallot`). -/
def Inv.prepReplyHighest (S : Sys) : Prop :=
  ∀ r m e, S.prepReport r m e → ∀ b st v,
    S.evBefore r (.vote ⟨toN m.replica, toN m.inst⟩ b st v) r e → zz b ≤ zz m.vballot

/-- (a7, B12 (1)) The bookkeeping of the ballot `r` leads for `x` (`lb.lastTriedBallot`):
* `r` made it; `lb.ballot ≤` it; TryPreAccept is never tried; every Phase 1 and Accept of `r`
  for `x` is at a ballot `≤` it (so no reply carries a higher ballot: the nack branches of
  `handlePreAcceptReply`/`handleAcceptReply`, and their unguarded `makeBallot`, are dead);
* pre-accepted with a counted reply: `lb.ballot` is it, the prepare phase is over, and `lb.cmds`
  are its Phase 1's;
* `preAcceptOKs` counts distinct acceptors (not `r`) whose delivered `PreAcceptReply` is at it;
  while pre-accepted, `lb`'s attributes are the merge (`≥`) of theirs, equal to each when
  `allEqual` (`mergeAttributes` merges and compares every row, the leader's own included: fix
  R-ROW3);
* `acceptOKs` counts distinct acceptors (not `r`) whose delivered `AcceptReply` is at it;
* accepting at it (its instance ACCEPTED at it, out of the prepare phase): `r` sent the Accept
  of `lb`'s value at it and voted for it;
* while preparing: `prepareReplies` are from distinct acceptors, at it, each a delivered
  `PrepareReply` or `r`'s own report. -/
def Inv.lbInv (S : Sys) : Prop :=
  ∀ r < nR, ∀ x w lb, (S.rep r).inst x = some w → w.lb = some lb →
    S.ev r (.makeBallot x lb.lastTriedBallot) ∧
    zz lb.ballot ≤ zz lb.lastTriedBallot ∧
    lb.tryingToPreAccept = false ∧
    (∀ b v, (S.ev r (.phase1 x b v) ∨ S.ev r (.accept x b v)) → zz b ≤ zz lb.lastTriedBallot) ∧
    (isPA lb.status → lb.preAcceptOKs ≠ W64 0 →
      lb.ballot = lb.lastTriedBallot ∧ lb.preparing = false ∧
      ∃ v, S.ev r (.phase1 x lb.lastTriedBallot v) ∧ lb.cmds = some v.cmds) ∧
    (∃ Q : List (Nat × PreAcceptReply), (Q.map (·.1)).Nodup ∧
      Q.length = lb.preAcceptOKs.toNat ∧
      ∀ a m, (a, m) ∈ Q → a < nR ∧ a ≠ r ∧ S.deliveredMsg a r (.preAcceptReply m) ∧
        (Msg.preAcceptReply m).instOf = some x ∧ m.ballot = lb.lastTriedBallot ∧
        (isPA lb.status → depsLe m.deps lb.deps ∧ zz m.seq ≤ zz lb.seq ∧
          (lb.allEqual = true → m.seq = lb.seq ∧ m.deps = lb.deps))) ∧
    (∃ Q : List Nat, Q.Nodup ∧ Q.length = lb.acceptOKs.toNat ∧
      ∀ a ∈ Q, a < nR ∧ a ≠ r ∧ ∃ m : AcceptReply, S.deliveredMsg a r (.acceptReply m) ∧
        (Msg.acceptReply m).instOf = some x ∧ m.ballot = lb.lastTriedBallot) ∧
    (lb.status = stACCEPTED → w.status = stACCEPTED → w.bal = lb.lastTriedBallot →
      lb.preparing = false →
      S.ev r (.accept x lb.lastTriedBallot ⟨lb.cmds.getD [], lb.seq, lb.deps⟩) ∧
      S.ev r (.vote x lb.lastTriedBallot stACCEPTED ⟨lb.cmds.getD [], lb.seq, lb.deps⟩)) ∧
    (lb.preparing = true →
      (lb.prepareReplies.map (·.m.acceptorId)).Nodup ∧
      ∀ e ∈ lb.prepareReplies, e.m.ballot = lb.lastTriedBallot ∧
        (Msg.prepareReply e.m).instOf = some x ∧
        ((toN e.m.acceptorId ≠ r ∧ S.deliveredMsg (toN e.m.acceptorId) r (.prepareReply e.m)) ∨
         (toN e.m.acceptorId = r ∧ S.ev r (.selfReply e.m))))

/-- (b1) Agreement: one decided value per instance (every commit event, Commit message and
committed/executed record agree), and a committed record has commands. -/
def Inv.agreement (S : Sys) : Prop :=
  (∀ x v v', S.committedVal x v → S.committedVal x v' → v = v') ∧
  (∀ r < nR, ∀ x w, (S.rep r).inst x = some w → isCommitted w.status →
    w.cmds ≠ none ∧ S.committedVal x (instVal w))

/-- (b2) A decided value was chosen: by a majority of accept votes at some ballot, or by the fast
path (its `2F - 1` replies and the leader's fast commit, T2-5). -/
def Inv.decidedChosen (S : Sys) : Prop :=
  ∀ x v, S.committedVal x v →
    (∃ b, S.slowChosen x b v) ∨ (S.fastReplies x v ∧ S.ev x.q (.fastCommit x v))

/-- (b3) The Paxos-with-fast-path invariant: if `v` can be chosen at ballot `b` (slow: a majority
of accept votes at `b`; fast: `b` the initial ballot and `fastLive`), every proposal at a higher
ballot carries `v`: every Accept at `b' > b` is for `v`, and there is no Phase 1 at `b' > b`
(recovery takes sub-case 1, 2 or 3: SOSP'13 Sec. 4.4 with fast quorum 2F, D2; R-PREP). -/
def Inv.chosenSafe (S : Sys) : Prop :=
  ∀ x b v, (S.slowChosen x b v ∨ (b = initBal x ∧ S.fastLive x v)) →
    ∀ b', zz b < zz b' →
      (∀ r v', S.ev r (.accept x b' v') → v' = v) ∧ (∀ r v', ¬ S.ev r (.phase1 x b' v'))

/-- (c1) Dependencies: of two interfering decided instances, one covers the other in its deps
(fix B3: every attribute computation covers every row; the same-row escape is gone). -/
def Inv.depsCover (S : Sys) : Prop :=
  ∀ x y vx vy, x ≠ y → S.committedVal x vx → S.committedVal y vy → interfere vx.cmds vy.cmds →
    covers vx.deps y ∨ covers vy.deps x

/-- (c2) Witnesses: a decided value's attributes were computed by at least `F + 1` replicas, each
of which, in one event, computed attributes for it, at most the decided deps, and recorded it
(for the value's commands) in its conflicts map (fix B13). -/
def Inv.witnesses (S : Sys) : Prop :=
  ∀ x v, S.committedVal x v → v.cmds ≠ noop →
    ∃ W : List Nat, W.Nodup ∧ fR + 1 ≤ W.length ∧
      ∀ r ∈ W, r < nR ∧ ∃ d, S.ev r (.attrsRec x v.cmds d) ∧ depsLe d v.deps

/-- (c3) Attributes cover what was recorded before: when a replica computes attributes for `y`
after recording an interfering `x` (alone or with its own attribute computation), they cover `x`
(every row: fix B3). -/
def Inv.attrsCover (S : Sys) : Prop :=
  ∀ r e x cx y cy d, e.recorded = some (x, cx) → x ≠ y →
    S.evBefore r e r (.attrsRec y cy d) → interfereCode cy cx → covers d x

/-- (d1) Execution is closed under deps: an executed instance is decided (with the value the
replica holds) and everything it points to is executed or in the component being executed
(changed in the prove phase: an instance executed first in a multi-instance component points to
the component's later ones); the log lists exactly the executed instances, once each. -/
def Inv.execClosed (S : Sys) : Prop :=
  ∀ r < nR,
    (S.execLog r).Nodup ∧ (∀ x, x ∈ S.execLog r ↔ (S.rep r).executed x) ∧
    (∀ x w, (S.rep r).inst x = some w → w.status = stEXECUTED →
      S.committedVal x (instVal w) ∧
        ∀ y, (S.rep r).depEdge x y → (S.rep r).executed y ∨ y ∈ S.execCur r)

/-- (d2) The executor's progress (fix B8): while it executes a component, the component is the
sort of a closed strongly connected set of the replica's graph whose executed prefix is
EXECUTED, whose rest is committed with commands, and whose head's command index is in range. -/
def Inv.execCursor (S : Sys) : Prop :=
  ∀ r < nR, (S.execCur r = [] → S.execIdx r = 0) ∧
    (S.execCur r ≠ [] →
      ∃ done C : List InstId, sccSort (S.rep r) C = done ++ S.execCur r ∧ C.Nodup ∧
        (∀ x ∈ done, (S.rep r).executed x) ∧ (∀ x ∈ S.execCur r, (S.rep r).ready x) ∧
        (∀ x ∈ C, ∀ y, (S.rep r).depEdge x y → (S.rep r).executed y ∨ y ∈ C) ∧
        (∀ x ∈ C, ∀ y ∈ C, x = y ∨
          Relation.TransGen (fun a b => (S.rep r).depEdge a b ∧ a ∈ C ∧ b ∈ C) x y) ∧
        ∀ x w, (S.execCur r).head? = some x → (S.rep r).inst x = some w →
          S.execIdx r ≤ (w.cmds.getD []).length)

/-- (d3) Execution order (fix B2): whatever an earlier-executed instance reaches in the decided
graph reaches it back (is in its component), and inside a component the order is
`(seq, replica, instance)` (fix E2). -/
def Inv.execOrder (S : Sys) : Prop :=
  ∀ r < nR, ∀ (i j : Nat) (x y : InstId), i < j → (S.execLog r)[i]? = some x →
    (S.execLog r)[j]? = some y →
    Relation.TransGen S.dEdge x y → Relation.TransGen S.dEdge y x ∧ S.sccOrd x y

/-- (d4) Execution consistency: each replica's executed writes of a key are a prefix of the key's
global writes; each replica's store is the replay of its executed sequences; and an executed
slot is in the global sequence, preceded there by the same writes as at the replica (GETs on one
key commute and may run in different orders at different replicas). -/
def Inv.execPrefix (S : Sys) : Prop :=
  (∀ r < nR, ∀ k, Sys.writes (S.lexec r k) <+: Sys.writes (S.gexec k)) ∧
  (∀ r < nR, ∀ k, (S.rep r).store k = Sys.lastPut (S.lexec r k)) ∧
  (∀ r < nR, ∀ k pre e post, S.lexec r k = pre ++ e :: post →
    ∃ gpre gpost, S.gexec k = gpre ++ e :: gpost ∧ Sys.writes pre = Sys.writes gpre)

/-- (e1) Slots: a decided value is its instance's batch (the owners' commands, in order) or a
no-op; the owners of an instance are client proposals that reached its leader. -/
def Inv.slots (S : Sys) : Prop :=
  (∀ x v, S.committedVal x v → v.cmds = noop ∨ ∃ ps, S.owner x = some ps ∧ v.cmds = ps.map (·.cmd)) ∧
  (∀ x ps, S.owner x = some ps → ∀ p ∈ ps, (x.q, p) ∈ S.ops)

/-- (e2) Client ops: connection ids are distinct; an op's command appears in the global
sequences in one slot only, once in each sequence, and in the sequence of every key it touches
if in any; every entry of a global sequence is a decided client command touching its key with
its slot's op; the fired ops are exactly those whose slot is in a global sequence, with the
output against the sequences before it. -/
def Inv.clientOps (S : Sys) : Prop :=
  (S.ops.map (·.2.cid)).Nodup ∧
  (∀ k k' e e' p p', e ∈ S.gexec k → e' ∈ S.gexec k' → S.slotOp e.1 = some p →
    S.slotOp e'.1 = some p' → p.cid = p'.cid → e.1 = e'.1) ∧
  (∀ k, ((S.gexec k).map (·.1)).Nodup) ∧
  (∀ k e, e ∈ S.gexec k → Sys.touches e.2 k ∧ e.2.op ≠ opNONE ∧
    (∀ k', Sys.touches e.2 k' → e ∈ S.gexec k') ∧
    (∃ p, S.slotOp e.1 = some p ∧ p.cmd = e.2) ∧
    ∃ v, S.committedVal e.1.1 v ∧ v.cmds[e.1.2]? = some e.2) ∧
  (∀ cid o, S.fired cid = some o ↔
    ∃ e p, e ∈ S.gexec e.2.key ∧ S.slotOp e.1 = some p ∧ p.cid = cid ∧
      o = Sys.outOf (fun k => Sys.before (S.gexec k) e) e.2)

/-- (aux, added in the prove phase) Every Commit message carries the value of a commit event
for its instance (so `committedVal` is witnessed by events; needed by `lose`, which drops outbox
messages). -/
def Inv.commitMsgs (S : Sys) : Prop :=
  ∀ fr to (m : Commit), Msg.commit m ∈ S.msgs fr to →
    ∃ r b, S.ev r (.commit ⟨toN m.replica, toN m.inst⟩ b ⟨m.command, m.seq, m.deps⟩)

/-- A broadcast's message kind: Prepare, PreAccept, Accept or Commit. -/
def Msg.isBcast : Msg → Bool
  | .prepare _ | .preAccept _ | .accept _ | .commit _ => true
  | _ => false

/-- (aux, added in the prove phase) A pending broadcast carries a Prepare, PreAccept, Accept or
Commit (so its sends log no reply event). -/
def Inv.pendingKind (S : Sys) : Prop :=
  ∀ r b, S.pending r = some b → b.m.isBcast = true

/-! ## The Paxos safety invariant (added in the prove phase)

`chosenSafe` speaks only of values chosen *now*; it is not inductive (an accept vote that
completes a majority at `b` needs every proposal above `b` to be safe already). `Inv.safe` is the
classical inductive form (Lamport's `SafeAt`): a proposal at `b'` was made knowing that no other
value can ever be chosen at a lower ballot, because a majority promised above it without
accepting that value there (`Sys.blocked`), and (fast path) that no other value can ever be
fast-chosen (`Sys.fastBlocked`). `chosenSafe` follows (`Proof/Safe.lean`, `chosenSafe_of_safe`). -/

/-- A ballot of `x` a proposal can be at: the initial ballot or a recovery ballot (`≥ N`). -/
def realBal (x : InstId) (b : w32) : Prop := b = initBal x ∨ (nR : Int) ≤ zz b

namespace Sys

/-- `w` can never be chosen on the slow path at ballot `b`: a majority of replicas did not vote
ACCEPTED for `w` at `b` and promised above `b` (their `bal > b`: `bal` never decreases and a vote
at `b` needs `b ≥ bal`). -/
def blocked (S : Sys) (x : InstId) (b : w32) (w : Val) : Prop :=
  ∃ Q : List Nat, Q.Nodup ∧ nR / 2 + 1 ≤ Q.length ∧
    ∀ a ∈ Q, a < nR ∧ ¬ S.ev a (.vote x b stACCEPTED w) ∧
      ∃ wa, (S.rep a).inst x = some wa ∧ zz b < zz wa.bal

/-- Replica `a` did not and will never pre-accept `w` at `x`'s initial ballot: it did not, and
it promised above the initial ballot or holds the instance at least ACCEPTED (a PreAccept then
gets no pre-accept vote), or it pre-accepted another value there (one pre-accept vote per
ballot), or the initial ballot's Phase 1 is made and its PreAccept never went to `a` (the thrifty
broadcast). -/
def noPA (S : Sys) (x : InstId) (a : Nat) (w : Val) : Prop :=
  (∀ st, isPA st → ¬ S.ev a (.vote x (initBal x) st w)) ∧
  ((∃ wa, (S.rep a).inst x = some wa ∧
      (zz (initBal x) < zz wa.bal ∨ stGe wa.status stACCEPTED = true)) ∨
   (∃ st u, isPA st ∧ u ≠ w ∧ S.ev a (.vote x (initBal x) st u)) ∨
   ((∃ v0, S.ev x.q (.phase1 x (initBal x) v0)) ∧
     ∀ m : PreAccept, Msg.preAccept m ∈ S.msgs x.q a → (Msg.preAccept m).instOf = some x →
       m.ballot ≠ initBal x))

/-- `w` can never be fast-chosen: two replicas other than the leader will never pre-accept `w`
at the initial ballot (`noPA`; so at most `2F - 2` can), or the leader promised above the initial
ballot without having fast-committed `w` (so it never will). -/
def fastBlocked (S : Sys) (x : InstId) (w : Val) : Prop :=
  (∃ B : List Nat, B.Nodup ∧ 2 ≤ B.length ∧ ∀ a ∈ B, a < nR ∧ a ≠ x.q ∧ S.noPA x a w) ∨
  ((∃ wl, (S.rep x.q).inst x = some wl ∧ zz (initBal x) < zz wl.bal) ∧
    ¬ S.ev x.q (.fastCommit x w))

/-- An Accept of `v'` at `b'` is safe: at every real ballot below `b'` every other value is
blocked, and, if `b'` is above the initial ballot, no other value can be fast-chosen. -/
def safeAcc (S : Sys) (x : InstId) (b' : w32) (v' : Val) : Prop :=
  (∀ b, realBal x b → zz b < zz b' → ∀ w, w ≠ v' → S.blocked x b w) ∧
  (zz (initBal x) < zz b' → ∀ w, w ≠ v' → S.fastBlocked x w)

/-- A Phase 1 at `b'` is safe: at every real ballot below `b'` every value is blocked, and, if
`b'` is above the initial ballot, no value can be fast-chosen. -/
def safePh (S : Sys) (x : InstId) (b' : w32) : Prop :=
  (∀ b, realBal x b → zz b < zz b' → ∀ w, S.blocked x b w) ∧
  (zz (initBal x) < zz b' → ∀ w, S.fastBlocked x w)

end Sys

/-- (aux, added in the prove phase; Paxos `SafeAt`) Every Accept and every Phase 1 was made
safe (`Sys.safeAcc`, `Sys.safePh`). -/
def Inv.safe (S : Sys) : Prop :=
  (∀ r x b' v', S.ev r (.accept x b' v') → S.safeAcc x b' v') ∧
  (∀ r x b' v', S.ev r (.phase1 x b' v') → S.safePh x b')

/-- (aux, added in the prove phase) What the recovery's decision needs of the reports
(`Proof/Decide.lean`, `decide_safe`), with `x` the report's instance:
* a report's status is NONE, pre-accepted, ACCEPTED or committed; NONE has `vballot = -1`; a
  non-NONE report's deps have `N` entries; `vballot ≤ ballot`;
* an ACCEPTED vote of the replica before the report, at a ballot at least `vballot`, makes the
  report ACCEPTED or committed (the record keeps its last vote's status);
* the replica's current `bal` is at least the report's ballot (`bal` never decreases: fix R-PROM);
* one pre-accept value per (replica, instance, ballot);
* a leader that fast-committed reports a committed status;
* the leader's Accept at the initial ballot (its slow path) is made when no value can be
  fast-chosen any more (thrifty counting: at most `F` PreAccepts sent, or two counted replies
  differ). -/
def Inv.reports (S : Sys) : Prop :=
  (∀ r m e, S.prepReport r m e →
    m.status = stNONE ∨ isPA m.status ∨ m.status = stACCEPTED ∨ isCommitted m.status) ∧
  (∀ r m e, S.prepReport r m e → m.status = stNONE → zz m.vballot = -1) ∧
  (∀ r m e, S.prepReport r m e → m.status ≠ stNONE → m.deps.length = nR) ∧
  (∀ r m e, S.prepReport r m e → ∀ b u,
    S.evBefore r (.vote ⟨toN m.replica, toN m.inst⟩ b stACCEPTED u) r e →
    zz m.vballot ≤ zz b → m.status = stACCEPTED ∨ isCommitted m.status) ∧
  (∀ r m e, r < nR → S.prepReport r m e →
    ∃ w, (S.rep r).inst ⟨toN m.replica, toN m.inst⟩ = some w ∧ zz m.ballot ≤ zz w.bal) ∧
  (∀ r x b st st' v v', isPA st → isPA st' → S.ev r (.vote x b st v) →
    S.ev r (.vote x b st' v') → v = v') ∧
  (∀ x v m e, S.ev x.q (.fastCommit x v) → S.prepReport x.q m e →
    (⟨toN m.replica, toN m.inst⟩ : InstId) = x → isCommitted m.status) ∧
  (∀ r x v, S.ev r (.accept x (initBal x) v) → ∀ w, S.fastBlocked x w) ∧
  (∀ r m e, S.prepReport r m e → zz m.vballot ≤ zz m.ballot)

/-- The protocol invariant's first part: the conjuncts above (`Inv` adds `InvAux`). -/
def Inv0 (S : Sys) : Prop :=
  Inv.wf S ∧ Inv.msgWf S ∧ Inv.replyTargets S ∧ Inv.noTPA S ∧
  Inv.ballots S ∧ Inv.ballotOwner S ∧ Inv.oneProposal S ∧
  Inv.votesFollowProposals S ∧ Inv.repliesReportVotes S ∧ Inv.prepReplyHighest S ∧
  Inv.lbInv S ∧
  Inv.agreement S ∧ Inv.decidedChosen S ∧ Inv.chosenSafe S ∧
  Inv.depsCover S ∧ Inv.witnesses S ∧ Inv.attrsCover S ∧
  Inv.execClosed S ∧ Inv.execCursor S ∧ Inv.execOrder S ∧ Inv.execPrefix S ∧
  Inv.slots S ∧ Inv.clientOps S ∧
  Inv.commitMsgs S ∧ Inv.pendingKind S ∧ Inv.safe S ∧ Inv.reports S

/-! ## Auxiliary conjuncts (prove phase, third agent)

The record ↔ history link, commit finality, the makers' bookkeeping, `crtInstance` bounds, the
pre-accepting and preparing leader's facts, and the message-counting facts (one PreAccept/Accept
per (ballot, peer); one counted reply per acceptor). Gathered in one structure so that the
finished step proofs of `Inv0` stay as they are. -/

/-- The instance an event is about (`sent` events: none, they are about messages). -/
def Event.instOf : Event → Option InstId
  | .makeBallot x _ | .vote x .. | .phase1 x .. | .accept x .. | .commit x .. | .fastCommit x _
  | .record x _ | .attrsRec x .. => some x
  | .selfReply m => some ⟨toN m.replica, toN m.inst⟩
  | .sent .. => none

/-- A PreAccept about `x` at ballot `b`. -/
def Msg.isPAat (x : InstId) (b : w32) : Msg → Bool
  | .preAccept p => decide ((⟨toN p.replica, toN p.inst⟩ : InstId) = x ∧ p.ballot = b)
  | _ => false

/-- A PreAcceptReply about `x` at ballot `b`. -/
def Msg.isPARat (x : InstId) (b : w32) : Msg → Bool
  | .preAcceptReply p => decide ((⟨toN p.replica, toN p.inst⟩ : InstId) = x ∧ p.ballot = b)
  | _ => false

/-- An Accept about `x` at ballot `b`. -/
def Msg.isAccAt (x : InstId) (b : w32) : Msg → Bool
  | .accept p => decide ((⟨toN p.replica, toN p.inst⟩ : InstId) = x ∧ p.ballot = b)
  | _ => false

/-- An AcceptReply about `x` at ballot `b`. -/
def Msg.isARat (x : InstId) (b : w32) : Msg → Bool
  | .acceptReply p => decide ((⟨toN p.replica, toN p.inst⟩ : InstId) = x ∧ p.ballot = b)
  | _ => false

namespace Sys

/-- The number of messages from `fr` to `to` satisfying `p`. -/
def cnt (S : Sys) (fr to : Nat) (p : Msg → Bool) : Nat := ((S.msgs fr to).filter p).length

/-- Every message from `fr` to `to` satisfying `p` was delivered (at its position). -/
def allDeliv (S : Sys) (fr to : Nat) (p : Msg → Bool) : Prop :=
  ∀ n m, (S.msgs fr to)[n]? = some m → p m = true → (fr, to, n) ∈ S.delivered

/-- Replica `r`'s bookkeeping for `x` tries a ballot above `b`. -/
def lastAbove (S : Sys) (r : Nat) (x : InstId) (b : w32) : Prop :=
  ∃ w lb, (S.rep r).inst x = some w ∧ w.lb = some lb ∧ zz b < zz lb.lastTriedBallot

end Sys

/-- The command list a message carries for its receiver to store (PreAccept, Accept, Commit,
TryPreAccept). -/
def Msg.commandField : Msg → Option (List WCmd)
  | .preAccept m => some m.command
  | .accept m => some m.command
  | .commit m => some m.command
  | .tryPreAccept m => some m.command
  | _ => none

/-! ## Execution conjuncts (prove phase, p-modelexec)

The executors' consistency: each replica's *execution sequence* (its log, then the rest of the
component it is executing) is closed under the decided graph's edges and ordered by it (an
instance comes after what it reaches, unless they reach each other, and then in
`(seq, replica, instance)` order); every slot of a global sequence was executed by some replica;
and each client op owns at most one live slot (the proposal tokens: a proposal is in one
`ProposeChan` or owns one slot, until its instance is decided as a NONE command and its leader
re-proposed it). -/

namespace Sys

/-- Replica `r`'s execution sequence: its log, then the rest of the component it executes. -/
def eseq (S : Sys) (r : Nat) : List InstId := S.execLog r ++ S.execCur r

/-- Instance `x` no longer holds its proposals: it is decided as one NONE command
(`handleCommit`'s re-proposal test) and its leader's bookkeeping dropped the proposals. -/
def propDead (S : Sys) (x : InstId) : Prop :=
  (∃ v c, S.committedVal x v ∧ v.cmds = [c] ∧ c.op = opNONE) ∧
  ∀ w lb, (S.rep x.q).inst x = some w → w.lb = some lb → lb.clientProposals = none

end Sys

/-- (p-modelexec) The execution conjuncts. -/
structure InvExec (S : Sys) : Prop where
  /-- an execution sequence is closed under the decided graph's edges -/
  reach : ∀ r < nR, ∀ a b, a ∈ S.eseq r → S.dEdge a b → b ∈ S.eseq r
  /-- an execution sequence is ordered: what comes later is not reached, unless it reaches back
  and comes later in `(seq, replica, instance)` order -/
  ord : ∀ r < nR, ∀ (l1 l2 : List InstId) (a b : InstId), S.eseq r = l1 ++ l2 → a ∈ l1 →
    b ∈ l2 → Relation.TransGen S.dEdge a b → Relation.TransGen S.dEdge b a ∧ S.sccOrd a b
  /-- every slot of a global sequence was executed by some replica -/
  gloc : ∀ k e, e ∈ S.gexec k → ∃ r < nR, e ∈ S.lexec r k
  /-- two slots of one client op: one of their instances no longer holds its proposals -/
  tokSlot : ∀ (s s' : Slot) (p p' : Proposal), s ≠ s' → S.slotOp s = some p → S.slotOp s' = some p' →
    p.cid = p'.cid → S.propDead s.1 ∨ S.propDead s'.1
  /-- a proposal in a channel: every slot of its op is in an instance that no longer holds it -/
  tokChan : ∀ (i : Nat) (p : Proposal) (s : Slot) (p' : Proposal), p ∈ S.proposeChan i →
    S.slotOp s = some p' → p'.cid = p.cid → S.propDead s.1
  /-- the channels hold each op at most once -/
  chanOnce : ∀ (i j n m : Nat) (p p' : Proposal), (S.proposeChan i)[n]? = some p →
    (S.proposeChan j)[m]? = some p' → p.cid = p'.cid → i = j ∧ n = m
  /-- the channels hold client ops, each in the channel of the replica it reached (changed by
  p-model2, was: its connection id is an op's; `handlePropose` needs `Inv.slots`' `(x.q, p) ∈ ops`
  for the batch) -/
  chanOps : ∀ (i : Nat) (p : Proposal), p ∈ S.proposeChan i → (i, p) ∈ S.ops

/-! ## Reply-handler conjuncts (prove phase, p-model, sixth agent)

What `handlePreAcceptReply` and `handleAcceptReply` need: a committed acceptor's `AcceptReply`
is counted only when it is harmless (G3, decisions.md D5), commits and Commit messages at or below
the initial ballot carry the initial Phase 1's commands (a COMMITTED `PreAcceptReply` counted by
the fast path), the replies' ranges, the thrifty PreAccept count at the initial ballot
(`lb.preAcceptsSent`), and the witnesses of accepted values. -/

namespace Sys

/-- Commands `cs` were proposed for `x` at ballot `c`: some vote or Phase 1 at `c` carries
them. -/
def propAt (S : Sys) (x : InstId) (c : w32) (cs : List WCmd) : Prop :=
  (∃ q st u, (isPA st ∨ st = stACCEPTED) ∧ S.ev q (.vote x c st u) ∧ u.cmds = cs) ∨
    (∃ q u, S.ev q (.phase1 x c u) ∧ u.cmds = cs)

/-- `v`'s attributes were computed by `F + 1` replicas (as `Inv.witnesses` asks of a decided
value). -/
def witnessed (S : Sys) (x : InstId) (v : Val) : Prop :=
  ∃ W : List Nat, W.Nodup ∧ fR + 1 ≤ W.length ∧
    ∀ r ∈ W, r < nR ∧ ∃ d, S.ev r (.attrsRec x v.cmds d) ∧ depsLe d v.deps

/-- The replicas other than the leader `x.q` that replica `x.q` sent (or is about to hand to the
wire) a PreAccept of `x` at its initial ballot: the thrifty broadcast's recipients so far. -/
def paRcpt (S : Sys) (x : InstId) : List Nat :=
  (List.range nR).filter (fun a => (S.sent x.q a ++ S.outbox x.q a).any (Msg.isPAat x (initBal x)))

/-- (SLOW-WIT, seventh agent) Commands `Z` can never be chosen at the command level at ballot
`c` (a majority of votes of any status at `c` with commands `Z`): a majority promised above `c`
without any vote at `c` with commands `Z`. -/
def cmdBlocked (S : Sys) (x : InstId) (c : w32) (Z : List WCmd) : Prop :=
  ∃ Q : List Nat, Q.Nodup ∧ nR / 2 + 1 ≤ Q.length ∧
    ∀ a ∈ Q, a < nR ∧
      (∀ st u, (isPA st ∨ st = stACCEPTED) → S.ev a (.vote x c st u) → u.cmds ≠ Z) ∧
      ∃ wa, (S.rep a).inst x = some wa ∧ zz c < zz wa.bal

/-- (SLOW-WIT) Commands `Z` are chosen at the command level at ballot `c`: a majority voted (any
status) at `c` for values with commands `Z`. -/
def cmdChosen (S : Sys) (x : InstId) (c : w32) (Z : List WCmd) : Prop :=
  ∃ Q : List Nat, Q.Nodup ∧ nR / 2 + 1 ≤ Q.length ∧
    ∀ a ∈ Q, a < nR ∧ ∃ st u, (isPA st ∨ st = stACCEPTED) ∧ S.ev a (.vote x c st u) ∧ u.cmds = Z

end Sys

/-- The instance an `AcceptReply` is about. -/
abbrev arX (m : AcceptReply) : InstId := ⟨toN m.replica, toN m.inst⟩

/-- The instance a `PreAcceptReply` is about. -/
abbrev parX (m : PreAcceptReply) : InstId := ⟨toN m.replica, toN m.inst⟩

/-- (p-model, sixth agent) The reply handlers' conjuncts. -/
structure InvPM (S : Sys) : Prop where
  /-- (G3) an `AcceptReply` of `a` to `r` at `b`, for the value `v` of `r`'s Accept at `b`: `a`
  voted `v` at `b`, or `v` is decided, or `r` promised above `b`, or a majority without `a`
  promised above `b` without voting `v` there and sent `r` no `AcceptReply` at `b` (so `r` can
  never count a third one) -/
  arOk : ∀ a r (m : AcceptReply), Msg.acceptReply m ∈ S.msgs a r → ∀ v,
    S.ev r (.accept (arX m) m.ballot v) →
    S.ev a (.vote (arX m) m.ballot stACCEPTED v) ∨ S.committedVal (arX m) v ∨
    (∃ w, (S.rep r).inst (arX m) = some w ∧ zz m.ballot < zz w.bal) ∨
    ∃ M : List Nat, M.Nodup ∧ nR / 2 + 1 ≤ M.length ∧ a ∉ M ∧ ∀ q ∈ M, q < nR ∧
      ¬ S.ev q (.vote (arX m) m.ballot stACCEPTED v) ∧
      (∃ wq, (S.rep q).inst (arX m) = some wq ∧ zz m.ballot < zz wq.bal) ∧
      ∀ m' : AcceptReply, Msg.acceptReply m' ∈ S.msgs q r → arX m' = arX m → m'.ballot ≠ m.ballot
  /-- a commit at or below the initial ballot: its commands were proposed at its ballot -/
  commitProp : ∀ r x c u, S.ev r (.commit x c u) → zz c ≤ zz (initBal x) → S.propAt x c u.cmds
  /-- a Commit message's commands were proposed at its ballot -/
  commitMsgProp : ∀ fr to (m : Commit), Msg.commit m ∈ S.msgs fr to →
    S.propAt ⟨toN m.replica, toN m.inst⟩ m.ballot m.command
  /-- an accepting bookkeeping that made its Accept: its commands were proposed at `lb.ballot`
  (the ballot its Commit will carry) -/
  lbProp : ∀ r < nR, ∀ x w lb, (S.rep r).inst x = some w → w.lb = some lb →
    lb.status = stACCEPTED → (∃ v, S.ev r (.accept x lb.lastTriedBallot v)) →
    S.propAt x lb.ballot (lb.cmds.getD [])
  /-- a committed `PreAcceptReply` follows a commit of its sender at a ballot at most its
  ballot, with its attributes -/
  parCom : ∀ a r (m : PreAcceptReply), Msg.preAcceptReply m ∈ S.msgs a r →
    isCommitted m.status → ∃ c u, S.ev a (.commit (parX m) c u) ∧ zz c ≤ zz m.ballot ∧
      u.seq = m.seq ∧ u.deps = m.deps
  /-- a `PreAcceptReply`'s status is a vote's or committed, `0 ≤ vballot ≤ ballot`, and it
  answers a PreAccept at its ballot that its target handed to the wire -/
  parSt : ∀ a r (m : PreAcceptReply), Msg.preAcceptReply m ∈ S.msgs a r →
    (isPA m.status ∨ m.status = stACCEPTED ∨ isCommitted m.status) ∧ 0 ≤ zz m.vballot ∧
    zz m.vballot ≤ zz m.ballot ∧ ∃ p : PreAccept, Msg.preAccept p ∈ S.sent r a ∧
      (⟨toN p.replica, toN p.inst⟩ : InstId) = parX m ∧ p.ballot = m.ballot
  /-- a pre-accepting bookkeeping past its Phase 1 without counted replies has `ballot = -1` -/
  paFresh : ∀ r < nR, ∀ x w lb, (S.rep r).inst x = some w → w.lb = some lb → isPA lb.status →
    lb.preAcceptOKs = W64 0 → (∃ v, S.ev r (.phase1 x lb.lastTriedBallot v)) → zz lb.ballot = -1
  /-- the thrifty PreAccept at the initial ballot: at most `2F - 1` sends; while its broadcast is
  pending, `lb.preAcceptsSent` is its send count; the recipients handed to the wire (or about
  to be) are at most `lb.preAcceptsSent` -/
  paSent : ∀ x w lb, x.q < nR → (S.rep x.q).inst x = some w → w.lb = some lb →
    lb.lastTriedBallot = initBal x →
    lb.preAcceptsSent.toNat ≤ 2 * fR - 1 ∧
    (∀ b, S.pending x.q = some b → b.x = x → b.trackPA = true →
      b.m.isPAat x (initBal x) = true ∧ b.sent = lb.preAcceptsSent.toNat ∧ b.need ≤ 2 * fR - 1) ∧
    (S.paRcpt x).length ≤ lb.preAcceptsSent.toNat
  /-- a pending broadcast of a PreAccept is the tracking one of its instance -/
  pendPA : ∀ r b, S.pending r = some b → ∀ x c, b.m.isPAat x c = true → b.trackPA = true ∧ b.x = x
  /-- a non-leader's pre-accept vote at the initial ballot answers a PreAccept the leader handed
  to the wire -/
  paVoteMsg : ∀ r x st v, isPA st → r ≠ x.q → S.ev r (.vote x (initBal x) st v) →
    ∃ p : PreAccept, Msg.preAccept p ∈ S.sent x.q r ∧ (⟨toN p.replica, toN p.inst⟩ : InstId) = x ∧
      p.ballot = initBal x
  /-- an acceptor that answered a PreAccept without pre-accepting never pre-accepts at that
  ballot -/
  parNoPA : ∀ a r (m : PreAcceptReply), Msg.preAcceptReply m ∈ S.msgs a r → ¬ isPA m.status →
    ∀ st u, isPA st → ¬ S.ev a (.vote (parX m) m.ballot st u)
  /-- a pre-accepting bookkeeping with `allEqual = false` received two replies at its ballot
  with different attributes -/
  aeF : ∀ r < nR, ∀ x w lb, (S.rep r).inst x = some w → w.lb = some lb → isPA lb.status →
    lb.allEqual = false → ∃ (a a' : Nat) (m m' : PreAcceptReply), Msg.preAcceptReply m ∈ S.sent a r ∧
      Msg.preAcceptReply m' ∈ S.sent a' r ∧ parX m = x ∧ parX m' = x ∧
      m.ballot = lb.lastTriedBallot ∧ m'.ballot = lb.lastTriedBallot ∧
      (m.seq ≠ m'.seq ∨ m.deps ≠ m'.deps)
  /-- a leader that reported on its own instance promised above the initial ballot -/
  repLead : ∀ r m e, S.prepReport r m e → r = toN m.replica →
    ∃ w, (S.rep r).inst ⟨toN m.replica, toN m.inst⟩ = some w ∧
      zz (initBal ⟨toN m.replica, toN m.inst⟩) < zz w.bal
  /-- a pre-accept vote's deps are at least its Phase 1's -/
  paGe : ∀ r x b st v ℓ v0, isPA st → S.ev r (.vote x b st v) → S.ev ℓ (.phase1 x b v0) →
    depsLe v0.deps v.deps
  /-- a Phase 1's maker computed its attributes -/
  phAttrs : ∀ ℓ x b v0, S.ev ℓ (.phase1 x b v0) → S.ev ℓ (.attrsRec x v0.cmds v0.deps)
  /-- an accepted value (not a no-op) is witnessed, unless the instance is decided -/
  accWit : ∀ r x b v, S.ev r (.accept x b v) → v.cmds ≠ noop →
    S.witnessed x v ∨ ∃ u, S.committedVal x u
  /-- a pre-accepting bookkeeping holds its Phase 1's commands -/
  paCmds : ∀ r < nR, ∀ x w lb, (S.rep r).inst x = some w → w.lb = some lb → isPA lb.status →
    ∀ v, S.ev r (.phase1 x lb.lastTriedBallot v) → lb.cmds = some v.cmds
  /-- the maker of an Accept voted for it -/
  accVote : ∀ r x b v, S.ev r (.accept x b v) → S.ev r (.vote x b stACCEPTED v)
  /-- (SLOW-WIT, seventh agent) the command-level Paxos invariant (`SafeAt` over commands, with
  pre-accept and accept votes alike): a Phase 1 at `n` was made when no other commands could be
  chosen at the command level at a real ballot below `n`; its maker pre-accepted its commands -/
  cmdSafe : ∀ ℓ x n v, S.ev ℓ (.phase1 x n v) →
    (∃ st u, isPA st ∧ S.ev ℓ (.vote x n st u) ∧ u.cmds = v.cmds) ∧
    ∀ c, realBal x c → zz c < zz n → ∀ Z, Z ≠ v.cmds → S.cmdBlocked x c Z
  /-- (SLOW-WIT) an Accept's commands are chosen at the command level at a real ballot at most
  its own, unless the instance is committed somewhere (a slow path counts a majority of votes at
  its ballot, or an ACCEPTED/COMMITTED reply whose Accept is supported in turn; sub-case 2 copies
  a supported Accept; sub-case 3 has two pre-accept votes and the leader's at the initial
  ballot) -/
  accSup : ∀ r x c v, S.ev r (.accept x c v) → (∃ r' b u, S.ev r' (.commit x b u)) ∨
    ∃ c0, realBal x c0 ∧ zz c0 ≤ zz c ∧ S.cmdChosen x c0 v.cmds

/-- (p-exec, MODEL-REQUEST exec-M1) every replica's `ExecedUpTo[q]` is at least `-1` (its initial
value; `execBump` only increments it): the executor's scan indexes the row at `ExecedUpTo[q] + 1`.
(The upper bound follows from `Inv.wf`: an executed instance is in range.) -/
def ExecLo (S : Sys) : Prop := ∀ r < nR, ∀ q < nR, -1 ≤ zz ((S.rep r).execedUpTo q)

/-- (aux, third agent) The auxiliary conjuncts. -/
structure InvAux (S : Sys) : Prop where
  /-- a record's status is one of the six -/
  stRange : ∀ r < nR, ∀ x w, (S.rep r).inst x = some w →
    w.status = stNONE ∨ isPA w.status ∨ w.status = stACCEPTED ∨ isCommitted w.status
  /-- a record past NONE has commands -/
  cmdsSome : ∀ r < nR, ∀ x w, (S.rep r).inst x = some w → w.status ≠ stNONE → w.cmds ≠ none
  /-- a NONE record: `vbal = -1`, and its replica never voted for the instance -/
  noneRec : ∀ r < nR, ∀ x w, (S.rep r).inst x = some w → w.status = stNONE →
    zz w.vbal = -1 ∧ ∀ b st v, ¬ S.ev r (.vote x b st v)
  /-- a record past NONE has `vbal ≥ 0` -/
  vbalNonneg : ∀ r < nR, ∀ x w, (S.rep r).inst x = some w → w.status ≠ stNONE → 0 ≤ zz w.vbal
  /-- `vbal` is the highest vote ballot of the replica for the instance -/
  votesLe : ∀ r < nR, ∀ x w, (S.rep r).inst x = some w →
    ∀ b st v, S.ev r (.vote x b st v) → zz b ≤ zz w.vbal
  /-- a voted record (pre-accepted or accepted) holds one of its replica's votes -/
  recVote : ∀ r < nR, ∀ x w, (S.rep r).inst x = some w → (isPA w.status ∨ w.status = stACCEPTED) →
    S.ev r (.vote x w.vbal w.status (instVal w))
  /-- an ACCEPTED vote at `vbal` or above leaves the record ACCEPTED or committed -/
  accKeep : ∀ r < nR, ∀ x w, (S.rep r).inst x = some w → ∀ b u,
    S.ev r (.vote x b stACCEPTED u) → zz w.vbal ≤ zz b → w.status = stACCEPTED ∨ isCommitted w.status
  /-- a committed record follows a commit event of its replica at a ballot at most its `bal` -/
  recCommit : ∀ r < nR, ∀ x w, (S.rep r).inst x = some w → isCommitted w.status →
    ∃ b v, S.ev r (.commit x b v) ∧ zz b ≤ zz w.bal
  /-- commit finality: a replica that committed an instance holds it committed -/
  commitRec : ∀ r x b v, r < nR → S.ev r (.commit x b v) →
    ∃ w, (S.rep r).inst x = some w ∧ isCommitted w.status
  /-- a fast commit is the leader's, with a commit event -/
  fastCommitEv : ∀ r x v, S.ev r (.fastCommit x v) → r = x.q ∧ ∃ b, S.ev r (.commit x b v)
  /-- a ballot's maker holds a bookkeeping whose `lastTriedBallot` is at least it -/
  makerLb : ∀ r x b, r < nR → S.ev r (.makeBallot x b) →
    ∃ w lb, (S.rep r).inst x = some w ∧ w.lb = some lb ∧ zz b ≤ zz lb.lastTriedBallot
  /-- `lastTriedBallot ≤ bal` -/
  lastLeBal : ∀ r < nR, ∀ x w lb, (S.rep r).inst x = some w → w.lb = some lb →
    zz lb.lastTriedBallot ≤ zz w.bal
  /-- the broadcasts' peers: the first `N - 1` of the peer order are distinct other replicas -/
  peerOk : ∀ r < nR, ((S.rep r).peerOrder.take (nR - 1)).Nodup ∧
    ∀ p ∈ (S.rep r).peerOrder.take (nR - 1), p < nR ∧ p ≠ r
  /-- every replica's `crtInstance[q]` is at most `q`'s own -/
  crtOwn : ∀ r < nR, ∀ q < nR, zz ((S.rep r).crtInstance q) ≤ zz ((S.rep q).crtInstance q)
  /-- records, messages and events are about instances up to their row owner's `crtInstance` -/
  crtRec : ∀ r < nR, ∀ x w, (S.rep r).inst x = some w →
    (x.i : Int) ≤ zz ((S.rep x.q).crtInstance x.q)
  crtMsg : ∀ fr to m x, m ∈ S.msgs fr to → m.instOf = some x →
    (x.i : Int) ≤ zz ((S.rep x.q).crtInstance x.q)
  crtEv : ∀ r e x, S.ev r e → e.instOf = some x → x.q < nR ∧
    (x.i : Int) ≤ zz ((S.rep x.q).crtInstance x.q)
  /-- a replica holds every instance of its row up to its `crtInstance`, with bookkeeping -/
  ownRow : ∀ q < nR, ∀ j : Nat, (j : Int) ≤ zz ((S.rep q).crtInstance q) →
    ∃ w lb, (S.rep q).inst ⟨q, j⟩ = some w ∧ w.lb = some lb
  /-- a pre-accepting bookkeeping made no Accept at its ballot -/
  paNoAcc : ∀ r < nR, ∀ x w lb, (S.rep r).inst x = some w → w.lb = some lb → isPA lb.status →
    ∀ v, ¬ S.ev r (.accept x lb.lastTriedBallot v)
  /-- a pre-accepting leader past its Phase 1, still at its ballot and not committed, holds its
  own vote at it -/
  paLeader : ∀ r < nR, ∀ x w lb, (S.rep r).inst x = some w → w.lb = some lb → isPA lb.status →
    (∃ v, S.ev r (.phase1 x lb.lastTriedBallot v)) → stGe w.status stCOMMITTED = false →
    w.bal = lb.lastTriedBallot → w.vbal = lb.lastTriedBallot ∧ isPA w.status
  /-- a preparing bookkeeping: its ballot is a recovery ballot without Phase 1 or Accept yet;
  only a NONE own report has `nil` commands; `leaderResponded` means the leader's report is
  among the replies -/
  prepNoProp : ∀ r < nR, ∀ x w lb, (S.rep r).inst x = some w → w.lb = some lb →
    lb.preparing = true →
    (nR : Int) ≤ zz lb.lastTriedBallot ∧ (∀ v, ¬ S.ev r (.phase1 x lb.lastTriedBallot v)) ∧
    (∀ v, ¬ S.ev r (.accept x lb.lastTriedBallot v)) ∧
    (∀ e ∈ lb.prepareReplies, e.cmdsNil = true → e.m.status = stNONE) ∧
    (lb.leaderResponded = true → ∃ e ∈ lb.prepareReplies, toN e.m.acceptorId = x.q)
  /-- one PreAccept and one Accept per (instance, ballot, sender, peer) -/
  paMsgOnce : ∀ fr to x b, S.cnt fr to (Msg.isPAat x b) ≤ 1
  accMsgOnce : ∀ fr to x b, S.cnt fr to (Msg.isAccAt x b) ≤ 1
  /-- a pre-accept vote at `b` is the maker's own, or every PreAccept at `b` to the voter was
  delivered -/
  paVoteDeliv : ∀ r x b st v, isPA st → S.ev r (.vote x b st v) →
    (∃ v0, S.ev r (.phase1 x b v0)) ∨ ∀ fr, S.allDeliv fr r (Msg.isPAat x b)
  /-- one PreAcceptReply per (instance, ballot, acceptor, leader), after the PreAccept's
  delivery -/
  parOnce : ∀ a r x b, 1 ≤ S.cnt a r (Msg.isPARat x b) →
    S.cnt a r (Msg.isPARat x b) = 1 ∧ S.allDeliv r a (Msg.isPAat x b)
  /-- an AcceptReply at `b` answers an Accept at `b' ≥ b` of its target; two of them (or one
  sent before the Accept at `b` to it was delivered) only once the target tries above `b` -/
  arFrom : ∀ a r (m : AcceptReply), Msg.acceptReply m ∈ S.msgs a r →
    ∃ b' v, zz m.ballot ≤ zz b' ∧ S.ev r (.accept ⟨toN m.replica, toN m.inst⟩ b' v)
  arOnce : ∀ a r x b, 1 ≤ S.cnt a r (Msg.isARat x b) →
    S.lastAbove r x b ∨ (S.cnt a r (Msg.isARat x b) = 1 ∧ S.allDeliv r a (Msg.isAccAt x b))
  /-- a Commit's ballot is nonnegative (so is a committed record's `vbal`) -/
  commitBal : ∀ fr to (m : Commit), Msg.commit m ∈ S.msgs fr to → 0 ≤ zz m.ballot
  /-- every `PrepareReply` ever sent (even if since dropped) is a promise: its ballot is at most
  its sender's current `bal`, and the sender votes only at ballots at least it after it -/
  sentPR : ∀ r to (m : PrepareReply), S.ev r (.sent to (.prepareReply m)) →
    (r < nR → ∃ w, (S.rep r).inst ⟨toN m.replica, toN m.inst⟩ = some w ∧ zz m.ballot ≤ zz w.bal) ∧
    (∀ b st v, S.evBefore r (.sent to (.prepareReply m)) r
      (.vote ⟨toN m.replica, toN m.inst⟩ b st v) → zz m.ballot ≤ zz b) ∧
    ∀ to' (m2 : AcceptReply), S.evBefore r (.sent to (.prepareReply m)) r (.sent to' (.acceptReply m2)) →
      (⟨toN m2.replica, toN m2.inst⟩ : InstId) = ⟨toN m.replica, toN m.inst⟩ → zz m.ballot ≤ zz m2.ballot
  /-- (fourth agent, for `attrsCover`) the conflicts map covers every instance its replica
  recorded: for each recorded command, the entry of its key in the instance's row is at least the
  instance (and its `lastWrite` too for a non-GET) -/
  confCover : ∀ r < nR, ∀ e x cx, S.ev r e → e.recorded = some (x, cx) → ∀ c ∈ cx,
    ∃ p, (S.rep r).conflicts x.q c.key = some p ∧ (x.i : Int) ≤ zz p.last ∧
      (c.op ≠ opGET → (x.i : Int) ≤ zz p.lastWrite)
  /-- (stage 2, review T1-1) `lastScan[q]`/`lastPut[q]`, when not `-1`, name an existing
  instance of row `q` (`updateAttributes` reads `InstanceSpace[q][d].Seq` for them) -/
  classWf : ∀ r < nR, ∀ q < nR,
    (0 ≤ zz ((S.rep r).lastScan q) → (S.rep r).inst ⟨q, toN ((S.rep r).lastScan q)⟩ ≠ none) ∧
    (0 ≤ zz ((S.rep r).lastPut q) → (S.rep r).inst ⟨q, toN ((S.rep r).lastPut q)⟩ ≠ none) ∧
    -1 ≤ zz ((S.rep r).lastScan q) ∧ -1 ≤ zz ((S.rep r).lastPut q)
  /-- (stage 2, for `attrsCover`'s class clause, fix S1) every recorded SCAN / PUT is covered by
  its row's last SCAN / last PUT -/
  classCover : ∀ r < nR, ∀ e x cx, S.ev r e → e.recorded = some (x, cx) → ∀ c ∈ cx,
    (c.op = opSCAN → (x.i : Int) ≤ zz ((S.rep r).lastScan x.q)) ∧
    (c.op = opPUT → (x.i : Int) ≤ zz ((S.rep r).lastPut x.q))
  /-- (fourth agent, for `witnesses`) a pre-accept vote comes with an attribute computation
  (and record) of its commands and deps -/
  paAttrs : ∀ r x b st v, isPA st → S.ev r (.vote x b st v) → S.ev r (.attrsRec x v.cmds v.deps)
  /-- (fourth agent, for `slots`) a proposal's commands are the instance's batch or a no-op -/
  valOk : ∀ r x b v, (S.ev r (.phase1 x b v) ∨ S.ev r (.accept x b v)) →
    v.cmds = noop ∨ ∃ ps, S.owner x = some ps ∧ v.cmds = ps.map (·.cmd)
  /-- (fourth agent, MODEL-REQUEST epaxos-2) stored and sent command lists are not empty: the
  commands a message carries to be stored; a record's and a bookkeeping's commands; a non-NONE
  PrepareReply's and own report's commands; a proposal's commands -/
  cmdsNe : (∀ fr to m, m ∈ S.msgs fr to → ∀ cs, m.commandField = some cs → cs ≠ []) ∧
    (∀ r < nR, ∀ x w cs, (S.rep r).inst x = some w → w.cmds = some cs → cs ≠ []) ∧
    (∀ r < nR, ∀ x w lb cs, (S.rep r).inst x = some w → w.lb = some lb → lb.cmds = some cs →
      cs ≠ []) ∧
    (∀ fr to (m : PrepareReply), Msg.prepareReply m ∈ S.msgs fr to → m.status ≠ stNONE →
      m.command ≠ []) ∧
    (∀ r (m : PrepareReply), S.ev r (.selfReply m) → m.status ≠ stNONE → m.command ≠ []) ∧
    (∀ r x b v, (S.ev r (.phase1 x b v) ∨ S.ev r (.accept x b v)) → v.cmds ≠ [])
  /-- (fourth agent, for `handlePrepareReply`) a PrepareReply in the messages was sent by its
  sender (so a delivered one is a `prepReport`) -/
  prSent : ∀ fr to (m : PrepareReply), Msg.prepareReply m ∈ S.msgs fr to →
    S.ev fr (.sent to (.prepareReply m))
  /-- (fourth agent, for `handlePrepareReply`) an own report past NONE has followable deps -/
  selfOk : ∀ r (m : PrepareReply), S.ev r (.selfReply m) → m.status ≠ stNONE → depsOk m.deps
  -- protocol fields (p-model)
  /-- (fifth agent, for `handlePrepareReply`'s decision) an own report names its instance's row
  as a raw `int32` in range (`DecideProof.Reports`: `prepDecide` compares `AcceptorId` with
  `Replica`) -/
  selfRaw : ∀ r (m : PrepareReply), S.ev r (.selfReply m) → m.replica = W32 (toN m.replica)
  /-- (sixth agent, for the reply handlers) the reply handlers' conjuncts (`InvPM`) -/
  pm : InvPM S
  -- propose fields (p-model2)
  /-- (p-model2, for `handlePropose`: its new instance has no owner yet) an owned instance is in
  range and at most its row owner's `crtInstance` (`owner` is set only by `handlePropose`, at
  `crtInstance + 1`, which `crtInstance` then becomes; `crtInstance` only grows) -/
  ownerCrt : ∀ x ps, S.owner x = some ps → x.q < nR ∧ (x.i : Int) ≤ zz ((S.rep x.q).crtInstance x.q)
  -- exec-M1 fields (p-exec)
  /-- (p-exec) `ExecedUpTo[q] ≥ -1` -/
  execLo : ExecLo S
  -- execution fields (p-modelexec)
  /-- (p-modelexec) the execution conjuncts (`InvExec`) -/
  exec : InvExec S

/-- The protocol invariant. -/
def Inv (S : Sys) : Prop := Inv0 S ∧ InvAux S

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
