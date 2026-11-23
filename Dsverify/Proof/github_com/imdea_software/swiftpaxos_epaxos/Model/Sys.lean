/-
The whole system as the pure model sees it (`Sys`) and its steps (`Step`): the five replicas'
`RState`s by replica id, the peer messages, the pending broadcasts, the client proposals, the
slots' owners, the executors' progress, the global per-key execution sequences, the fired
outputs, and the ghost history of events.

**Messages.** A handler's direct sends (its replies) go to its replica's *outbox* (`outbox fr to`,
in order) at the handler's ghost step; a broadcast is recorded as pending (`pending fr`, see
`Epaxos/Model/State.lean`) and each of its `r.alive(q)` reads is a step (`bcastStep`) that puts
the message into the outbox when the read is true. Each `SendMsg(to, ...)` call then moves the
head of the outbox to `sent fr to` (the `flush` step, taken inside `SendMsg`'s send update,
`ep_sendUpd`), so `sent fr to` is exactly the wire layer's list of protocol messages from `fr` to
`to` (`sentHalf`, `msgSent`: a position `n` names a message `(fr, to, n)`). It is what `SendMsg`
handed to a peer's writer, not necessarily what reached the stream (a break loses a suffix).
When the peer's writer is `nil`, `SendMsg` writes nothing and does not run the send update: the
head of the outbox is dropped instead (the `lose` step), so that the positions of `sent` stay
those of the stream (a writer installed later, by `serveConn`, starts an empty stream).
`msgs fr to = sent fr to ++ outbox fr to ++ intended fr to` (the pending broadcast's message, if
`to` is among its unread peers) is everything the replica's handlers decided to send, less the
dropped messages: what the invariant speaks of. `delivered` is the set of positions a handler has
consumed (each with the reader's one-shot delivery token): delivery is at most once and in any
order (the reader hands each message to the run loop from a goroutine of its own).

**Client proposals.** `ops` lists the client proposals in the order they reached a replica's
`ProposeChan` (`clientListener`'s `dchan.Write`), each with the replica; `proposeChan i` is the
channel's content, a bag (fix B5: the run loop knows only the bag's tokens; order never matters to
the protocol): `handlePropose` takes any non-empty sub-multiset of it (the `select`'s proposal and
the `len(ProposeChan)` that follow), `handleCommit`'s re-proposals are added. `owner x` is the
batch (`lb.clientProposals`) instance `x` was created with by its leader's `handlePropose`: slot
`(x, idx)`'s owner is its `idx`-th proposal.

**Recovery (fix B6, T2-2).** `instancesToRecover` is not modeled: the executor asks for the
recovery of instances `≤ crtInstance` of a row, and `crtInstance` only grows, so a request is any
in-range instance `≤` the replica's current `crtInstance` (`Step.recover`).

**Execution.** `execLog i` is replica `i`'s executed instances in execution order; `execCur i` the
rest of the component its executor is executing (in execution order: `sccSort`), `execIdx i` the
next command of its head; `gexec k` is the global sequence of key `k`: every slot (with its
command) *touching* key `k` (`touches`: on key `k`, or a SCAN whose range holds `k`) in the
order of its *first* execution at any replica (a SCAN's slot is in the sequence of every key it
reads, at the point it first executed); `fired cid` is the output the op of connection `cid`
linearized with (at its slot's first execution; the escrow's
`firedAuth` holds the same map). The executor's steps are per component start, per command and
per instance end (fix B8).

**Steps** (`Step S S'`): one per handler, broadcast read and executor action, each "replica `i`
applies `h` to its input: its `RState` becomes `h`'s result and its outputs are applied"
(`Sys.applyStep`): direct sends appended to the outbox `outbox i to` (and logged as
`Event.sent`), a broadcast made pending, re-proposals added to `proposeChan i`, ghost events to
`hist`; client replies have no `Sys` effect (the Iris layer sends them with the `fired` witness).
A handler step of replica `i` needs `i` idle (no pending broadcast, no component being executed):
the instance lock is held from the handler's start to its broadcast's end, and through a whole
executor pass.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.State

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

/-- A slot: an instance and a position in its command batch. -/
abbrev Slot := InstId × Nat

/-- The system. -/
structure Sys where
  /-- replica `i`'s protocol state (`i < 5`) -/
  rep : Nat → RState
  /-- the messages replica `fr` handed to `SendMsg(to, ...)`, in order -/
  sent : Nat → Nat → List Msg
  /-- the messages replica `fr`'s handlers decided to send to `to` and not yet handed to
  `SendMsg`, in order -/
  outbox : Nat → Nat → List Msg
  /-- replica `fr`'s pending broadcast -/
  pending : Nat → Option Bcast
  /-- the consumed message positions `(fr, to, n)` -/
  delivered : List (Nat × Nat × Nat)
  /-- the client proposals, with the replica whose `ProposeChan` they reached -/
  ops : List (Nat × Proposal)
  /-- each replica's `ProposeChan` (a bag) -/
  proposeChan : Nat → List Proposal
  /-- each instance's batch, as its leader's `handlePropose` created it -/
  owner : InstId → Option (List Proposal)
  /-- each replica's executed instances, in execution order -/
  execLog : Nat → List InstId
  /-- the rest of the component each executor is executing, in execution order -/
  execCur : Nat → List InstId
  /-- the next command of `execCur`'s head -/
  execIdx : Nat → Nat
  /-- each key's global execution sequence (the slots touching it, with their commands) -/
  gexec : w64 → List (Slot × WCmd)
  /-- the fired outputs, by connection id -/
  fired : w64 → Option (KvsOutput (List w8))
  /-- the ghost history: every event, with the replica, in order -/
  hist : List (Nat × Event)

/-- The start: every replica as `epaxos.New` builds it, nothing sent or proposed. -/
def Sys.init : Sys where
  rep := RState.init
  sent := fun _ _ => []
  outbox := fun _ _ => []
  pending := fun _ => none
  delivered := []
  ops := []
  proposeChan := fun _ => []
  owner := fun _ => none
  execLog := fun _ => []
  execCur := fun _ => []
  execIdx := fun _ => 0
  gexec := fun _ => []
  fired := fun _ => none
  hist := []

namespace Sys

/-- The pending broadcast's message to `to`, if `to` is among its unread peers. -/
def intended (S : Sys) (fr to : Nat) : List Msg :=
  match S.pending fr with
  | some b => if to ∈ b.peers then [b.m] else []
  | none => []

/-- Everything replica `fr`'s handlers decided to send to `to`. -/
def msgs (S : Sys) (fr to : Nat) : List Msg := S.sent fr to ++ S.outbox fr to ++ S.intended fr to

/-- Replica `i` holds no instance lock-long action in progress: no pending broadcast, no
component being executed. -/
def idle (S : Sys) (i : Nat) : Prop := S.pending i = none ∧ S.execCur i = []

/-- One output of replica `i` applied. -/
def emit (S : Sys) (i : Nat) (o : Out) : Sys :=
  match o with
  | .send to m =>
    { S with outbox := upd S.outbox i (upd (S.outbox i) to (S.outbox i to ++ [m])),
             hist := S.hist ++ [(i, .sent to m)] }
  | .bcast b => { S with pending := upd S.pending i b.norm }
  | .reply _ _ => S
  | .repropose p => { S with proposeChan := upd S.proposeChan i (S.proposeChan i ++ [p]) }
  | .ev e => { S with hist := S.hist ++ [(i, e)] }

/-- Replica `i`'s state becomes `σ'` and its outputs are applied in order. -/
def applyStep (S : Sys) (i : Nat) (r : RState × List Out) : Sys :=
  r.2.foldl (fun S o => S.emit i o) { S with rep := upd S.rep i r.1 }

/-- The command of a slot as replica `i` holds it. -/
def slotCmd (σ : RState) (s : Slot) : WCmd :=
  (((σ.inst s.1).bind (·.cmds)).getD []).getD s.2 default

/-- Command `c` touches key `k`: `k` is its key, or it is a SCAN and `k` is a key of its range
(every key its output may depend on or it writes, and a SCAN's own key even when its range wraps
and it reads nothing: an extra ordering only). -/
def touches (c : WCmd) (k : w64) : Prop := c.key = k ∨ (c.op = opSCAN ∧ k ∈ rangeKeys c)

instance (c : WCmd) (k : w64) : Decidable (touches c k) := by unfold touches; infer_instance

/-- The slots (with their commands) of the instances `xs`, in order, whose command is not NONE
and touches key `k`. -/
def slotsOn (σ : RState) (xs : List InstId) (k : w64) : List (Slot × WCmd) :=
  xs.flatMap (fun x =>
    let cmds := ((σ.inst x).bind (·.cmds)).getD []
    ((List.range cmds.length).map (fun idx => ((x, idx), cmds.getD idx default))).filter
      (fun e => e.2.op ≠ opNONE ∧ touches e.2 k))

/-- The value of a key after a sequence: the last PUT's value. -/
def lastPut (seq : List (Slot × WCmd)) : Option (List w8) :=
  seq.foldl (fun v e => if e.2.op = opPUT then some e.2.val else v) none

/-- The output of command `c` after the sequences `G` of the keys it touches: a GET's key's value,
a SCAN's present values of its range in key order, concatenated, `done` otherwise. -/
def outOf (G : w64 → List (Slot × WCmd)) (c : WCmd) : KvsOutput (List w8) :=
  if c.op = opGET then .got (lastPut (G c.key))
  else if c.op = opSCAN then .scanned (((rangeKeys c).filterMap (fun k => lastPut (G k))).flatten)
  else .done

/-- The part of a sequence before entry `e`. -/
def before (seq : List (Slot × WCmd)) (e : Slot × WCmd) : List (Slot × WCmd) :=
  seq.takeWhile (· ≠ e)

/-- The op of a slot: its owner's proposal at the slot's position. -/
def slotOp (S : Sys) (s : Slot) : Option Proposal := (S.owner s.1).bind (·[s.2]?)

/-- The slots of key `k` replica `i`'s executor has executed in the instance it is executing. -/
def curSlots (S : Sys) (i : Nat) (k : w64) : List (Slot × WCmd) :=
  match S.execCur i with
  | [] => []
  | x :: _ => (slotsOn (S.rep i) [x] k).filter (fun e => e.1.2 < S.execIdx i)

/-- Replica `i`'s executed sequence of key `k` (its log's, then the current instance's executed
commands). -/
def lexec (S : Sys) (i : Nat) (k : w64) : List (Slot × WCmd) :=
  slotsOn (S.rep i) (S.execLog i) k ++ S.curSlots i k

/-- The PUTs of a sequence (what a key's value depends on; GETs on one key commute, so replicas
may execute them in different orders). -/
def writes (seq : List (Slot × WCmd)) : List (Slot × WCmd) := seq.filter (fun e => e.2.op = opPUT)

/-- Slot `e` executed: if for the first time anywhere (not yet in its key's sequence), its op
fires with the output against the global sequences, and it is appended to the sequence of every
key it touches. -/
def fire (S : Sys) (e : Slot × WCmd) : Sys :=
  if e ∈ S.gexec e.2.key then S
  else
    let S' := match S.slotOp e.1 with
      | some p => { S with fired := upd S.fired p.cid (some (outOf S.gexec e.2)) }
      | none => S
    { S' with gexec := fun k => if touches e.2 k then S'.gexec k ++ [e] else S'.gexec k }

/-- The executor starts component `C` (`sccReady`, sorted: `sort.Sort(nodeArray(list))`). -/
def startSCC (S : Sys) (i : Nat) (C : List InstId) : Sys :=
  { S with execCur := upd S.execCur i (sccSort (S.rep i) C), execIdx := upd S.execIdx i 0 }

/-- The executor runs command `execIdx i` of instance `x` (record `w`, the head of `execCur i`):
its state and reply as `execCmdAt` computes them, the next command, and, if the slot is executed
for the first time anywhere (and not NONE), the slot appended to the global sequences of the keys
it touches and its op fired with the output against them (`fire`). -/
def execCmd (S : Sys) (i : Nat) (x : InstId) (w : InstRec) : Sys :=
  let idx := S.execIdx i
  let c := (w.cmds.getD []).getD idx default
  let S1 := S.applyStep i (execCmdAt (S.rep i) w idx)
  let S2 := { S1 with execIdx := upd S1.execIdx i (idx + 1) }
  if c.op = opNONE then S2 else S2.fire ((x, idx), c)

/-- The executor ends instance `x` (`w.Status = EXECUTED`): appended to the log. -/
def instDone (S : Sys) (i : Nat) (x : InstId) (rest : List InstId) : Sys :=
  { S with rep := upd S.rep i (execDone (S.rep i) x), execLog := upd S.execLog i (S.execLog i ++ [x]),
           execCur := upd S.execCur i rest, execIdx := upd S.execIdx i 0 }

/-- `handlePropose` at replica `i` on `batch` (a sub-multiset of its channel, removed from it); the
new instance (unless the row is full) is owned by the batch. -/
def propose (S : Sys) (i : Nat) (batch : List Proposal) : Sys :=
  let σ := S.rep i
  let x : InstId := ⟨i, toN (σ.crtInstance i + 1)⟩
  let S1 := { S with proposeChan := upd S.proposeChan i ((S.proposeChan i).diff batch) }
  let S2 := if rowFull σ then S1 else { S1 with owner := upd S1.owner x (some batch) }
  S2.applyStep i (hPropose σ batch)

/-- Delivery of message `(fr, i, n)` = `m` to replica `i`. -/
def deliver (S : Sys) (fr i n : Nat) (m : Msg) : Sys :=
  let S1 := { S with delivered := S.delivered ++ [(fr, i, n)] }
  S1.applyStep i (hMsg (S.rep i) m)

/-- Replica `i`'s pending broadcast `b` reads `alive` = `a` for its next peer: on `true`, the
message goes to that peer's outbox (logged as `Event.sent`) and `bcastPreAccept`'s
`lb.preAcceptsSent` is updated; the broadcast moves on (or is over). -/
def bcastStep (S : Sys) (i : Nat) (b : Bcast) (a : Bool) : Sys :=
  let S1 := { S with rep := upd S.rep i (bcastRep (S.rep i) b a), pending := upd S.pending i (b.next a) }
  match b.peers, a with
  | p :: _, true => S1.emit i (.send p b.m)
  | _, _ => S1

/-- A framework-side permutation: `UpdatePreferredPeerOrder`'s result for replica `i` (its first
`N - 1` entries are the other replicas). -/
def peerOrderOk (i : Nat) (o : List Nat) : Prop :=
  o.length = nR ∧ (o.take (nR - 1)).Perm ((List.range nR).filter (· ≠ i))

end Sys

/-- The steps. -/
inductive Step : Sys → Sys → Prop where
  /-- a client's `PROPOSE` reaches replica `i`'s `ProposeChan` (`clientListener`); its connection
  id is fresh -/
  | clientPropose (S : Sys) (i : Nat) (p : Proposal) :
      i < nR → p.cid ∉ S.ops.map (·.2.cid) →
      Step S { S with ops := S.ops ++ [(i, p)],
                      proposeChan := upd S.proposeChan i (S.proposeChan i ++ [p]) }
  /-- the run loop's `handlePropose` on a non-empty sub-multiset of the channel (one proposal if
  the row is full) -/
  | propose (S : Sys) (i : Nat) (batch : List Proposal) :
      i < nR → S.idle i → batch ≠ [] → batch.Subperm (S.proposeChan i) →
      (rowFull (S.rep i) = true → batch.length = 1) →
      Step S (S.propose i batch)
  /-- the run loop handles message `(fr, i, n)` (not yet delivered) -/
  | deliver (S : Sys) (fr i n : Nat) (m : Msg) :
      i < nR → fr < nR → S.idle i → (S.sent fr i)[n]? = some m → (fr, i, n) ∉ S.delivered →
      Step S (S.deliver fr i n m)
  /-- the run loop's `startRecoveryForInstance` on an executor's request: any instance in range,
  at most the replica's `crtInstance` of its row -/
  | recover (S : Sys) (i : Nat) (x : InstId) :
      i < nR → S.idle i → x.q < nR → (x.i : Int) ≤ sint.Z ((S.rep i).crtInstance x.q) →
      Step S (S.applyStep i (hRecover (S.rep i) x))
  /-- a pending broadcast's `r.alive(q)` read returned `a` -/
  | bcastStep (S : Sys) (i : Nat) (b : Bcast) (a : Bool) :
      i < nR → S.pending i = some b → b.peers ≠ [] →
      Step S (S.bcastStep i b a)
  /-- `BeTheLeader` (rpc goroutine, under the instance lock) -/
  | beTheLeader (S : Sys) (i : Nat) :
      i < nR → Step S { S with rep := upd S.rep i (hBeTheLeader (S.rep i)) }
  /-- `ComputeClosestPeers` sets the peer order (before the run loop handles anything) -/
  | peerOrder (S : Sys) (i : Nat) (o : List Nat) :
      i < nR → Sys.peerOrderOk i o →
      Step S { S with rep := upd S.rep i { S.rep i with peerOrder := o } }
  /-- `SendMsg` hands the head of replica `i`'s outbox to `to` to the wire -/
  | flush (S : Sys) (i to : Nat) (m : Msg) (rest : List Msg) :
      S.outbox i to = m :: rest →
      Step S { S with sent := upd S.sent i (upd (S.sent i) to (S.sent i to ++ [m])),
                      outbox := upd S.outbox i (upd (S.outbox i) to rest) }
  /-- `SendMsg` drops the head of replica `i`'s outbox to `to` (the peer's writer is `nil`) -/
  | lose (S : Sys) (i to : Nat) (m : Msg) (rest : List Msg) :
      S.outbox i to = m :: rest →
      Step S { S with outbox := upd S.outbox i (upd (S.outbox i) to rest) }
  /-- the executor starts a component (Tarjan popped it; sorted) -/
  | execSCC (S : Sys) (i : Nat) (C : List InstId) :
      i < nR → S.idle i → sccReady (S.rep i) C → Step S (S.startSCC i C)
  /-- the executor runs the next command of the instance it is executing -/
  | execCmd (S : Sys) (i : Nat) (x : InstId) (rest : List InstId) (w : InstRec) :
      i < nR → S.execCur i = x :: rest → (S.rep i).inst x = some w →
      S.execIdx i < (w.cmds.getD []).length →
      Step S (S.execCmd i x w)
  /-- the executor ends the instance it is executing (all its commands run) -/
  | instDone (S : Sys) (i : Nat) (x : InstId) (rest : List InstId) (w : InstRec) :
      i < nR → S.execCur i = x :: rest → (S.rep i).inst x = some w →
      S.execIdx i = (w.cmds.getD []).length →
      Step S (S.instDone i x rest)
  /-- the executor's scan moves `ExecedUpTo[q]` over an executed instance -/
  | execBump (S : Sys) (i q : Nat) :
      i < nR → q < nR →
      (S.rep i).executed ⟨q, toN ((S.rep i).execedUpTo q + 1)⟩ →
      Step S { S with rep := upd S.rep i (execBump (S.rep i) q) }

/-- Reachability from `S`. -/
inductive Reach : Sys → Sys → Prop where
  | refl (S : Sys) : Reach S S
  | step (S S' S'' : Sys) : Reach S S' → Step S' S'' → Reach S S''

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
