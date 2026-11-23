/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Inv.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The SwiftPaxos protocol's slot (HUBS.md) in full: its ghost names, the persistent facts its
messages carry, the wire protocols of the replicas' port, the master's and the replicas' rpc
method specs, the protocol invariant `sp.inv` and the nodes' shares, and the laws its clients
use (theorems, `sorry`: the Prove phase's).

## Ghost state (`Names`) and who holds it

Every ghost map below has its authority in `sp.inv` (allocated by `alloc` at the start); its
elements are persistent facts (but `node`, `tok`, `seqs`, see below), which messages carry:
* `cmds`: `x ↦ c`, command `x` is `c` (`cmdIs`): registered by its client when it invokes `x`
  (`client_invoke`, change log C12);
* `loc`: `(r, b, i) ↦ x`: replica `r`'s sequence in ballot `b` (`locAt`, `locLb`; the leader's
  is the ballot's order, `Model.lean`);
* `sync`: `b ↦ M`, ballot `b`'s `MSync` (`syncIs`);
* `acc`, `pre`, `com`: `r` accepted, pre-accepted (with dependencies `D`), committed `x` in `b`
  (`accepted`, `preacc`, `committed`);
* `path`: `(r, b, x) ↦ P`, the dependency path `r` sent with `x` in `b` (`pathIs`);
* `rep`: `(r, b) ↦ R`, `r`'s recovery report for ballot `b` (`reported`);
* `node`: `k ↦ st`, replica node `k`'s protocol state: half in `sp.inv`, half with the replica
  (`nodeSt`, from `replicaStart k`), so only the replica changes it;
* `hist` (change log C12): the client node's history of invocations and acceptances (mono-list
  of `Ev`): half in `sp.inv` (with the protocol state's snapshots, `HistOk`), half with the
  client node's linearization lock (`histOwn`, from `clientsStart`);
* `dec` (change log C12): `x ↦ v`, `x` was possibly chosen with leader result `v` (`doneRes`,
  persistent elements);
* `own` (change log C12): the client node's claim token of `linOwn`'s other half (`lin_claim`);
* `seqs`: client `cl`'s next sequence number: half in `sp.inv`, half with the client
  (`clientSeq`, from `clientsStart`);
* `conn`: `cid ↦ kind`: what a connection to a replica's port carries (a peer's or client `cl`'s
  messages: `connKind`), registered by its dialer with the `Dial`'s fresh token (`conn_register`),
  which `sp.inv` keeps.

`sp.inv γ γc γm γl` (namespace `spN`) holds the authorities, the protocol state `S` they
represent (`Model.lean`'s `PState`), and: before the configuration and the membership are fixed,
nothing happened; after, `PInv S N fr` (`Model.lean`) with `N`, `fr` the configuration's and the
replicas' states those of their nodes (by the membership), with the client node's history `sh`
(`HistOk`: each event with its snapshot of the protocol state) and the decided results (`dec`);
`lin`'s other half (`γl`) until the client node claims it (`lin_claim`) for its linearization
lock. **Change log C12** (decisions D12, D13; notes/prophecy-client.md): the linearization is
the client node's (a node-wide prophecy, Proof/client/LinHelp.lean); `sp.inv` holds no atomic
update any more (`G`, the slots and the collection tokens are gone); the client's laws are
`client_invoke` (an invocation, with the registration) and `client_accept` (an acceptance), each
giving the linearizability of the history so far (`sp.lin_now`).

## The wire protocols

A stream to a replica's port (`inP`) is empty, or (`connKind`) a client's: frames of its
proposals; or a peer's: `helloBytes id`, then frames of peer messages. A replica's stream back
(`outQ`) is frames of messages for the connection's kind: to a client `cl`, `MReply`,
`MFastAckClient`, `MLightSlowAck` of `cl`'s commands; to a peer, the peer messages. Each complete
message carries its persistent witness (`msgOk`); a stream may be cut short (a prefix).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.LinWitness
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Hash
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.WireWf
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.L2Words
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.LinCut
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetRpc

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

/-- The protocol's invariant namespace (disjoint from `clientN`). -/
def spN : Namespace := ndot nroot "swiftpaxos.sp"

/-- What a connection to a replica's port carries, fixed by its dialer. -/
inductive ConnKind where
  | peer
  | client (cl : w32)
  deriving DecidableEq

instance ConnKind.countable : Pos.Countable ConnKind :=
  .ofInjective (fun k => Pos.Countable.encode (match k with
      | .peer => (false, (0 : w32)) | .client c => (true, c)))
    (by rintro (_ | a) (_ | b) h <;> have h := Pos.encode_inj h <;> simp_all)

/-- The protocol's ghost names (see the file header). -/
structure Names where
  cmds : GName
  loc : GName
  sync : GName
  acc : GName
  pre : GName
  com : GName
  path : GName
  rep : GName
  node : GName
  hist : GName
  dec : GName
  own : GName
  seqs : GName
  conn : GName
  /-- change log C22 (M3, decision D19): the replicas' numbering of their proposals -/
  num : GName
  /-- stage 2, L2 (notes/l2-design.md §5): the registration tokens (a ghost map `PNode ↦ ()`:
  `sp.inv`'s half of each node's element, the node's share's other half `predTok`, given to
  `sp.inv` when the node registers) -/
  preg : GName
  /-- L2: the registered nodes (a ghost map `PNode ↦ ()`, persistent elements `predReg`, made
  only by the registration) -/
  regd : GName
  /-- L2: each registered node's future words (a ghost map `PNode ↦ List w64`: half in
  `sp.inv`, half in the node's ghost lock) -/
  pred : GName
  /-- L2: the pending operations' slots (a ghost map `CmdId ↦ Cmd × GName`: the client's
  element is its ticket `pend`, the name its continuation's saved predicate) -/
  slot : GName

/-- A predicted node (L2): client `c` (client node `c`, node `1 + c`) or replica node `k`
(server node `k + 2`). -/
inductive PNode where
  | cl (c : Nat)
  | rep (k : Nat)
  deriving DecidableEq

instance PNode.countable : Pos.Countable PNode :=
  .ofInjective (fun n => Pos.Countable.encode (match n with
      | .cl c => (true, c)
      | .rep k => (false, k)))
    (by rintro (a | a) (b | b) h <;> have h := Pos.encode_inj h <;> simp_all)

/-- The client node's history (change log C12) as a ghost mono-list. -/
instance Ev.countable : Pos.Countable Ev :=
  .ofInjective (fun e => Pos.Countable.encode (match e with
      | .inv x c => (true, x, c, ([] : List w8))
      | .resp x v => (false, x, (default : Cmd), v)))
    (by
      rintro (⟨x, c⟩ | ⟨x, v⟩) (⟨x', c'⟩ | ⟨x', v'⟩) h <;> have h := Pos.encode_inj h <;>
        simp_all)

/-! ## The abstract state's change (`lin`) -/

/-- A command's effect on the abstract state and its result: a put sets its key, a get
returns its key's value (empty if none). -/
def lin.apply (c : Cmd) (σ : (kv GoString GoString).State) :
    (kv GoString GoString).State × List w8 :=
  if c.isPut then ((fun k => if k = lin.keyName c.key then some c.val else σ k), [])
  else (σ, (σ (lin.keyName c.key)).getD [])

/-- The puts of `G` as the model's pairs (the other half of `lin`). -/
def linPuts (G : Seq) : List (GoString × GoString) :=
  (G.filter (fun p => p.2.isPut)).map (fun p => (lin.keyName p.2.key, p.2.val))

section defs
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS] [sp.GobFmt]

/-! ## Persistent facts -/

/-- **L2: node `n`'s prediction is registered** (persistent; notes/l2-design.md §5): its
node's ghost was claimed and its predicted future is in `sp.inv`. -/
def predReg (γ : Names) (n : PNode) : IProp netDistGF :=
  ghostMapElem γ.regd n .discard ()

/-- **L2: node `n`'s right to register its prediction** (once; in its share). -/
def predTok (γ : Names) (n : PNode) : IProp netDistGF :=
  ghostMapElem γ.preg n (DFrac.own (1 : Qp).half) ()

/-- Every predicted node of the deployment: the six clients, the five replica nodes. -/
def allPNodes : List PNode := (List.range 6).map PNode.cl ++ (List.range 5).map PNode.rep

/-- **L2: every predicted node of the configuration registered its prediction**: the six
clients and the configuration's `N` replicas (what the orchestrator gathers from the
configuration acknowledgments before any client operation; `own_state` carries it). -/
def allPredsReg (γ : Names) (γc : GName) : IProp netDistGF :=
  iprop(∃ c : Conf, confIs γc c ∗ ([∗list] k ∈ List.range c.n, predReg γ (PNode.rep k)) ∗
    [∗list] cl ∈ List.range 6, predReg γ (PNode.cl cl))

/-- Command `x` is `c` (registered by its client). -/
def cmdIs (γ : Names) (x : CmdId) (c : Cmd) : IProp netDistGF :=
  ghostMapElem γ.cmds x .discard c
/-- `x` is at index `i` of replica `r`'s sequence in ballot `b`. -/
def locAt (γ : Names) (r b i : Nat) (x : CmdId) : IProp netDistGF :=
  ghostMapElem γ.loc (r, b, i) .discard x
/-- Replica `r`'s sequence in ballot `b` starts with `l`, whose commands are `s`. -/
def locLb (γ : Names) (r b : Nat) (s : Seq) : IProp netDistGF :=
  iprop([∗list] i ↦ p ∈ s, locAt γ r b i p.1 ∗ cmdIs γ p.1 p.2)
/-- Ballot `b`'s `MSync` is `M`. -/
def syncIs (γ : Names) (b : Nat) (M : SyncMsg) : IProp netDistGF :=
  ghostMapElem γ.sync b .discard M
/-- Replica `r` accepted `x` in `b`. -/
def accepted (γ : Names) (r b : Nat) (x : CmdId) : IProp netDistGF :=
  ghostMapElem γ.acc (r, b, x) .discard ()
/-- Replica `r` pre-accepted `x` in `b` with dependencies `D`. -/
def preacc (γ : Names) (r b : Nat) (x : CmdId) (D : List CmdId) : IProp netDistGF :=
  ghostMapElem γ.pre (r, b, x) .discard D
/-- Replica `r`'s dependency path for `x` in `b` is `P` (the ids whose hash chain is the path
hash it sent with `x`). -/
def pathIs (γ : Names) (r b : Nat) (x : CmdId) (P : List CmdId) : IProp netDistGF :=
  ghostMapElem γ.path (r, b, x) .discard P
/-- Replica `r` committed `x` in `b`. -/
def committed (γ : Names) (r b : Nat) (x : CmdId) : IProp netDistGF :=
  ghostMapElem γ.com (r, b, x) .discard ()
/-- Replica `r`'s recovery report for ballot `b` is `R`. -/
def reported (γ : Names) (r b : Nat) (R : Report) : IProp netDistGF :=
  ghostMapElem γ.rep (r, b) .discard R
/-- `x` is decided with result `o`: possibly chosen, with its leader's result `o` (change log
C12). -/
def doneRes (γ : Names) (x : CmdId) (o : List w8) : IProp netDistGF :=
  ghostMapElem γ.dec x .discard o
/-- Connection `cid` to a replica's port carries `k`'s messages. -/
def connKind (γ : Names) (cid : Nat) (k : ConnKind) : IProp netDistGF :=
  ghostMapElem γ.conn cid .discard k

/-- Change log C22 (M3, decision D19): replica `r` numbered `x` with `s` when it handled it in
ballot `b` (its run loop's `seqnum` if it leads `b`, else -1, as `handleProposal`'s `seqnum`).
The leader's numbers are non-negative and follow its sequence's order (`numOk`). -/
def numIs (γ : Names) (r b : Nat) (x : CmdId) (s : w64) : IProp netDistGF :=
  ghostMapElem γ.num (r, some (b, x)) .discard s

/-! ## Exclusive resources -/

/-- Change log C22: replica node `k`'s next number is `n` (its run loop's `seqnum`; from
`replicaStart k`). -/
def numHi (γ : Names) (k : Nat) (n : w64) : IProp netDistGF :=
  ghostMapElem γ.num (k, (none : Option (Nat × CmdId))) (DFrac.own 1) n

/-- Replica node `k`'s protocol state is `st` (fraction `q`: the replica's half, `sp.inv`'s). -/
def nodeSt (γ : Names) (k : Nat) (q : Qp) (st : RState) : IProp netDistGF :=
  ghostMapElem γ.node k (DFrac.own q) st
/-- The client node's half of the history (change log C12; its linearization lock's). -/
def histOwn (γ : Names) (H : Hist) : IProp netDistGF :=
  monoListAuthOwn γ.hist (1 : Qp).half H
/-- Client `cl`'s next sequence number is `s` (the client's half). -/
def clientSeq (γ : Names) (cl : w32) (s : Nat) : IProp netDistGF :=
  ghostMapElem γ.seqs cl (DFrac.own (1 : Qp).half) s

/-! ## The configuration as the protocol sees it -/

/-- The configuration has `N` replicas and fast reads `fr`, the membership is `l`, and every
member is a configured replica node (`nodeOf l r = some k → k < N`: the master registers only
`replicaAddrs[k]` with `k < N`; REQUEST R-E2, D90) (persistent). -/
def cfg (γc γm : GName) (N : Nat) (fr : Bool) (l : List GoString) : IProp netDistGF :=
  iprop(∃ c : Conf, (confIs γc c ∗ ⌜∀ r k, nodeOf l r = some k → k < N⌝) ∗ memIs γm l ∗
    ⌜c.n = N ∧ fr = (c.fastRead == 1) ∧ l.length = N⌝)

/-! ## The messages' witnesses -/

/-- Ballot `b` (a wire `int32`) as a `Nat`. -/
def bal (b : w32) : Nat := b.toInt.toNat
/-- A replica id on the wire as a `Nat`. -/
def rid (r : w32) : Nat := r.toInt.toNat

/-- A message's replica id and ballot are non-negative (the code's ids and ballots; see
notes/interface-findings.md, F1, on the ballots' overflow): the wire values are the `Nat`s the
witnesses speak of, so two distinct wire ids are two replicas. -/
def wireOk (r b : w32) : Prop := 0 ≤ r.toInt ∧ 0 ≤ b.toInt

/-- Decision D23 (SWB-F5): an ack's `Seqnum` `s` against its sender's number of `x`: equal, or
the sender numbered `x` with -1 (a follower: its ack's `Seqnum` is unconstrained; the leader's
numbers are non-negative, `numOk`, so the leader's ack carries its number). -/
def numAck (γ : Names) (r b : Nat) (x : CmdId) (s : w64) : IProp netDistGF :=
  iprop(∃ s', numIs γ r b x s' ∗ ⌜s' = s ∨ s' = W64 (-1)⌝)

/-- Round 53 (D73 (1), 52-1): replica `r`'s sequence of `b` has `x`, with the dependencies `D`
there (`depsIn`): the pre-accepting sender's own `locLb` (`handlePropose`'s proposal facts), so
that a follower adopting the ballot's leader's dependencies keeps the leader's prefix. -/
def locDeps (γ : Names) (r b : Nat) (x : CmdId) (D : List CmdId) : IProp netDistGF :=
  iprop(∃ s : Seq, locLb γ r b s ∗ ⌜x ∈ s.map Prod.fst ∧ D.Perm (depsIn s x)⌝)

/-- An `MOptAcks` entry's witness: `Dep = [id]` is a slow ack (`NilDepOfCmdId`), else a fast
ack (with its sender's number of the command: change log C22). -/
def ackOk (γ : Names) (r b : Nat) (a : Ack) : IProp netDistGF :=
  if a.dep = [a.id] then accepted γ r b a.id
  else iprop(preacc γ r b a.id a.dep ∗
    ∃ P, pathIs γ r b a.id P ∗ pathHashes [P] a.cs ∗ numAck γ r b a.id a.seqnum ∗
      locDeps γ r b a.id a.dep)

/-- A fast ack's witness: its sender pre-accepted the command with these dependencies; its
checksum is the hash of its dependency path; its `Seqnum` is its sender's number of the command
(change log C22, M3: the leader's numbering, `numIs`); round 53 (52-1): its sender's sequence
with the command and these dependencies (`locDeps`). -/
def fastAckOk (γ : Names) (f : FastAck) : IProp netDistGF :=
  iprop(⌜wireOk f.rep f.bal⌝ ∗ preacc γ (rid f.rep) (bal f.bal) f.id f.dep ∗
    ∃ P, pathIs γ (rid f.rep) (bal f.bal) f.id P ∗ pathHashes [P] f.cs ∗
      numAck γ (rid f.rep) (bal f.bal) f.id f.seqnum ∗
      locDeps γ (rid f.rep) (bal f.bal) f.id f.dep)

/-- The wire `MSync` `m` lists the contents of `M` (its maps' entries in some order, every
phase `COMMIT`; an empty dependency list may be nil after gob). -/
def syncWireOk (m : SyncWire) (M : SyncMsg) : Prop :=
  (∃ ps, m.phases = some ps ∧ ps.Perm (M.map (fun p => (p.1, phCOMMIT)))) ∧
  (∃ cs, m.cmds = some cs ∧ cs.Perm (M.map (fun p => (p.1, p.2.1)))) ∧
  (∃ ds, m.deps = some ds ∧ ds.Perm (M.map (fun p => (p.1, p.2.2))))

/-- D33: ballot `b`'s leader `L` executed (`deliver`ed) `x` in `b`, hence its whole dependency
closure (the model's `PState.lexec`): a set `E ∋ x` each of whose commands is in `b`'s `MSync`
(`handleSync` executed it) or pre-accepted by `L` with dependencies in `E` (`deliver` checks,
under `execL`, that each of the descriptor's `dep` was delivered; at the leader `dep` is its
pre-acceptance's). Persistent. -/
def execW (γ : Names) (L b : Nat) (x : CmdId) : IProp netDistGF :=
  iprop(∃ E : List CmdId, ⌜x ∈ E⌝ ∗ [∗list] y ∈ E,
    (∃ M, syncIs γ b M ∗ ⌜y ∈ syncOrder M⌝) ∨ (∃ D, preacc γ L b y D ∗ ⌜∀ d ∈ D, d ∈ E⌝))

instance execW_persistent (γ : Names) (L b : Nat) (x : CmdId) : Persistent (execW γ L b x) := by
  unfold execW syncIs preacc; infer_instance

/-- The persistent witness of a message (see the file header and `Model.lean`). -/
def msgOk (γ : Names) (γc γm : GName) : Msg → IProp netDistGF
  | .propose seq cl c _ => cmdIs γ ⟨cl, seq⟩ c
  | .beacon _ => iprop(True)
  | .beaconReply _ => iprop(True)
  | .fastAck f => fastAckOk γ f
  | .fastAckClient r b x cs => iprop(∃ (D P : List CmdId) (c : Cmd),
      ⌜wireOk r b⌝ ∗ preacc γ (rid r) (bal b) x D ∗ pathIs γ (rid r) (bal b) x P ∗
      checksum [P] D cs ∗ cmdIs γ x c ∗
      ∃ N fr l, cfg γc γm N fr l ∗ ⌜rid r = leaderOf N (bal b) → fr = true ∧ c.isGet⌝)
  -- change log C16: a light slow ack's sender is not the ballot's leader (the leader never
  -- sends one; the receiver adds an ack of the leader as the sets' leader message)
  | .lightSlowAck s => iprop(⌜wireOk s.rep s.bal⌝ ∗ accepted γ (rid s.rep) (bal s.bal) s.id ∗
      ∃ N fr l, cfg γc γm N fr l ∗ ⌜rid s.rep ≠ leaderOf N (bal s.bal)⌝)
  | .acks fs ss => iprop(([∗list] f ∈ fs, fastAckOk γ f) ∗
      [∗list] s ∈ ss, ⌜wireOk s.rep s.bal⌝ ∗ accepted γ (rid s.rep) (bal s.bal) s.id ∗
        ∃ N fr l, cfg γc γm N fr l ∗ ⌜rid s.rep ≠ leaderOf N (bal s.bal)⌝)
  -- change log C16: an `MOptAcks` with a slow ack (`Dep = [id]`) is not from the leader
  | .optAcks r b al => iprop(⌜wireOk r b⌝ ∗ ([∗list] a ∈ al, ackOk γ (rid r) (bal b) a) ∗
      (⌜∀ a ∈ al, a.dep ≠ [a.id]⌝ ∨ ∃ N fr l, cfg γc γm N fr l ∗ ⌜rid r ≠ leaderOf N (bal b)⌝))
  | .reply r b x cs v => iprop(∃ (N : Nat) (fr : Bool) (l : List GoString) (s : Seq)
        (Ps : List (List CmdId)) (c : Cmd),
      cfg γc γm N fr l ∗ locLb γ (rid r) (bal b) s ∗ checksum Ps (depsIn s x) cs ∗
      ⌜wireOk r b ∧ rid r = leaderOf N (bal b) ∧ cmdIn s x = some c ∧ v = resultIn s x⌝ ∗
      -- the leader's path for a proposal it handled; none for an `MSync`'s command
      (⌜Ps = []⌝ ∨ ∃ P, ⌜Ps = [P]⌝ ∗ pathIs γ (rid r) (bal b) x P) ∗
      -- D33: the leader executed `x` (its reply goroutine sends what `deliver` queued)
      execW γ (rid r) (bal b) x)
  -- D56 N1-b: a replica sends its own `Id` (`0 ≤ r < N`)
  | .newLeader r _ => iprop(∃ N fr l, cfg γc γm N fr l ∗ ⌜0 ≤ r.toInt ∧ rid r < N⌝)
  | .newLeaderAckN r b c es => iprop(⌜wireOk r b ∧ 0 ≤ c.toInt⌝ ∗
      reported γ (rid r) (bal b) ⟨bal c, es⟩ ∗ ∃ N fr l, cfg γc γm N fr l ∗ ⌜rid r < N⌝)
  -- round 54 (D74 (2), 53-4): with the sender's (the ballot's leader's) `locLb` of the
  -- `MSync`'s sequence, so that a follower's sync entry keeps the leader's prefix
  | .sync m _ => iprop(∃ (M : SyncMsg) (N : Nat) (fr : Bool) (l : List GoString),
      syncIs γ (bal m.bal) M ∗ (cfg γc γm N fr l ∗ locLb γ (rid m.rep) (bal m.bal) (syncSeq M)) ∗
      ⌜wireOk m.rep m.bal ∧ syncWireOk m M ∧ rid m.rep = leaderOf N (bal m.bal)⌝)

/-- The messages a client writes: its proposals. -/
def Msg.isProposeOf (cl : w32) : Msg → Prop
  | .propose _ cl' _ _ => cl' = cl
  | _ => False

/-- The messages a replica writes to client `cl`: replies and acks of `cl`'s commands. -/
def Msg.isToClient (cl : w32) : Msg → Prop
  | .reply _ _ x _ _ => x.cl = cl
  | .fastAckClient _ _ x _ => x.cl = cl
  | .lightSlowAck s => s.id.cl = cl
  | _ => False

/-- The messages a replica writes to a peer. -/
def Msg.isPeer : Msg → Prop
  | .beacon _ | .beaconReply _ | .fastAck _ | .lightSlowAck _ | .acks _ _ | .optAcks _ _ _
  | .newLeader _ _ | .newLeaderAckN _ _ _ _ | .sync _ _ => True
  | _ => False

/-- A stream of the messages `ms` (cut short anywhere), each well formed (`Msg.wf`,
Spec/swift/WireWf.lean) with its witness. (change log C9: `Msg.wf`) -/
def framesProto (γ : Names) (γc γm : GName) (head : List w8) (ok : Msg → Prop)
    (bs : List w8) : IProp netDistGF :=
  iprop(∃ ms : List Msg, ⌜bs <+: head ++ framesOf ms ∧ ∀ m ∈ ms, ok m ∧ Msg.wf m⌝ ∗
    [∗list] m ∈ ms, msgOk γ γc γm m)

/-! ## The wire protocols (the hubs' `protoP`, `protoQ` of the replicas' ports) -/

/-- What a dialer of a replica's port writes: nothing yet, or, for the connection's registered
kind, a client's proposals or a peer's `helloBytes id` and peer messages. -/
@[no_expose] def inP (γ : Names) (γc γm : GName) : Proto netDistGF := fun cid bs =>
  iprop(⌜bs = []⌝ ∨ ∃ k, connKind γ cid k ∗ match k with
    | .client cl => framesProto γ γc γm [] (Msg.isProposeOf cl) bs
    | .peer => ∃ id : w32, framesProto γ γc γm (helloBytes id) Msg.isPeer bs)

/-- What a replica writes back on an accepted connection: for the connection's kind, client
messages of its commands or peer messages. -/
@[no_expose] def outQ (γ : Names) (γc γm : GName) : Proto netDistGF := fun cid bs =>
  iprop(⌜bs = []⌝ ∨ ∃ k, connKind γ cid k ∗ match k with
    | .client cl => framesProto γ γc γm [] (Msg.isToClient cl) bs
    | .peer => framesProto γ γc γm [] Msg.isPeer bs)

/-! ## The rpc services (over the codec's encodings, `KitVal.encode`) -/

/-- `"ip:port"` (`fmt.Sprintf("%s:%d", ...)`). -/
def addrPort (ip : GoString) (port : w64) : GoString :=
  ip ++ [W8 58] ++ (Nat.toDigits 10 port.toNat).map (fun ch => W8 ch.toNat)

/-- The master's methods (`master.go`):
* `Register(addr, port)`, from a replica node `k` of the configuration (its address
  `replicaAddrs[k]`, `k < N`: the adapter registers only when `id - 2 < N`; another address
  could be the `N + 1`-th distinct one, which the master's `nodeList[0 : nlen+1]` cannot take):
  `Ready` only once the membership is fixed, then the membership (with the configuration's `N`)
  and the caller's id, the index of its address;
* `GetReplicaList`: the membership, `Ready`, an alive flag per replica (`Ready` is true because
  the method blocks until `finishInit`, which `run` sets once the membership is full);
* `GetLeader`: some id.
Every method answers without error; another method is not called (`False`). -/
@[no_expose] def masterSpec (γc γm : GName) : net.rpc.MethodSpec netDistGF := fun m args Φ =>
  if m = go!"Register" then
    iprop(∃ (ip : GoString) (port : w64) (c : Conf) (k : Nat),
      ⌜args = (KitVal.registerArgs ip port).encode ∧
        replicaAddrs[k]? = some (addrPort ip port) ∧ k < c.n⌝ ∗ confIs γc c ∗
      ∀ (id : w64) (nodes : List GoString) (ready isL : Bool),
        (if ready then iprop(∃ fr, cfg γc γm nodes.length fr nodes ∗
            ⌜nodes[id.toNat]? = some (addrPort ip port)⌝) else iprop(True)) -∗
        Φ (KitVal.registerReply id nodes ready isL).encode [])
  else if m = go!"GetReplicaList" then
    iprop(⌜args = KitVal.getReplicaListArgs.encode⌝ ∗
      ∀ (nodes : List GoString) (alive : List Bool),
        (∃ fr, cfg γc γm nodes.length fr nodes) -∗ ⌜alive.length = nodes.length⌝ -∗
        Φ (KitVal.getReplicaListReply nodes alive true).encode [])
  else if m = go!"GetLeader" then
    iprop(⌜args = KitVal.getLeaderArgs.encode⌝ ∗
      ∀ id : w64, Φ (KitVal.getLeaderReply id).encode [])
  else iprop(False)

/-- `BeTheLeaderReply`'s fields as the replica sends them (0 sent as -2, gob's zero), so that
the master's `leader[...]` indexes stay in range: `Leader` -2 or a replica id from 1,
`NextLeader` -2, -1 (no planned ballot) or an id from 1. -/
def btlOk (N : Nat) (ld nl : w32) : Prop :=
  (ld = -2 ∨ (1 ≤ ld.toInt ∧ ld.toInt < N)) ∧ (nl = -2 ∨ nl = -1 ∨ (1 ≤ nl.toInt ∧ nl.toInt < N))

/-- A replica's methods: `BeTheLeader` (start a recovery, if the replica executed something)
and `Ping`, with no precondition; another method is not called. -/
@[no_expose] def replicaRpcSpec (γc γm : GName) : net.rpc.MethodSpec netDistGF := fun m args Φ =>
  if m = go!"BeTheLeader" then
    iprop(⌜args = KitVal.beTheLeaderArgs.encode⌝ ∗
      ∀ (ld nl : w32), (∃ N fr l, cfg γc γm N fr l ∗ ⌜btlOk N ld nl⌝) -∗
        Φ (KitVal.beTheLeaderReply ld nl).encode [])
  else if m = go!"Ping" then
    iprop(∃ a : w8, ⌜args = (KitVal.pingArgs a).encode⌝ ∗ Φ KitVal.pingReply.encode [])
  else iprop(False)

/-! ## The invariant -/

/-- A command's client's atomic update, at `sp.inv`'s outer mask: the abstract state changes as
the command does (`lin.apply`), the continuation gets its result. -/
def cmdAU (γl : GName) (c : Cmd) (Ψ : List w8 → IProp netDistGF) : IProp netDistGF :=
  iprop(AU <{ ∃∃ σ, linOwn γl σ }> @ ⊤ \ ↑spN, ∅
    <{ linOwn γl (lin.apply c σ).1, COMM Ψ (lin.apply c σ).2 }>)

/-- An operation's slot (L2; stage 1's, Spec/client/Ghost.lean): `cg` is its command and the
name of its client's saved continuation; before it is committed (in `G`), its client's update;
after, the continuation applied to its result in `G`. -/
def slotL (γl : GName) (G : Seq) (x : CmdId) (cg : Cmd × GName) : IProp netDistGF :=
  iprop(∃ Ψ : List w8 → IProp netDistGF, savedPredOwn cg.2 .discard Ψ ∗
    ((⌜x ∉ G.map Prod.fst⌝ ∗ cmdAU γl cg.1 Ψ) ∨ (⌜x ∈ G.map Prod.fst⌝ ∗ Ψ (resultIn G x))))

/-- The ghost maps represent the protocol state `S`. -/
structure Repr (S : PState) (mC : GMap CmdId Cmd) (mL : GMap (Nat × Nat × Nat) CmdId)
    (mS : GMap Nat SyncMsg) (mA : GMap (Nat × Nat × CmdId) Unit)
    (mP : GMap (Nat × Nat × CmdId) (List CmdId)) (mCo : GMap (Nat × Nat × CmdId) Unit)
    (mR : GMap (Nat × Nat) Report) (mPa : GMap (Nat × Nat × CmdId) (List CmdId)) : Prop where
  cmds : ∀ x, mC.lookup x = S.cmds x
  loc : ∀ r b i, mL.lookup (r, b, i) = (S.loc r b)[i]?
  sync : ∀ b, mS.lookup b = S.sync b
  acc : ∀ r b x, (mA.lookup (r, b, x)).isSome ↔ S.acc r b x
  pre : ∀ r b x, mP.lookup (r, b, x) = S.pre r b x
  path : ∀ r b x, mPa.lookup (r, b, x) = S.path r b x
  com : ∀ r b x, (mCo.lookup (r, b, x)).isSome ↔ S.com r b x
  rep : ∀ r b, mR.lookup (r, b) = S.rep r b

/-- A ballot's `MSync` is in its leader's rows (the leader computed it and set its sequence of
the ballot: `PState.computeSync`; rows only grow), so a leader without a row for `b` knows `b`
has no `MSync` yet (`PInv_computeSync`'s premise). An invariant of `sp.inv`'s body beside
`PInv` (the swift group's: notes/prove-swift.md §8). -/
def PState.syncRows (S : PState) (N : Nat) : Prop :=
  ∀ b M, S.sync b = some M → ∃ l, (b, l) ∈ (S.rs (leaderOf N b)).locR

/-- Nothing happened yet (before the configuration and the membership are fixed); every replica
at its initial state (L2: the first replica step keeps the state, `sp.inv`'s L2 part included). -/
def PState.empty (S : PState) : Prop :=
  (∀ r b, S.loc r b = []) ∧ (∀ b, S.sync b = none) ∧ (∀ r b x, ¬ S.acc r b x) ∧
  (∀ r b x, S.pre r b x = none) ∧ (∀ r b x, S.path r b x = none) ∧ (∀ r b x, ¬ S.com r b x) ∧ (∀ r b, S.rep r b = none) ∧
  S.G = [] ∧ ∀ r, S.rs r = RState.init

/-- The decided results (change log C12): each possibly chosen with its leader's result. -/
def decOk (N : Nat) (S : PState) (mD : GMap CmdId (List w8)) : Prop :=
  ∀ x v, mD.lookup x = some v → ∃ b, S.possiblyChosen N b x ∧ resultIn (S.ordSeq N b) x = v

/-- Change log C22 (M3): the numbering `mNu` (keys `(r, some (b, x))`: replica `r` numbered `x`
in `b`; `(k, none)`: node `k`'s next number) against the sequences `loc`: a numbered command is
in its replica's sequence; a ballot's leader's numbers are non-negative, below its node's next
number, and follow its sequence's order. -/
def numOk (N : Nat) (l : List GoString) (loc : Nat → Nat → List CmdId)
    (mNu : GMap (Nat × Option (Nat × CmdId)) w64) : Prop :=
  ∀ r b x s, mNu.lookup (r, some (b, x)) = some s → x ∈ loc r b ∧
    (r = leaderOf N b → 0 ≤ sint.Z s ∧
      (∀ k, nodeOf l r = some k → ∃ n, mNu.lookup (k, none) = some n ∧ sint.Z s < sint.Z n) ∧
      ∀ y s', mNu.lookup (r, some (b, y)) = some s' →
        ((loc r b).idxOf x ≤ (loc r b).idxOf y ↔ sint.Z s ≤ sint.Z s'))

/-- `f 0 + … + f (n - 1)`. -/
def locSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => locSum f n + f n

/-- Decision D22 (2), the numbering's count: node `k`'s next number is at most the number of
commands in its replica's sequences of the ballots below `2 ^ 31` (the leader numbers each
command of its sequence once, in a ballot of an `int32`). With D13's bound on a sequence's
length (`loc_bound`) it keeps `seqnum` below `2 ^ 62`. -/
def numCnt (l : List GoString) (loc : Nat → Nat → List CmdId)
    (mNu : GMap (Nat × Option (Nat × CmdId)) w64) : Prop :=
  ∀ r k n, nodeOf l r = some k → mNu.lookup (k, none) = some n →
    sint.Z n ≤ locSum (fun b => (loc r b).length) (2 ^ 31)

/-- Change log C22 (M3): `sp.inv`'s part of the numbering (its authority; nothing numbered before
the configuration, every next number 0; then `numOk` and the count `numCnt`, D22 (2)). -/
def numInv (γ : Names) (γc γm : GName) (loc : Nat → Nat → List CmdId) : IProp netDistGF :=
  iprop(∃ mNu : GMap (Nat × Option (Nat × CmdId)) w64, ghostMapAuth γ.num 1 mNu ∗
    (⌜(∀ r b x, mNu.lookup (r, some (b, x)) = none) ∧
        ∀ k n, mNu.lookup (k, none) = some n → sint.Z n ≤ 0⌝ ∨
      ∃ (N : Nat) (fr : Bool) (l : List GoString), cfg γc γm N fr l ∗
        ⌜numOk N l loc mNu ∧ numCnt l loc mNu⌝))

/-! ## L2: the predictions, the committed prefix, the pending slots (notes/prove-s2-e.md) -/

/-- The cut's nodes in a configuration with `N` replicas (D's `Nd`). -/
def l2Nodes (N : Nat) : List Nd := (List.range 6).map Nd.cl ++ (List.range N).map Nd.rep

/-- The predicted nodes a configuration with `N` replicas needs registered (`allPredsReg`'s). -/
def cfgPNodes (N : Nat) : List PNode := (List.range 6).map PNode.cl ++ (List.range N).map PNode.rep

/-- The predictions of the registered nodes' future words `mW` in a configuration with `N`
replicas and the membership `l` (replica `r` is replica node `nodeOf l r`); nothing for a node
outside the configuration. -/
def predsOf (N : Nat) (mW : GMap PNode (List w64)) (l : List GoString) : Preds
  | .cl k => if k < 6 then decodeP ((mW.lookup (PNode.cl k)).getD []) else []
  | .rep r => if r < N then
      (match nodeOf l r with
      | some k => decodeP ((mW.lookup (PNode.rep k)).getD [])
      | none => [])
    else []

/-- The pending slots are exactly the invoked, not yet accepted operations, with their
commands. -/
def SlotOk (h : SHist) (mSl : GMap CmdId (Cmd × GName)) : Prop :=
  (∀ x cg, mSl.lookup x = some cg → Ev.inv x cg.1 ∈ SHist.hist h ∧
    ∀ v, Ev.resp x v ∉ SHist.hist h) ∧
  (∀ x c, Ev.inv x c ∈ SHist.hist h → (∀ v, Ev.resp x v ∉ SHist.hist h) →
    ∃ γΨ, mSl.lookup x = some (c, γΨ))

/-- **L2's part of `sp.inv`** (it replaces stage 1's `ghostVar γl ½ [] ∨ token γ.own`), over the
protocol state `S` and the history `sh`:
* the registration tokens' authority (`preg`, its domain `allPNodes`), `sp.inv`'s half of each
  token, and the node's half of each registered node's token;
* the registered nodes (`regd`, with their `predReg`), each with its future words (`pred`: the
  words its ghost will still resolve, from its current event's first word; half here, half in the
  node's ghost lock);
* the history's other half, the abstract state's half at the committed prefix `G`
  (`linOwn γl`'s other half is the clients'), the pending slots;
* before any client event: nothing committed, nothing pending; after (then every node of the
  configuration `c` is registered and the slots are the pending operations): before any replica
  step (`S.empty`), nothing committed and nothing accepted; then D's strategy invariant
  `StratOk` over the predictions. -/
def l2Inv (γ : Names) (γc γm γl : GName) (S : PState) (sh : SHist) : IProp netDistGF :=
  iprop(∃ (mG : GMap PNode Unit) (mW : GMap PNode (List w64)) (mRg : GMap PNode Unit) (G : Seq)
      (mSl : GMap CmdId (Cmd × GName)),
    ghostMapAuth γ.preg 1 mG ∗ ⌜∀ n, mG.lookup n = if n ∈ allPNodes then some () else none⌝ ∗
    ([∗map] n ↦ u ∈ mG, ghostMapElem γ.preg n (DFrac.own (1 : Qp).half) u) ∗
    ghostMapAuth γ.regd 1 mRg ∗ ghostMapAuth γ.pred 1 mW ∗
    ⌜∀ n, mRg.lookup n = (mW.lookup n).map (fun _ => ())⌝ ∗
    ([∗map] n ↦ W ∈ mW, ghostMapElem γ.preg n (DFrac.own (1 : Qp).half) () ∗
      ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) W ∗ predReg γ n) ∗
    monoListAuthOwn γ.hist (1 : Qp).half (SHist.hist sh) ∗
    ghostVar γl (1 : Qp).half (linPuts G) ∗
    ghostMapAuth γ.slot 1 mSl ∗ ([∗map] x ↦ cg ∈ mSl, slotL γl G x cg) ∗
    (⌜sh = [] ∧ G = [] ∧ mSl = ∅⌝ ∨
      ∃ c : Conf, confIs γc c ∗
        ⌜(∀ n ∈ cfgPNodes c.n, (mW.lookup n).isSome) ∧ SlotOk sh mSl⌝ ∗
        (⌜S.empty ∧ G = [] ∧ ∀ x v, Ev.resp x v ∉ SHist.hist sh⌝ ∨
          ∃ (fr : Bool) (l : List GoString), cfg γc γm c.n fr l ∗
            ⌜StratOk c.n fr (l2Nodes c.n) S sh (predsOf c.n mW l) G⌝)))

/-- The body of `sp.inv` (see the file header). -/
def invBody (γ : Names) (γc γm γl : GName) : IProp netDistGF :=
  iprop(∃ (S : PState) (mC : GMap CmdId Cmd) (mL : GMap (Nat × Nat × Nat) CmdId)
      (mS : GMap Nat SyncMsg) (mA : GMap (Nat × Nat × CmdId) Unit)
      (mP : GMap (Nat × Nat × CmdId) (List CmdId)) (mCo : GMap (Nat × Nat × CmdId) Unit)
      (mR : GMap (Nat × Nat) Report) (mN : GMap Nat RState) (sh : SHist)
      (mD : GMap CmdId (List w8)) (mQ : GMap w32 Nat) (mK : GMap Nat ConnKind)
      (mPa : GMap (Nat × Nat × CmdId) (List CmdId)),
    ghostMapAuth γ.cmds 1 mC ∗ ghostMapAuth γ.loc 1 mL ∗ ghostMapAuth γ.sync 1 mS ∗
    ghostMapAuth γ.acc 1 mA ∗ ghostMapAuth γ.pre 1 mP ∗ ghostMapAuth γ.com 1 mCo ∗
    ghostMapAuth γ.rep 1 mR ∗ ghostMapAuth γ.node 1 mN ∗
    -- change log C12: the history's half, the decided results; L2's part (`l2Inv`)
    monoListAuthOwn γ.hist (1 : Qp).half (SHist.hist sh) ∗
    -- (with a persistent copy of each decided result, so a second decision can return it)
    (ghostMapAuth γ.dec 1 mD ∗ [∗map] x ↦ v ∈ mD, doneRes γ x v) ∗
    l2Inv γ γc γm γl S sh ∗ ghostMapAuth γ.seqs 1 mQ ∗
    ghostMapAuth γ.conn 1 mK ∗ ghostMapAuth γ.path 1 mPa ∗
    ⌜Repr S mC mL mS mA mP mCo mR mPa⌝ ∗
    -- the replica nodes' halves (each node's other half is its replica's)
    ([∗map] k ↦ st ∈ mN, nodeSt γ k (1 : Qp).half st) ∗
    -- the protocol: nothing before the configuration and the membership (only invocations);
    -- then `PInv`, with each replica's state its node's, the history's snapshots (`HistOk`) and
    -- the decided results (`decOk`)
    (⌜S.empty ∧ (∀ k, mN.lookup k = if k < 5 then some RState.init else none) ∧
        (∀ N fr, HistOk N fr sh S) ∧ ∀ x, mD.lookup x = none⌝ ∨
      ∃ (N : Nat) (fr : Bool) (l : List GoString), cfg γc γm N fr l ∗
        ⌜S.PInv N fr ∧ (∀ r k, r < N → nodeOf l r = some k → mN.lookup k = some (S.rs r)) ∧
          S.syncRows N ∧ HistOk N fr sh S ∧ decOk N S mD⌝) ∗
    -- the clients: each registered command's sequence number is below its client's next one
    -- (and below 2^10, change log C13', decision D13; the port lowered the lab's 2^25 so that a
    -- new leader's `MSync` fits gob's size limit, `swift.syncFits_of`, `GobFmt.fits_of`)
    ([∗map] cl ↦ n ∈ mQ, ghostMapElem γ.seqs cl (DFrac.own (1 : Qp).half) n) ∗
    ⌜∀ x c, mC.lookup x = some c → (∃ n, mQ.lookup x.cl = some n ∧ x.seq.toNat < n) ∧
      (c.isPut ∨ c.isGet) ∧ x.cl.toInt ≥ 1 ∧ c.val.length < 2 ^ 16 ∧ 0 ≤ x.seq.toInt ∧
      x.seq.toNat < 2 ^ 10⌝ ∗
    -- an invoked command is registered (C12); a tracked client's id is in `1 .. 6` (C13, D13)
    ⌜(∀ x c, Ev.inv x c ∈ SHist.hist sh → mC.lookup x = some c) ∧
      (∀ cl n, mQ.lookup cl = some n → 1 ≤ cl.toInt ∧ cl.toInt ≤ 6)⌝ ∗
    -- a persistent copy of every registration fragment (D11)
    ([∗map] x ↦ c ∈ mC, cmdIs γ x c) ∗
    -- the connections: each registered one's dialer gave up its fresh token
    ([∗map] cid ↦ _k ∈ mK, connFresh cid false) ∗
    -- change log C22 (M3): the replicas' numbering
    numInv γ γc γm S.loc)

/-- **The protocol invariant** (persistent; see the file header). -/
@[no_expose] def inv (γ : Names) (γc γm γl : GName) : IProp netDistGF :=
  Iris.inv spN (invBody γ γc γm γl)

/-- **Client `x.cl`'s ticket for its pending command `x`** (L2), invoked with the continuation
`Ψ`: its slot's element (the command `c`, the continuation's saved predicate). -/
def pend (γ : Names) (x : CmdId) (Ψ : List w8 → IProp netDistGF) : IProp netDistGF :=
  iprop(∃ (c : Cmd) (γΨ : GName), ghostMapElem γ.slot x (DFrac.own 1) (c, γΨ) ∗
    savedPredOwn γΨ .discard Ψ)

/-! ## The nodes' shares -/

/-- The clients' shares: each client `c`'s next sequence number 0 (client id `c + 1`). -/
@[no_expose] def clientsStart (γ : Names) : IProp netDistGF :=
  iprop([∗list] c ∈ (List.range 6 : List Nat), clientSeq γ (W32 (((c : Nat) + 1 : Nat) : Int)) 0)

/-- Client `c`'s share (client node `c`, stage 2): its next sequence number 0 (client id
`c + 1`). -/
@[no_expose] def clientStart (γ : Names) (c : Nat) : IProp netDistGF :=
  clientSeq γ (W32 (((c : Nat) + 1 : Nat) : Int)) 0

/-- Replica node `k`'s share (node `k + 2`): its protocol state's half, initially ballot 0; its
next number 0 (change log C22). -/
@[no_expose] def replicaStart (γ : Names) (k : Nat) : IProp netDistGF :=
  iprop(nodeSt γ k (1 : Qp).half RState.init ∗ numHi γ k (W64 0))

end defs

/-! ## Laws (the Prove phase's) -/

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS] [sp.GobFmt]
variable {γ : Names} {γc γm γl : GName}

instance inv_persistent : Persistent (inv γ γc γm γl) := by unfold inv; infer_instance

instance cfg_persistent (N : Nat) (fr : Bool) (l : List GoString) :
    Persistent (cfg γc γm N fr l) := by unfold cfg; infer_instance

/-! ### Persistence of the facts (helpers of the laws below) -/

instance cmdIs_persistent (x : CmdId) (c : Cmd) : Persistent (cmdIs γ x c) := by
  unfold cmdIs; infer_instance
instance predReg_persistent (n : PNode) : Persistent (predReg γ n) := by
  unfold predReg; infer_instance
instance predReg_timeless (n : PNode) : Timeless (predReg γ n) := by
  unfold predReg; infer_instance
instance allPredsReg_persistent : Persistent (allPredsReg γ γc) := by
  unfold allPredsReg; infer_instance
instance allPredsReg_timeless : Timeless (allPredsReg γ γc) := by
  unfold allPredsReg confIs; infer_instance
instance locAt_persistent (r b i : Nat) (x : CmdId) : Persistent (locAt γ r b i x) := by
  unfold locAt; infer_instance
instance locLb_persistent (r b : Nat) (s : Seq) : Persistent (locLb γ r b s) := by
  unfold locLb; infer_instance
instance syncIs_persistent (b : Nat) (M : SyncMsg) : Persistent (syncIs γ b M) := by
  unfold syncIs; infer_instance
instance accepted_persistent (r b : Nat) (x : CmdId) : Persistent (accepted γ r b x) := by
  unfold accepted; infer_instance
instance preacc_persistent (r b : Nat) (x : CmdId) (D : List CmdId) :
    Persistent (preacc γ r b x D) := by
  unfold preacc; infer_instance
instance pathIs_persistent (r b : Nat) (x : CmdId) (P : List CmdId) :
    Persistent (pathIs γ r b x P) := by
  unfold pathIs; infer_instance
instance committed_persistent (r b : Nat) (x : CmdId) : Persistent (committed γ r b x) := by
  unfold committed; infer_instance
instance reported_persistent (r b : Nat) (R : Report) : Persistent (reported γ r b R) := by
  unfold reported; infer_instance
instance numIs_persistent (r b : Nat) (x : CmdId) (s : w64) : Persistent (numIs γ r b x s) := by
  unfold numIs; infer_instance
instance connKind_persistent (cid : Nat) (k : ConnKind) : Persistent (connKind γ cid k) := by
  unfold connKind; infer_instance
instance numAck_persistent (r b : Nat) (x : CmdId) (s : w64) : Persistent (numAck γ r b x s) := by
  unfold numAck; infer_instance
instance locDeps_persistent (r b : Nat) (x : CmdId) (D : List CmdId) :
    Persistent (locDeps γ r b x D) := by
  unfold locDeps; infer_instance
instance ackOk_persistent (r b : Nat) (a : Ack) : Persistent (ackOk γ r b a) := by
  unfold ackOk; split <;> infer_instance
instance fastAckOk_persistent (f : FastAck) : Persistent (fastAckOk γ f) := by
  unfold fastAckOk; infer_instance

/-- The protocol's view of the configuration, from the configuration and the membership (the
same `N`). -/
theorem cfg_intro (c : Conf) (l : List GoString) :
    confIs γc c ∗ memIs γm l ∗ ⌜l.length = c.n ∧ ∀ r k, nodeOf l r = some k → k < c.n⌝ ⊢
      cfg γc γm c.n (c.fastRead == 1) l := by
  unfold cfg
  iintro ⟨#Hc, #Hm, %Hl⟩
  iexists c
  iframe Hc Hm
  isplitl []
  · ipureintro; exact Hl.2
  ipureintro
  exact ⟨rfl, rfl, Hl.1⟩

/-- The view's members are configured replica nodes (R-E2). -/
theorem cfg_nodeOf (N : Nat) (fr : Bool) (l : List GoString) :
    cfg γc γm N fr l ⊢ ⌜∀ r k, nodeOf l r = some k → k < N⌝ := by
  unfold cfg
  iintro ⟨%c, ⟨-, %H⟩, -, -⟩
  ipureintro; exact H

/-- Two views agree. -/
theorem cfg_agree (N N' : Nat) (fr fr' : Bool) (l l' : List GoString) :
    cfg γc γm N fr l ∗ cfg γc γm N' fr' l' ⊢ ⌜N = N' ∧ fr = fr' ∧ l = l'⌝ := by
  unfold cfg
  iintro ⟨⟨%c, ⟨#Hc, -⟩, #Hm, %H⟩, ⟨%c', ⟨#Hc', -⟩, #Hm', %H'⟩⟩
  ihave %Hcc : ⌜c = c'⌝ $$ []
  · iapply confIs_agree
    isplitl []
    · iexact Hc
    · iexact Hc'
  ihave %Hll : ⌜l = l'⌝ $$ []
  · iapply memIs_agree
    isplitl []
    · iexact Hm
    · iexact Hm'
  ipureintro
  subst Hcc Hll
  obtain ⟨h1, h2, -⟩ := H
  obtain ⟨h1', h2', -⟩ := H'
  exact ⟨h1.symm.trans h1', h2.trans h2'.symm, rfl⟩

/-- The view's `N` and fast reads are the configuration's. -/
theorem cfg_conf (N : Nat) (fr : Bool) (l : List GoString) (c : Conf) :
    cfg γc γm N fr l ∗ confIs γc c ⊢ ⌜c.n = N ∧ fr = (c.fastRead == 1)⌝ := by
  unfold cfg
  iintro ⟨⟨%c', ⟨#Hc', -⟩, -, %H⟩, #Hc⟩
  ihave %Hcc : ⌜c' = c⌝ $$ []
  · iapply confIs_agree
    isplitl []
    · iexact Hc'
    · iexact Hc
  ipureintro
  subst Hcc
  exact ⟨H.1, H.2.1⟩

/-- The view's membership is the membership, with `N` addresses. -/
theorem cfg_mem (N : Nat) (fr : Bool) (l l' : List GoString) :
    cfg γc γm N fr l ∗ memIs γm l' ⊢ ⌜l = l' ∧ l.length = N⌝ := by
  unfold cfg
  iintro ⟨⟨%c, -, #Hm, %H⟩, #Hm'⟩
  ihave %Hll : ⌜l = l'⌝ $$ []
  · iapply memIs_agree
    isplitl []
    · iexact Hm
    · iexact Hm'
  ipureintro
  exact ⟨Hll, H.2.2⟩

/-- The view gives the configuration's fact. -/
theorem cfg_confIs (N : Nat) (fr : Bool) (l : List GoString) :
    cfg γc γm N fr l ⊢ ∃ c, confIs γc c ∗ ⌜c.n = N ∧ fr = (c.fastRead == 1)⌝ := by
  unfold cfg
  iintro ⟨%c, ⟨#Hc, -⟩, -, %H⟩
  iexists c
  iframe Hc
  ipureintro
  exact ⟨H.1, H.2.1⟩

/-- The view gives the membership's fact. -/
theorem cfg_memIs (N : Nat) (fr : Bool) (l : List GoString) :
    cfg γc γm N fr l ⊢ memIs γm l ∗ ⌜l.length = N⌝ := by
  unfold cfg
  iintro ⟨%c, -, #Hm, %H⟩
  iframe Hm
  ipureintro
  exact H.2.2

/-! ### The sealed slots' laws (`inP`, `outQ`, `masterSpec`, `replicaRpcSpec`, `inv`,
`clientsStart`, `replicaStart` are `@[no_expose]`: clients use these, not their bodies) -/

/-- An empty stream is in either protocol. -/
theorem inP_nil (cid : Nat) : ⊢ inP γ γc γm cid [] := by
  unfold inP; ileft; ipureintro; rfl
theorem outQ_nil (cid : Nat) : ⊢ outQ γ γc γm cid [] := by
  unfold outQ; ileft; ipureintro; rfl

/-- A client's stream of proposals on a connection it registered as its own. -/
theorem inP_client (cid : Nat) (cl : w32) (bs : List w8) :
    connKind γ cid (.client cl) ∗ framesProto γ γc γm [] (Msg.isProposeOf cl) bs ⊢
      inP γ γc γm cid bs := by
  unfold inP
  iintro ⟨#Hk, H⟩
  iright
  iexists .client cl
  iframe Hk
  iexact H

/-- A peer's stream: its hello, then peer messages. -/
theorem inP_peer (cid : Nat) (id : w32) (bs : List w8) :
    connKind γ cid .peer ∗ framesProto γ γc γm (helloBytes id) Msg.isPeer bs ⊢
      inP γ γc γm cid bs := by
  unfold inP
  iintro ⟨#Hk, H⟩
  iright
  iexists .peer
  iframe Hk
  iexists id
  iexact H

/-- What a replica's reader learns of a dialer's stream. -/
theorem inP_elim (cid : Nat) (bs : List w8) :
    inP γ γc γm cid bs ⊢ ⌜bs = []⌝ ∨ ∃ k, connKind γ cid k ∗ match k with
      | .client cl => framesProto γ γc γm [] (Msg.isProposeOf cl) bs
      | .peer => ∃ id : w32, framesProto γ γc γm (helloBytes id) Msg.isPeer bs := by
  unfold inP; exact .rfl

/-- A replica's stream back to a client. -/
theorem outQ_client (cid : Nat) (cl : w32) (bs : List w8) :
    connKind γ cid (.client cl) ∗ framesProto γ γc γm [] (Msg.isToClient cl) bs ⊢
      outQ γ γc γm cid bs := by
  unfold outQ
  iintro ⟨#Hk, H⟩
  iright
  iexists .client cl
  iframe Hk
  iexact H

/-- A replica's stream back to a peer. -/
theorem outQ_peer (cid : Nat) (bs : List w8) :
    connKind γ cid .peer ∗ framesProto γ γc γm [] Msg.isPeer bs ⊢ outQ γ γc γm cid bs := by
  unfold outQ
  iintro ⟨#Hk, H⟩
  iright
  iexists .peer
  iframe Hk
  iexact H

/-- What a dialer's reader learns of the replica's stream. -/
theorem outQ_elim (cid : Nat) (bs : List w8) :
    outQ γ γc γm cid bs ⊢ ⌜bs = []⌝ ∨ ∃ k, connKind γ cid k ∗ match k with
      | .client cl => framesProto γ γc γm [] (Msg.isToClient cl) bs
      | .peer => framesProto γ γc γm [] Msg.isPeer bs := by
  unfold outQ; exact .rfl

/-- The master's `Register` (see `masterSpec`). -/
theorem masterSpec_register (args : List w8) (Φ : List w8 → List w8 → IProp netDistGF) :
    masterSpec γc γm go!"Register" args Φ ⊣⊢
      ∃ (ip : GoString) (port : w64) (c : Conf) (k : Nat),
        ⌜args = (KitVal.registerArgs ip port).encode ∧
          replicaAddrs[k]? = some (addrPort ip port) ∧ k < c.n⌝ ∗ confIs γc c ∗
        ∀ (id : w64) (nodes : List GoString) (ready isL : Bool),
          (if ready then iprop(∃ fr, cfg γc γm nodes.length fr nodes ∗
              ⌜nodes[id.toNat]? = some (addrPort ip port)⌝) else iprop(True)) -∗
          Φ (KitVal.registerReply id nodes ready isL).encode [] := by
  unfold masterSpec; rw [if_pos rfl]; exact .rfl

/-- The master's `GetReplicaList`. -/
theorem masterSpec_getReplicaList (args : List w8) (Φ : List w8 → List w8 → IProp netDistGF) :
    masterSpec γc γm go!"GetReplicaList" args Φ ⊣⊢
      ⌜args = KitVal.getReplicaListArgs.encode⌝ ∗
        ∀ (nodes : List GoString) (alive : List Bool),
          (∃ fr, cfg γc γm nodes.length fr nodes) -∗ ⌜alive.length = nodes.length⌝ -∗
          Φ (KitVal.getReplicaListReply nodes alive true).encode [] := by
  unfold masterSpec; rw [if_neg (by decide), if_pos rfl]; exact .rfl

/-- The master's `GetLeader`. -/
theorem masterSpec_getLeader (args : List w8) (Φ : List w8 → List w8 → IProp netDistGF) :
    masterSpec γc γm go!"GetLeader" args Φ ⊣⊢
      ⌜args = KitVal.getLeaderArgs.encode⌝ ∗ ∀ id : w64, Φ (KitVal.getLeaderReply id).encode [] := by
  unfold masterSpec; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]; exact .rfl

/-- No other method of the master is called. -/
theorem masterSpec_other (m : GoString) (args : List w8)
    (Φ : List w8 → List w8 → IProp netDistGF)
    (h : m ≠ go!"Register" ∧ m ≠ go!"GetReplicaList" ∧ m ≠ go!"GetLeader") :
    masterSpec γc γm m args Φ ⊢ False := by
  unfold masterSpec; rw [if_neg h.1, if_neg h.2.1, if_neg h.2.2]

/-- A replica's `BeTheLeader`. -/
theorem replicaRpcSpec_beTheLeader (args : List w8) (Φ : List w8 → List w8 → IProp netDistGF) :
    replicaRpcSpec γc γm go!"BeTheLeader" args Φ ⊣⊢
      ⌜args = KitVal.beTheLeaderArgs.encode⌝ ∗
        ∀ (ld nl : w32), (∃ N fr l, cfg γc γm N fr l ∗ ⌜btlOk N ld nl⌝) -∗
          Φ (KitVal.beTheLeaderReply ld nl).encode [] := by
  unfold replicaRpcSpec; rw [if_pos rfl]; exact .rfl

/-- A replica's `Ping`. -/
theorem replicaRpcSpec_ping (args : List w8) (Φ : List w8 → List w8 → IProp netDistGF) :
    replicaRpcSpec γc γm go!"Ping" args Φ ⊣⊢
      ∃ a : w8, ⌜args = (KitVal.pingArgs a).encode⌝ ∗ Φ KitVal.pingReply.encode [] := by
  unfold replicaRpcSpec; rw [if_neg (by decide), if_pos rfl]; exact .rfl

/-- No other method of a replica is called. -/
theorem replicaRpcSpec_other (m : GoString) (args : List w8)
    (Φ : List w8 → List w8 → IProp netDistGF) (h : m ≠ go!"BeTheLeader" ∧ m ≠ go!"Ping") :
    replicaRpcSpec γc γm m args Φ ⊢ False := by
  unfold replicaRpcSpec; rw [if_neg h.1, if_neg h.2]

/-- Client `c`'s share: its next sequence number, 0. -/
theorem clientStart_elim (c : Nat) :
    clientStart γ c ⊢ clientSeq γ (W32 (((c : Nat) + 1 : Nat) : Int)) 0 := by
  unfold clientStart; exact .rfl

/-- The six clients' shares from the client node's earlier share (stage 2: one per client node;
the history's half and the claim token are dropped). -/
theorem clientsStart_split :
    clientsStart γ ⊢ [∗list] c ∈ (List.range 6 : List Nat), clientStart γ c := by
  unfold clientsStart clientStart
  exact .rfl

/-- Replica node `k`'s share: its protocol state's half, initially. -/
theorem replicaStart_elim (k : Nat) :
    replicaStart γ k ⊢ nodeSt γ k (1 : Qp).half RState.init := by
  unfold replicaStart; iintro ⟨H, -⟩; iexact H

/-- Replica node `k`'s share with its numbering's (change log C22). -/
theorem replicaStart_num (k : Nat) :
    replicaStart γ k ⊢ nodeSt γ k (1 : Qp).half RState.init ∗ numHi γ k (W64 0) := by
  unfold replicaStart; exact .rfl

/-- Every message's witness is persistent (a protocol's values are). -/
theorem msgOk_persistent (m : Msg) : Persistent (msgOk γ γc γm m) := by
  cases m <;> unfold msgOk <;> infer_instance

/-- A prefix of a stream of frames is one (helper of the prefix-closure laws). -/
theorem framesProto_prefix (head : List w8) (ok : Msg → Prop) (x y : List w8) :
    framesProto γ γc γm head ok (x ++ y) ⊢ framesProto γ γc γm head ok x := by
  unfold framesProto
  iintro ⟨%ms, %H, Hms⟩
  iexists ms
  iframe Hms
  ipureintro
  exact ⟨(List.prefix_append x y).trans H.1, H.2⟩

/-- The protocols are prefix-closed (what `bufio`'s writer over a connection needs:
`writerOk_conn`). -/
theorem inP_prefixClosed (cid : Nat) :
    ⊢ (□ (∀ (x y : List w8), inP γ γc γm cid (x ++ y) -∗ inP γ γc γm cid x) : IProp netDistGF) := by
  unfold inP
  iintro !> %x %y (%H | ⟨%k, #Hk, H⟩)
  · ileft; ipureintro; exact (List.append_eq_nil_iff.mp H).1
  · iright
    iexists k
    iframe Hk
    cases k with
    | client cl => iapply framesProto_prefix $$ H
    | peer =>
      icases H with ⟨%id, H⟩
      iexists id
      iapply framesProto_prefix $$ H

theorem outQ_prefixClosed (cid : Nat) :
    ⊢ (□ (∀ (x y : List w8), outQ γ γc γm cid (x ++ y) -∗ outQ γ γc γm cid x) : IProp netDistGF) := by
  unfold outQ
  iintro !> %x %y (%H | ⟨%k, #Hk, H⟩)
  · ileft; ipureintro; exact (List.append_eq_nil_iff.mp H).1
  · iright
    iexists k
    iframe Hk
    cases k with
    | client cl => iapply framesProto_prefix $$ H
    | peer => iapply framesProto_prefix $$ H

/-- The empty protocol state (nothing happened; every replica at `RState.init`). -/
def PState.init : PState :=
  ⟨fun _ => none, fun _ _ => [], fun _ => none, fun _ => RState.init, fun _ _ _ => False,
    fun _ _ _ => none, fun _ _ _ => none, fun _ _ _ => False, fun _ _ => none, []⟩

instance PState.inhabited : Inhabited PState := ⟨PState.init⟩

/-- Allocate a ghost map holding `f a ↦ v` for each `a ∈ l`, each element as two halves:
one half in a `[∗map]` over the map, the other per `a ∈ l` (helper of `alloc`). -/
theorem ghostMap_alloc_list {α K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (f : α → K) (v : V) (l : List α) (hnd : (l.map f).Nodup) :
    ⊢ (|==> ∃ (g : GName) (m : GMap K V), ghostMapAuth g 1 m ∗
      ⌜∀ k, m.lookup k = if k ∈ l.map f then some v else none⌝ ∗
      ([∗map] k ↦ w ∈ m, ghostMapElem g k (DFrac.own (1 : Qp).half) w) ∗
      [∗list] a ∈ l, ghostMapElem g (f a) (DFrac.own (1 : Qp).half) v : IProp netDistGF) := by
  induction l with
  | nil =>
    imod ghost_map_alloc_empty (GF := netDistGF) (K := K) (V := V) with ⟨%g, H⟩
    imodintro
    iexists g, ∅
    iframe H
    isplitr
    · ipureintro; intro k; simp
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; itrivial
    · iapply BigSepL.bigSepL_nil.2; itrivial
  | cons a l ih =>
    have hnd' := List.nodup_cons.mp (by simpa using hnd : (f a :: l.map f).Nodup)
    imod ih hnd'.2 with ⟨%g, %m, H, %Hm, HM, HL⟩
    have hnone : m.lookup (f a) = none := by rw [Hm]; simp [hnd'.1]
    imod ghost_map_insert (f a) v hnone $$ H with ⟨H, He⟩
    icases (ghostMapElem_halves g (f a) v).1 $$ He with ⟨He1, He2⟩
    imodintro
    iexists g, _
    iframe H
    isplitr
    · ipureintro
      intro k
      rw [GMap.lookup_insert_eq_iff, Hm]
      by_cases hk : f a = k
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    isplitl [He1 HM]
    · iapply (BigSepM.bigSepM_insert hnone).2
      iframe
    · iapply BigSepL.bigSepL_cons.2
      iframe

/-- Allocate a ghost map holding `f a ↦ v` for each `a ∈ l`, each element whole (helper of
`alloc`, change log C22). -/
theorem ghostMap_alloc_full {α K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (f : α → K) (v : V) (l : List α) (hnd : (l.map f).Nodup) :
    ⊢ (|==> ∃ (g : GName) (m : GMap K V), ghostMapAuth g 1 m ∗
      ⌜∀ k, m.lookup k = if k ∈ l.map f then some v else none⌝ ∗
      [∗list] a ∈ l, ghostMapElem g (f a) (DFrac.own 1) v : IProp netDistGF) := by
  induction l with
  | nil =>
    imod ghost_map_alloc_empty (GF := netDistGF) (K := K) (V := V) with ⟨%g, H⟩
    imodintro
    iexists g, ∅
    iframe H
    isplitr
    · ipureintro; intro k; simp
    · iapply BigSepL.bigSepL_nil.2; itrivial
  | cons a l ih =>
    have hnd' := List.nodup_cons.mp (by simpa using hnd : (f a :: l.map f).Nodup)
    imod ih hnd'.2 with ⟨%g, %m, H, %Hm, HL⟩
    have hnone : m.lookup (f a) = none := by rw [Hm]; simp [hnd'.1]
    imod ghost_map_insert (f a) v hnone $$ H with ⟨H, He⟩
    imodintro
    iexists g, _
    iframe H
    isplitr
    · ipureintro
      intro k
      rw [GMap.lookup_insert_eq_iff, Hm]
      by_cases hk : f a = k
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    · iapply BigSepL.bigSepL_cons.2
      iframe

/-- A mono-list's authority as two halves, both ways. -/
theorem monoList_halves {A : Type} [Pos.Countable A] (γh : GName) (l : List A) :
    (monoListAuthOwn γh 1 l : IProp netDistGF) ⊣⊢
      monoListAuthOwn γh (1 : Qp).half l ∗ monoListAuthOwn γh (1 : Qp).half l := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (monoListAuthOwn_fractional γh l).fractional _ _

/-- **Allocation** (the start): from `lin`'s other half at the empty state, the names, the
invariant, the clients' and the replica nodes' shares (change log C12: `lin`'s half stays in the
invariant until the client node claims it, `lin_claim`). -/
theorem alloc (γc γm γl : GName) :
    ghostVar (A := List (GoString × GoString)) γl (1 : Qp).half [] ⊢
      |={⊤}=> ∃ γ : Names, inv γ γc γm γl ∗ clientsStart γ ∗
        ([∗list] k ∈ List.range 5, replicaStart γ k) ∗ [∗list] n ∈ allPNodes, predTok γ n := by
  iintro Hl
  imod ghost_map_alloc_empty (GF := netDistGF) (K := CmdId) (V := Cmd) with ⟨%gC, HC⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat × Nat × Nat) (V := CmdId) with ⟨%gL, HL⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat) (V := SyncMsg) with ⟨%gS, HS⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat × Nat × CmdId) (V := Unit) with ⟨%gA, HA⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat × Nat × CmdId) (V := List CmdId)
    with ⟨%gP, HP⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat × Nat × CmdId) (V := Unit) with ⟨%gCo, HCo⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat × Nat × CmdId) (V := List CmdId)
    with ⟨%gPa, HPa⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat × Nat) (V := Report) with ⟨%gR, HRp⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := CmdId) (V := List w8) with ⟨%gD, HD⟩
  imod token_alloc (GF := netDistGF) with ⟨%gO, HO⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat) (V := ConnKind) with ⟨%gK, HK⟩
  imod mono_list_own_alloc (GF := netDistGF) (A := Ev) [] with ⟨%gH, HH, -⟩
  icases (monoList_halves gH ([] : List Ev)).1 $$ HH with ⟨HH1, HH2⟩
  imod ghostMap_alloc_list (fun c : Nat => W32 (((c : Nat) + 1 : Nat) : Int)) (0 : Nat)
    (List.range 6) (by decide) with ⟨%gQ, %mQ, HQ, %HmQ, HQs, Hcl⟩
  imod ghostMap_alloc_list (fun k : Nat => k) RState.init (List.range 5) (by decide)
    with ⟨%gN, %mN, HN, %HmN, HNs, Hrs⟩
  imod ghostMap_alloc_full (fun k : Nat => ((k, none) : Nat × Option (Nat × CmdId))) (W64 0)
    (List.range 5) (by decide) with ⟨%gNu, %mNu, HNu, %HmNu, HNus⟩
  imod ghostMap_alloc_list (fun n : PNode => n) () allPNodes (by decide)
    with ⟨%gPr, %mPr, HPrA, %HmPr, HPrs, HPr⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := PNode) (V := Unit) with ⟨%gRg, HRg⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := PNode) (V := List w64) with ⟨%gW, HW⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := CmdId) (V := Cmd × GName) with ⟨%gSl, HSl⟩
  let γ : Names := ⟨gC, gL, gS, gA, gP, gCo, gPa, gR, gN, gH, gD, gO, gQ, gK, gNu, gPr, gRg, gW,
    gSl⟩
  imod inv_alloc spN ⊤ (invBody γ γc γm γl) $$
    [HC HL HS HA HP HCo HPa HRp HD HK HH1 HH2 HQ HQs HN HNs Hl HNu HPrA HPrs HRg HW HSl] with #Hinv
  · inext
    ihave Hl2 : l2Inv γ γc γm γl PState.init [] $$ [HPrA HPrs HRg HW HSl HH2 Hl]
    · unfold l2Inv
      iexists mPr, ∅, ∅, [], ∅
      rw [show linPuts [] = [] by simp [linPuts], show SHist.hist ([] : SHist) = ([] : Hist) from rfl]
      iframe HPrA HPrs HRg HW HSl Hl HH2
      isplitr
      · ipureintro; intro n; rw [HmPr]; simp
      isplitr
      · ipureintro; intro n; simp
      isplitl []
      · iapply BigSepM.bigSepM_empty.2; itrivial
      isplitl []
      · iapply BigSepM.bigSepM_empty.2; itrivial
      ileft; ipureintro; exact ⟨rfl, rfl, rfl⟩
    unfold invBody
    iexists PState.init, ∅, ∅, ∅, ∅, ∅, ∅, ∅, mN, [], ∅, mQ, ∅, ∅
    iframe
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · ipureintro
      constructor <;> intros <;> simp [PState.init]
    isplitr
    · ileft
      ipureintro
      refine ⟨?_, ?_, fun N fr => HistOk.nil N fr _ (fun x => rfl), fun x => by simp⟩
      · unfold PState.empty; simp [PState.init]
      · intro k
        rw [HmN]
        simp
    isplitr
    · ipureintro
      intro x c h
      simp at h
    isplitr
    · ipureintro
      refine ⟨fun x c h => by simp [SHist.hist] at h, fun cl n h => ?_⟩
      rw [HmQ] at h
      split at h
      · rename_i hm
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
        have hc6 : c < 6 := List.mem_range.mp hc
        rcases c with _ | _ | _ | _ | _ | _ | c
        all_goals first | decide | omega
      · cases h
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; itrivial
    · unfold numInv
      iexists mNu
      iframe HNu
      ileft
      ipureintro
      refine ⟨fun r b x => by rw [HmNu]; simp, fun k n hk => ?_⟩
      rw [HmNu] at hk
      split at hk
      · cases hk; decide
      · cases hk
  imodintro
  iexists γ
  unfold inv clientsStart replicaStart clientSeq nodeSt numHi predTok
  iframe Hinv
  isplitl [Hcl]
  · iexact Hcl
  isplitl [Hrs HNus]
  · iapply BigSepL.bigSepL_sep_eqv.2
    iframe Hrs HNus
  · iexact HPr

/-- A dialer registers its connection's kind, once, with the `Dial`'s fresh token. -/
theorem conn_register (E : CoPset) (hE : ↑spN ⊆ E) (cid : Nat) (k : ConnKind) :
    inv γ γc γm γl ∗ connFresh cid false ⊢ |={E}=> connKind γ cid k := by
  unfold inv connKind
  iintro ⟨#Hinv, Hfresh⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, >HK, HPa, HRepr, Hnodes, Hproto, HQs, HCl, HDom, Hcmds, >Hconns, HNu⟩
  cases hlk : mK.lookup cid with
  | some k0 =>
    ihave Hf := (BigSepM.bigSepM_lookup (show Iris.Std.PartialMap.get? mK cid = some k0 from hlk)) $$ Hconns
    iexfalso
    iapply connFresh_excl cid false
    isplitl [Hf]
    · iexact Hf
    · iexact Hfresh
  | none =>
    imod ghost_map_insert_persist cid k hlk $$ HK with ⟨HK, #Hk⟩
    ihave Hconns := (BigSepM.bigSepM_insert (show Iris.Std.PartialMap.get? mK cid = none from hlk)).2 $$ [Hfresh Hconns]
    · iframe
    imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa HRepr Hnodes Hproto HQs HCl HDom Hcmds Hconns HNu] with -
    · inext
      iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK.insert cid k, mPa
      iframe
    imodintro
    iexact Hk

/-- A connection's kind is unique. -/
theorem connKind_agree (cid : Nat) (k1 k2 : ConnKind) :
    connKind γ cid k1 ∗ connKind γ cid k2 ⊢ ⌜k1 = k2⌝ := by
  unfold connKind
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- A history without acceptances is linearizable (nothing to place). -/
theorem lin_of_no_resp (H : Hist) (h : ∀ x v, Ev.resp x v ∉ H) : Lin H :=
  ⟨[], ⟨by simp, by simp, fun x v hm => absurd hm (h x v), fun x y hx => by simp at hx⟩⟩

/-- Before the configuration, the history has no acceptance (nothing is possibly chosen). -/
theorem empty_no_resp {S : PState} {sh : SHist} (hE : S.empty) (hH : ∀ N fr, HistOk N fr sh S) :
    ∀ x v, Ev.resp x v ∉ SHist.hist sh := by
  intro x v hm
  obtain ⟨S', hm⟩ := SHist.mem_hist.mp hm
  obtain ⟨-, b, hpc, -⟩ := (hH 0 false).resp x v S' hm
  have := ((hH 0 false).le_now _ hm).loc (leaderOf 0 b) b
  have hx := this.subset hpc.1
  rw [hE.1] at hx
  simp at hx

/-- The protocol disjunct of `invBody` after an invocation and its registration (helper of
`client_invoke`): the same disjunct for `S.register x c` and the history with the invocation,
which is linearizable (`lin_now`). -/
theorem proto_invoke (S : PState) (mN : GMap Nat RState) (mD : GMap CmdId (List w8)) (sh : SHist)
    (x : CmdId) (c : Cmd) (hx : S.cmds x = none) (hnew : ∀ c' S', (Ev.inv x c', S') ∉ sh)
    (hpg : c.isPut = true ∨ c.isGet = true) :
    (⌜S.empty ∧ (∀ k, mN.lookup k = if k < 5 then some RState.init else none) ∧
        (∀ N fr, HistOk N fr sh S) ∧ ∀ x, mD.lookup x = none⌝ ∨
      ∃ (N : Nat) (fr : Bool) (l : List GoString), cfg γc γm N fr l ∗
        ⌜S.PInv N fr ∧ (∀ r k, r < N → nodeOf l r = some k → mN.lookup k = some (S.rs r)) ∧
          S.syncRows N ∧ HistOk N fr sh S ∧ decOk N S mD⌝ : IProp netDistGF) ⊢
    (⌜(S.register x c).empty ∧ (∀ k, mN.lookup k = if k < 5 then some RState.init else none) ∧
        (∀ N fr, HistOk N fr (sh ++ [(Ev.inv x c, S)]) (S.register x c)) ∧
        ∀ x, mD.lookup x = none⌝ ∨
      ∃ (N : Nat) (fr : Bool) (l : List GoString), cfg γc γm N fr l ∗
        ⌜(S.register x c).PInv N fr ∧
          (∀ r k, r < N → nodeOf l r = some k → mN.lookup k = some ((S.register x c).rs r)) ∧
          (S.register x c).syncRows N ∧
          HistOk N fr (sh ++ [(Ev.inv x c, S)]) (S.register x c) ∧
          decOk N (S.register x c) mD⌝) ∗
    ⌜Lin (SHist.hist sh ++ [Ev.inv x c])⌝ := by
  have hinv : Ev.inv x c ∈ SHist.hist (sh ++ [(Ev.inv x c, S)]) := by
    simp [SHist.hist]
  have hh : SHist.hist (sh ++ [(Ev.inv x c, S)]) = SHist.hist sh ++ [Ev.inv x c] := by
    simp [SHist.hist]
  iintro (%H | ⟨%N, %fr, %l, #Hcfg, %H⟩)
  · obtain ⟨hE, hN, hH, hD⟩ := H
    have hH' : ∀ N fr, HistOk N fr (sh ++ [(Ev.inv x c, S)]) (S.register x c) := fun N fr =>
      HistOk_register (HistOk_inv (hH N fr) hx hnew hpg) hx hinv
    isplitl
    · ileft; ipureintro; exact ⟨hE, hN, hH', hD⟩
    · ipureintro
      apply lin_of_no_resp
      intro y v hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · exact empty_no_resp hE hH y v hm
      · simp at hm
  · obtain ⟨hI, hN, hR, hH, hD⟩ := H
    have hI' := PState.PInv_register hI x c hx
    have hH' := HistOk_register (HistOk_inv hH hx hnew hpg) hx hinv
    isplitl
    · iright
      iexists N, fr, l
      iframe Hcfg
      ipureintro
      refine ⟨hI', hN, hR, hH', fun y v hy => ?_⟩
      obtain ⟨b, hpc, hres⟩ := hD y v hy
      obtain ⟨hpc', hres'⟩ := PState.possiblyChosen_le hI (PState.le_register x c hx) hpc
      exact ⟨b, hpc', hres'.trans hres⟩
    · ipureintro
      rw [← hh]; exact lin_now hI' hH'

/-- A tracked client's id is at least 1 (change log C13, HUB-REQUEST 10 of the client group:
`clientsStart`'s ids are `1 .. 6`; `client.ready` holds it). -/
theorem clientSeq_pos (E : CoPset) (hE : ↑spN ⊆ E) (cl : w32) (s : Nat) :
    inv γ γc γm γl ∗ clientSeq γ cl s ⊢ |={E}=> ⌜1 ≤ cl.toInt⌝ ∗ clientSeq γ cl s := by
  unfold inv clientSeq
  iintro ⟨#Hinv, Hs⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, >HQ, HK, HPa, HRepr, Hnodes, Hproto, HQs, HCl, >%Hdom, Hcmds, Hconns⟩
  ihave %HlkQ := ghost_map_lookup $$ HQ Hs
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa HRepr Hnodes Hproto HQs HCl Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    ipureintro; exact Hdom
  imodintro
  iframe Hs
  ipureintro
  exact (Hdom.2 cl s HlkQ).1

/-- A decided command is registered (helper): its decided result comes with a possibly chosen
command, which its leader ordered, so registered (`PInv.loc_ok`). -/
theorem dec_registered {S : PState} {N : Nat} {fr : Bool} {mC : GMap CmdId Cmd}
    {mD : GMap CmdId (List w8)} {x : CmdId} {o : List w8} (hI : S.PInv N fr)
    (hD : decOk N S mD) (hcmds : ∀ y, mC.lookup y = S.cmds y) (hx : mD.lookup x = some o) :
    ∃ c, mC.lookup x = some c := by
  obtain ⟨b, hpc, -⟩ := hD x o hx
  have := (hI.loc_ok _ _).2.1 x hpc.1
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp this
  exact ⟨c, by rw [hcmds]; exact hc⟩

/-- A decided command's sequence number is non-negative (change log C8, HUB-REQUEST 9 of the
client group: the slow path's certificate carries no `cmdIs`). -/
theorem doneRes_seq_nonneg (E : CoPset) (hE : ↑spN ⊆ E) (x : CmdId) (o : List w8) :
    inv γ γc γm γl ∗ doneRes γ x o ⊢ |={E}=> ⌜0 ≤ x.seq.toInt⌝ := by
  unfold inv doneRes
  iintro ⟨#Hinv, #Hd⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, HS, HA, HP, HCo, HRp, HN, HH, ⟨>HD, HDs⟩, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, >%Hcl, HDom, Hcmds, Hconns⟩
  ihave %HlkD := ghost_map_lookup $$ HD Hd
  icases Hproto with (>%Hemp | ⟨%N, %fr, %l, #Hcfg, >%Hp⟩)
  · exfalso; rw [Hemp.2.2.2 x] at HlkD; cases HlkD
  obtain ⟨c, hc⟩ := dec_registered Hp.1 Hp.2.2.2.2 Hrepr.cmds HlkD
  obtain ⟨-, -, -, -, hnn, -⟩ := Hcl x c hc
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD HDs Hown HQ HK HPa Hnodes HQs HDom Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    isplitr
    · iright
      iexists N, fr, l
      iframe Hcfg
      ipureintro; exact Hp
    ipureintro; exact Hcl
  imodintro
  ipureintro
  exact hnn

/-- A command's registration is unique. -/
theorem cmdIs_agree (x : CmdId) (c1 c2 : Cmd) : cmdIs γ x c1 ∗ cmdIs γ x c2 ⊢ ⌜c1 = c2⌝ := by
  unfold cmdIs
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- A registered command is a client's put or get (what a replica's execution needs: no
`SCAN`, values below 2^16). -/
theorem cmdIs_ok (x : CmdId) (c : Cmd) :
    inv γ γc γm γl ∗ cmdIs γ x c ⊢ |={↑spN}=> ⌜(c.isPut ∨ c.isGet) ∧ x.cl.toInt ≥ 1 ∧
      c.val.length < 2 ^ 16⌝ := by
  unfold inv cmdIs
  iintro ⟨#Hinv, #Hc⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, >%Hcl, HDom, Hcmds, Hconns⟩
  ihave %Hlk := ghost_map_lookup $$ HC Hc
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes Hproto HQs HDom Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    ipureintro
    exact ⟨Hrepr, Hcl⟩
  imodintro
  ipureintro
  obtain ⟨-, h1, h2, h3, -⟩ := Hcl x c Hlk
  exact ⟨h1, h2, h3⟩

/-- **A registered command is well formed** (change log C20, decision D15, GAP C-wf): its value
fits `Value.Marshal`'s 16 bits (`invBody`'s registration facts: `client_invoke`'s commands are
well formed by the kit's input premise and the client's construction). -/
theorem cmdIs_wf (x : CmdId) (c : Cmd) :
    inv γ γc γm γl ∗ cmdIs γ x c ⊢ |={⊤}=> ⌜c.wf⌝ := by
  iintro H
  ihave Hok := cmdIs_ok x c $$ H
  imod (fupd_mask_mono (E1 := ↑spN) (E2 := ⊤) (by simp)) $$ Hok with %h
  imodintro
  ipureintro
  exact h.2.2

/-- **Checksums** (R1's dependency hash, the ideal hash): two checksums equal as `SHashesEq`
compares them, of dependency lists shorter than `2^32` (the length round hashes `int32(len)`),
have the same dependencies (as multisets). (change log C9: the length bound) -/
theorem checksum_deps (Ps1 Ps2 : List (List CmdId)) (D1 D2 : List CmdId) (cs1 cs2 : List Hash) :
    checksum Ps1 D1 cs1 ∗ checksum Ps2 D2 cs2 ∗ ⌜shashesEq cs1 cs2⌝ ∗
      ⌜D1.length < 2 ^ 32 ∧ D2.length < 2 ^ 32⌝ ⊢ ⌜D1.Perm D2⌝ := by
  iintro ⟨H1, H2, %Heq, %Hb⟩
  iapply checksum_deps_perm Ps1 Ps2 D1 D2 cs1 cs2 Hb
  iframe H1 H2
  ipureintro; exact Heq

/-- **Checksums' paths** (the ideal hash, start-marked path hashes since F2's fix): two
single-path checksums equal as `SHashesEq` compares them have equal paths. (change log C9: was
`PState.pathRel P1 P2`) -/
theorem checksum_path (P1 P2 D1 D2 : List CmdId) (cs1 cs2 : List Hash) :
    checksum [P1] D1 cs1 ∗ checksum [P2] D2 cs2 ∗ ⌜shashesEq cs1 cs2⌝ ⊢ ⌜P1 = P2⌝ :=
  checksum_path_eq P1 P2 D1 D2 cs1 cs2


/-! ### A command's result depends only on the sequence up to it (helpers) -/

theorem cmdIn_append (s u : Seq) (x : CmdId) (h : x ∈ s.map Prod.fst) :
    cmdIn (s ++ u) x = cmdIn s x := by
  induction s with
  | nil => simp at h
  | cons p s ih =>
    by_cases hp : p.1 = x
    · simp [cmdIn, hp]
    · have h' : x ∈ s.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hp
        · exact h
      have hb : (p.1 == x) = false := by simpa using hp
      have := ih h'
      simp only [cmdIn, List.cons_append, List.find?_cons, hb] at this ⊢
      exact this

theorem before_append (s u : Seq) (x : CmdId) (h : x ∈ s.map Prod.fst) :
    before (s ++ u) x = before s x := by
  induction s with
  | nil => simp at h
  | cons p s ih =>
    by_cases hp : p.1 = x
    · simp [before, hp]
    · have h' : x ∈ s.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hp
        · exact h
      have hb : (p.1 != x) = true := by simpa using hp
      have := ih h'
      simp only [before, List.cons_append, List.takeWhile_cons, hb] at this ⊢
      rw [this]

theorem resultIn_append (s u : Seq) (x : CmdId) (h : x ∈ s.map Prod.fst) :
    resultIn (s ++ u) x = resultIn s x := by
  unfold resultIn putsBefore
  rw [cmdIn_append s u x h, before_append s u x h]

/-- `resultIn s x` for `x ∈ s` depends only on the prefix of `s` up to `x`. -/
theorem resultIn_prefix {s t : Seq} {x : CmdId} (hst : s <+: t) (h : x ∈ s.map Prod.fst) :
    resultIn t x = resultIn s x := by
  obtain ⟨u, rfl⟩ := hst
  exact resultIn_append s u x h

theorem mem_of_cmdIn {s : Seq} {x : CmdId} {c : Cmd} (h : cmdIn s x = some c) :
    x ∈ s.map Prod.fst := by
  simp only [cmdIn, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, -⟩ := h
  have hm := List.mem_of_find?_eq_some hp
  have hx := List.find?_some hp
  simp only [beq_iff_eq] at hx
  exact List.mem_map.mpr ⟨p, hm, hx⟩

/-- Two lists that agree wherever both are defined are comparable. -/
theorem prefix_of_agree {α : Type} (s s' : List α)
    (h : ∀ (i : Nat) (p p' : α), s[i]? = some p → s'[i]? = some p' → p = p') : s <+: s' ∨ s' <+: s := by
  induction s generalizing s' with
  | nil => exact .inl (List.nil_prefix)
  | cons a s ih =>
    cases s' with
    | nil => exact .inr (List.nil_prefix)
    | cons a' s' =>
      have ha : a = a' := h 0 a a' rfl rfl
      subst ha
      rcases ih s' (fun i p p' h1 h2 => h (i + 1) p p' h1 h2) with h | h
      · exact .inl (List.prefix_cons_inj a |>.mpr h)
      · exact .inr (List.prefix_cons_inj a |>.mpr h)

/-- Two sequences of the same replica and ballot agree at each index. -/
theorem locLb_at (r b i : Nat) (s s' : Seq) (p p' : CmdId × Cmd) (h : s[i]? = some p)
    (h' : s'[i]? = some p') : locLb γ r b s ∗ locLb γ r b s' ⊢ ⌜p = p'⌝ := by
  obtain ⟨x, c⟩ := p
  obtain ⟨x', c'⟩ := p'
  unfold locLb
  iintro ⟨H1, H2⟩
  ihave ⟨Hl1, Hc1⟩ := BigSepL.bigSepL_lookup h $$ H1
  ihave ⟨Hl2, Hc2⟩ := BigSepL.bigSepL_lookup h' $$ H2
  ihave %hx : ⌜x = x'⌝ $$ [Hl1 Hl2]
  · unfold locAt
    iapply ghostMapElem_agree $$ Hl1 Hl2
  subst hx
  ihave %hc : ⌜c = c'⌝ $$ [Hc1 Hc2]
  · iapply cmdIs_agree
    isplitl [Hc1]
    · iexact Hc1
    · iexact Hc2
  ipureintro
  rw [hc]

/-- Two sequences of the same replica and ballot are comparable. -/
theorem locLb_agree (r r' b : Nat) (s s' : Seq) (hr : r = r') :
    locLb γ r b s ∗ locLb γ r' b s' ⊢ ⌜s <+: s' ∨ s' <+: s⌝ := by
  subst hr
  by_cases hc : s <+: s' ∨ s' <+: s
  · iintro -
    ipureintro
    exact hc
  · have : ∃ (i : Nat) (p p' : CmdId × Cmd), s[i]? = some p ∧ s'[i]? = some p' ∧ p ≠ p' := by
      apply Classical.byContradiction
      intro hn
      apply hc
      apply prefix_of_agree
      intro i p p' h1 h2
      apply Classical.byContradiction
      intro hne
      exact hn ⟨i, p, p', h1, h2, hne⟩
    obtain ⟨i, p, p', h1, h2, hne⟩ := this
    refine (locLb_at r b i s s' p p' h1 h2).trans ?_
    iintro %heq
    exact absurd heq hne

/-- Two leader replies of the same ballot and command carry the same result. -/
theorem reply_agree (rL rL' b : w32) (x : CmdId) (cs cs' : List Hash) (v v' : List w8) :
    msgOk γ γc γm (.reply rL b x cs v) ∗ msgOk γ γc γm (.reply rL' b x cs' v') ⊢ ⌜v = v'⌝ := by
  unfold msgOk
  iintro ⟨⟨%N, %fr, %l, %s, %Ps, %c, #Hcfg, #Hs, -, %H, -⟩,
    ⟨%N', %fr', %l', %s', %Ps', %c', #Hcfg', #Hs', -, %H', -⟩⟩
  obtain ⟨-, hr, hc, hv⟩ := H
  obtain ⟨-, hr', hc', hv'⟩ := H'
  ihave %hN : ⌜N = N' ∧ fr = fr' ∧ l = l'⌝ $$ []
  · iapply cfg_agree
    isplitl []
    · iexact Hcfg
    · iexact Hcfg'
  obtain ⟨rfl, -, -⟩ := hN
  ihave %hp : ⌜s <+: s' ∨ s' <+: s⌝ $$ []
  · iapply locLb_agree (rid rL) (rid rL') (bal b) s s' (hr.trans hr'.symm)
    isplitl []
    · iexact Hs
    · iexact Hs'
  ipureintro
  subst hv hv'
  rcases hp with hp | hp
  · exact (resultIn_prefix hp (mem_of_cmdIn hc)).symm
  · exact resultIn_prefix hp (mem_of_cmdIn hc')

/-- A decided command of client `cl` was registered: its sequence number is below the
client's next one. -/
theorem doneRes_seq (E : CoPset) (hE : ↑spN ⊆ E) (x : CmdId) (o : List w8) (s : Nat) :
    inv γ γc γm γl ∗ doneRes γ x o ∗ clientSeq γ x.cl s ⊢ |={E}=> ⌜x.seq.toNat < s⌝ ∗
      clientSeq γ x.cl s := by
  unfold inv doneRes clientSeq
  iintro ⟨#Hinv, #Hd, Hs⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, HS, HA, HP, HCo, HRp, HN, HH, ⟨>HD, HDs⟩, Hown, >HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, >%Hcl, HDom, Hcmds, Hconns⟩
  ihave %HlkD := ghost_map_lookup $$ HD Hd
  ihave %HlkQ := ghost_map_lookup $$ HQ Hs
  icases Hproto with (>%Hemp | ⟨%N, %fr, %l, #Hcfg, >%Hp⟩)
  · exfalso; rw [Hemp.2.2.2 x] at HlkD; cases HlkD
  obtain ⟨c, hc⟩ := dec_registered Hp.1 Hp.2.2.2.2 Hrepr.cmds HlkD
  obtain ⟨⟨n, hn, hlt⟩, -⟩ := Hcl x c hc
  rw [HlkQ] at hn
  cases hn
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD HDs Hown HQ HK HPa Hnodes HQs HDom Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    isplitr
    · iright
      iexists N, fr, l
      iframe Hcfg
      ipureintro; exact Hp
    ipureintro; exact Hcl
  imodintro
  iframe Hs
  ipureintro
  exact hlt

/-- A decided non-get's result is empty (change log C12: `Write` accepts its put with `nil`). -/
theorem doneRes_put (E : CoPset) (hE : ↑spN ⊆ E) (x : CmdId) (c : Cmd) (o : List w8)
    (hg : c.isGet = false) :
    inv γ γc γm γl ∗ doneRes γ x o ∗ cmdIs γ x c ⊢ |={E}=> ⌜o = []⌝ := by
  unfold inv doneRes cmdIs
  iintro ⟨#Hinv, #Hd, #Hc⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, HL, HS, HA, HP, HCo, HRp, HN, HH, ⟨>HD, HDs⟩, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, HCl, HDom, Hcmds, Hconns⟩
  ihave %HlkD := ghost_map_lookup $$ HD Hd
  ihave %HlkC := ghost_map_lookup $$ HC Hc
  icases Hproto with (>%Hemp | ⟨%N, %fr, %l, #Hcfg, >%Hp⟩)
  · exfalso; rw [Hemp.2.2.2 x] at HlkD; cases HlkD
  obtain ⟨b, hpc, hres⟩ := Hp.2.2.2.2 x o HlkD
  have hcx : S.cmds x = some c := by rw [← Hrepr.cmds]; exact HlkC
  have h0 : resultIn (S.ordSeq N b) x = [] :=
    Ctx.resultIn_nonget (S := S) _ ((Hp.1.loc_ok _ _).2.1) x c hpc.1 hcx hg
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD HDs Hown HQ HK HPa Hnodes HQs HCl HDom Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    iright
    iexists N, fr, l
    iframe Hcfg
    ipureintro; exact Hp
  imodintro
  ipureintro
  rw [← hres, h0]

/-- A decided command's result is unique. -/
theorem doneRes_agree (x : CmdId) (o1 o2 : List w8) :
    doneRes γ x o1 ∗ doneRes γ x o2 ⊢ ⌜o1 = o2⌝ := by
  unfold doneRes
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- **The registered commands are fewer than `2 ^ 31`** (decision D13, GAP M-c of the swift
group): from `invBody`'s client facts (ids `1 .. 6`, sequence numbers below `2 ^ 10`), any list of
distinct registered commands is shorter than `6 · 2 ^ 10 < 2 ^ 31`. -/
theorem cmds_bound {S : PState} {mC : GMap CmdId Cmd} {mQ : GMap w32 Nat}
    (hrepr : ∀ x, mC.lookup x = S.cmds x)
    (hcl : ∀ x c, mC.lookup x = some c → (∃ n, mQ.lookup x.cl = some n ∧ x.seq.toNat < n) ∧
      (c.isPut ∨ c.isGet) ∧ x.cl.toInt ≥ 1 ∧ c.val.length < 2 ^ 16 ∧ 0 ≤ x.seq.toInt ∧
      x.seq.toNat < 2 ^ 10)
    (hdom : ∀ cl n, mQ.lookup cl = some n → 1 ≤ cl.toInt ∧ cl.toInt ≤ 6)
    (l : List CmdId) (hnd : l.Nodup) (hreg : ∀ x ∈ l, S.cmds x ≠ none) : l.length < 2 ^ 31 := by
  have hb : ∀ x ∈ l, 1 ≤ x.cl.toInt ∧ x.cl.toInt ≤ 6 ∧ x.seq.toNat < 2 ^ 10 := by
    intro x hx
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hreg x hx)
    rw [← hrepr] at hc
    obtain ⟨⟨n, hn, -⟩, -, -, -, -, hs⟩ := hcl x c hc
    exact ⟨(hdom _ _ hn).1, (hdom _ _ hn).2, hs⟩
  let f : CmdId → Nat := fun x => (x.cl.toInt.toNat - 1) * 2 ^ 10 + x.seq.toNat
  have hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := by
    intro x hx y hy he
    obtain ⟨hx1, hx2, hx3⟩ := hb x hx
    obtain ⟨hy1, hy2, hy3⟩ := hb y hy
    simp only [f] at he
    have h1 : x.cl.toInt.toNat = y.cl.toInt.toNat := by
      have := Nat.div_add_mod' ((x.cl.toInt.toNat - 1) * 2 ^ 10 + x.seq.toNat) (2 ^ 10)
      omega
    have h2 : x.seq.toNat = y.seq.toNat := by omega
    have hcl : x.cl = y.cl := BitVec.toInt_inj.mp (by omega)
    have hseq : x.seq = y.seq := BitVec.eq_of_toNat_eq h2
    cases x; cases y; simp_all
  have key : ∀ l' : List CmdId, l' ⊆ l → l'.Nodup → (l'.map f).Nodup := by
    intro l' hsub hn
    induction l' with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, List.nodup_cons]
      have hn' := List.nodup_cons.mp hn
      refine ⟨fun hm => ?_, ih (fun z hz => hsub (List.mem_cons_of_mem _ hz)) hn'.2⟩
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
      have := hf y (hsub (List.mem_cons_of_mem _ hy)) a (hsub (List.mem_cons_self ..)) he
      subst this; exact hn'.1 hy
  have hnd' : (l.map f).Nodup := key l (fun _ h => h) hnd
  have hsub : l.map f ⊆ List.range (6 * 2 ^ 10) := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hn
    obtain ⟨hx1, hx2, hx3⟩ := hb x hx
    rw [List.mem_range]
    simp only [f]
    have : x.cl.toInt.toNat - 1 ≤ 5 := by omega
    have := Nat.mul_le_mul_right (2 ^ 10) this
    omega
  have := (List.subperm_of_subset hnd' hsub).length_le
  rw [List.length_map, List.length_range] at this
  omega

/-! ### The quorums' acceptance (`accept_fast`, `accept_slow`; change log C12) -/

attribute [local instance] msgOk_persistent

theorem cfg_timeless_acc (N : Nat) (fr : Bool) (l : List GoString) :
    Timeless (cfg γc γm N fr l) := by
  unfold cfg confIs memIs; infer_instance

attribute [local instance] cfg_timeless_acc

theorem doneRes_persistent_acc (x : CmdId) (o : List w8) : Persistent (doneRes γ x o) := by
  unfold doneRes; infer_instance

attribute [local instance] doneRes_persistent_acc

theorem doneRes_timeless_acc (x : CmdId) (o : List w8) : Timeless (doneRes γ x o) := by
  unfold doneRes; infer_instance

attribute [local instance] doneRes_timeless_acc

/-- The fast quorum has `N / 2 + 1` members. -/
theorem AQ_length (N b : Nat) (hN : 0 < N) : (AQ N b).length = N / 2 + 1 := by
  unfold AQ
  have hL : leaderOf N b < N := Nat.mod_lt _ hN
  obtain ⟨q, hq, hql, hLq⟩ := range_sublist_witness N (leaderOf N b) hL
  have hmem : q ∈ (combos (N / 2 + 1) (List.range N)).filter (fun q => leaderOf N b ∈ q) := by
    rw [List.mem_filter]; exact ⟨combos_complete _ _ q hq hql, by simp [hLq]⟩
  generalize hl : (combos (N / 2 + 1) (List.range N)).filter (fun q => leaderOf N b ∈ q) = lqs at hmem
  have hpos : 0 < lqs.length := List.length_pos_of_mem hmem
  have hi : (b / N) % lqs.length < lqs.length := Nat.mod_lt _ hpos
  simp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp only [Option.getD_some]
  have hin : lqs[(b / N) % lqs.length] ∈ lqs := List.getElem_mem hi
  have hin' : lqs[(b / N) % lqs.length] ∈ (combos (N / 2 + 1) (List.range N)).filter
      (fun q => leaderOf N b ∈ q) := by rw [hl]; exact hin
  rw [List.mem_filter] at hin'
  exact (combos_sub _ _ _ hin'.1).2

/-- `N / 2` distinct non-leader members of the fast quorum are all of its non-leaders. -/
theorem AQ_all (N b : Nat) (hN : 0 < N) (rs : List Nat) (hnd : rs.Nodup) (hlen : N / 2 ≤ rs.length)
    (hrs : ∀ r ∈ rs, r ∈ AQ N b ∧ r ≠ leaderOf N b) : ∀ r ∈ AQ N b, r ≠ leaderOf N b → r ∈ rs := by
  obtain ⟨⟨hAnd, -, -⟩, hLA⟩ := AQ_majority N b hN
  have hsub : rs ⊆ (AQ N b).erase (leaderOf N b) := fun r hr =>
    (List.mem_erase_of_ne (hrs r hr).2).mpr (hrs r hr).1
  have hsp := List.subperm_of_subset hnd hsub
  have hel : ((AQ N b).erase (leaderOf N b)).length = N / 2 := by
    rw [List.length_erase_of_mem hLA, AQ_length N b hN]; simp
  have hp := hsp.perm_of_length_le (by omega)
  intro r hr hne
  exact hp.mem_iff.mpr ((List.mem_erase_of_ne hne).mpr hr)

/-- A leader's sequence prefix with `x`: `x` in the order, the dependencies and the result
are the order's. -/
theorem prefix_facts {S : PState} {N : Nat} {B : Nat} {x : CmdId}
    {s : Seq} {c : Cmd} (hs : s <+: S.ordSeq N B) (hc : cmdIn s x = some c) :
    x ∈ S.ord N B ∧ depsIn (S.ordSeq N B) x = depsIn s x ∧
      resultIn (S.ordSeq N B) x = resultIn s x := by
  have hxs := mem_of_cmdIn hc
  refine ⟨?_, ?_, resultIn_prefix hs hxs⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hxs
    exact (Ctx.mem_seqOf (S := S) (hs.subset hp)).2
  · obtain ⟨u, hu⟩ := hs
    rw [← hu]; unfold depsIn; rw [cmdIn_append s u x hxs, before_append s u x hxs]

/-- **The fast path's quorum** (the model's side of `accept_fast`). -/
theorem fast_chosen_of {S : PState} {N : Nat} {fr : Bool} (hI : S.PInv N fr) {B : Nat}
    {x : CmdId} {s : Seq} {c : Cmd} {PL : List CmdId} (hs : s <+: S.ordSeq N B)
    (hc : cmdIn s x = some c) (hpL : S.path (leaderOf N B) B x = some PL) (rs : List Nat)
    (hnd : rs.Nodup) (hlen : N / 2 ≤ rs.length)
    (hrs : ∀ r ∈ rs, r ≠ leaderOf N B ∧ ∃ D, S.pre r B x = some D ∧ D.Perm (depsIn s x) ∧
      S.path r B x = some PL) (hlx : S.lexec N B x) :
    S.possiblyChosen N B x ∧ resultIn (S.ordSeq N B) x = resultIn s x := by
  obtain ⟨hx, hdeps, hres⟩ := prefix_facts hs hc
  have hN : 0 < N := by
    have hne : S.loc (leaderOf N B) B ≠ [] := fun h => by unfold PState.ord at hx; rw [h] at hx; simp at hx
    have := ((hI.loc_ok _ _).2.2 hne).1; omega
  have hall := AQ_all N B hN rs hnd hlen (fun r hr => by
    obtain ⟨hne, D, hD, -⟩ := hrs r hr
    exact ⟨(hI.pre_ok _ _ _ _ hD).1, hne⟩)
  refine ⟨⟨hx, Or.inr ⟨PL, hpL, fun r hr hne => ?_⟩, hlx⟩, hres⟩
  obtain ⟨-, D, hD, hp, hpath⟩ := hrs r (hall r hr hne)
  exact ⟨D, hD, by rw [hdeps]; exact hp, hpath⟩

/-- **The slow path's quorum** (the model's side of `accept_slow`). -/
theorem slow_chosen_of {S : PState} {N : Nat} {fr : Bool} (hI : S.PInv N fr) {B : Nat}
    {x : CmdId} {s : Seq} {c : Cmd} (hs : s <+: S.ordSeq N B)
    (hc : cmdIn s x = some c) (rs : List Nat) (hnd : rs.Nodup) (hlen : N / 2 ≤ rs.length)
    (hrs : ∀ r ∈ rs, r ≠ leaderOf N B ∧ S.acc r B x) (hlx : S.lexec N B x) :
    S.possiblyChosen N B x ∧ resultIn (S.ordSeq N B) x = resultIn s x := by
  obtain ⟨hx, -, hres⟩ := prefix_facts hs hc
  have hL : leaderOf N B < N := by
    have hne : S.loc (leaderOf N B) B ≠ [] := fun h => by unfold PState.ord at hx; rw [h] at hx; simp at hx
    exact ((hI.loc_ok _ _).2.2 hne).1
  refine ⟨⟨hx, Or.inl ⟨leaderOf N B :: rs, ⟨?_, ?_, ?_⟩, ?_⟩, hlx⟩, hres⟩
  · exact List.nodup_cons.mpr ⟨fun h => (hrs _ h).1 rfl, hnd⟩
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hL
    · exact (hI.acc_ok _ _ _ (hrs r hr).2).1
  · simp; omega
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Or.inl rfl
    · exact Or.inr (hrs r hr).2

/-- Distinct non-negative wire ids are distinct replicas. -/
theorem rid_nodup {α : Type} (l : List α) (f : α → w32) (hnd : (l.map f).Nodup)
    (hpos : ∀ a ∈ l, 0 ≤ (f a).toInt) : (l.map (fun a => rid (f a))).Nodup := by
  unfold List.Nodup at hnd ⊢
  rw [List.pairwise_map] at hnd ⊢
  refine hnd.imp_of_mem ?_
  intro a a' ha ha' hne he
  apply hne
  unfold rid at he
  have h1 := hpos a ha
  have h2 := hpos a' ha'
  have : (f a).toInt = (f a').toInt := by omega
  exact BitVec.toInt_inj.mp this

/-- A list's dependencies are at most one longer than the list. -/
theorem lkDeps_length (s : Seq) (c : Cmd) : (lkDeps s c).length ≤ s.length + 1 := by
  unfold lkDeps
  simp only
  have h1 : ((s.filter (fun p => p.2.key == c.key)).reverse.find? (fun p => p.2.isPut)).toList.length ≤ 1 := by
    cases (s.filter (fun p => p.2.key == c.key)).reverse.find? (fun p => p.2.isPut) <;> simp
  have h2 : ((((s.filter (fun p => p.2.key == c.key)).reverse.takeWhile (fun p => !p.2.isPut)).map
      Prod.fst).reverse).length ≤ s.length := by
    simp only [List.length_reverse, List.length_map]
    exact Nat.le_trans (List.takeWhile_sublist _).length_le
      (by rw [List.length_reverse]; exact List.length_filter_le _ _)
  split <;> simp only [List.length_append, List.length_map] at * <;> omega

theorem depsIn_length (s : Seq) (x : CmdId) : (depsIn s x).length ≤ s.length + 1 := by
  unfold depsIn
  split
  · exact Nat.le_trans (lkDeps_length _ _) (by
      have := (List.takeWhile_sublist (fun p : CmdId × Cmd => p.1 != x) (l := s)).length_le
      unfold before; omega)
  · simp


omit [GoGlobalContext] G in
theorem acc_seqOf_map_fst (S : PState) (s : Seq) (h : ∀ p ∈ s, S.cmds p.1 = some p.2) :
    S.seqOf (s.map Prod.fst) = s := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    have hp := h p (by simp)
    have ih' := ih (fun q hq => h q (by simp [hq]))
    simp only [PState.seqOf] at ih' ⊢
    simp [List.filterMap_cons, hp, ih']

/-- What a `locLb` says against the authorities: its ids are a prefix of the replica's
sequence, its commands registered (as Proof/swift/Steps.lean's `locLb_lookups`,
`locLb_prefix`). -/
theorem acc_locLb (L b : Nat) (s : Seq) {S : PState} {mC : GMap CmdId Cmd}
    {mL : GMap (Nat × Nat × Nat) CmdId} (hC : ∀ x, mC.lookup x = S.cmds x)
    (hL : ∀ r b i, mL.lookup (r, b, i) = (S.loc r b)[i]?) :
    ghostMapAuth γ.loc 1 mL ∗ ghostMapAuth γ.cmds 1 mC ∗ locLb γ L b s ⊢
    ⌜s.map Prod.fst <+: S.loc L b ∧ s <+: S.seqOf (S.loc L b)⌝ := by
  have key : ghostMapAuth γ.loc 1 mL ∗ ghostMapAuth γ.cmds 1 mC ∗ locLb γ L b s ⊢
      ⌜∀ i p, s[i]? = some p → mL.lookup (L, b, i) = some p.1 ∧ mC.lookup p.1 = some p.2⌝ := by
    refine (BI.forall_intro fun i => BI.forall_intro fun p => ?_).trans
      ((BI.forall_mono fun _ => BI.pure_forall.2).trans BI.pure_forall.2)
    by_cases hs : s[i]? = some p
    · unfold locLb
      iintro ⟨HL, HC, #Hlb⟩
      ihave ⟨#Hl, #Hc⟩ := (BigSepL.bigSepL_lookup hs) $$ Hlb
      unfold locAt cmdIs
      ihave %H1 := ghost_map_lookup $$ HL Hl
      ihave %H2 := ghost_map_lookup $$ HC Hc
      ipureintro
      exact fun _ => ⟨H1, H2⟩
    · exact BI.pure_intro (fun h => absurd h hs)
  refine key.trans (BI.pure_mono fun h => ?_)
  have h1 : s.map Prod.fst <+: S.loc L b := by
    rw [List.prefix_iff_eq_take, List.length_map]
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_take]
    by_cases hi : i < s.length
    · rw [if_pos hi, List.getElem?_map, List.getElem?_eq_getElem hi]
      have := (h i (s[i]'hi) (List.getElem?_eq_getElem hi)).1
      rw [hL] at this; rw [this]; rfl
    · rw [if_neg hi]; simp; omega
  refine ⟨h1, ?_⟩
  obtain ⟨t, ht⟩ := h1
  rw [← ht, PState.seqOf, List.filterMap_append]
  have : (s.map Prod.fst).filterMap (fun x => (S.cmds x).map (x, ·)) = s :=
    acc_seqOf_map_fst S s (fun p hp => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      rw [← hC]; exact (h i _ (by simp [hi])).2)
  rw [this]; exact List.prefix_append _ _

/-- A checksum has one hash per path, then the dependencies' hash. -/
theorem checksum_len (Ps : List (List CmdId)) (D : List CmdId) (cs : List Hash) :
    checksum Ps D cs ⊢ ⌜cs.length = Ps.length + 1⌝ := by
  unfold checksum
  iintro ⟨%hs, %d, %Hc, Hp, -⟩
  ihave %Hl := pathHashes_len $$ Hp
  ipureintro; subst Hc; simp [Hl]

/-- The fast acks' checksums have one path. -/
theorem fast_acks_len (b : w32) (x : CmdId) (acks : List (w32 × List Hash)) :
    ([∗list] a ∈ acks, msgOk γ γc γm (.fastAckClient a.1 b x a.2)) ⊢
      ⌜∀ a ∈ acks, a.2.length = 2⌝ := by
  refine (BI.forall_intro fun a => ?_).trans BI.pure_forall.2
  by_cases ha : a ∈ acks
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
    iintro HL
    ihave Ha := (BigSepL.bigSepL_lookup hi) $$ HL
    unfold msgOk
    icases Ha with ⟨%D, %P, %c, -, -, -, Hck, -⟩
    ihave %Hl := checksum_len [P] D a.2 $$ Hck
    ipureintro; exact fun _ => Hl
  · exact BI.pure_intro (fun h => absurd h ha)

/-- The fast acks against the authorities: each sender pre-accepted the command with the
leader's dependencies and path (equal checksums). -/
theorem fast_acks_lookups (mP : GMap (Nat × Nat × CmdId) (List CmdId))
    (mPa : GMap (Nat × Nat × CmdId) (List CmdId)) (b : w32) (x : CmdId) (PL DL : List CmdId)
    (csL : List Hash) (acks : List (w32 × List Hash)) (heq : ∀ a ∈ acks, shashesEq csL a.2)
    (hbL : DL.length < 2 ^ 32)
    (hb : ∀ r D, mP.lookup (r, bal b, x) = some D → D.length < 2 ^ 32) :
    ghostMapAuth γ.pre 1 mP ∗ ghostMapAuth γ.path 1 mPa ∗ checksum [PL] DL csL ∗
      ([∗list] a ∈ acks, msgOk γ γc γm (.fastAckClient a.1 b x a.2)) ⊢
    ⌜∀ a ∈ acks, wireOk a.1 b ∧ ∃ D, mP.lookup (rid a.1, bal b, x) = some D ∧ D.Perm DL ∧
      mPa.lookup (rid a.1, bal b, x) = some PL⌝ := by
  refine (BI.forall_intro fun a => ?_).trans BI.pure_forall.2
  by_cases ha : a ∈ acks
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
    iintro ⟨HP, HPa, #Hck, HL⟩
    ihave Ha := (BigSepL.bigSepL_lookup hi) $$ HL
    unfold msgOk
    icases Ha with ⟨%D, %P, %c, %Hw, #Hpre, #Hpath, #Hck', -⟩
    unfold preacc pathIs
    ihave %H1 := ghost_map_lookup $$ HP Hpre
    ihave %H2 := ghost_map_lookup $$ HPa Hpath
    ihave %Hpp : ⌜PL = P⌝ $$ []
    · iapply checksum_path PL P DL D csL a.2
      isplitl []
      · iexact Hck
      isplitl []
      · iexact Hck'
      ipureintro; exact heq a ha
    ihave %Hdp : ⌜DL.Perm D⌝ $$ []
    · iapply checksum_deps [PL] [P] DL D csL a.2
      isplitl []
      · iexact Hck
      isplitl []
      · iexact Hck'
      isplitl []
      · ipureintro; exact heq a ha
      ipureintro; exact ⟨hbL, hb _ D H1⟩
    ipureintro
    intro _
    subst Hpp
    exact ⟨Hw, D, H1, Hdp.symm, H2⟩
  · exact BI.pure_intro (fun h => absurd h ha)

/-- The slow acks against the authorities: each sender accepted the command. -/
theorem slow_acks_lookups (mA : GMap (Nat × Nat × CmdId) Unit) (b : w32) (x : CmdId)
    (rs : List w32) :
    ghostMapAuth γ.acc 1 mA ∗ ([∗list] r ∈ rs, msgOk γ γc γm (.lightSlowAck ⟨r, b, x⟩)) ⊢
    ⌜∀ r ∈ rs, wireOk r b ∧ (mA.lookup (rid r, bal b, x)).isSome⌝ := by
  refine (BI.forall_intro fun r => ?_).trans BI.pure_forall.2
  by_cases hr : r ∈ rs
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
    iintro ⟨HA, HL⟩
    ihave Ha := (BigSepL.bigSepL_lookup hi) $$ HL
    unfold msgOk
    icases Ha with ⟨%Hw, #Hacc, -⟩
    unfold accepted
    ihave %H1 := ghost_map_lookup $$ HA Hacc
    ipureintro
    intro _
    exact ⟨Hw, by simp [H1]⟩
  · exact BI.pure_intro (fun h => absurd h hr)

/-- A leader's reply's witness, unfolded. -/
theorem reply_body (r b : w32) (x : CmdId) (cs : List Hash) (v : List w8) :
    msgOk γ γc γm (.reply r b x cs v) ⊢ iprop(∃ (N : Nat) (fr : Bool) (l : List GoString) (s : Seq)
        (Ps : List (List CmdId)) (c : Cmd),
      cfg γc γm N fr l ∗ locLb γ (rid r) (bal b) s ∗ checksum Ps (depsIn s x) cs ∗
      ⌜wireOk r b ∧ rid r = leaderOf N (bal b) ∧ cmdIn s x = some c ∧ v = resultIn s x⌝ ∗
      (⌜Ps = []⌝ ∨ ∃ P, ⌜Ps = [P]⌝ ∗ pathIs γ (rid r) (bal b) x P) ∗
      execW γ (rid r) (bal b) x) := by
  unfold msgOk; exact .rfl

/-- D33: the leader's execution witness against the authorities. -/
theorem execW_lookups (mS : GMap Nat SyncMsg) (mP : GMap (Nat × Nat × CmdId) (List CmdId))
    (L b : Nat) (E : List CmdId) :
    ghostMapAuth γ.sync 1 mS ∗ ghostMapAuth γ.pre 1 mP ∗
      ([∗list] y ∈ E, (∃ M, syncIs γ b M ∗ ⌜y ∈ syncOrder M⌝) ∨
        (∃ D, preacc γ L b y D ∗ ⌜∀ d ∈ D, d ∈ E⌝)) ⊢
    ⌜∀ y ∈ E, (∃ M, mS.lookup b = some M ∧ y ∈ syncOrder M) ∨
      ∃ D, mP.lookup (L, b, y) = some D ∧ ∀ d ∈ D, d ∈ E⌝ := by
  refine (BI.forall_intro fun y => ?_).trans BI.pure_forall.2
  by_cases hy : y ∈ E
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hy
    iintro ⟨HS, HP, HL⟩
    ihave Ha := (BigSepL.bigSepL_lookup hi) $$ HL
    icases Ha with (⟨%M, #HM, %hM⟩ | ⟨%D, #HD, %hD⟩)
    · unfold syncIs
      ihave %H1 := ghost_map_lookup $$ HS HM
      ipureintro; intro _; exact Or.inl ⟨M, H1, hM⟩
    · unfold preacc
      ihave %H1 := ghost_map_lookup $$ HP HD
      ipureintro; intro _; exact Or.inr ⟨D, H1, hD⟩
  · exact BI.pure_intro (fun h => absurd h hy)

/-- D33: a leader's execution witness gives the model's execution. -/
theorem execW_lexec {S : PState} {N : Nat} {mC : GMap CmdId Cmd} {mL : GMap (Nat × Nat × Nat) CmdId}
    {mS : GMap Nat SyncMsg} {mA : GMap (Nat × Nat × CmdId) Unit}
    {mP : GMap (Nat × Nat × CmdId) (List CmdId)} {mCo : GMap (Nat × Nat × CmdId) Unit}
    {mR : GMap (Nat × Nat) Report} {mPa : GMap (Nat × Nat × CmdId) (List CmdId)}
    (hrepr : Repr S mC mL mS mA mP mCo mR mPa) (L b : Nat) (x : CmdId) (hL : L = leaderOf N b) :
    ghostMapAuth γ.sync 1 mS ∗ ghostMapAuth γ.pre 1 mP ∗ execW γ L b x ⊢ ⌜S.lexec N b x⌝ := by
  unfold execW
  iintro ⟨HS, HP, %E, %hxE, HE⟩
  ihave %Hlk := execW_lookups (γ := γ) mS mP L b E $$ [HS HP HE]
  · iframe HS HP HE
  ipureintro
  refine ⟨E, hxE, fun y hy => ?_⟩
  rcases Hlk y hy with ⟨M, hM, hyM⟩ | ⟨D, hD, hDE⟩
  · left
    show y ∈ ((S.sync b).map syncOrder).getD []
    rw [← hrepr.sync, hM]; exact hyM
  · right; refine ⟨D, ?_, hDE⟩; rw [← hL, ← hrepr.pre]; exact hD

/-- A decided result from the model's fact: inserted, or already there (`result_agree`). -/
theorem dec_add {S : PState} {N : Nat} {fr : Bool} (hI : S.PInv N fr)
    {mD : GMap CmdId (List w8)} (hdec : decOk N S mD) (x : CmdId) (v : List w8) (B : Nat)
    (hB : S.possiblyChosen N B x) (hres : resultIn (S.ordSeq N B) x = v) :
    ghostMapAuth γ.dec 1 mD ∗ ([∗map] y ↦ w ∈ mD, doneRes γ y w) ⊢ |==> ∃ mD',
      ghostMapAuth γ.dec 1 mD' ∗ ([∗map] y ↦ w ∈ mD', doneRes γ y w) ∗ ⌜decOk N S mD'⌝ ∗
      doneRes γ x v := by
  unfold doneRes
  iintro ⟨HD, HDs⟩
  cases hlk : mD.lookup x with
  | some v0 =>
    obtain ⟨b0, h0, hres0⟩ := hdec x v0 hlk
    have hv : v0 = v := by rw [← hres0, ← hres]; exact PState.result_agree hI h0 hB
    subst hv
    icases (BigSepM.bigSepM_lookup_acc (show Iris.Std.PartialMap.get? mD x = some v0 from hlk)).1
      $$ HDs with ⟨#Hd, HDs⟩
    ihave HDs := HDs $$ Hd
    imodintro
    iexists mD
    isplitl [HD]
    · iexact HD
    isplitl [HDs]
    · iexact HDs
    isplitl []
    · ipureintro; exact hdec
    iexact Hd
  | none =>
    imod ghost_map_insert_persist x v hlk $$ HD with ⟨HD, #Hd⟩
    ihave HDs := (BigSepM.bigSepM_insert (Φ := fun y w => ghostMapElem γ.dec y .discard w) (show Iris.Std.PartialMap.get? mD x = none from hlk)).2
      $$ [HDs]
    · isplitl []
      · iexact Hd
      · iexact HDs
    imodintro
    iexists mD.insert x v
    isplitl [HD]
    · iexact HD
    isplitl [HDs]
    · iexact HDs
    isplitl []
    · ipureintro
      intro y w hy
      rw [GMap.lookup_insert_eq_iff] at hy
      by_cases hxy : x = y
      · subst hxy; rw [if_pos rfl] at hy; cases hy; exact ⟨B, hB, hres⟩
      · rw [if_neg hxy] at hy; exact hdec y w hy
    iexact Hd

/-- A replica's sequences are shorter than `2 ^ 31` (D13's bound). -/
theorem loc_bound {S : PState} {N : Nat} {fr : Bool} (hI : S.PInv N fr) {mC : GMap CmdId Cmd}
    {mQ : GMap w32 Nat} (hrepr : ∀ x, mC.lookup x = S.cmds x)
    (hcl : ∀ x c, mC.lookup x = some c → (∃ n, mQ.lookup x.cl = some n ∧ x.seq.toNat < n) ∧
      (c.isPut ∨ c.isGet) ∧ x.cl.toInt ≥ 1 ∧ c.val.length < 2 ^ 16 ∧ 0 ≤ x.seq.toInt ∧
      x.seq.toNat < 2 ^ 10)
    (hdom : ∀ cl n, mQ.lookup cl = some n → 1 ≤ cl.toInt ∧ cl.toInt ≤ 6) (r b : Nat) :
    (S.loc r b).length < 2 ^ 31 :=
  cmds_bound hrepr hcl hdom _ (hI.loc_ok r b).1 (hI.loc_ok r b).2.1

/-- A pre-acceptance's dependencies are shorter than `2 ^ 32`. -/
theorem pre_bound {S : PState} {N : Nat} {fr : Bool} (hI : S.PInv N fr)
    (hloc : ∀ r b, (S.loc r b).length < 2 ^ 31) (r b : Nat) (x : CmdId) (D : List CmdId)
    (h : S.pre r b x = some D) : D.length < 2 ^ 32 := by
  obtain ⟨-, -, -, hD, -⟩ := hI.pre_ok _ _ _ _ h
  subst hD
  have h1 := depsIn_length (S.seqOf (S.loc r b)) x
  have h2 : (S.seqOf (S.loc r b)).length ≤ (S.loc r b).length := List.length_filterMap_le _ _
  have h3 := hloc r b
  omega

/-- **The fast path** (`handleFastAndSlowAcks` on `fastPathH`): the leader's `MReply` of ballot
`b` and the `MFastAckClient`s of `b` of `N / 2` distinct replicas other than `b`'s leader (N4:
the client ignores the leader's own acks), each checksum `SHashesEq` the leader's: the command
is decided with the leader's result (change log C12: `doneRes` is "possibly chosen with the
leader's result",: the quorum's witnesses unpacked into `fastChosen`, `sp.fast_chosen_of`; with no ack
(`N ≤ 1`) the leader alone is a majority). -/
theorem accept_fast (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (rL b : w32) (x : CmdId) (csL : List Hash) (v : List w8) (acks : List (w32 × List Hash)) :
    ⌜(acks.map Prod.fst).Nodup ∧ N / 2 ≤ acks.length ∧
      ∀ a ∈ acks, shashesEq csL a.2 ∧ rid a.1 ≠ leaderOf N (bal b)⌝ ∗
      inv γ γc γm γl ∗ cfg γc γm N fr l ∗ msgOk γ γc γm (.reply rL b x csL v) ∗
      ([∗list] a ∈ acks, msgOk γ γc γm (.fastAckClient a.1 b x a.2)) ⊢
    |={E}=> doneRes γ x v := by
  unfold inv
  iintro ⟨%Hacks, #Hinv, #Hcfg, #Hrep, #Hl⟩
  ihave ⟨%N', %fr', %l', %s, %Ps, %c, #Hcfg', #Hs, #Hcs, %Hrp, #HPs, #HX⟩ := reply_body rL b x csL v $$ Hrep
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, >HL, >HS, HA, >HP, HCo, HRp, HN, HH, ⟨>HD, >HDs⟩, Hown, HQ, HK, >HPa, >%Hrepr, Hnodes, Hproto, HQs, >%Hcl, >%HDom, Hcmds, Hconns⟩
  obtain ⟨-, hrL, hcx, hv⟩ := Hrp
  ihave %HN' : ⌜N = N' ∧ fr = fr' ∧ l = l'⌝ $$ []
  · iapply cfg_agree
    isplitl []
    · iexact Hcfg
    · iexact Hcfg'
  obtain ⟨e1, -, -⟩ := HN'
  subst e1
  ihave %Hpre := acc_locLb (γ := γ) (rid rL) (bal b) s Hrepr.cmds Hrepr.loc $$ [HL HC Hs]
  · iframe HL HC Hs
  icases Hproto with (>%Hemp | ⟨%N0, %fr0, %l0, >#Hcfg0, >%Hp⟩)
  · iexfalso; ipureintro
    have hx := Hpre.1.subset (mem_of_cmdIn hcx)
    rw [Hemp.1.1] at hx; simp at hx
  ihave %HN0 : ⌜N = N0 ∧ fr = fr0 ∧ l = l0⌝ $$ []
  · iapply cfg_agree
    isplitl []
    · iexact Hcfg
    · iexact Hcfg0
  obtain ⟨e1, e2, e3⟩ := HN0
  subst e1 e2 e3
  obtain ⟨hI, hN, hR, hH, hDok⟩ := Hp
  have hs : s <+: S.ordSeq N (bal b) := by
    unfold PState.ordSeq PState.ord; rw [← hrL]; exact Hpre.2
  ihave %Hlx := execW_lexec (γ := γ) (N := N) Hrepr (rid rL) (bal b) x hrL $$ [HS HP HX]
  · iframe HS HP HX
  have hlocb : ∀ r b, (S.loc r b).length < 2 ^ 31 := loc_bound hI Hrepr.cmds Hcl HDom.2
  have hsL : s.length < 2 ^ 31 := by
    have h1 := Hpre.1.length_le; simp only [List.length_map] at h1
    have h2 := hlocb (rid rL) (bal b); omega
  ihave %Hlen := fast_acks_len (γ := γ) (γc := γc) (γm := γm) b x acks $$ Hl
  ihave %HcsL := checksum_len Ps (depsIn s x) csL $$ Hcs
  ihave %hB : ⌜∃ B, S.possiblyChosen N B x ∧ resultIn (S.ordSeq N B) x = v⌝ $$ [HP HPa]
  · by_cases hne : acks = []
    · ipureintro
      have hc := slow_chosen_of hI hs hcx [] List.nodup_nil
        (by have := Hacks.2.1; rw [hne] at this; simpa using this) (by simp) Hlx
      exact ⟨bal b, hc.1, hc.2.trans hv.symm⟩
    obtain ⟨a0, ha0⟩ := List.exists_mem_of_ne_nil acks hne
    have hPs1 : Ps.length = 1 := by
      have h1 := Hlen a0 ha0; have h2 := (Hacks.2.2 a0 ha0).1.1; omega
    icases HPs with (%hP0 | ⟨%PL, %hPL, #HPL⟩)
    · iexfalso; ipureintro; rw [hP0] at hPs1; simp at hPs1
    subst hPL
    ihave %Hlk := fast_acks_lookups (γ := γ) (γc := γc) (γm := γm) mP mPa b x PL (depsIn s x) csL
      acks (fun a ha => (Hacks.2.2 a ha).1)
      (by have := depsIn_length s x; omega)
      (fun r D h => pre_bound hI hlocb r _ x D (by rw [← Hrepr.pre]; exact h)) $$ [HP HPa Hcs Hl]
    · iframe HP HPa Hcs Hl
    unfold pathIs
    ihave %HlkL := ghost_map_lookup $$ HPa HPL
    ipureintro
    have hpL : S.path (leaderOf N (bal b)) (bal b) x = some PL := by
      rw [← hrL, ← Hrepr.path]; exact HlkL
    have hc := fast_chosen_of hI hs hcx hpL (acks.map (fun a => rid a.1))
      (rid_nodup acks Prod.fst Hacks.1 (fun a ha => (Hlk a ha).1.1)) (by simpa using Hacks.2.1)
      (by
        intro r hr
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        obtain ⟨-, D, hD, hDp, hpa⟩ := Hlk a ha
        exact ⟨(Hacks.2.2 a ha).2, D, by rw [← Hrepr.pre]; exact hD, hDp,
          by rw [← Hrepr.path]; exact hpa⟩) Hlx
    exact ⟨bal b, hc.1, hc.2.trans hv.symm⟩
  obtain ⟨B, hBc, hBr⟩ := hB
  imod dec_add (γ := γ) hI hDok x v B hBc hBr $$ [HD HDs] with ⟨%mD', HD, HDs, %Hdec', #Hd⟩
  · isplitl [HD]
    · iexact HD
    · iexact HDs
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD HDs Hown HQ HK HPa Hnodes HQs Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD', mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    isplitr
    · iright
      iexists N, fr, l
      iframe Hcfg
      ipureintro; exact ⟨hI, hN, hR, hH, Hdec'⟩
    isplitr
    · ipureintro; exact Hcl
    ipureintro; exact HDom
  imodintro
  iexact Hd


/-- **The slow path** (`handleFastAndSlowAcks` on `slowPathH`): the leader's `MReply` of ballot
`b` and `MLightSlowAck`s of `b` of `N / 2` distinct replicas other than `b`'s leader (N4): the
command is decided with the leader's result (change log C12: `doneRes` is "possibly chosen with
the leader's result",: the leader and the acceptors are a majority, `sp.slow_chosen_of`). -/
theorem accept_slow (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (rL b : w32) (x : CmdId) (csL : List Hash) (v : List w8) (rs : List w32) :
    ⌜rs.Nodup ∧ N / 2 ≤ rs.length ∧ ∀ r ∈ rs, rid r ≠ leaderOf N (bal b)⌝ ∗
      inv γ γc γm γl ∗ cfg γc γm N fr l ∗ msgOk γ γc γm (.reply rL b x csL v) ∗
      ([∗list] r ∈ rs, msgOk γ γc γm (.lightSlowAck ⟨r, b, x⟩)) ⊢
    |={E}=> doneRes γ x v := by
  unfold inv
  iintro ⟨%Hrs, #Hinv, #Hcfg, #Hrep, #Hl⟩
  ihave ⟨%N', %fr', %l', %s, %Ps, %c, #Hcfg', #Hs, #Hcs, %Hrp, #HPs, #HX⟩ := reply_body rL b x csL v $$ Hrep
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, >HL, >HS, >HA, >HP, HCo, HRp, HN, HH, ⟨>HD, >HDs⟩, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, >%Hcl, >%HDom, Hcmds, Hconns⟩
  obtain ⟨-, hrL, hcx, hv⟩ := Hrp
  ihave %HN' : ⌜N = N' ∧ fr = fr' ∧ l = l'⌝ $$ []
  · iapply cfg_agree
    isplitl []
    · iexact Hcfg
    · iexact Hcfg'
  obtain ⟨e1, -, -⟩ := HN'
  subst e1
  ihave %Hpre := acc_locLb (γ := γ) (rid rL) (bal b) s Hrepr.cmds Hrepr.loc $$ [HL HC Hs]
  · iframe HL HC Hs
  icases Hproto with (>%Hemp | ⟨%N0, %fr0, %l0, >#Hcfg0, >%Hp⟩)
  · iexfalso; ipureintro
    have hx := Hpre.1.subset (mem_of_cmdIn hcx)
    rw [Hemp.1.1] at hx; simp at hx
  ihave %HN0 : ⌜N = N0 ∧ fr = fr0 ∧ l = l0⌝ $$ []
  · iapply cfg_agree
    isplitl []
    · iexact Hcfg
    · iexact Hcfg0
  obtain ⟨e1, e2, e3⟩ := HN0
  subst e1 e2 e3
  obtain ⟨hI, hN, hR, hH, hDok⟩ := Hp
  have hs : s <+: S.ordSeq N (bal b) := by
    unfold PState.ordSeq PState.ord; rw [← hrL]; exact Hpre.2
  ihave %Hlk := slow_acks_lookups (γ := γ) (γc := γc) (γm := γm) mA b x rs $$ [HA Hl]
  · iframe HA Hl
  ihave %Hlx := execW_lexec (γ := γ) (N := N) Hrepr (rid rL) (bal b) x hrL $$ [HS HP HX]
  · iframe HS HP HX
  have hc := slow_chosen_of hI hs hcx (rs.map (fun r => rid r))
    (rid_nodup rs (fun r => r) (by simpa using Hrs.1) (fun r hr => (Hlk r hr).1.1))
    (by simpa using Hrs.2.1)
    (by
      intro r' hr'
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
      exact ⟨Hrs.2.2 r hr, (Hrepr.acc _ _ _).mp (Hlk r hr).2⟩) Hlx
  imod dec_add (γ := γ) hI hDok x v (bal b) hc.1 (hc.2.trans hv.symm) $$ [HD HDs]
    with ⟨%mD', HD, HDs, %Hdec', #Hd⟩
  · isplitl [HD]
    · iexact HD
    · iexact HDs
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD HDs Hown HQ HK HPa Hnodes HQs Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD', mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    isplitr
    · iright
      iexists N, fr, l
      iframe Hcfg
      ipureintro; exact ⟨hI, hN, hR, hH, Hdec'⟩
    isplitr
    · ipureintro; exact Hcl
    ipureintro; exact HDom
  imodintro
  iexact Hd

/-! ### The leader's numbering (change log C22, M3) -/

/-- `numOk` only depends on the sequences as prefixes: it is kept by an extension. -/
theorem numOk_mono {N : Nat} {l : List GoString} {loc loc' : Nat → Nat → List CmdId}
    {mNu : GMap (Nat × Option (Nat × CmdId)) w64} (h : numOk N l loc mNu)
    (hle : ∀ r b, loc r b <+: loc' r b) : numOk N l loc' mNu := by
  intro r b x s hx
  obtain ⟨hmem, hld⟩ := h r b x s hx
  obtain ⟨t, ht⟩ := hle r b
  have hidx : ∀ z, z ∈ loc r b → (loc' r b).idxOf z = (loc r b).idxOf z := fun z hz => by
    rw [← ht, List.idxOf_append, if_pos hz]
  refine ⟨by rw [← ht]; exact List.mem_append_left _ hmem, fun hL => ?_⟩
  obtain ⟨h0, hn, hord⟩ := hld hL
  refine ⟨h0, hn, fun y s' hy => ?_⟩
  rw [hidx x hmem, hidx y (h r b y s' hy).1]
  exact hord y s' hy

theorem locSum_mono {f g : Nat → Nat} (h : ∀ b, f b ≤ g b) : ∀ n, locSum f n ≤ locSum g n
  | 0 => Nat.le_refl _
  | n + 1 => by unfold locSum; have := locSum_mono h n; have := h n; omega

/-- A sum of `n` terms below `M`. -/
theorem locSum_le {f : Nat → Nat} {M : Nat} (h : ∀ b, f b ≤ M) : ∀ n, locSum f n ≤ n * M
  | 0 => by simp [locSum]
  | n + 1 => by
    unfold locSum; have := locSum_le h n; have := h n
    rw [Nat.succ_mul]; omega

/-- One term grown by one (below `n`): the sum grows by at least one. -/
theorem locSum_succ {f g : Nat → Nat} (h : ∀ b, f b ≤ g b) (b : Nat) (hb : f b + 1 ≤ g b) :
    ∀ n, b < n → locSum f n + 1 ≤ locSum g n
  | 0, h0 => absurd h0 (Nat.not_lt_zero _)
  | n + 1, h1 => by
    unfold locSum
    by_cases e : b = n
    · subst e; have := locSum_mono h b; omega
    · have := locSum_succ h b hb n (by omega); have := h n; omega

/-- The count only depends on the sequences as prefixes. -/
theorem numCnt_mono {l : List GoString} {loc loc' : Nat → Nat → List CmdId}
    {mNu : GMap (Nat × Option (Nat × CmdId)) w64} (h : numCnt l loc mNu)
    (hle : ∀ r b, loc r b <+: loc' r b) : numCnt l loc' mNu := by
  intro r k n hk hn
  refine Int.le_trans (h r k n hk hn) ?_
  exact_mod_cast locSum_mono (fun b => (hle r b).length_le) _

/-- The count's bound: with sequences shorter than `2 ^ 31`, the sum is below `2 ^ 62`. -/
theorem locSum_bound {loc : Nat → Nat → List CmdId} (r : Nat)
    (hlen : ∀ b, (loc r b).length < 2 ^ 31) :
    locSum (fun b => (loc r b).length) (2 ^ 31) ≤ 2 ^ 62 := by
  have := locSum_le (f := fun b => (loc r b).length) (M := 2 ^ 31)
    (fun b => Nat.le_of_lt (hlen b)) (2 ^ 31)
  omega

/-- The key-`k` ids of a list of pairs up to `x` (included) are a prefix of those up to `y` when
`x` comes first (helper of `keyPrefix_prefix`). -/
theorem keyIds_prefix (k : w64) (x y : CmdId) (cx cy : Cmd) :
    ∀ (U : Seq), x ∈ U.map Prod.fst → (∀ q ∈ U, q.1 = x → q.2 = cx) →
      (∀ q ∈ U, q.1 = y → q.2 = cy) → cx.key = k → cy.key = k →
      (U.map Prod.fst).idxOf x ≤ (U.map Prod.fst).idxOf y →
      ((U.takeWhile (·.1 != x)).filter (·.2.key == k)).map Prod.fst ++ [x] <+:
        ((U.takeWhile (·.1 != y)).filter (·.2.key == k)).map Prod.fst ++ [y]
  | [], hx, _, _, _, _, _ => by simp at hx
  | p :: U, hx, hcx, hcy, hkx, hky, hle => by
    by_cases hpx : p.1 = x
    · have hq := hcx p (List.mem_cons_self) hpx
      by_cases hpy : p.1 = y
      · rw [← hpx, ← hpy]; exact List.prefix_refl _
      · have e1 : (p.1 != y) = true := by simpa using hpy
        have e2 : (p.1 != x) = false := by simpa using hpx
        have hL : (((p :: U).takeWhile (·.1 != x)).filter (·.2.key == k)).map Prod.fst = [] := by
          simp [e2]
        have hR : (((p :: U).takeWhile (·.1 != y)).filter (·.2.key == k)).map Prod.fst =
            x :: ((U.takeWhile (·.1 != y)).filter (·.2.key == k)).map Prod.fst := by
          have hxy : x ≠ y := fun h => hpy (hpx.trans h)
          simp [hq, hkx, hpx, hxy]
        rw [hL, hR]
        exact ⟨_, rfl⟩
    · have hpy : p.1 ≠ y := by
        intro e
        simp only [List.map_cons, List.idxOf_cons] at hle
        rw [e] at hle hpx
        simp at hle
        first | exact hpx hle | exact hpx hle.symm
      have hx' : x ∈ U.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at hx
        exact hx.resolve_left (fun e => hpx e.symm)
      have hle' : (U.map Prod.fst).idxOf x ≤ (U.map Prod.fst).idxOf y := by
        simp only [List.map_cons, List.idxOf_cons] at hle
        have h1 : (p.1 == x) = false := by simpa using hpx
        have h2 : (p.1 == y) = false := by simpa using hpy
        rw [h1, h2] at hle
        simpa using hle
      have ih := keyIds_prefix k x y cx cy U hx' (fun q hq => hcx q (List.mem_cons_of_mem _ hq))
        (fun q hq => hcy q (List.mem_cons_of_mem _ hq)) hkx hky hle'
      have e1 : (p.1 != x) = true := by simpa using hpx
      have e2 : (p.1 != y) = true := by simpa using hpy
      simp only [List.takeWhile_cons, e1, e2, if_true, List.filter_cons]
      split
      · simp only [List.map_cons, List.cons_append]
        exact (List.prefix_cons_inj _).mpr ih
      · exact ih

/-- **The leader's paths follow its order**: the leader's path of `x` (its key's commands up to
`x`) is a prefix of its path of a later `y` of the key (helper of `num_paths`). -/
theorem keyPrefix_prefix {S : PState} {N : Nat} {fr : Bool} (hI : S.PInv N fr) (r b : Nat)
    (x y : CmdId) (cx cy : Cmd) (hcx : S.cmds x = some cx) (hcy : S.cmds y = some cy)
    (hk : cx.key = cy.key) (hx : x ∈ S.loc r b) (hy : y ∈ S.loc r b) (hxb : x ∉ S.base b)
    (hyb : y ∉ S.base b) (hle : (S.loc r b).idxOf x ≤ (S.loc r b).idxOf y) :
    S.keyPrefix r b x <+: S.keyPrefix r b y := by
  have hbase : S.loc r b = S.base b ++ (S.loc r b).drop (S.base b).length := by
    have hne : S.loc r b ≠ [] := List.ne_nil_of_mem hx
    obtain ⟨-, hreg, hrest⟩ := hI.loc_ok r b
    by_cases hb : b > 0
    · obtain ⟨t, ht⟩ := ((hrest hne).2.2 hb).2
      conv => lhs; rw [← ht]
      rw [← ht, List.drop_left]
    · have : S.base b = [] := by
        unfold PState.base
        cases h : S.sync b with
        | none => rfl
        | some M => exact absurd (hI.sync_ok b M h).1 hb
      rw [this]; simp
  generalize hT : (S.loc r b).drop (S.base b).length = T at hbase
  have hreg : ∀ z ∈ T, S.cmds z ≠ none := fun z hz =>
    (hI.loc_ok r b).2.1 z (List.mem_of_mem_drop (by rw [hT]; exact hz))
  have hmapT : (S.seqOf T).map Prod.fst = T := by
    unfold PState.seqOf
    clear hT hbase
    induction T with
    | nil => rfl
    | cons z T ih =>
      have hz := hreg z (List.mem_cons_self)
      obtain ⟨cz, hcz⟩ := Option.ne_none_iff_exists'.mp hz
      simp only [List.filterMap_cons, hcz, Option.map_some, List.map_cons]
      rw [ih (fun w hw => hreg w (List.mem_cons_of_mem _ hw))]
  have hmemT : ∀ z, z ∈ S.loc r b → z ∉ S.base b → z ∈ T := fun z hz hzb => by
    rw [hbase, List.mem_append] at hz; exact hz.resolve_left hzb
  have hidx : ∀ z, z ∉ S.base b → (S.loc r b).idxOf z = T.idxOf z + (S.base b).length :=
    fun z hzb => by
      conv => lhs; rw [hbase]
      rw [List.idxOf_append, if_neg hzb]
  have hseq : ∀ q ∈ S.seqOf T, S.cmds q.1 = some q.2 := fun q hq => by
    unfold PState.seqOf at hq
    obtain ⟨z, -, hz⟩ := List.mem_filterMap.mp hq
    cases h : S.cmds z with
    | none => rw [h] at hz; cases hz
    | some c => rw [h] at hz; cases hz; exact h
  unfold PState.keyPrefix
  rw [hcx, hcy]
  simp only
  rw [← hk, hT]
  refine keyIds_prefix cx.key x y cx cy (S.seqOf T) (by rw [hmapT]; exact hmemT x hx hxb)
    (fun q hq e => by have := hseq q hq; rw [e, hcx] at this; cases this; rfl)
    (fun q hq e => by have := hseq q hq; rw [e, hcy] at this; cases this; rfl) rfl hk.symm ?_
  rw [hmapT]
  have := hle; rw [hidx x hxb, hidx y hyb] at this; omega

/-- Decision D23: ballot `b`'s leader's numbers are non-negative (so its ack's `numAck` is its
number). -/
theorem num_nonneg (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (b : Nat) (x : CmdId) (s : w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ numIs γ (leaderOf N b) b x s ⊢
    |={E}=> ⌜0 ≤ sint.Z s⌝ := by
  unfold inv
  iintro ⟨#Hinv, #Hcfg, #Hnx⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, HRepr, Hnodes, Hproto, HQs, HCl, HDom, Hcmds, Hconns, HNu⟩
  unfold numInv
  icases HNu with ⟨%mNu, >HNu, >#HNo⟩
  unfold numIs
  ihave %Lnx := ghost_map_lookup $$ HNu Hnx
  ihave %Hres : ⌜0 ≤ sint.Z s⌝ $$ [HNo]
  · icases HNo with (%Hno | ⟨%N2, %fr2, %l2, #Hcfg2, %Hok⟩)
    · rw [Hno.1] at Lnx; cases Lnx
    ihave %Hag2 := cfg_agree (γc := γc) (γm := γm) N N2 fr fr2 l l2 $$ [Hcfg Hcfg2]
    · isplitl []
      · iexact Hcfg
      · iexact Hcfg2
    obtain ⟨rfl, rfl, rfl⟩ := Hag2
    ipureintro
    exact ((Hok.1 _ _ _ _ Lnx).2 rfl).1
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa HRepr Hnodes Hproto HQs HCl HDom Hcmds Hconns HNu] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    iexact HNo
  imodintro
  ipureintro; exact Hres

/-- **The leader's numbering (change log C22, M3)**: two commands of one key that ballot `b`'s
leader numbered: the first's number is non-negative, its path ends with it, and the paths
follow the numbers (a number at most another's: its path is a prefix of the other's). -/
theorem num_paths (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (b : Nat) (x y : CmdId) (s s' : w64) (P P' : List CmdId) (cx cy : Cmd) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗
      numIs γ (leaderOf N b) b x s ∗ pathIs γ (leaderOf N b) b x P ∗ cmdIs γ x cx ∗
      numIs γ (leaderOf N b) b y s' ∗ pathIs γ (leaderOf N b) b y P' ∗ cmdIs γ y cy ⊢
    |={E}=> ⌜cx.key = cy.key → 0 ≤ sint.Z s ∧ P.getLast? = some x ∧
      (sint.Z s ≤ sint.Z s' → P <+: P')⌝ := by
  unfold inv
  iintro ⟨#Hinv, #Hcfg, #Hnx, #Hpx, #Hcx, #Hny, #Hpy, #Hcy⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, >HPa, >%Hrepr, Hnodes, >#Hproto, HQs, >%Hcl, >%Hdom, Hcmds, Hconns, HNu⟩
  unfold numInv
  icases HNu with ⟨%mNu, >HNu, >#HNo⟩
  unfold numIs pathIs cmdIs
  ihave %Lnx := ghost_map_lookup $$ HNu Hnx
  ihave %Lny := ghost_map_lookup $$ HNu Hny
  ihave %Lpx := ghost_map_lookup $$ HPa Hpx
  ihave %Lpy := ghost_map_lookup $$ HPa Hpy
  ihave %Lcx := ghost_map_lookup $$ HC Hcx
  ihave %Lcy := ghost_map_lookup $$ HC Hcy
  ihave %Hres : ⌜cx.key = cy.key → 0 ≤ sint.Z s ∧ P.getLast? = some x ∧
      (sint.Z s ≤ sint.Z s' → P <+: P')⌝ $$ [Hproto HNo]
  · icases HNo with (%Hno | ⟨%N2, %fr2, %l2, #Hcfg2, %Hok⟩)
    · rw [Hno.1] at Lnx; cases Lnx
    icases Hproto with (%Hemp | ⟨%N1, %fr1, %l1, #Hcfg1, %Hpr⟩)
    · have := Hemp.1.2.2.2.2.1 (leaderOf N b) b x
      rw [← Hrepr.path] at this; rw [this] at Lpx; cases Lpx
    ihave %Hag1 := cfg_agree (γc := γc) (γm := γm) N N1 fr fr1 l l1 $$ [Hcfg Hcfg1]
    · isplitl []
      · iexact Hcfg
      · iexact Hcfg1
    ihave %Hag2 := cfg_agree (γc := γc) (γm := γm) N N2 fr fr2 l l2 $$ [Hcfg Hcfg2]
    · isplitl []
      · iexact Hcfg
      · iexact Hcfg2
    obtain ⟨rfl, rfl, rfl⟩ := Hag1
    obtain ⟨rfl, rfl, rfl⟩ := Hag2
    ipureintro
    intro hk
    have HI := Hpr.1
    rw [Hrepr.path] at Lpx Lpy
    rw [Hrepr.cmds] at Lcx Lcy
    obtain ⟨hxl, hxb, hxlast, hxL, -⟩ := HI.path_ok _ _ _ _ Lpx
    obtain ⟨hyl, hyb, -, hyL, -⟩ := HI.path_ok _ _ _ _ Lpy
    obtain ⟨-, hlx⟩ := Hok.1 _ _ _ _ Lnx
    obtain ⟨h0, -, hord⟩ := hlx rfl
    refine ⟨h0, hxlast, fun hss => ?_⟩
    rw [hxL rfl, hyL rfl]
    exact keyPrefix_prefix HI _ _ x y cx cy Lcx Lcy hk hxl hyl hxb hyb ((hord y s' Lny).mpr hss)
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs Hcmds Hconns HNu] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    isplitr
    · iexact Hproto
    isplitr
    · ipureintro; exact Hcl
    isplitr
    · ipureintro; exact Hdom
    iexact HNo
  imodintro
  ipureintro; exact Hres

end laws

end sp

end Perennial.github_com.imdea_software.swiftpaxos
