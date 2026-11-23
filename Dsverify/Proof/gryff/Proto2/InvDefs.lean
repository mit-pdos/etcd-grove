/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2/InvDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Stage 2's invariant (`gryffInv2 γ`, namespace `gryffN`): its state, its pure facts, its body, and
the ghost resources it shares with the replicas, the listeners and the client (D9;
`notes/stage2-plan.md` §1, §5; `notes/stage2-interface-I.md`).

**What it holds** (`gryffInv2Body`, an `Inv2St` with `Inv2Facts`):
* each replica id's real trace of model events `T k` (half of `γ.s2.trace k`; the replica's lock
  invariant has the other half, `traceHalf`), and the real history `l1` of labels in real order
  (`γ.s2.hist`), a global run of the model whose projections are the traces;
* each replica id's predicted words `P k` (`γ.s2.pred`: `none` until the master registers the
  node that becomes replica id `k`, D13), each trace's encoding a prefix of them; each replica
  node's recorded prediction `NP n` (`γ.s2.nodePred`, keyed by the registry's node index, set at
  the node's boot from its package prophecy, `pred_set`), and the registry's node of each set
  replica id (`idNode`, with its `nodeIdIs`): a replica id's prediction is its node's; while some is unset, nothing has happened (`l1 = []`); once all
  three are set, with `T' = decodeAll ∘ P` the real positions are reachable in `T'` and a
  continuation `l2` of `l1` to the closure `close T'` exists, which the linearization is computed
  in: the linearized list (`γ.lin`) is `lin (l1 ++ l2) |l1|` with the operations' outputs;
* the abstract register's half (`γ.reg`), equal to the frontier's value `frontVal l1 |l1|`;
* the client operations' registrations (`γ.ops`, stage 1's `OpInfo`) and their atomic updates
  while not linearized (stage 1's `opRes`), the client ids' turns (`γ.turns`) and connection
  bindings (`γ.conns`), half of the connections' request counters (`γ.placers`, stage 1's; the other
  half is the placers' invariant's), the connections' replica ids (`γ.s2.connRep`);
* the clients' operation budget (D14): the units not yet spent (`γ.s2.budget`, keys below 24);
  every registration spent a distinct unit, so there are at most 24, and every real request's
  replica has handled fewer than 24 requests (the model's `nReqs` budget);
* the message bookkeeping: per directed pair `(k, q)` the number of messages of `k`'s stream to `q`
  handed out as receive tokens (`γ.s2.rxCur`) and the tokens not yet consumed (`γ.s2.rx`); every
  message a replica handled is one handed out and consumed; the client requests' tokens not yet
  consumed (`γ.s2.reqs`).

The laws are in `Proto2/Laws.lean`, `Proto2/Replica.lean` (the replica's: prophecy, step,
request tokens) and `Proto2/Wire.lean` (the peer streams); the client's in `Proto/ClientLaws.lean`
(stage 1's statements, re-targeted at `gryffInv2`).
-/
module

public import Dsverify.Proof.gryff.Names
public import Dsverify.Proof.gryff.Proto.InvDefs
public import Dsverify.Proof.gryff.Pure.Lin
public import Dsverify.Proof.gryff.Model.Codec

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto dsverify_lab.harness
open model kahn pure

/-! ## Countability (ghost state over model events) -/

theorem evEnc_inj {a b : Ev} (h : evCodec.enc a = evCodec.enc b) : a = b := by
  have h1 := evCodec.dec_enc a []
  have h2 := evCodec.dec_enc b []
  rw [h, h2] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  exact h1.1.symm

instance ev.countable : Pos.Countable Ev :=
  .ofInjective (fun e => Pos.Countable.encode (evCodec.enc e))
    (fun _ _ h => evEnc_inj (Pos.encode_inj h))

instance msg.countable : Pos.Countable Msg :=
  .ofInjective (fun m => Pos.Countable.encode (Ev.msg m))
    (fun _ _ h => by have := Pos.encode_inj h; cases this; rfl)

/-! ## Vocabulary -/

/-- Replica `k`'s outputs after its events `t` (`[]` if a step fails: never for a real trace). -/
def outsP (k : Fin 3) (t : List Ev) : List Out := ((runP gNet k t).map Prod.snd).getD []

/-- The messages to `q` among outputs `o` (`kahn.sentTo` at the model's types). -/
def sentToR (q : Fin 3) (o : List Out) : List Msg := sentTo gNet q o

/-- Replica `k`'s stream of messages to `q` (`q = k`: to itself) after its events `t`, in order. -/
def streamOf (k q : Fin 3) (t : List Ev) : List Msg := sentToR q (outsP k t)

/-- An operation's id (stage 1's `OpId`: client id, request id, as integers). -/
def _root_.Perennial.gryff.pure.Op.idZ (o : Op) : OpId := (sint.Z o.cid, sint.Z o.rid)

/-- A reply's operation id. -/
def _root_.Perennial.gryff.model.Ext.keyZ (x : Ext) : OpId := (sint.Z x.key.1, sint.Z x.key.2)

/-- Label `n` of `l` outputs a reply to operation `id`. -/
def replyAt (l : List Label) (n : Nat) (id : OpId) : Prop :=
  n < l.length ∧ ∃ x ∈ extsAt l n, x.keyZ = id

/-- Some label of `l` replies to operation `id` (stable under extension of `l`). -/
def repliedIn (l : List Label) (id : OpId) : Prop := ∃ n, replyAt l n id

/-- The linearized list at cut `k` of a run, as the ghost list records it: ids and outputs. -/
def linEntries (l : List Label) (k : Nat) : List (OpId × RegOutput w64) :=
  (lin l k).map fun o => (o.idZ, opOut l o)

/-- The predicted traces, from the predicted words. -/
def decodeT (ws : Fin 3 → List w64) : Fin 3 → List Ev := fun k => evCodec.decodeAll (ws k)

/-- The messages to `q` handed out (`n < cur (k, q)`) and consumed (no token left), over every
sender `k`, by stream index. -/
def consumedTo (T : Fin 3 → List Ev) (cur : GMap (Nat × Nat) Nat)
    (rx : GMap (Nat × Nat × Nat) Msg) (q : Fin 3) : List Msg :=
  (List.finRange 3).flatMap fun k =>
    ((List.range ((cur.lookup (k.val, q.val)).getD 0)).filter
      (fun n => (rx.lookup (k.val, q.val, n)).isNone)).filterMap
      (fun n => (streamOf k q (T k))[n]?)

/-- A registration as stage 1's `OpMeta` (for `opRes`; places are not used in stage 2). -/
def infoMeta (n : OpInfo) : OpMeta := ⟨n.input, .unplaced, n.au, n.rcpt, n.claim⟩

/-! ## The state and its facts -/

/-- The invariant's abstract state. -/
structure Inv2St where
  /-- each replica id's real trace -/
  T : Fin 3 → List Ev
  /-- the real history, in real order -/
  l1 : List Label
  /-- each replica id's predicted words (keys 0, 1, 2; `none` until set) -/
  P : GMap Nat (Option (List w64))
  /-- each replica node's predicted words, by the registry's node index (D13) -/
  NP : GMap Nat (Option (List w64))
  /-- the registry's node of each set replica id (D13) -/
  idNode : GMap Nat Nat
  /-- the budget units not yet spent (D14) -/
  B : GMap Nat Unit
  /-- the abstract register -/
  σ : w64
  /-- the linearized operations with their outputs -/
  linL : List (OpId × RegOutput w64)
  /-- the registrations -/
  info : GMap OpId OpInfo
  /-- each client id's turn (next request id, last request pending) -/
  turns : GMap Int (Int × Bool)
  /-- client ids' connections -/
  conns : GMap w32 (Option w64)
  /-- connections' request counters (the last request id handed out as a token) -/
  placers : GMap w64 Int
  /-- connections' replica ids -/
  connRep : GMap w64 Nat
  /-- per pair `(k, q)`: messages of `k`'s stream to `q` handed out as tokens -/
  cur : GMap (Nat × Nat) Nat
  /-- receive tokens not yet consumed -/
  rx : GMap (Nat × Nat × Nat) Msg
  /-- request tokens not yet consumed: replica id and input -/
  reqs : GMap OpId (Nat × RegInput w64)

/-- The invariant's pure facts. -/
structure Inv2Facts (S : Inv2St) : Prop where
  /-- the history is a run of the model; its projections are the traces -/
  run : ∃ c, GRun (Cfg.init gNet) S.l1 c
  proj : ∀ r : Fin 3, projR S.l1 r = S.T r
  /-- predictions: a slot per replica id; each set prediction extends its trace's encoding -/
  predKeys : ∀ k : Fin 3, (S.P.lookup k.val).isSome
  predPrefix : ∀ (k : Fin 3) ws, S.P.lookup k.val = some (some ws) →
    ∃ rest, ((S.T k).map evCodec.enc).flatten ++ rest = ws
  /-- a set replica id's prediction is its registry node's (D13) -/
  predNode : ∀ i ws, S.P.lookup i = some (some ws) →
    ∃ n, S.idNode.lookup i = some n ∧ S.NP.lookup n = some (some ws)
  /-- while a prediction is unset, nothing happened -/
  unset : (∃ k : Fin 3, S.P.lookup k.val = some none) → S.l1 = [] ∧ S.linL = []
  /-- once all are set: reality is reachable in the predicted traces, and a continuation of the
  real history to their closure fixes the linearization -/
  closure : ∀ ws : Fin 3 → List w64, (∀ k : Fin 3, S.P.lookup k.val = some (some (ws k))) →
    Reach (N := gNet) (decodeT ws) (fun k => (S.T k).length) ∧
    ∃ (l2 : List Label) (c : Cfg gNet), GRun (Cfg.init gNet) (S.l1 ++ l2) c ∧
      (∀ r : Fin 3, projR (S.l1 ++ l2) r = (decodeT ws r).take (close (N := gNet) (decodeT ws) r)) ∧
      S.linL = linEntries (S.l1 ++ l2) S.l1.length
  /-- the abstract register is the frontier's value -/
  val : S.σ = frontVal S.l1 S.l1.length
  /-- well-behaved clients (the pure layer's hypothesis) -/
  wb : WB S.l1
  linNodup : (S.linL.map Prod.fst).Nodup
  /-- every client operation handled is registered, with its input -/
  reg : ∀ o ∈ ops S.l1, ∃ n, S.info.lookup o.idZ = some n ∧ n.input = o.inp
  /-- request tokens: of registered operations, at a replica id, never handled yet -/
  reqReg : ∀ id k i, S.reqs.lookup id = some (k, i) →
    k < 3 ∧ ∃ n, S.info.lookup id = some n ∧ n.input = i
  reqFresh : ∀ id ki, S.reqs.lookup id = some ki → ∀ o ∈ ops S.l1, o.idZ ≠ id
  /-- a request (token or handled) is of a client id bound to a connection, within the
  connection's counter, at the connection's replica id -/
  binding : ∀ id k, ((∃ i, S.reqs.lookup id = some (k, i)) ∨
      (∃ o ∈ ops S.l1, o.idZ = id ∧ o.r.val = k)) →
    ∃ (hs : w32) (conn : w64) (n : Int), id.1 = sint.Z hs ∧
      S.conns.lookup hs = some (some conn) ∧ S.placers.lookup conn = some n ∧ id.2 ≤ n ∧
      S.connRep.lookup conn = some k
  /-- a connection's replica id is recorded at its first request token (so a connection with
  no request yet, counter `-1` or no counter, has none) -/
  repSet : ∀ conn k, S.connRep.lookup conn = some k →
    ∃ n, S.placers.lookup conn = some n ∧ 0 ≤ n
  /-- turns: registrations are below the turn; an idle client id's registrations are replied to,
  a busy one's except the last -/
  turnsReg : ∀ id, (S.info.lookup id).isSome → ∃ n b, S.turns.lookup id.1 = some (n, b) ∧ id.2 < n
  turnsIdle : ∀ cid n, S.turns.lookup cid = some (n, false) →
    ∀ r, (S.info.lookup (cid, r)).isSome → repliedIn S.l1 (cid, r)
  turnsBusy : ∀ cid n, S.turns.lookup cid = some (n, true) →
    ∀ r, r + 1 ≠ n → (S.info.lookup (cid, r)).isSome → repliedIn S.l1 (cid, r)
  /-- a client id's later request is handled after a reply to its earlier one (for `WB`) -/
  order : ∀ cid r1 r2, r1 < r2 → (S.info.lookup (cid, r1)).isSome →
    (S.info.lookup (cid, r2)).isSome →
    ∃ n, replyAt S.l1 n (cid, r1) ∧ ∀ o ∈ ops S.l1, o.idZ = (cid, r2) → n < o.g
  /-- the budget (D14): unspent units are below 24; each registration spent its own unit -/
  budgetKeys : ∀ u, (S.B.lookup u).isSome → u < 24
  budgetSpent : ∃ unit : OpId → Nat,
    (∀ id, (S.info.lookup id).isSome → unit id < 24 ∧ S.B.lookup (unit id) = none) ∧
    ∀ id1 id2, (S.info.lookup id1).isSome → (S.info.lookup id2).isSome → unit id1 = unit id2 →
      id1 = id2
  /-- hence the model's per-replica budget at every real request (a request token's replica
  has handled fewer than 24 client requests) -/
  reqBudget : ∀ id (k : Fin 3) i, S.reqs.lookup id = some (k.val, i) →
    (stOf k (S.T k)).nReqs < 24
  /-- messages: per pair, the tokens handed out are within the sender's stream; a token names
  its stream's message; a replica's handled messages are exactly the consumed ones -/
  curOk : ∀ k q : Fin 3, ∃ c, S.cur.lookup (k.val, q.val) = some c ∧
    c ≤ (streamOf k q (S.T k)).length
  rxOk : ∀ k q n m, S.rx.lookup (k, q, n) = some m → ∃ (k' q' : Fin 3), k'.val = k ∧ q'.val = q ∧
    n < (S.cur.lookup (k, q)).getD 0 ∧ (streamOf k' q' (S.T k'))[n]? = some m
  recvdOk : ∀ q : Fin 3, (recvd gNet (S.T q)).Perm (consumedTo S.T S.cur S.rx q)

/-! ## Resources -/

section defs
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [InvGS_gen .hasLC GF]

/-- The invariant's body. -/
def gryffInv2Body (γ : ProtoNames) : IProp GF :=
  iprop(∃ S : Inv2St,
    ghostVar γ.reg (1 : Qp).half S.σ ∗
    monoListAuthOwn (γ.s2.trace 0) (1 : Qp).half (S.T 0) ∗
    monoListAuthOwn (γ.s2.trace 1) (1 : Qp).half (S.T 1) ∗
    monoListAuthOwn (γ.s2.trace 2) (1 : Qp).half (S.T 2) ∗
    monoListAuthOwn γ.s2.hist 1 S.l1 ∗
    ghostMapAuth γ.s2.pred 1 S.P ∗ ghostMapAuth γ.s2.nodePred 1 S.NP ∗
    ([∗list] i ∈ List.range 3, match S.idNode.lookup i with
      | some n => nodeIdIs γ n (W64 i)
      | none => iprop(True)) ∗
    ghostMapAuth γ.s2.budget 1 S.B ∗
    monoListAuthOwn γ.lin 1 S.linL ∗
    ghostMapAuth γ.ops 1 S.info ∗ ghostMapAuth γ.turns 1 S.turns ∗
    ghostMapAuth γ.conns 1 S.conns ∗ ghostMapAuth γ.placers (1 : Qp).half S.placers ∗
    ghostMapAuth γ.s2.connRep 1 S.connRep ∗
    ghostMapAuth γ.s2.rxCur 1 S.cur ∗ ghostMapAuth γ.s2.rx 1 S.rx ∗
    ghostMapAuth γ.s2.reqs 1 S.reqs ∗
    ⌜Inv2Facts S⌝ ∗
    [∗map] id ↦ n ∈ S.info, opRes γ S.linL id (infoMeta n))

/-- Stage 2's invariant. -/
def gryffInv2 (γ : ProtoNames) : IProp GF := iprop(inv gryffN (gryffInv2Body γ))

instance gryffInv2_persistent (γ : ProtoNames) : Persistent (gryffInv2 (GF := GF) γ) := by
  unfold gryffInv2; infer_instance

/-- Replica id `k`'s trace is `t`: the lock invariant's half (the invariant has the other). -/
def traceHalf (γ : ProtoNames) (k : Fin 3) (t : List Ev) : IProp GF :=
  monoListAuthOwn (γ.s2.trace k) (1 : Qp).half t

/-- Replica id `k`'s trace extends `t` (persistent). -/
def traceLb (γ : ProtoNames) (k : Fin 3) (t : List Ev) : IProp GF :=
  monoListLbOwn (γ.s2.trace k) t

/-- The real history extends `l` (persistent). -/
def histLb (γ : ProtoNames) (l : List Label) : IProp GF := monoListLbOwn γ.s2.hist l

/-- Replica node `n`'s predicted words are `ws` (persistent; D13: keyed by the registry's node
index, `n < 3` for node `n + 2`; recorded once, at the node's boot, from the gryff package's
prophecy: `pred_set`). -/
def predIs (γ : ProtoNames) (n : Nat) (ws : List w64) : IProp GF :=
  ghostMapElem γ.s2.nodePred n DFrac.discard (some ws)

/-- Replica node `n` has not recorded its prediction (exclusive; the start gives it to node `n`'s
boot). -/
def predTok (γ : ProtoNames) (n : Nat) : IProp GF :=
  ghostMapElem γ.s2.nodePred n (DFrac.own 1) (none : Option (List w64))

/-- Replica id `i`'s predicted words are `ws` (persistent; set once, when the master registers
the node that becomes replica id `i`: `pred_register`; the invariant's predictions). -/
def predIdIs (γ : ProtoNames) (i : Nat) (ws : List w64) : IProp GF :=
  ghostMapElem γ.s2.pred i DFrac.discard (some ws)

/-- Replica id `i`'s prediction is not set yet (exclusive; the start puts the three in the
registry's invariant, `deployInv`, which spends slot `i` at the `i`-th registration). -/
def predSlot (γ : ProtoNames) (i : Nat) : IProp GF :=
  ghostMapElem γ.s2.pred i (DFrac.own 1) (none : Option (List w64))

/-- All three replica ids' predictions are set (persistent): what a replica needs before its
first step (D13: the registry's `Ready` answer gives it, before `NewReplica`). -/
def predsSet (γ : ProtoNames) : IProp GF :=
  iprop(∃ ws0 ws1 ws2, predIdIs γ 0 ws0 ∗ predIdIs γ 1 ws1 ∗ predIdIs γ 2 ws2)

/-- Replica node `n` has not claimed its replica id's start resources from the registry
(exclusive; the start gives it to node `n`'s boot; `deploy_claim`). -/
def slotClaimTok (γ : ProtoNames) (n : Nat) : IProp GF :=
  ghostMapElem γ.s2.claim n (DFrac.own 1) ()

/-- `n` budget units (D14; exclusive): `op_begin` spends one per registration. The start gives
24, 4 to each client node (stage 3); the client token at operation `j` holds `4 - j`. -/
def budget (γ : ProtoNames) (n : Nat) : IProp GF :=
  iprop(∃ us : List Nat, ⌜us.length = n⌝ ∗
    [∗list] u ∈ us, ghostMapElem γ.s2.budget u (DFrac.own 1) ())

/-- The receiving side's cursor on `k`'s stream to `q` (exclusive): `n` messages handed out as
tokens. For `k ≠ q` the listener of `q`'s connection with `k`; for `k = q` the replica's lock. -/
def rxCurTok (γ : ProtoNames) (k q : Fin 3) (n : Nat) : IProp GF :=
  ghostMapElem γ.s2.rxCur (k.val, q.val) (DFrac.own 1) n

/-- The receive token of message `n` of `k`'s stream to `q`, which is `m` (exclusive; consumed
by `q`'s step handling it). -/
def rxTok (γ : ProtoNames) (k q : Fin 3) (n : Nat) (m : Msg) : IProp GF :=
  ghostMapElem γ.s2.rx (k.val, q.val, n) (DFrac.own 1) m

/-- The request token of operation `id` with input `i`, at replica id `k` (exclusive; minted by
`k`'s client listener, consumed by `k`'s step handling the request). -/
def reqTok (γ : ProtoNames) (k : Fin 3) (id : OpId) (i : RegInput w64) : IProp GF :=
  ghostMapElem γ.s2.reqs id (DFrac.own 1) (k.val, i)

/-- Client connection `conn` is accepted at replica id `k` (persistent). -/
def connRepIs (γ : ProtoNames) (conn : w64) (k : Fin 3) : IProp GF :=
  ghostMapElem γ.s2.connRep conn DFrac.discard k.val

/-- The first messages `ms` of `k`'s stream to `q` (persistent). -/
def streamLb (γ : ProtoNames) (k q : Fin 3) (ms : List Msg) : IProp GF :=
  iprop(∃ t, traceLb γ k t ∗ ⌜ms <+: streamOf k q t⌝)

/-- Replica id `i`'s start resources, which wait in the registry's invariant until the node
registered as `i` claims them (`deploy_claim`): its lock's trace half at `[]` and its receiving
cursors on the three streams to it (`k`'s listener of its connection with `q`, `q ≠ i`; its lock,
`q = i`), at `0`. -/
def idSlotRes (γ : ProtoNames) (i : Fin 3) : IProp GF :=
  iprop(traceHalf γ i [] ∗ rxCurTok γ 0 i 0 ∗ rxCurTok γ 1 i 0 ∗ rxCurTok γ 2 i 0)

/-- What a replica's step on `e` consumes: a message's receive token, a client request's token
(its id and input from the event's fields), nothing for a timer, a recovery trigger or an
execution. -/
def evTok (γ : ProtoNames) (k : Fin 3) (e : Ev) : IProp GF :=
  match e with
  | .msg m => iprop(∃ (k' : Fin 3) (n : Nat), rxTok γ k' k n m)
  | e => match e.clientReq with
    | some (cid, rid, i) => reqTok γ k (sint.Z cid, sint.Z rid) i
    | none => iprop(True)

instance traceLb_persistent (γ : ProtoNames) (k : Fin 3) (t : List Ev) :
    Persistent (traceLb (GF := GF) γ k t) := by unfold traceLb; infer_instance
instance histLb_persistent (γ : ProtoNames) (l : List Label) :
    Persistent (histLb (GF := GF) γ l) := by unfold histLb; infer_instance
instance predIs_persistent (γ : ProtoNames) (n : Nat) (ws : List w64) :
    Persistent (predIs (GF := GF) γ n ws) := by unfold predIs; infer_instance
instance predIdIs_persistent (γ : ProtoNames) (i : Nat) (ws : List w64) :
    Persistent (predIdIs (GF := GF) γ i ws) := by unfold predIdIs; infer_instance
instance predsSet_persistent (γ : ProtoNames) : Persistent (predsSet (GF := GF) γ) := by
  unfold predsSet; infer_instance
instance connRepIs_persistent (γ : ProtoNames) (conn : w64) (k : Fin 3) :
    Persistent (connRepIs (GF := GF) γ conn k) := by unfold connRepIs; infer_instance
instance streamLb_persistent (γ : ProtoNames) (k q : Fin 3) (ms : List Msg) :
    Persistent (streamLb (GF := GF) γ k q ms) := by unfold streamLb; infer_instance

end defs

end Perennial.gryff
