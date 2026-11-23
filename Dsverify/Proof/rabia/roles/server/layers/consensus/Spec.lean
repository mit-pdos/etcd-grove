/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/Spec.lean`, run `rabia-r1wake-1`.)

`rabia/roles/server/layers/consensus`'s specs (interface, stage 1b).

The consensus layer of server `k`: `ConsensusInit`, its two routines (they never return: `Done`
is never closed), `Executor` (decides the slots in order: proposals from the pending queue,
Rabia's phases, the decision's facts, `SetDecision`) and `MsgHandler` (counts the received
messages per slot and round, notifies the executor on the slot's queue, answers proposal
requests), and `SlotStats` (the terminal logger's).

**The slots' invariant** (`slotsInv`, one invariant per slot, namespace `slotN k s`): the slot's
shared state `slotSt` (the ledger's half), the facts of its decision when it is done (`decInfo`:
`fact (dec s) d`, the decision object's facts `decObjOk`, the facts of the slots before,
`prefixFacts`: what the proxy needs to execute it), and the consensus layer's ghost state of the
slot (`slotGhost`: the tallies of each round with the senders' receipts, the frozen rounds, the
queue's history; this package's, under its own names `ConsNames`). The proxy reads decisions
through it (`readDecision`).

The slots' queues (handler → executor) are this package's: `slotQP` (the notifications in round
order), with its logs `qLb` and the frozen rounds `roundDone`.

`ServerInit` allocates the invariant from the ledger's fresh slots (`slotsInv_alloc`), before
`ProxyInit` and `ConsensusInit`, which both take it.
-/
module

public import Dsverify.Proof.rabia.Core.Chans
public import Dsverify.GeneratedProof.rabia.roles.server.layers.consensus
public import Dsverify.Proof.rabia.internal.config.Spec
public import Dsverify.Proof.rabia.Core.PkgState
public import Dsverify.Proof.rabia.internal.queue.Spec
public import Perennial.Proof.sync.Base
public import Perennial.Golang.Theory.Map

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model NetConn Dsv rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

/-- The consensus layer's own ghost names (allocated by `slotsInv_alloc`). -/
structure ConsNames where
  /-- per slot: its queue's SPSC names -/
  queue : Nat → SpscNames
  /-- per slot: its queue's notifications (mono-list of `Option Nat`) -/
  qlog : Nat → GName
  /-- the frozen tallies (ghost map `Nat × Nat ↦ ()`, persistent elements) -/
  frz : GName

/-- Slot `s`'s invariant's namespace (server `k`). -/
def slotN (k s : Nat) : Namespace :=
  ndot (ndot (ndot rabiaR "slot") (toString k)) (toString s)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- `l` is a prefix of slot `s`'s queue notifications (persistent). -/
def qLb (γc : ConsNames) (s : Nat) (l : List (Option Nat)) : IProp GF :=
  monoListLbOwn (γc.qlog s) l
def qAuth (γc : ConsNames) (s : Nat) (l : List (Option Nat)) : IProp GF :=
  monoListAuthOwn (γc.qlog s) 1 l

/-- Slot `s`'s tally of round `ρ` is frozen (persistent; its meaning: `slotGhost`). -/
def roundDone (γc : ConsNames) (s ρ : Nat) : IProp GF := ghostMapElem γc.frz (s, ρ) .discard ()

/-- Slot `s`'s `Queue` (handler → executor, SPSC): the `i`-th notification is the queue log's
`i`-th: round `ρ`'s (frozen), the rounds notified in order `0, 1, …` without gaps; or the slot's
decision (once), with its facts. -/
def slotQP (γ : Names) (cf : RCfg) (γc : ConsNames) (s : Nat) (i : Int) (v : Msg) : IProp GF :=
  iprop(∃ (m : MsgV) (ql : List (Option Nat)) (e : Option Nat), msgRep v m ∗ qLb γc s ql ∗
    ⌜ql.length = i.toNat + 1 ∧ ql[i.toNat]? = some e⌝ ∗
    (match e with
     | some ρ => iprop(⌜roundOf m = some ρ ∧ (ql.take i.toNat).filterMap id = List.range ρ⌝ ∗
          roundDone γc s ρ)
     | none => iprop(∃ (o : ObjV) (d : DVal), ⌜m.ty = tyDecision ∧ m.obj = some o ∧
          o.svrSeq.toNat = s ∧ none ∉ ql.take i.toNat⌝ ∗
          fact γ.rab (.dec s) (.dval d) ∗ decObjOk γ cf s d o)))

/-- What a slot's state says of its decision (persistent): when done, slot `s` is decided `d`,
the decision object is `d`'s, and the facts of the slots before (the proxy executes it). -/
def decInfo (γ : Names) (cf : RCfg) (s : Nat) (st : SlotSt) : IProp GF :=
  if st.isDone then
    iprop(∃ (d : DVal) (cmds : List GoString), fact γ.rab (.dec s) (.dval d) ∗
      decObjOk γ cf s d st.decision ∗ prefixFacts γ.rab s cmds)
  else iprop(True)

/-! ### The slots' ghost state (the prover's definitions)

Each slot `s` has, besides its queue log `γc.qlog s`, five more ghost names, taken from `γc.qlog`
beyond the slots (`auxName`: `slotsInv_alloc` allocates them): the counted messages (`entName`, a
mono-list, halves: the slot's invariant and the handler), the handler's pending notification
(`pendName`, halves), the executor's mirror of `isDone` (`exName`, halves), and two monotone flags
(`dwName`: the slot is done; `rdName`: it has received a decision), whose authorities are in the
invariant. -/

/-- A counted message: its round, its sender, its index in the sender's broadcast log, itself. -/
abbrev Ent := Nat × Nat × Nat × MsgV

def auxName (γl : SrvNames) (γc : ConsNames) (i s : Nat) : GName :=
  γc.qlog (γl.slots.length + 5 * s + i)
def entName (γl : SrvNames) (γc : ConsNames) (s : Nat) : GName := auxName γl γc 0 s
def pendName (γl : SrvNames) (γc : ConsNames) (s : Nat) : GName := auxName γl γc 1 s
def exName (γl : SrvNames) (γc : ConsNames) (s : Nat) : GName := auxName γl γc 2 s
def dwName (γl : SrvNames) (γc : ConsNames) (s : Nat) : GName := auxName γl γc 3 s
def rdName (γl : SrvNames) (γc : ConsNames) (s : Nat) : GName := auxName γl γc 4 s

/-- The counted messages of round `ρ`. -/
def tally (ents : List Ent) (ρ : Nat) : List Ent := ents.filter (fun e => e.1 = ρ)

/-- The counts of values (`PutRecvBCMsgs`'s: `0`, `1`, anything else). -/
def countsOf (vs : List Nat) : Counts :=
  (vs.count 0, vs.count 1, (vs.filter (fun x => x ≠ 0 ∧ x ≠ 1)).length)

/-- `PutRecvProposals`'s tallies (`SlotSt.addProp`'s list part). -/
def addPropL (ps : List (ObjV × Nat)) (o : ObjV) : List (ObjV × Nat) :=
  if ps.any (fun t => t.1.sameId o) then
    ps.map (fun t => if t.1.sameId o then (t.1, t.2 + 1) else t)
  else ps ++ [(o, 1)]

/-- The tallies of a sequence of proposals. -/
def groupProps (os : List ObjV) : List (ObjV × Nat) := os.foldl addPropL []

/-- The counted messages of each round make the slot's counts. -/
def TallyOk (st : SlotSt) (ents : List Ent) : Prop :=
  st.total 0 1 = (tally ents 0).length ∧
  st.props.Perm (groupProps ((tally ents 0).filterMap (fun e => e.2.2.2.obj))) ∧
  (∀ p r, (r = 1 ∧ 1 ≤ p) ∨ r = 2 →
    st.total p r = (tally ents (2 * p + r - 1)).length ∧
    st.counts p r = countsOf ((tally ents (2 * p + r - 1)).map (fun e => e.2.2.2.value.toNat)))

/-- The slot's pure invariant: tallies, at most `n - f` messages of a round from distinct senders, the
notifications (rounds in order, a round notified (or pending) exactly when full; the decision
notified exactly when `hasRecvDec`, but in the handler's window), the flags. -/
def SlotOk (cf : RCfg) (s : Nat) (st : SlotSt) (ents : List Ent) (ql : List (Option Nat))
    (pend : Option (Option Nat)) (exd : Bool) (dl rl : List Unit) : Prop :=
  TallyOk st ents ∧
  (∀ e ∈ ents, e.2.1 < cf.n ∧ msgRound e.2.2.2 = some (s, e.1)) ∧
  (∀ ρ, (tally ents ρ).length ≤ cf.q ∧ ((tally ents ρ).map (fun e => e.2.1)).Nodup) ∧
  ql.filterMap id = List.range (ql.filterMap id).length ∧
  (∀ ρ, (some ρ ∈ ql ∨ pend = some (some ρ)) ↔ (tally ents ρ).length = cf.q) ∧
  (st.hasRecvDec = true ↔ (none ∈ ql ∧ pend ≠ some none)) ∧
  st.isDone = exd ∧ (dl ≠ [] → st.isDone = true) ∧ (rl ≠ [] → st.hasRecvDec = true)

/-- Sender `X`'s message of round `ρ` is counted at slot `s` (persistent). -/
def counted (γl : SrvNames) (γc : ConsNames) (s ρ X : Nat) : IProp GF :=
  iprop(∃ l : List Ent, monoListLbOwn (entName γl γc s) l ∗ ⌜∃ j m, (ρ, X, j, m) ∈ l⌝)

/-- Round `ρ` of slot `s` is notified (persistent). -/
def notified (γc : ConsNames) (s ρ : Nat) : IProp GF :=
  iprop(∃ ql, qLb γc s ql ∗ ⌜some ρ ∈ ql⌝)

/-- Slot `s` is done (persistent). -/
def doneW (γl : SrvNames) (γc : ConsNames) (s : Nat) : IProp GF :=
  monoListLbOwn (dwName γl γc s) [()]

/-- Slot `s` has received a decision (persistent). -/
def rdW (γl : SrvNames) (γc : ConsNames) (s : Nat) : IProp GF :=
  monoListLbOwn (rdName γl γc s) [()]

/-- A counted message's resources: it is `B_X[j]` with its facts and receipt; a message of round
`ρ + 1`: its sender's message of round `ρ` was counted, or round `ρ` was full. -/
def entRes (γ : Names) (cf : RCfg) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : Ent) : IProp GF :=
  iprop((∃ l, bcastLb γ e.2.1 l ∗ ⌜l[e.2.2.1]? = some e.2.2.2⌝) ∗ bmsgOk γ cf e.2.1 e.2.2.2 ∗
    rcpt γl e.2.1 e.2.2.1 ∗
    (match e.1 with
     | 0 => iprop(True)
     | ρ + 1 => iprop(counted γl γc s ρ e.2.1 ∨ notified γc s ρ)))

/-- The consensus layer's ghost state of slot `s` at state `st`. -/
def slotGhost (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (st : SlotSt) :
    IProp GF :=
  iprop(∃ (ents : List Ent) (ql : List (Option Nat)) (pend : Option (Option Nat)) (exd : Bool)
      (dl rl : List Unit),
    monoListAuthOwn (entName γl γc s) (1 : Qp).half ents ∗
    monoListAuthOwn (γc.qlog s) (1 : Qp).half ql ∗
    ghostVar (pendName γl γc s) (1 : Qp).half pend ∗ ghostVar (exName γl γc s) (1 : Qp).half exd ∗
    monoListAuthOwn (dwName γl γc s) 1 dl ∗ monoListAuthOwn (rdName γl γc s) 1 rl ∗
    ([∗list] e ∈ ents, entRes γ cf γl γc s e) ∗ ⌜SlotOk cf s st ents ql pend exd dl rl⌝)

/-- Slot `s`'s invariant. -/
def slotInv (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) :
    IProp GF :=
  iprop(∃ st : SlotSt, slotSt e.γ st ∗ decInfo γ cf s st ∗ slotGhost γ cf k γl γc s st)

/-- The slots' invariants (persistent). -/
def slotsInv (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) : IProp GF :=
  iprop([∗list] s ↦ e ∈ γl.slots, inv (slotN k s) (slotInv γ cf k γl γc s e))

/-- A slot-queue notification's shape beyond `slotQP` (what `wait`'s checks need): a proposal's
notification is of phase 0, a state's of a phase `≥ 1`. -/
def notifWf (v : Msg) : Prop :=
  (v.Type' = tyProposal → v.Phase' = 0) ∧ (v.Type' = tyState → 1 ≤ v.Phase'.toNat)

/-- The slot queue's element predicate: `slotQP` and the shape. -/
def slotQPx (γ : Names) (cf : RCfg) (γc : ConsNames) (s : Nat) (i : Int) (v : Msg) : IProp GF :=
  iprop(slotQP γ cf γc s i v ∗ ⌜notifWf v⌝)

/-- Slot `s`'s queue, with its protocol (persistent). -/
def slotChan (γ : Names) (cf : RCfg) (γc : ConsNames) (s : Nat) (e : SlotV) : IProp GF :=
  isSpsc (γc.queue s) e.q (slotQPx γ cf γc s) (fun _ => iprop(False))

/-- The executor's part of a fresh slot. -/
def slotExecPart (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) : IProp GF :=
  iprop(slotPriv e.loc { phase := 0, round := 0, myProp := default, myBC := [] } ∗
    spscConsumer (γc.queue s) ([] : List Msg) ∗ ghostVar (exName γl γc s) (1 : Qp).half false)

/-- The handler's part of a fresh slot. -/
def slotHandlerPart (γl : SrvNames) (γc : ConsNames) (s : Nat) : IProp GF :=
  iprop(spscProducer (γc.queue s) ([] : List Msg) ∗
    monoListAuthOwn (γc.qlog s) (1 : Qp).half ([] : List (Option Nat)) ∗
    monoListAuthOwn (entName γl γc s) (1 : Qp).half ([] : List Ent) ∗
    ghostVar (pendName γl γc s) (1 : Qp).half (none : Option (Option Nat)))

/-- The consensus layer's private resources of the slots (each slot's executor part, its queue's
producer and consumer tokens, the logs' authorities), from `slotsInv_alloc`. -/
def consSlotsRes (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) : IProp GF :=
  iprop(ghostMapAuth γc.frz 1 (∅ : GMap (Nat × Nat) Unit) ∗
    [∗list] s ↦ e ∈ γl.slots, slotChan γ cf γc s e ∗ slotExecPart γl γc s e ∗ slotHandlerPart γl γc s)

/-- A pending object (in the pending queue, or the executor's proposal): its facts, and the
receipt of its client request `B_X[j]` (each object is received once: what makes `PropOk`). -/
def pendOk (γ : Names) (cf : RCfg) (γl : SrvNames) (o : ObjV) : IProp GF :=
  iprop(objOk γ cf o ∗ ∃ (X j : Nat) (l : List MsgV), bcastLb γ X l ∗ rcpt γl X j ∗
    ⌜X = o.proId.toNat ∧ ∃ m, l[j]? = some m ∧ m.ty = tyClientRequest ∧ m.obj = some o⌝)

/-- The pending queue's lock invariant (`QLock`). -/
def pqInv (γ : Names) (cf : RCfg) (γl : SrvNames) (c : Loc) : IProp GF :=
  iprop(∃ xs, pqOwn (structFieldRef Consensus go!"Queue" c) xs ∗ [∗list] o ∈ xs, pendOk γ cf γl o)

/-- The statistics' lock invariant (`StatLock`). -/
def statInv (c : Loc) : IProp GF :=
  iprop(∃ (a b d e : w64), structFieldRef Consensus go!"NormalSlots" c ↦ a ∗
    structFieldRef Consensus go!"UnmatchedSlots" c ↦ b ∗
    structFieldRef Consensus go!"NullSlots" c ↦ d ∗
    structFieldRef Consensus go!"NumClientBatchedRequests" c ↦ e)

/-- The read-only fields both routines use, the locks, and the shared persistent facts. -/
def consRO (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) :
    IProp GF :=
  iprop(∃ (ledger : GoSlice) (ql wg : Loc),
    structFieldRef Consensus go!"SvrId" c ↦□ (W32 k : w32) ∗
    structFieldRef Consensus go!"Wg" c ↦□ wg ∗
    structFieldRef Consensus go!"Done" c ↦□ ch.done ∗
    structFieldRef Consensus go!"NetToMsgHandler" c ↦□ ch.n2h ∗
    structFieldRef Consensus go!"MsgHandlerToNet" c ↦□ ch.h2n ∗
    structFieldRef Consensus go!"NetToConExecutor" c ↦□ ch.n2e ∗
    structFieldRef Consensus go!"ConExecutorToNet" c ↦□ ch.e2n ∗
    structFieldRef Consensus go!"QLock" c ↦□ ql ∗
    structFieldRef Consensus go!"Ledger" c ↦□ ledger ∗
    sync.isMutex ql (pqInv γ cf γl c) ∗ sync.isMutex (structFieldRef Consensus go!"StatLock" c) (statInv c) ∗
    srvChans γ cf k γl ch ∗ ledgerRO γl ledger ∗ slotsInv γ cf k γl γc ∗
    ([∗list] s ↦ e ∈ γl.slots, slotChan γ cf γc s e) ∗ isSrvKeys γ k γl)

/-- What server `k`'s consensus layer needs at its start besides its slots (`ServerInit` gives
it): the handler's consumer token, the executor's producer token and its log `E_k`, its part of
server `k`'s keys. -/
def consensusBootRes (γ : Names) (k : Nat) (γl : SrvNames) : IProp GF :=
  iprop(spscConsumer γl.n2h ([] : List Msg) ∗ spscProducer γl.e2n ([] : List Msg) ∗
    exAuth γl [] ∗ keysPart γl false [] ∗ isSrvKeys γ k γl)

/-- The executor's resources after `ConsensusInit`. -/
def consExecRes (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) :
    IProp GF :=
  iprop(consRO γ cf k γl γc ch c ∗
    structFieldRef Consensus go!"SvrSeq" c ↦ (W64 (2 ^ 64 - 1) : w64) ∗
    (∃ coin : Loc, structFieldRef Consensus go!"Coin" c ↦ coin) ∗
    (∃ (mp : GoMap), structFieldRef Consensus go!"Discard" c ↦ mp ∗
      ownMap mp (DFrac.own 1) (∅ : GMap w64 Bool)) ∗
    (∃ (a b d : w64), structFieldRef Consensus go!"CurrConsecutiveNulls" c ↦ a ∗
      structFieldRef Consensus go!"MaxConsecutiveNulls" c ↦ b ∗
      structFieldRef Consensus go!"MaxConsecutiveNullsEndSeq" c ↦ d) ∗
    (∃ t : w32, structFieldRef Consensus go!"TotalRounds" c ↦ t) ∗
    (∃ (sl : GoSlice) (xs : List w64), structFieldRef Consensus go!"NumOfRoundsDist" c ↦ sl ∗
      sl ↦* xs ∗ ⌜xs.length = 2 * cf.blockLen + 2⌝) ∗
    ([∗list] s ↦ e ∈ γl.slots, slotExecPart γl γc s e) ∗
    spscProducer γl.e2n ([] : List Msg) ∗ exAuth γl [] ∗ keysPart γl false [] ∗ ⌜k < cf.n⌝)

/-- The handler's resources after `ConsensusInit`. -/
def consHandlerRes (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) : IProp GF :=
  iprop(consRO γ cf k γl γc ch c ∗
    (∃ n : w64, structFieldRef Consensus go!"OlderThanTermMsg" c ↦ n) ∗
    ghostMapAuth γc.frz 1 (∅ : GMap (Nat × Nat) Unit) ∗
    ([∗list] s ↦ _e ∈ γl.slots, slotHandlerPart γl γc s) ∗
    spscConsumer γl.n2h ([] : List Msg))

/-- The statistics' lock (persistent). -/
def consStatsRO (c : Loc) : IProp GF :=
  sync.isMutex (structFieldRef Consensus go!"StatLock" c) (statInv c)

theorem cons_prefixFacts_persistent (γ : RabiaNames) :
    ∀ (s : Nat) (cmds : List GoString), Persistent (prefixFacts (GF := GF) γ s cmds) :=
  prefixFacts_persistent' γ

instance cons_prefixFacts_persistent_inst (γ : RabiaNames) (s : Nat) (cmds : List GoString) :
    Persistent (prefixFacts (GF := GF) γ s cmds) := cons_prefixFacts_persistent γ s cmds

instance cons_objOk_persistent (γ : Names) (cf : RCfg) (o : ObjV) : Persistent (objOk (GF := GF) γ cf o) := by
  unfold objOk; infer_instance

instance cons_decObjOk_persistent (γ : Names) (cf : RCfg) (s : Nat) (d : DVal) (o : ObjV) :
    Persistent (decObjOk (GF := GF) γ cf s d o) := by
  unfold decObjOk; cases d <;> infer_instance

instance decInfo_persistent (γ : Names) (cf : RCfg) (s : Nat) (st : SlotSt) :
    Persistent (decInfo (GF := GF) γ cf s st) := by
  unfold decInfo; split <;> infer_instance
instance slotsInv_persistent (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) :
    Persistent (slotsInv (GF := GF) γ cf k γl γc) := by
  unfold slotsInv; infer_instance
instance consStatsRO_persistent (c : Loc) : Persistent (consStatsRO (GF := GF) c) := by
  unfold consStatsRO; infer_instance

/-- (A missing law of `Proof/Rabia/Chans.lean`: `isSrvKeys` is an invariant, persistent.) -/
instance cons_isSrvKeys_persistent (γ : Names) (k : Nat) (γl : SrvNames) :
    Persistent (isSrvKeys (GF := GF) γ k γl) := by
  unfold isSrvKeys; infer_instance

instance cons_slotChan_persistent (γ : Names) (cf : RCfg) (γc : ConsNames) (s : Nat) (e : SlotV) :
    Persistent (slotChan (GF := GF) γ cf γc s e) := by
  unfold slotChan; infer_instance

instance cons_consRO_persistent (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) : Persistent (consRO (GF := GF) γ cf k γl γc ch c) := by
  unfold consRO
  refine ⟨?_⟩
  iintro ⟨%a, %b, %d, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9, #H10, #H11, #H12, #H13, #H14,
    #H15, #H16⟩
  imodintro
  iexists a, b, d
  iframe #


end defs

/-! ## The laws (statements; proved in Prove) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-! ### slotsInv_alloc's helpers (fork F1) -/

/-- The names allocated for one slot. -/
structure SlotAllocNs where
  cn : ChanNames
  sent : GName
  recv : GName
  q : GName
  ent : GName
  pend : GName
  ex : GName
  dw : GName
  rd : GName

/-- `γc.qlog` from the slots' allocated names (`n` slots): slot `j`'s queue log for `j < n`, then
each slot's five auxiliary names. -/
def allocQlog (n : Nat) (L : List SlotAllocNs) (j : Nat) : GName :=
  if j < n then (L[j]?.map (·.q)).getD 0
  else match L[(j - n) / 5]? with
    | some ns => [ns.ent, ns.pend, ns.ex, ns.dw, ns.rd].getD ((j - n) % 5) 0
    | none => 0

/-- `γc.queue` from the slots' allocated names. -/
def allocQueue (L : List SlotAllocNs) (s : Nat) : SpscNames :=
  match L[s]? with
  | some ns => ⟨ns.cn, ns.sent, ns.recv⟩
  | none => ⟨⟨0, 0, 0, 0, 0, 0⟩, 0, 0⟩

theorem allocQlog_slot {n : Nat} {L : List SlotAllocNs} {s : Nat} {ns : SlotAllocNs}
    (hn : s < n) (h : L[s]? = some ns) : allocQlog n L s = ns.q := by
  simp [allocQlog, hn, h]

theorem allocQlog_aux {n : Nat} {L : List SlotAllocNs} {s i : Nat} {ns : SlotAllocNs}
    (hi : i < 5) (h : L[s]? = some ns) :
    allocQlog n L (n + 5 * s + i) = [ns.ent, ns.pend, ns.ex, ns.dw, ns.rd].getD i 0 := by
  have h1 : ¬ (n + 5 * s + i < n) := by omega
  have h2 : (n + 5 * s + i - n) / 5 = s := by omega
  have h3 : (n + 5 * s + i - n) % 5 = i := by omega
  simp only [allocQlog, h1, ↓reduceIte, h2, h3, h]

theorem slotOk_init (cf : RCfg) (hc : cf.Ok) (s : Nat) :
    SlotOk cf s (SlotSt.init cf.blockLen) [] [] none false [] [] := by
  have hL : 0 < cf.blockLen := by
    have h4 := hc.2.2.2
    unfold RCfg.blockLen
    generalize cf.blocks = b at h4 ⊢
    match b, h4 with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
  have hq : 0 < cf.q := by have := hc.nf; unfold RCfg.q; omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp [SlotSt.total, SlotSt.init, tally, List.getElem?_replicate, hL]
  · simp [SlotSt.init, tally, groupProps]
  · intro p r _
    simp only [tally, List.filter_nil, List.length_nil, List.map_nil]
    constructor
    · have hb : (SlotSt.init cf.blockLen).bcT = List.replicate cf.blockLen ((0 : Nat), (0 : Nat)) := rfl
      simp only [SlotSt.total, hb, List.getElem?_replicate]
      by_cases hp : p < cf.blockLen <;> simp [hp]
    · have hb : (SlotSt.init cf.blockLen).bc = List.replicate cf.blockLen (((0 : Nat), (0 : Nat), (0 : Nat)),
          ((0 : Nat), (0 : Nat), (0 : Nat))) := rfl
      simp only [SlotSt.counts, hb, List.getElem?_replicate]
      by_cases hp : p < cf.blockLen <;> simp [hp, countsOf]
  · simp [tally, SlotSt.init, Nat.ne_of_lt hq]

/-- A fresh slot with its allocated names. -/
def slotFresh (cf : RCfg) (e : SlotV) (ns : SlotAllocNs) : IProp GF :=
  iprop(slotSt e.γ (SlotSt.init cf.blockLen) ∗
    slotPriv e.loc { phase := 0, round := 0, myProp := default, myBC := [] } ∗
    isChan e.q ns.cn Msg ∗ ownChan ns.cn Msg (ChanState.Buffered []) ∗
    dghostVar ns.sent (DFrac.own 1) ([] : List Msg) ∗ dghostVar ns.recv (DFrac.own 1) ([] : List Msg) ∗
    monoListAuthOwn ns.q 1 ([] : List (Option Nat)) ∗ monoListAuthOwn ns.ent 1 ([] : List Ent) ∗
    ghostVar ns.pend 1 (none : Option (Option Nat)) ∗ ghostVar ns.ex 1 false ∗
    monoListAuthOwn ns.dw 1 ([] : List Unit) ∗ monoListAuthOwn ns.rd 1 ([] : List Unit))

theorem slotFresh_alloc (cf : RCfg) (E : CoPset) (e : SlotV) :
    (slotSt (GF := GF) e.γ (SlotSt.init cf.blockLen) ∗
        slotPriv e.loc { phase := 0, round := 0, myProp := default, myBC := [] } ∗
        queueFresh e.q) ⊢ |={E}=> ∃ ns, slotFresh cf e ns := by
  iintro ⟨Hst, Hpv, Hq⟩
  unfold queueFresh
  icases Hq with ⟨%cn, #Hch, -, Hoc⟩
  imod dghostVar_alloc (GF := GF) ([] : List Msg) with ⟨%γsent, Hsent⟩
  imod dghostVar_alloc (GF := GF) ([] : List Msg) with ⟨%γrecv, Hrecv⟩
  imod mono_list_own_alloc (GF := GF) ([] : List (Option Nat)) with ⟨%γq, Hql, -⟩
  imod mono_list_own_alloc (GF := GF) ([] : List Ent) with ⟨%γent, Hent, -⟩
  imod ghostVar_alloc (GF := GF) (none : Option (Option Nat)) with ⟨%γpend, Hpend⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γex, Hex⟩
  imod mono_list_own_alloc (GF := GF) ([] : List Unit) with ⟨%γdw, Hdw, -⟩
  imod mono_list_own_alloc (GF := GF) ([] : List Unit) with ⟨%γrd, Hrd, -⟩
  imodintro
  iexists ⟨cn, γsent, γrecv, γq, γent, γpend, γex, γdw, γrd⟩
  unfold slotFresh
  iframe
  iexact Hch

/-- Pulling the elements' witnesses out of a big separating conjunction. -/
theorem bigSepL_exists_list {A B : Type} (Φ : Nat → A → B → IProp GF) :
    ∀ l : List A, ([∗list] i ↦ x ∈ l, ∃ y, Φ i x y) ⊢
      ∃ L : List B, ⌜L.length = l.length⌝ ∗ [∗list] i ↦ x ∈ l, ∃ y, ⌜L[i]? = some y⌝ ∗ Φ i x y
  | [] => by
    iintro -
    iexists ([] : List B)
    isplitr
    · ipureintro; rfl
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | x :: l => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%y, Hy⟩, H⟩
    ihave ⟨%L, %hL, H⟩ := bigSepL_exists_list (fun i x y => Φ (i + 1) x y) l $$ H
    iexists y :: L
    isplitr
    · ipureintro; simp [hL]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hy]
      · iexists y; iframe Hy; ipureintro; rfl
      · simp only [List.getElem?_cons_succ]
        iexact H

theorem mlAuth_halves {A : Type} [Pos.Countable A] (γ' : GName) (l : List A) :
    monoListAuthOwn (GF := GF) γ' 1 l ⊢
      monoListAuthOwn γ' (1 : Qp).half l ∗ monoListAuthOwn γ' (1 : Qp).half l := by
  conv => lhs; rw [← Qp.half_add_half (1 : Qp)]
  exact ((monoListAuthOwn_fractional γ' l).fractional _ _).1

theorem slotFresh_finish (γ : Names) (cf : RCfg) (hc : cf.Ok) (k : Nat) (γl : SrvNames) (γc : ConsNames) (E : CoPset)
    (s : Nat) (e : SlotV) (ns : SlotAllocNs)
    (hq : γc.queue s = ⟨ns.cn, ns.sent, ns.recv⟩) (hql : γc.qlog s = ns.q)
    (hent : entName γl γc s = ns.ent) (hpend : pendName γl γc s = ns.pend)
    (hex : exName γl γc s = ns.ex) (hdw : dwName γl γc s = ns.dw) (hrd : rdName γl γc s = ns.rd) :
    slotFresh (GF := GF) cf e ns ⊢
      |={E}=> inv (slotN k s) (slotInv γ cf k γl γc s e) ∗
        (slotChan γ cf γc s e ∗ slotExecPart γl γc s e ∗ slotHandlerPart γl γc s) := by
  unfold slotFresh
  iintro ⟨Hst, Hpv, #Hch, Hoc, Hsent, Hrecv, Hql, Hent, Hpend, Hex, Hdw, Hrd⟩
  icases dghostVar_halves _ _ $$ Hsent with ⟨HsentA, HsentF⟩
  icases dghostVar_halves _ _ $$ Hrecv with ⟨HrecvA, HrecvF⟩
  icases mlAuth_halves _ _ $$ Hql with ⟨HqlA, HqlF⟩
  icases mlAuth_halves _ _ $$ Hent with ⟨HentA, HentF⟩
  icases (ghostVar_split_half _ _ _).1 $$ Hpend with ⟨HpendA, HpendF⟩
  icases (ghostVar_split_half _ _ _).1 $$ Hex with ⟨HexA, HexF⟩
  imod inv_alloc nroot E (spscInv (⟨ns.cn, ns.sent, ns.recv⟩ : SpscNames) (slotQPx γ cf γc s)
      (fun _ => iprop(False))) $$ [Hoc HsentA HrecvA] with #Hinv
  · inext
    unfold spscInv
    iexists .Buffered [], [], []
    simp only [spscInvMatch, inflight, List.append_nil]
    iframe
    isplitr
    · itrivial
    · iapply BigSepL.bigSepL_nil.2
      iempintro
  imod inv_alloc (slotN k s) E (slotInv γ cf k γl γc s e) $$ [Hst HqlA HentA HpendA HexA Hdw Hrd]
    with #Hsi
  · inext
    unfold slotInv
    iexists (SlotSt.init cf.blockLen)
    iframe Hst
    isplitr
    · unfold decInfo; simp only [SlotSt.init, Bool.false_eq_true, ↓reduceIte]; itrivial
    unfold slotGhost
    iexists [], [], none, false, [], []
    rw [hent, hql, hpend, hex, hdw, hrd]
    iframe
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · ipureintro; exact slotOk_init cf hc s
  imodintro
  iframe Hsi
  unfold slotChan slotExecPart slotHandlerPart isSpsc spscConsumer spscProducer
  rw [hq, hql, hent, hpend, hex]
  iframe
  iframe Hch Hinv


/-- The consensus layer's names from the slots' allocated names. -/
def allocCons (γl : SrvNames) (L : List SlotAllocNs) (γf : GName) : ConsNames :=
  ⟨allocQueue L, allocQlog γl.slots.length L, γf⟩

theorem slotFresh_finish_L (γ : Names) (cf : RCfg) (hc : cf.Ok) (k : Nat) (γl : SrvNames) (E : CoPset) (γf : GName)
    (L : List SlotAllocNs) (hL : L.length = γl.slots.length) (i : Nat) (e : SlotV) :
    (∃ ns, ⌜L[i]? = some ns⌝ ∗ slotFresh (GF := GF) cf e ns) ⊢
      |={E}=> inv (slotN k i) (slotInv γ cf k γl (allocCons γl L γf) i e) ∗
        (slotChan γ cf (allocCons γl L γf) i e ∗ slotExecPart γl (allocCons γl L γf) i e ∗
          slotHandlerPart γl (allocCons γl L γf) i) := by
  iintro ⟨%ns, %h, H⟩
  have hi : i < γl.slots.length := by
    rw [← hL]; exact (List.getElem?_eq_some_iff.mp h).1
  have haux : ∀ j, j < 5 → auxName γl (allocCons γl L γf) j i =
      [ns.ent, ns.pend, ns.ex, ns.dw, ns.rd].getD j 0 := by
    intro j hj
    simp only [auxName, allocCons]
    exact allocQlog_aux hj h
  iapply slotFresh_finish γ cf hc k γl (allocCons γl L γf) E i e ns
    (by simp [allocCons, allocQueue, h]) (allocQlog_slot hi h)
    (haux 0 (by decide)) (haux 1 (by decide)) (haux 2 (by decide)) (haux 3 (by decide))
    (haux 4 (by decide)) $$ H
/-- The slots' invariants, from the ledger's fresh slots (`Reset`'s); the consensus layer's names
are its own. -/
theorem slotsInv_alloc (γ : Names) (cf : RCfg) (hc : cf.Ok) (k : Nat) (γl : SrvNames) (E : CoPset) :
    ([∗list] e ∈ γl.slots, slotSt (GF := GF) e.γ (SlotSt.init cf.blockLen) ∗
        slotPriv e.loc { phase := 0, round := 0, myProp := default, myBC := [] } ∗
        queueFresh e.q) ⊢
      |={E}=> ∃ γc : ConsNames, slotsInv γ cf k γl γc ∗ consSlotsRes γ cf k γl γc := by
  iintro H
  ihave H := (BigSepL.bigSepL_mono_of_forall
    (Ψ := fun _ e => iprop(|={E}=> ∃ ns, slotFresh (GF := GF) cf e ns))
    (fun {_ e} => slotFresh_alloc cf E e)) $$ H
  imod (BigSepL2.bigSepL_fupd E (fun _ e => iprop(∃ ns, slotFresh (GF := GF) cf e ns)) γl.slots) $$ H
    with H
  ihave ⟨%L, %hL, H⟩ := bigSepL_exists_list (fun _ e ns => slotFresh (GF := GF) cf e ns) γl.slots $$ H
  imod ghost_map_alloc_empty (GF := GF) (K := Nat × Nat) (V := Unit) with ⟨%γf, Hf⟩
  ihave H := (BigSepL.bigSepL_mono_of_forall
    (Ψ := fun i e => iprop(|={E}=> inv (slotN k i) (slotInv γ cf k γl (allocCons γl L γf) i e) ∗
        (slotChan γ cf (allocCons γl L γf) i e ∗ slotExecPart γl (allocCons γl L γf) i e ∗
          slotHandlerPart γl (allocCons γl L γf) i)))
    (fun {i e} => slotFresh_finish_L γ cf hc k γl E γf L hL i e)) $$ H
  imod (BigSepL2.bigSepL_fupd E _ γl.slots) $$ H with H
  icases BigSepL.bigSepL_sep_eqv.1 $$ H with ⟨Hi, Hr⟩
  imodintro
  iexists allocCons γl L γf
  unfold slotsInv consSlotsRes
  iframe Hi Hr
  have hfz : (allocCons γl L γf).frz = γf := rfl
  rw [hfz]
  iexact Hf

/-- **`readDecision`** (the proxy's `GetDecision`): with a later credit (the slot's invariant's
contents need not be timeless), slot `s`'s state, to give back unchanged, and then the facts of
its decision if it is done. -/
theorem readDecision (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV)
    (he : γl.slots[s]? = some e) (E : CoPset) (hE : ↑(slotN k s) ⊆ E) :
    slotsInv (GF := GF) γ cf k γl γc ∗ £ 1 ⊢
      |={E, E \ ↑(slotN k s)}=> ∃ st, slotSt e.γ st ∗
        (slotSt e.γ st -∗ |={E \ ↑(slotN k s), E}=> decInfo γ cf s st) := by
  iintro ⟨#Hinv, Hlc⟩
  unfold slotsInv
  ihave #Hi := (BigSepL.bigSepL_lookup
    (Φ := fun s e => iprop(inv (slotN k s) (slotInv (GF := GF) γ cf k γl γc s e))) he) $$ Hinv
  imod inv_acc hE $$ Hi with ⟨Hc, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc Hc with Hc
  unfold slotInv
  icases Hc with ⟨%st, Hst, #Hd, Hg⟩
  imodintro
  iexists st
  iframe Hst
  iintro Hst
  imod Hclose $$ [Hst Hg] with -
  · inext; iexists st; iframe Hst Hg; iexact Hd
  imodintro
  iexact Hd

end laws

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions]

/-- `ConsensusInit(k, 0, done, wg, NetToMsgHandler, MsgHandlerToNet, NetToConExecutor,
ConExecutorToNet, ledger)`. -/
abbrev ConsensusInit.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (id : w32) (wg : Loc)
    (ledger : GoSlice), id.toNat = k → k < cf.n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ confRO cf ∗
      srvChans γ cf k γl ch ∗ ledgerRO γl ledger ∗ slotsInv γ cf k γl γc ∗ consSlotsRes γ cf k γl γc ∗
      consensusBootRes γ k γl }}
    (App (App (App (App (App (App (App (App (App (Val (@! ConsensusInit)) (Val #id))
      (Val #(W32 0))) (Val #ch.done)) (Val #wg)) (Val #ch.n2h)) (Val #ch.h2n)) (Val #ch.n2e))
      (Val #ch.e2n)) (Val #ledger))
  {{ (c : Loc), RET #c; consExecRes γ cf k γl γc ch c ∗ consHandlerRes γ cf k γl γc ch c ∗ consStatsRO c }}

/-- `c.Executor()`: never returns. -/
abbrev Consensus.Executor.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ confRO cf ∗
      shared γ ∗ cfgIs γ.rab cf ∗ consExecRes γ cf k γl γc ch c }}
    (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"Executor")) (Val #()))
  {{ RET #(); False }}

/-- `c.MsgHandler()`: never returns. -/
abbrev Consensus.MsgHandler.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ confRO cf ∗
      shared γ ∗ cfgIs γ.rab cf ∗ consHandlerRes γ cf k γl γc ch c }}
    (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"MsgHandler")) (Val #()))
  {{ RET #(); False }}

/-- `c.SlotStats()`: four numbers. -/
abbrev Consensus.SlotStats.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ consStatsRO c }}
    (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"SlotStats")) (Val #()))
  {{ (a b d e : w64), RET (PairV (PairV (PairV #a #b) #d) #e); True }}

end spec

end Perennial.rabia.roles.server.layers.consensus
