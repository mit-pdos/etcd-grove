/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecDefs.lean`, run `rabia-r1wake-1`.)

The executor's internal design (statements; proofs to come): its state between slots (`exIdle`) and
while deciding a slot (`exRun`), and the specs of the executor's functions against which each is
proved independently.

* History `H` (slots `< t`): my proposal and my decision of each; their facts (`histFacts`) give
  `PropOk`'s first clause, the pending tokens of the matched ones (`matchedToks`) its second (an
  object popped later has its own token: the same receipt `rcpt X j`, exclusive).
* Keys: the consensus side's keys `Ke` are of slots `< t`, or of slot `t` and written this slot
  (`cur`): a new key of slot `t` not in `cur` is free (`KeysEx`).
* `E_k`: the log `L` (its authority `exAuth`) and the SPSC sends, `ExLogOk L`, and the rounds of slot
  `t` sent so far are `0 .. ρs-1` (`ExLogPos`).
* The slot `t`'s local state (`ExSlot`): its private fields, my proposal with its token, the consumed
  notifications (in sync mode: rounds `0 .. n-1`, no decision), the executor's half of `exName`.
* The justification of the next state/vote to send (`nextJust`), of a decision (`decJust`), and the
  decided facts handed to `epilogue` (`decidedW`).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.Helpers
public import Dsverify.Proof.rabia.roles.server.layers.consensus.Pure

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

/-! ## Pure parts -/

/-- The slot of a key the executor writes (`none`: not the executor's kind). -/
def _root_.Perennial.rabia.model.FKey.slotOf : FKey → Option Nat
  | .prop _ s => some s
  | .st _ s _ => some s
  | .vt _ s _ => some s
  | .mydec _ s => some s
  | .preq _ s => some s
  | _ => none



/-- The consensus side's keys: of slots before `t`, or of slot `t` among `cur`. -/
def KeysEx (t : Nat) (cur Ke : List FKey) : Prop :=
  (∀ key ∈ Ke, ∃ s, key.slotOf = some s ∧ (s < t ∨ (s = t ∧ key ∈ cur))) ∧
  (∀ key ∈ cur, key.slotOf = some t)

/-- `E_k`'s round messages: of slots before `t`, or of slot `t` below `ρs`; slot `t`'s rounds
`0 .. ρs-1` all present. -/
def ExLogPos (L : List MsgV) (t ρs : Nat) : Prop :=
  (∀ m ∈ L, ∀ s ρ, msgRound m = some (s, ρ) → s < t ∨ (s = t ∧ ρ < ρs)) ∧
  (∀ ρ < ρs, ∃ m ∈ L, msgRound m = some (t, ρ))

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}

/-- The executor's global ghost knowledge. -/
structure ExSt where
  /-- the current (started) or next slot -/
  t : Nat
  /-- my proposal and decision of each slot before `t` -/
  H : List (ObjV × DVal)
  /-- the commands of the decided slots before `t` -/
  cmds : List GoString
  /-- the consensus side's keys -/
  Ke : List FKey
  /-- `E_k` -/
  L : List MsgV
  /-- the values sent on `ConExecutorToNet` -/
  sent : List Msg

/-- The executor's round of a slot at `(phase, round)` (`round ∈ {1, 2}`). -/
def exRound (pv : PrivSt) : Nat := 2 * pv.phase.toNat + pv.round.toNat - 1

/-- The slot's local knowledge. -/
structure ExSlot where
  /-- my proposal -/
  o : ObjV
  /-- the private fields -/
  pv : PrivSt
  /-- the consumed notifications and their log entries -/
  recv : List Msg
  ql : List (Option Nat)
  /-- the rounds of this slot sent on `E_k` -/
  ρs : Nat
  /-- the keys written this slot -/
  cur : List FKey

/-- Same slot, same history, same proposal and consumed notifications; the logs may grow. -/
def ExStep (σ : ExSt) (x : ExSlot) (σ' : ExSt) (x' : ExSlot) : Prop :=
  σ'.t = σ.t ∧ σ'.H = σ.H ∧ σ'.cmds = σ.cmds ∧ x'.o = x.o ∧ x'.recv = x.recv ∧ x'.ql = x.ql

/-- The facts of my proposals and decisions of the slots before (persistent). -/
def histFacts (γ : Names) (k : Nat) (H : List (ObjV × DVal)) : IProp GF :=
  iprop([∗list] i ↦ x ∈ H, fact γ.rab (.prop k i) (.obj (objId x.1)) ∗
    fact γ.rab (.mydec k i) (.dval x.2))

/-- The tokens of my matched proposals (decided as proposed). -/
def matchedToks (γ : Names) (cf : RCfg) (γl : SrvNames) (H : List (ObjV × DVal)) : IProp GF :=
  iprop([∗list] x ∈ H, if x.2 = .obj (objId x.1) then pendOk γ cf γl x.1 else iprop(emp))

/-- The `Coin` field holds a usable `rand.Rand` (as `Helpers.coinOk`, stated generically). -/
def exCoinOk (c : Loc) : IProp GF :=
  iprop(∃ (r : Loc) (R : Loc → IProp GF), structFieldRef Consensus go!"Coin" c ↦ r ∗ R r ∗
    ⌜math.rand.Rand.Intn.spec (GF := GF) R⌝)

/-- The messages the executor builds. -/
def propMsg (o : ObjV) (s : Nat) : MsgV :=
  { ty := tyProposal, phase := 0, value := 0, obj := some { o with svrSeq := W32 s } }
def bcMsg (s : Nat) (pse rod x : w32) : MsgV :=
  { ty := if rod = 1 then tyState else tyVote, phase := pse, value := x,
    obj := some { (default : ObjV) with svrSeq := W32 s } }
def decMsg (o : ObjV) (s : Nat) : MsgV :=
  { ty := tyDecision, phase := 0, value := 0, obj := some { o with svrSeq := W32 s } }

/-- The executor-owned fields but `SvrSeq` and `Coin`. -/
def exFields (cf : RCfg) (c : Loc) : IProp GF :=
  iprop((∃ (mp : GoMap) (dm : GMap w64 Bool), structFieldRef Consensus go!"Discard" c ↦ mp ∗
      ownMap mp (DFrac.own 1) dm) ∗
    (∃ (a b d : w64), structFieldRef Consensus go!"CurrConsecutiveNulls" c ↦ a ∗
      structFieldRef Consensus go!"MaxConsecutiveNulls" c ↦ b ∗
      structFieldRef Consensus go!"MaxConsecutiveNullsEndSeq" c ↦ d) ∗
    (∃ t : w32, structFieldRef Consensus go!"TotalRounds" c ↦ t) ∗
    (∃ (sl : GoSlice) (xs : List w64), structFieldRef Consensus go!"NumOfRoundsDist" c ↦ sl ∗
      sl ↦* xs ∗ ⌜xs.length = 2 * cf.blockLen + 2⌝))

/-- The slots from `n` on, fresh. -/
def freshSlots (γl : SrvNames) (γc : ConsNames) (n : Nat) : IProp GF :=
  iprop([∗list] s ↦ e ∈ γl.slots, if n ≤ s then slotExecPart γl γc s e else iprop(emp))

/-- What the executor keeps across slots and rounds (`cur`, `ρs`: the current slot's keys and
rounds sent; `n`: the first fresh slot). -/
def exCommon (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (σ : ExSt) (cur : List FKey) (ρs n : Nat) : IProp GF :=
  iprop(consRO γ cf k γl γc ch c ∗ exFields cf c ∗
    histFacts γ k σ.H ∗ matchedToks γ cf γl σ.H ∗ ⌜σ.H.length = σ.t⌝ ∗
    prefixFacts γ.rab σ.t σ.cmds ∗
    keysPart γl false σ.Ke ∗ ⌜KeysEx σ.t cur σ.Ke⌝ ∗
    exAuth γl σ.L ∗ spscProducer γl.e2n σ.sent ∗
    ⌜σ.sent.length = σ.L.length ∧ ExLogOk σ.L ∧ ExLogPos σ.L σ.t ρs⌝ ∗
    freshSlots γl γc n)

/-- Between slots: slot `σ.t` is next (`SvrSeq = t - 1`). -/
def exIdle (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (σ : ExSt) : IProp GF :=
  iprop(exCommon γ cf k γl γc ch c σ [] 0 σ.t ∗
    (∃ coin : Loc, structFieldRef Consensus go!"Coin" c ↦ coin) ∗
    structFieldRef Consensus go!"SvrSeq" c ↦ (W64 ((σ.t : Int) - 1) : w64) ∗ ⌜σ.t ≤ lenLedger⌝)

/-- Slot `t`'s local resources: its private part, my proposal's token, its queue's consumed
notifications (sync mode: the rounds `0 .. n-1` in order, no decision), the executor's half of
`exName` (not done). -/
def exSlotRes (γ : Names) (cf : RCfg) (γl : SrvNames) (γc : ConsNames) (t : Nat) (x : ExSlot) : IProp GF :=
  iprop(∃ e, ⌜γl.slots[t]? = some e⌝ ∗ slotPriv e.loc x.pv ∗ ⌜x.pv.myProp = x.o⌝ ∗
    pendOk γ cf γl x.o ∗ spscConsumer (γc.queue t) x.recv ∗ qLb γc t x.ql ∗
    ⌜x.recv.length = x.ql.length ∧ x.ql.filterMap id = List.range (x.ql.filterMap id).length ∧
      True⌝ ∗
    ghostVar (exName γl γc t) (1 : Qp).half false)

/-- Deciding slot `σ.t` (`SvrSeq = t`). -/
def exRun (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (σ : ExSt) (x : ExSlot) : IProp GF :=
  iprop(exCommon γ cf k γl γc ch c σ x.cur x.ρs (σ.t + 1) ∗ exCoinOk c ∗
    structFieldRef Consensus go!"SvrSeq" c ↦ (W64 (σ.t : Int) : w64) ∗ ⌜σ.t < lenLedger⌝ ∗
    exSlotRes γ cf γl γc σ.t x)

/-- A fact insertable by `fact_insert` (its rule's justification, persistent). -/
def factJust (γ : Names) (key : FKey) (val : FVal) : IProp GF :=
  iprop(∃ S : List (FKey × FVal), ([∗list] kv ∈ S, fact γ.rab kv.1 kv.2) ∗
    ⌜∀ M, Valid M → (∀ kv ∈ S, M kv.1 = some kv.2) → M key = none → Valid (M.set key val)⌝)

/-- The justification of the next message of slot `t` at `pv` (the state of a phase `≥ 1` at
round 1, the vote at round 2; the proposal's is `PropOk`, from the history). -/
def nextJust (γ : Names) (k t : Nat) (pv : PrivSt) : IProp GF :=
  if pv.round = 1 ∧ pv.phase ≠ 0 then
    factJust γ (.st k t pv.phase.toNat) (.bit (pv.my pv.phase.toNat 1).toNat)
  else if pv.round = 2 then
    factJust γ (.vt k t pv.phase.toNat) (.bit (pv.my pv.phase.toNat 2).toNat)
  else iprop(True)

/-- A decision's justification (`DecEvidence` in every valid record at `cf` with the facts `S`). -/
def decJust (γ : Names) (cf : RCfg) (t : Nat) (d : DVal) : IProp GF :=
  iprop(∃ S : List (FKey × FVal), ([∗list] kv ∈ S, fact γ.rab kv.1 kv.2) ∗
    ⌜∀ M, CfgOf M cf → ValidAt cf M → (∀ kv ∈ S, M kv.1 = some kv.2) → DecEvidence cf M t d⌝)

/-- The evidence of a decision on the bit `b` (`DecEvidence` once the decision means `b`:
`BitDec`), in every valid record at `cf` with the facts `S`. -/
def bitEvW (γ : Names) (cf : RCfg) (t b : Nat) : IProp GF :=
  iprop(∃ S : List (FKey × FVal), ([∗list] kv ∈ S, fact γ.rab kv.1 kv.2) ∗
    ⌜∀ M, CfgOf M cf → ValidAt cf M → (∀ kv ∈ S, M kv.1 = some kv.2) →
      ∀ d, BitDec cf M t b d → DecEvidence cf M t d⌝)

/-- Slot `t` decided `d` by me, the decision object `o` represented by `v`. -/
def decidedW (γ : Names) (cf : RCfg) (k t : Nat) (d : DVal) (o : ObjV) (v : ConsensusObj) : IProp GF :=
  iprop(fact γ.rab (.mydec k t) (.dval d) ∗ fact γ.rab (.dec t) (.dval d) ∗ decObjOk γ cf t d o ∗
    objRep v o)

/-- The `q` counted values of round `ρ` of slot `t` (frozen: persistent). -/
def frozenVals (cf : RCfg) (γl : SrvNames) (γc : ConsNames) (t ρ : Nat) (vs : List Nat) : IProp GF :=
  iprop(∃ ents : List Ent, monoListLbOwn (entName γl γc t) ents ∗
    ⌜(tally ents ρ).map (fun e => e.2.2.2.value.toNat) = vs ∧ (tally ents ρ).length = cf.q⌝)

/-- A majority of the servers proposed `id` for slot `t` (persistent; `MajProp`'s facts). -/
def majPropW (γ : Names) (cf : RCfg) (t : Nat) (id : ObjId) : IProp GF :=
  iprop(∃ W : List Nat, ⌜(W.Nodup ∧ ∀ X ∈ W, X < cf.n) ∧ W.length ≥ cf.maj⌝ ∗
    [∗list] X ∈ W, fact γ.rab (.prop X t) (.obj id))

/-- The executor's loop invariant. -/
def exLoopInv (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) :
    IProp GF :=
  iprop(∃ σ, exIdle γ cf k γl γc ch c σ)

end defs

/-! ## Laws (statements) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}

/-- (Unfolds Ghost's `rabiaInvAt`, `KeysOk`.) A writer's key set is the recorded keys it writes. -/
theorem invAt_keys (E : CoPset) (γ : RabiaNames) (M : Facts) (W : Writer) (K : List FKey) :
    ▷ rabiaInvAt (GF := GF) γ M ∗ keysOf γ W K ⊢
      |={E}=> ⌜∀ key, key.writer = some W → (key ∈ K ↔ M key ≠ none)⌝ ∗ keysOf γ W K ∗
        ▷ rabiaInvAt γ M := by
  iintro ⟨Hi, HK⟩
  unfold rabiaInvAt
  icases Hi with ⟨%MG, %KS, %n, Hf, HMG, Hfs, >Hk, >%HKS, Hrest⟩
  ihave %hl := keysOf_lookup γ KS W K $$ Hk HK
  imodintro
  isplitr
  · ipureintro
    intro key hw
    have h := HKS key
    constructor
    · intro hk
      exact (h.mp ⟨W, hw, K, hl, hk⟩).1
    · intro hm
      obtain ⟨W', hw', K', hl', hk'⟩ := h.mpr ⟨hm, by rw [hw]; simp⟩
      rw [hw] at hw'; cases hw'
      rw [hl] at hl'; cases hl'
      exact hk'
  iframe HK
  inext
  iexists MG, KS, n
  iframe
  ipureintro; exact HKS

/-- (A missing law of `Ghost.lean`, proved by unfolding `isRabia`/`rabiaInv`/`KeysOk`.) A recorded
fact whose writer is `W` is among `W`'s written keys. -/
theorem fact_mine (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (W : Writer) (K : List FKey)
    (key : FKey) (v : FVal) :
    isRabia (GF := GF) γ ∗ keysOf γ W K ∗ fact γ key v ⊢
      |={E}=> keysOf γ W K ∗ ⌜key.writer = some W → key ∈ K⌝ := by
  unfold isRabia
  iintro ⟨#Hinv, HK, #Hx⟩
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  unfold rabiaInv
  icases Hi with ⟨%M, >%HV, Hi⟩
  imod invAt_fact_in _ γ M key v $$ [Hi Hx] with ⟨%hm, Hi⟩
  · iframe Hi; iexact Hx
  imod invAt_keys _ γ M W K $$ [Hi HK] with ⟨%hk, HK, Hi⟩
  · iframe
  imod Hclose $$ [Hi] with -
  · inext; iexists M; iframe Hi; ipureintro; exact HV
  imodintro
  iframe HK
  ipureintro
  intro hw
  exact (hk key hw).mpr (by rw [hm]; simp)

end laws

/-! ## The functions' specs (statements) -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions] [π : NetProtoGS]

/-- The other packages' specs the executor uses. -/
structure ExDeps : Prop where
  getIsDone : Slot.GetIsDone.spec (GF := GF)
  getHasRecvDec : Slot.GetHasRecvDec.spec (GF := GF)
  setDecision : Slot.SetDecision.spec (GF := GF)
  majV : Slot.RecvProposalsMajV.spec (GF := GF)
  majT : Slot.RecvProposalsMajT.spec (GF := GF)
  bcMajV : Slot.RecvBCMsgsMajV.spec (GF := GF)
  bcMajT : Slot.RecvBCMsgsMajT.spec (GF := GF)
  setMyProposal : Slot.SetMyProposal.spec (GF := GF)
  getMyProposal : Slot.GetMyProposal.spec (GF := GF)
  setMyBC : Slot.SetMyBCMsgs.spec (GF := GF)
  getMyBC : Slot.GetMyBCMsgs.spec (GF := GF)
  incr : Slot.IncrPhaseDecrRound.spec (GF := GF)
  push : heapPush.spec (GF := GF)
  pop : heapPop.spec (GF := GF)
  len : PQueue.Len.spec (GF := GF)
  seqIdEq : ProxySeqIdEqual.spec (GF := GF)

/-- The common precondition: package, configuration, the shared state. -/
abbrev exPre (γ : Names) (cf : RCfg) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ confRO cf ∗ shared γ ∗
    cfgIs γ.rab cf)

variable (D : ExDeps (GF := GF))
include D
variable (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames)
  (ch : SrvChans) (c : Loc)

/-- The result of an AfterWait: decided (`true`: the decision's facts, `Round` moved on), or the
next message's justification. -/
def afterPost (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (σ : ExSt) (x : ExSlot) (pv' : PrivSt) (v : ConsensusObj) (b : Bool) : IProp GF :=
  if b then iprop(∃ σ' x' d o, exRun γ cf k γl γc ch c σ' x' ∗
      ⌜ExStep σ x σ' x' ∧ FKey.mydec k σ.t ∈ σ'.Ke⌝ ∗ decidedW γ cf k σ.t d o v)
  else iprop(∃ σ' x', exRun γ cf k γl γc ch c σ' x' ∗
      ⌜ExStep σ x σ' x' ∧ x'.pv = pv' ∧ x'.ρs = x.ρs ∧ x'.cur = x.cur ∧
        (pv'.phase = x.pv.phase ∨ pv'.phase.toNat = x.pv.phase.toNat + 1)⌝ ∗ nextJust γ k σ.t pv')

end spec

end Perennial.rabia.roles.server.layers.consensus
