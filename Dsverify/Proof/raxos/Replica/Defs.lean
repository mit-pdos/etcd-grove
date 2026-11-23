/-
Package `replica`'s representation predicates (below the sealed slots of `Slots.lean`): the
recorder's slot states (`slotRep`), its lock invariant (`recInv`: the slots hold the states of the
recorder's half `recHalf γ k m` of the consensus ghost state), its persistent facts
(`isRecorder`), and the server's state after each boot step (`srvProposers`, the bodies of
`serverNew`, `serverNet`, `serverProp`).
-/
module

public import Dsverify.Proof.raxos.Proxy.Slots

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- A Go `Value` holds the model value `pv` (its ids persistent, valid strings). -/
def valRep (v : Value) (pv : pure.Val) : IProp GF :=
  iprop(⌜sint.Z v.priority' = pv.prio ∧ sint.Z v.proposer_id' = pv.pid ∧
      sint.Z v.thread_id' = pv.tid ∧ ∀ x ∈ pv.ids, strOk x⌝ ∗ v.ids' ↦*□ pv.ids)

/-- A `RecorderSlot` holds the slot state `st`. -/
def slotRep (s : RecorderSlot) (st : RecSt) : IProp GF :=
  iprop(⌜sint.Z s.S' = st.S⌝ ∗ valRep s.F' st.F ∗ valRep s.A' st.A ∗ valRep s.M' st.M)

instance valRep_persistent (v : Value) (pv : pure.Val) : Persistent (valRep (GF := GF) v pv) := by
  unfold valRep; infer_instance
instance slotRep_persistent (s : RecorderSlot) (st : RecSt) :
    Persistent (slotRep (GF := GF) s st) := by
  unfold slotRep; infer_instance

/-- The recorder's lock invariant: its slots hold the states of its half `m` of the consensus
ghost state (a slot past the slice is new). -/
def recInv (γ : QNames) (k : Nat) (re : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ss : List RecorderSlot) (m : GMap Int RecSt),
    re.[Recorder, go!"slots"] ↦ sl ∗ sl ↦* ss ∗ ownSliceCap RecorderSlot sl (DFrac.own 1) ∗
    recHalf γ k m ∗
    □ (∀ (j : Nat) (s : RecorderSlot), ⌜ss[j]? = some s⌝ -∗
      slotRep s ((m !! (j : Int)).getD RecSt.init)) ∗
    ⌜∀ i : Int, (i < 0 ∨ (ss.length : Int) ≤ i) → (m !! i).getD RecSt.init = RecSt.init⌝)

/-- The recorder `re` of replica `k` (persistent): its constant fields, its store, its channel to
the proxy, its lock. -/
def isRecorder (γ : QNames) (k : Nat) (re : Loc) : IProp GF :=
  iprop(∃ (cb : Loc) (γs : GName) (ch : Loc) (γc : ChanNames) (mu : Loc),
    re.[Recorder, go!"clientBatches"] ↦□ cb ∗ isStore γ γs cb ∗
    re.[Recorder, go!"recorderToProxyChan"] ↦□ ch ∗ isChanBag γc ch (decisionP γ) ∗
    re.[Recorder, go!"name"] ↦□ (W64 k) ∗
    re.[Recorder, go!"instanceMutex"] ↦□ mu ∗ sync.isMutex mu (recInv γ k re) ∗
    inv consN (consInv γ) ∗ ⌜1 ≤ k ∧ k ≤ 5⌝)

instance decided_persistent' (γ : QNames) (i : Int) (ids : List GoString) :
    Persistent (decided (GF := GF) γ i ids) := by
  unfold decided; infer_instance

instance pmFacts_persistent (γ : QNames) (m : PM) : Persistent (pmFacts (GF := GF) γ m) := by
  unfold pmFacts; infer_instance

instance isRecorder_persistent (γ : QNames) (k : Nat) (re : Loc) :
    Persistent (isRecorder (GF := GF) γ k re) := by
  unfold isRecorder; infer_instance

instance spentLb_persistent' (γ : QNames) (m : Int) : Persistent (spentLb (GF := GF) γ m) := by
  unfold spentLb; infer_instance

instance cfgVal_persistent (n : Nat) (cv : raxos.configuration.InstanceConfig) :
    Persistent (cfgVal (GF := GF) n cv) := by
  unfold cfgVal; infer_instance

/-- The server's constant fields, its channels to and from the proxy, the configuration, the
shared invariants and protocols, the codec (persistent). -/
def srvConsts (γ : QNames) (c : QConf) (k : Nat) (s : Loc) : IProp GF :=
  iprop(∃ (cv : raxos.configuration.InstanceConfig) (toProp fromProp toFetch fromFetch toDec : Loc)
      (γ1 γ2 γ4 γ5 γ6 : ChanNames),
    s.[Server, go!"name"] ↦□ (W64 k) ∗ s.[Server, go!"cfg"] ↦□ cv ∗ cfgVal c.n cv ∗
    s.[Server, go!"numProposers"] ↦□ (W64 (c.pipe + 4)) ∗
    s.[Server, go!"proxyToProposerChan"] ↦□ toProp ∗ isChanBag γ1 toProp (proposeReqP γ k) ∗
    s.[Server, go!"proposerToProxyChan"] ↦□ fromProp ∗ isChanBag γ2 fromProp (proposeRespP γ k) ∗
    s.[Server, go!"proxyToProposerFetchChan"] ↦□ toFetch ∗ isChanBag γ4 toFetch fetchReqP ∗
    s.[Server, go!"proposerToProxyFetchChan"] ↦□ fromFetch ∗ isChanBag γ5 fromFetch (fetchRespP γ) ∗
    s.[Server, go!"proxyToProposerDecisionChan"] ↦□ toDec ∗ isChanBag γ6 toDec (decisionP γ) ∗
    s.[Server, go!"debugOn"] ↦□ false ∗ s.[Server, go!"debugLevel"] ↦□ (W64 0) ∗
    s.[Server, go!"serverMode"] ↦□ (W64 c.se) ∗ s.[Server, go!"isAsync"] ↦□ false ∗
    s.[Server, go!"asyncTimeOut"] ↦□ (W64 0) ∗ s.[Server, go!"timeEpochSize"] ↦□ (W64 500) ∗
    inv consN (consInv γ) ∗ inv smrN (smrInv γ) ∗ netProtos γ ∗ confIs γ c ∗ ⌜c.ok ∧ 1 ≤ k ∧ k ≤ c.n⌝)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance srvConsts_persistent (γ : QNames) (c : QConf) (k : Nat) (s : Loc) :
    Persistent (srvConsts (GF := GF) γ c k s) := by
  unfold srvConsts cfgVal; infer_instance

/-- What the server's proposers need: its constants and the proposers' slice (owned). -/
def srvProposers (γ : QNames) (c : QConf) (k : Nat) (s : Loc) : IProp GF :=
  iprop(srvConsts γ c k s ∗ ∃ psl : GoSlice,
    s.[Server, go!"ProposerInstances"] ↦ psl ∗ psl ↦* ([] : List Loc) ∗
    ownSliceCap Loc psl (DFrac.own 1))

/-- The server's proxy: its fields and its main loop's state. -/
def srvProxy (γ : QNames) (c : QConf) (k : Nat) (s : Loc) : IProp GF :=
  iprop(∃ pr : Loc, s.[Server, go!"ProxyInstance"] ↦□ pr ∗ proxyOwn γ c k pr ∗
    proxyShared γ c k pr)

/-- The server's recorder before `NetworkInit`, with the replica's network resources. -/
def srvRecorder (γ : QNames) (c : QConf) (k : Nat) (s : Loc) : IProp GF :=
  iprop(∃ (re c0 : Loc), s.[Server, go!"RecorderInstance"] ↦□ re ∗
    re.[Recorder, go!"connection"] ↦ c0 ∗
    re.[Recorder, go!"address"] ↦□ recLis k ∗
    isRecorder γ k re ∗ addrTok (proxyAddr k))

end defs

end Perennial.raxos
