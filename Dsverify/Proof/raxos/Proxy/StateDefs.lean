/-
Package `proxy`'s definitions of the proxy's state (the bodies of its sealed slots `proxyOwn`,
`proxyShared` are built from them): the resident store, the executed batches, the known batches,
the replicated log, the answers' channel.
-/
module

public import Dsverify.Proof.raxos.Proxy.StoreDefs
public import Dsverify.Proof.raxos.Proxy.Pure
public import Dsverify.Proof.raxos.Hyp
public import Dsverify.GeneratedProof.raxos.common

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

/-- A Go map holds the store `st`. -/
def storeRel (M : GMap GoString GoString) (st : pure.Store) : Prop := ∀ k, M !! k = st k

/-- The executed-batches map holds the done ids. -/
def doneRel (E : GMap GoString Bool) (done : List GoString) : Prop :=
  ∀ x, (E !! x = some true ↔ x ∈ done) ∧ (E !! x ≠ some false)

instance OutgoingRPC.countable [GooseExts] : Pos.Countable raxos.common.OutgoingRPC :=
  .ofInjective (fun v => Pos.Countable.encode (v.RpcPair', v.Peer'))
    (by rintro ⟨⟩ ⟨⟩ h; have h := Pos.encode_inj h; simp_all)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- A slice's `ClientBatch` values hold the batches `bs` (read for good). -/
def cbsRep (vs : List raxos.proto.client.ClientBatch) (bs : List Batch) : IProp GF :=
  iprop(⌜vs.length = bs.length⌝ ∗
    [∗list] k ↦ v ∈ vs, ∃ b, ⌜bs[k]? = some b⌝ ∗ repCBVal v .discard b)

/-- The resident store of a `Benchmark` (mode 0, key length 8), its map holding `st`. -/
def kvOwn (bm : Loc) (st : pure.Store) : IProp GF :=
  iprop(∃ (kvm : Loc) (M : GMap GoString GoString),
    bm.[Benchmark, go!"mode"] ↦□ W64 0 ∗ bm.[Benchmark, go!"keyLen"] ↦□ W64 8 ∗
    bm.[Benchmark, go!"KVStore"] ↦□ kvm ∗ kvm ↦$ M ∗ ⌜storeRel M st⌝)

/-- The registry's batches the proxy knows (persistent). -/
def knownP (γ : QNames) (Bm : GMap GoString Batch) : IProp GF :=
  iprop([∗map] x ↦ b ∈ Bm, batchReg γ x b ∗ ⌜batchFit b⌝)

instance knownP_persistent (γ : QNames) (Bm : GMap GoString Batch) :
    Persistent (knownP (GF := GF) γ Bm) := by
  unfold knownP; infer_instance

/-- An id the proxy may propose: in the store, a registered well-formed batch's (persistent). -/
def idP (γ : QNames) (γs : GName) (x : GoString) : IProp GF :=
  iprop(storeHasDef γs x ∗ ∃ b, batchReg γ x b ∗ ⌜batchFit b ∧ b.id = x⌝)

/-- Slot `i` of the replicated log, decided `ids` (`some ids`) or not (`none`, then its
proposed ids, if any, are proposable ids, but at a summary slot: its proposal is an epoch
summary, not in the store, never put back). -/
def slotP (γ : QNames) (γs : GName) (c : QConf) (i : Nat) (s : Slot) (o : Option (List GoString)) :
    IProp GF :=
  iprop(⌜s.decided' = o.isSome⌝ ∗
    match o with
    | some ids => s.decidedBatch' ↦*□ ids ∗ ⌜ids ≠ [] ∧ ∀ x ∈ ids, strOk x⌝ ∗
        (if i = 0 then ⌜ids = [go!"nil"]⌝ else decided γ i ids)
    | none => ∃ pids : List GoString, s.proposedBatch' ↦*□ pids ∗
        if decide (sumSlot c.n c.ep i) then iprop(True) else [∗list] x ∈ pids, idP γ γs x)

/-- The replicated log's slots, with their decisions `L`. -/
def logP (γ : QNames) (γs : GName) (c : QConf) (slots : List Slot)
    (L : List (Option (List GoString))) : IProp GF :=
  iprop(⌜slots.length = L.length⌝ ∗
    [∗list] i ↦ s ∈ slots, ∃ o, ⌜L[i]? = some o⌝ ∗ slotP γ γs c i s o)

/-- An answer on the proxy's outgoing channel: client `c`'s request `x`'s result `r`, its
output's answer (persistent). (Stage 3: any of the six clients; whether the answer can be
encoded is learned at the send, P4.) -/
def outP (γ : QNames) (v : raxos.common.OutgoingRPC) : IProp GF :=
  iprop(∃ (rp : raxos.common.RPCPair) (l : Loc) (c : Nat) (x r : GoString), v.RpcPair' ↦□ rp ∗
    ⌜rp.Code' = W8 1 ∧ rp.Obj' = interface.mkOk (go.GoType.PointerType raxos.proto.client.ClientBatch.ty) #l ∧
      c < 6 ∧ sint.Z v.Peer' = clientName c⌝ ∗
    repCB l .discard ⟨x, clientName c, [r]⟩ ∗ opAns γ x r)

/-- The executed prefix of the log: committed index `c`, the decided ids `D` of slots `1..c`,
executed on the resident store with the batches `Bm`. -/
def smrP (γ : QNames) (pr bm ebm : Loc) (L : List (Option (List GoString))) (c : w64)
    (D : List (List GoString)) (Bm : GMap GoString Batch) : IProp GF :=
  iprop(∃ (E : GMap GoString Bool) (t : time.Time),
    pr.[Proxy, go!"committedIndex"] ↦ c ∗ pr.[Proxy, go!"lastTimeCommitted"] ↦ t ∗
    ⌜sint.Z c = D.length ∧ D.length < L.length ∧ L.length ≤ 601 ∧
      ∀ i (h : i < D.length), L[i + 1]? = some (some D[i])⌝ ∗
    execLb γ D ∗ kvOwn bm (execLog (fun x => Bm !! x) D).store ∗ ebm ↦$ E ∗
    ⌜doneRel E (execLog (fun x => Bm !! x) D).done⌝ ∗ knownP γ Bm ∗
    ⌜(∀ x b, Bm !! x = some b → ∀ c ∈ b.cmds, cmdOk c) ∧ (∀ x b, Bm !! x = some b → b.id = x) ∧
      ∀ x ∈ D.flatten, (Bm !! x).isSome⌝)

/-! ## The proxy's state (the bodies of the slots `proxyOwn`, `proxyShared`) -/

instance spentLb_persistent_sd (γ : QNames) (m : Int) : Persistent (spentLb (GF := GF) γ m) := by
  unfold spentLb; infer_instance

def sharedFacts (γ : QNames) (c : QConf) (k : Nat) : IProp GF :=
  iprop(⌜c.ok ∧ 1 ≤ k ∧ k ≤ c.n⌝ ∗
    inv consN (consInv γ) ∗ inv smrN (smrInv γ) ∗ netProtos γ ∗ batchReg γ go!"nil" nilBatch ∗
    spentLb γ 0 ∗ confIs γ c)

instance sharedFacts_persistent (γ : QNames) (c : QConf) (k : Nat) :
    Persistent (sharedFacts (GF := GF) γ c k) := by
  unfold sharedFacts; infer_instance

def sharedConsts (c : QConf) (k : Nat) (pr : Loc) : IProp GF :=
  iprop(pr.[Proxy, go!"name"] ↦□ W64 k ∗
    pr.[Proxy, go!"clientBatchRpc"] ↦□ W8 1 ∗ pr.[Proxy, go!"batchSize"] ↦□ W64 50 ∗
    pr.[Proxy, go!"pipelineLength"] ↦□ W64 c.pipe ∗ pr.[Proxy, go!"leaderMode"] ↦□ W64 2 ∗
    pr.[Proxy, go!"leaderTimeout"] ↦□ W64 c.tmo ∗ pr.[Proxy, go!"epochSize"] ↦□ W64 c.ep ∗
    pr.[Proxy, go!"numReplicas"] ↦□ W64 c.n)

instance sharedConsts_persistent (c : QConf) (k : Nat) (pr : Loc) :
    Persistent (sharedConsts (GF := GF) c k pr) := by
  unfold sharedConsts; infer_instance

def sharedStore (γ : QNames) (γs : GName) (pr cb bm ebm : Loc) : IProp GF :=
  iprop(pr.[Proxy, go!"clientBatchStore"] ↦□ cb ∗ isStoreDef γ γs cb ∗
    pr.[Proxy, go!"benchmark"] ↦□ bm ∗ pr.[Proxy, go!"executedBatches"] ↦□ ebm)

instance sharedStore_persistent (γ : QNames) (γs : GName) (pr cb bm ebm : Loc) :
    Persistent (sharedStore (GF := GF) γ γs pr cb bm ebm) := by
  unfold sharedStore; infer_instance

/-- The proxy's field `f` holds a bag channel with elements `P` (persistent). -/
def chanField {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
    [IntoValTyped (GF := GF) V t] (pr : Loc) (f : GoString) (P : V → IProp GF) : IProp GF :=
  iprop(∃ (ch : Loc) (g : ChanNames), pr.[Proxy, f] ↦□ ch ∗ isChanBag g ch P)

instance chanField_persistent {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    (t : go.GoType) [IntoValTyped (GF := GF) V t] (pr : Loc) (f : GoString) (P : V → IProp GF) :
    Persistent (chanField t pr f P) := by
  unfold chanField; infer_instance

def sharedChans [raxos.replica.src.Assumptions] (γ : QNames) (k : Nat) (pr : Loc) : IProp GF :=
  iprop(chanField raxos.common.OutgoingRPC.ty pr go!"outgoingMessageChan" (outP γ) ∗
    chanField FetchRequest.ty pr go!"proxyToProposerFetchChan" fetchReqP ∗
    chanField ProposeRequest.ty pr go!"proxyToProposerChan" (proposeReqP γ k) ∗
    chanField Decision.ty pr go!"recorderToProxyChan" (decisionP γ) ∗
    chanField Decision.ty pr go!"proxyToProposerDecisionChan" (decisionP γ))

instance sharedChans_persistent [raxos.replica.src.Assumptions] (γ : QNames) (k : Nat) (pr : Loc) :
    Persistent (sharedChans (GF := GF) γ k pr) := by
  unfold sharedChans; infer_instance

end defs

end Perennial.raxos
