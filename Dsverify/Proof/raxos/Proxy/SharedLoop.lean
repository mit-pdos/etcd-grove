/-
Package `proxy`'s definitions of the proxy's state (the bodies of its sealed slots `proxyOwn`,
`proxyShared` are built from them): the resident store, the executed batches, the known batches,
the replicated log, the answers' channel.
-/
module

public import Dsverify.Proof.raxos.Proxy.StateDefs

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

instance NoUnkeyedLiterals.countable [GooseExts] :
    Pos.Countable google_golang_org.protobuf.internal.pragma.NoUnkeyedLiterals :=
  .ofInjective (fun _ => Pos.Countable.encode ()) (by rintro ⟨⟩ ⟨⟩ _; rfl)

instance noCopy.countable [GooseExts] : Pos.Countable Perennial.sync.noCopy :=
  .ofInjective (fun _ => Pos.Countable.encode ()) (by rintro ⟨⟩ ⟨⟩ _; rfl)

instance internalSyncMutex.countable [GooseExts] : Pos.Countable Perennial.internal.sync.Mutex :=
  .ofInjective (fun v => Pos.Countable.encode (v.state', v.sema'))
    (by rintro ⟨_, _⟩ ⟨_, _⟩ h; have h := Pos.encode_inj h; simp_all)

instance syncMutex.countable [GooseExts] : Pos.Countable Perennial.sync.Mutex :=
  .ofInjective (fun v => Pos.Countable.encode v.mu') (by rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩ h; have h := Pos.encode_inj h; simp_all)

instance ClientBatch.countable [GooseExts] : Pos.Countable raxos.proto.client.ClientBatch :=
  .ofInjective (fun v => Pos.Countable.encode ((v.state'.DoNotCompare', v.state'.DoNotCopy',
      v.state'.atomicMessageInfo'), v.sizeCache', v.unknownFields', v.Sender', v.Messages', v.Id'))
    (by rintro ⟨⟨⟨⟩, _, _, _⟩, _, _, _, _, _⟩ ⟨⟨⟨⟩, _, _, _⟩, _, _, _, _, _⟩ h
        have h := Pos.encode_inj h; simp_all)

instance ClientBatchTime.countable [GooseExts] : Pos.Countable ClientBatchTime :=
  .ofInjective (fun v => Pos.Countable.encode (v.batch', v.incomingTime'))
    (by rintro ⟨⟩ ⟨⟩ h; have h := Pos.encode_inj h; simp_all)

instance RPCPair.countable [GooseExts] : Pos.Countable raxos.common.RPCPair :=
  .ofInjective (fun v => Pos.Countable.encode (v.Code', v.Obj'))
    (by rintro ⟨⟩ ⟨⟩ h; have h := Pos.encode_inj h; simp_all)

/-- An element of `incomingChan` (`connectionListener` → main loop): a client batch frame read,
code 1, a registered well-formed batch, owned (the main loop copies `*clientBatch`, which reads
protobuf's runtime fields too), with the credit minted for its frame. Contract between
`NetworkInit` and `Run`. -/
def incomingP (γ : QNames) (v : raxos.common.RPCPair) : IProp GF :=
  iprop(∃ (l : Loc) (b : Batch) (t : Ticket),
    ⌜v.Code' = W8 1 ∧ v.Obj' = interface.mkOk (go.GoType.PointerType raxos.proto.client.ClientBatch.ty) #l ∧
      batchFit b⌝ ∗
    repCB l (DFrac.own 1) b ∗ batchReg γ b.id b ∗ credit γ t)

/-- A client batch ready to be replicated (an element of `clientRequestsChan`, the batch of an
element of `clientBatchTimer`): a registered well-formed batch, read for good, with the credit
minted for its frame. -/
def cbReqP (γ : QNames) (v : raxos.proto.client.ClientBatch) : IProp GF :=
  iprop(∃ (b : Batch) (t : Ticket), repCBVal v .discard b ∗ batchReg γ b.id b ∗ ⌜batchFit b⌝ ∗
    credit γ t)

/-- The main loop's input channels: `incomingChan` (`incomingP`, the contract with
`NetworkInit`), `clientBatchTimer`, `clientRequestsChan` (`cbReqP`), `proposerToProxyChan`
(`proposeRespP`), `proposerToProxyFetchChan` (`fetchRespP`); the batch timer's constant
`requestPropogationTime`. -/
def sharedLoop (γ : QNames) (k : Nat) (pr : Loc) : IProp GF :=
  iprop(∃ hs : raxos.replica.src.Assumptions,
    haveI := hs; iprop(chanField raxos.common.RPCPair.ty pr go!"incomingChan" (incomingP γ) ∗
    chanField ClientBatchTime.ty pr go!"clientBatchTimer" (fun v => cbReqP γ v.batch') ∗
    chanField raxos.proto.client.ClientBatch.ty pr go!"clientRequestsChan" (cbReqP γ) ∗
    chanField ProposeResponse.ty pr go!"proposerToProxyChan" (proposeRespP γ k) ∗
    chanField FetchResposne.ty pr go!"proposerToProxyFetchChan" (fetchRespP γ) ∗
    ∃ rpt : w64, pr.[Proxy, go!"requestPropogationTime"] ↦□ rpt))

instance sharedLoop_persistent (γ : QNames) (k : Nat) (pr : Loc) :
    Persistent (sharedLoop (GF := GF) γ k pr) := by
  unfold sharedLoop; infer_instance

end defs

end Perennial.raxos
