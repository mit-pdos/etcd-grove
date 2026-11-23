/-
The run loop's internal specs (`(*Replica).run`, `epaxos.go`): what `New` hands to `go r.run()`
(`runPre`), the specs of the functions `run` calls that this package's other provers own, taken as
hypotheses of the run proof (`HandlerSpecs`: the handlers but `handleCommit`, whose spec is
proved, `HandleCommit.lean`; `ExecuteCommandsSpec`: the executor goroutine), and what the
executor sends to the run loop on `instancesToRecover` (`recoverReq`).

Each handler's spec, in the form the run loop uses it: the instance lock held (its state `σ`,
`ownRep`), the ghost step of its input already taken (`ep_deliver`, `ep_recover`: the handler
starts from the step's outputs, `outsOk`), the handler sends what the step put in the outboxes and
runs its broadcast, and ends idle (`repIdle`) with the step's state. `handlePropose` takes its own
step (`ep_propose`, after draining `ProposeChan`), so its spec starts from the idle fragment.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.CommitWf

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

/-- The `*Replica` field holding the channel of the kind. -/
def MsgKind.chanField : MsgKind → GoString
  | .prepare => go!"prepareChan" | .prepareReply => go!"prepareReplyChan"
  | .preAccept => go!"preAcceptChan" | .preAcceptReply => go!"preAcceptReplyChan"
  | .accept => go!"acceptChan" | .acceptReply => go!"acceptReplyChan"
  | .commit => go!"commitChan" | .tryPreAccept => go!"tryPreAcceptChan"
  | .tryPreAcceptReply => go!"tryPreAcceptReplyChan"

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- A recovery request `iid` the executor sends on `instancesToRecover`: instance `(q, k)`, `k`
at most a known value `n` of the replica's `crtInstance[q]` (`crtLb`). -/
def recoverReq (γ : EpNames) (i : Nat) (iid : Loc) : IProp GF :=
  iprop(∃ (q k : Nat) (n : w32), iid ↦ epaxos.instanceId.mk (W32 q) (W32 k) ∗ crtLb γ i q n ∗
    ⌜q < nR ∧ (k : Int) ≤ zz n⌝)

instance prefOrder_persistent (r : Loc) (i : Nat) (L : List GoString) (ord : List w32) :
    Persistent (prefOrder (GF := GF) r i L ord) := by
  unfold prefOrder; infer_instance

/-- What the handlers know (persistent): the package, the handle, the framework's handle (`Rext`
the protocol layer's part of `r.M`'s invariant), the peer order `ComputeClosestPeers` fixed. -/
def hctx (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (ord : List w32) : IProp GF :=
  iprop(pkgInit_epaxos ∗ isReplica γ i r ∗ efld r go!"Replica" ↦□ rr ∗
    isReplicaFw γ rr i L p Rext ∗ prefOrder rr i L ord)

instance hctx_persistent (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (ord : List w32) : Persistent (hctx γ i r rr L p Rext ord) := by
  unfold hctx prefOrder; infer_instance

/-- The handler `meth` of the protocol messages of kind `k` (`handlePrepare`, ...): from the
delivery's ghost step (`ep_deliver`, with what it knows of the pre-state, `deliverPre`). -/
def HandlerSpec (k : MsgKind) (meth : GoString) : Prop :=
  ∀ (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (σ : RState) (l : Loc) (m : Msg) (fr n : Nat),
  deliverPre fr i n m σ → m.kind = some k → m.wf → fr ≠ i →
  σ.peerOrder = ord.map (fun x => sint.nat x) →
  {{ hctx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ ownMsg l m (DFrac.own 1) ∗
      repFrag γ i (hMsg σ m).1 ∗ outsOk γ i (hMsg σ m).2 }}
    (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! meth)) (Val #l))
  {{ RET #(); ∃ σ' : RState, ownRep γ i r σ' ∗ repFrag γ i σ' ∗ repIdle γ i }}

/-- The checkpoint counter `r.cpcounter` (fork workaround EP-GLOBALS: a `Replica` field;
`handlePropose`'s `r.cpcounter += len(cmds)`, never read for a decision): the run loop's, lent to
`handlePropose`. -/
def cpcOwn (r : Loc) : IProp GF :=
  iprop(∃ v : w64, efld r go!"cpcounter" ↦ v)

/-- `handlePropose(g)`: drains the rest of its batch from `ProposeChan` and takes the proposal
step itself (`ep_propose`); it bumps `r.cpcounter` (`cpcOwn`, lent by the run loop). -/
def ProposeSpec : Prop :=
  ∀ (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (σ : RState) (g : Loc),
  σ.peerOrder = ord.map (fun x => sint.nat x) →
  {{ hctx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ repFrag γ i σ ∗ repIdle γ i ∗
      proposal γ i g ∗ cpcOwn r }}
    (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handlePropose")) (Val #g))
  {{ RET #(); (∃ σ' : RState, ownRep γ i r σ' ∗ repFrag γ i σ' ∗ repIdle γ i) ∗ cpcOwn r }}

/-- `startRecoveryForInstance(q, k)`: from the recovery's ghost step (`ep_recover`). -/
def RecoverSpec : Prop :=
  ∀ (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (σ : RState) (x : InstId),
  (∃ S : Sys, Inv S ∧ i < nR ∧ S.rep i = σ) →
  x.q < nR → (x.i : Int) ≤ zz (σ.crtInstance x.q) →
  σ.peerOrder = ord.map (fun x => sint.nat x) →
  {{ hctx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ repFrag γ i (hRecover σ x).1 ∗
      outsOk γ i (hRecover σ x).2 }}
    (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"startRecoveryForInstance"))
      (Val #(W32 x.q))) (Val #(W32 x.i)))
  {{ RET #(); ∃ σ' : RState, ownRep γ i r σ' ∗ repFrag γ i σ' ∗ repIdle γ i }}

/-- The handlers' specs the run loop calls (their proofs are the handlers' provers'). -/
structure HandlerSpecs : Prop where
  prepare : HandlerSpec (GF := GF) .prepare go!"handlePrepare"
  preAccept : HandlerSpec (GF := GF) .preAccept go!"handlePreAccept"
  accept : HandlerSpec (GF := GF) .accept go!"handleAccept"
  prepareReply : HandlerSpec (GF := GF) .prepareReply go!"handlePrepareReply"
  preAcceptReply : HandlerSpec (GF := GF) .preAcceptReply go!"handlePreAcceptReply"
  acceptReply : HandlerSpec (GF := GF) .acceptReply go!"handleAcceptReply"
  tryPreAccept : HandlerSpec (GF := GF) .tryPreAccept go!"handleTryPreAccept"
  tryPreAcceptReply : HandlerSpec (GF := GF) .tryPreAcceptReply go!"handleTryPreAcceptReply"
  propose : ProposeSpec (GF := GF)
  recover : RecoverSpec (GF := GF)

/-- The executor goroutine (`go r.executeCommands()`, never returns): `r.exec` and its `r` field,
the recovery channel. (Its proof is the executor's prover's.) -/
def ExecuteCommandsSpec : Prop :=
  ∀ (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (e : Loc) (ch : GoChan) (γc : ChanNames),
  {{ hctx (GF := GF) γ i r rr L p Rext ord ∗ efld r go!"exec" ↦□ e ∗
      structFieldRef epaxos.Exec go!"r" e ↦□ r ∗ efld r go!"instancesToRecover" ↦□ ch ∗
      isChanBag γc ch (recoverReq γ i) }}
    (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"executeCommands")) (Val #()))
  {{ RET #(); False }}

/-- What `New` hands to `go r.run()`: the handle and the framework's parts (`fwRO`, the frozen
part, the start resources `ConnectToPeers` takes), the nine kinds' channels with their
invariants, the recovery channel, the executor's `r.exec`, `batchWait = 0`, and the fields only
`run` writes (fork workaround EP-GLOBALS): the clock channels (made and stored by `run` before it
starts `slowClock`, read-only after) and `cpcounter` (`cpcOwn`, lent to `handlePropose`). -/
def runPre (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) :
    IProp GF :=
  iprop(pkgInit_epaxos ∗ isReplica γ i r ∗ efld r go!"Replica" ↦□ rr ∗ fwRO γ rr i L p ∗
    fwFrozen γ rr i p ∗ fwStart γ rr i L p ∗
    ([∗list] k ∈ MsgKind.all, ∃ (ch : GoChan) (γc : ChanNames),
      efld r k.chanField ↦□ ch ∗ isChanBag γc ch (deliverChanP γ i k)) ∗
    (∃ (ch : GoChan) (γc : ChanNames), efld r go!"instancesToRecover" ↦□ ch ∗
      isChanBag γc ch (recoverReq γ i)) ∗
    (∃ e : Loc, efld r go!"exec" ↦□ e ∗ structFieldRef epaxos.Exec go!"r" e ↦□ r) ∗
    efld r go!"batchWait" ↦□ (W64 0) ∗
    (∃ ch : GoChan, efld r go!"slowClockChan" ↦ ch) ∗ (∃ ch : GoChan, efld r go!"fastClockChan" ↦ ch) ∗
    cpcOwn r)

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
