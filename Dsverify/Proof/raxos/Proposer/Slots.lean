/-
Package `proposer`'s sealed slots (interface of stage 2, `notes/stage2-plan.md`): their names and
types are the interface; their bodies are the package's to choose (placeholders until package
`proposer` defines them in Prove); clients use them only through the specs of `Replica.lean`.
-/
module

public import Dsverify.Proof.raxos.ReplicaDefs

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

/-! ## A proposer (package `proposer`'s slot) -/

/-- What `NewProposer` returns for replica `k` of the configuration `c` (the proposer's state,
its channels, its `c.n` peers, its server mode `c.se`), persistent: the `Proposer` struct
(read-only for good) with `createProposers`' parameters (`numReplicas = c.n`, name `k`,
`hi = 100000`, server mode `c.se`, not asynchronous), its peers' gRPC clients (`peersP`), its
five channels (bags with the replica's element predicates), the configuration, the consensus
invariant. (The lab's codec facts `codecSet`, `kitCodecOk` are gone: protobuf's specs are
hypotheses here, `Hyp.lean`.) -/
def proposerP (γ : QNames) (c : QConf) (k : Nat) (p : Loc) : IProp GF :=
  iprop(∃ (pv : Proposer) (γ1 γ2 γ4 γ5 γ6 : ChanNames),
    p ↦□ pv ∗
    ⌜c.ok ∧ 1 ≤ k ∧ k ≤ c.n ∧ pv.numReplicas' = W64 c.n ∧ pv.name' = W64 k ∧
      pv.hi' = W64 100000 ∧ pv.serverMode' = W64 c.se ∧ pv.isAsynchronous' = false⌝ ∗
    confIs γ c ∗ peersP γ c.n pv.peers' ∗
    isChanBag γ1 pv.proxyToProposerChan' (proposeReqP γ k) ∗
    isChanBag γ2 pv.proposerToProxyChan' (proposeRespP γ k) ∗
    isChanBag γ4 pv.proxyToProposerFetchChan' fetchReqP ∗
    isChanBag γ5 pv.proposerToProxyFetchChan' (fetchRespP γ) ∗
    isChanBag γ6 pv.proxyToProposerDecisionChan' (decisionP γ) ∗
    inv consN (consInv γ))

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
instance proposerP_persistent (γ : QNames) (c : QConf) (k : Nat) (p : Loc) :
    Persistent (proposerP (GF := GF) γ c k p) := by
  unfold proposerP peersP; infer_instance

end defs

end Perennial.raxos
