/-
The epaxos package closed (the part of dsverify-lab's `Interface/Epaxos.lean` that needs neither the
kit's `Server` nor net/rpc): `epaxos.New`'s spec as the kit's `serve` calls it
(`EpaxosNewSpecEp`, the lab's statement without its `addrTok`: in `Net/` the right to listen at
a replica address is its `addrProto`'s, in `clientInvs`), from `wp_New_of` with the handlers'
specs (`handlerSpecs_of`), the executor's (`executeCommandsSpec_of`), the replica package's
(`replica/Link.lean`) and the wire package's (`wire/Link.lean`) results.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.New
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandlersLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandlePropose
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecuteCommandsProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS] [io.Assumptions]
  [field_sem : net.FieldAssumptions]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- `epaxos.New`'s spec as `serve` calls it. -/
def EpaxosNewSpecEp (isRep : EpNames → Nat → Loc → IProp GF) : Prop :=
  ∀ (γ : EpNames) (k i : Nat) (L : List GoString) (sl : GoSlice) (cfg logger : Loc)
    (c : config.Config),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos ∗
      ⌜k ∈ replicaNodes ∧ L[i]? = some (peerAddrOf k)⌝ ∗ idTok γ i ∗ repFwStart γ i ∗
      epRepStart γ i ∗
      listFinal γ L ∗ sl ↦* L ∗ clientInvs γ ∗
      cfg ↦ c ∗ c.Proxy' ↦ (zeroValDef : config.ProxyInfo) ∗
      ⌜c.Leader' = null ∧ c.Port' = W64 (7500 + k)⌝ ∗
      logger ↦ (zeroValDef : dlog.Logger) }}
    (App (App (App (App (App (App (App (App (App (App (App
      (Val (@! epaxos.New)) (Val #c.Alias')) (Val #(W64 i))) (Val #sl)) (Val #true))
      (Val #false)) (Val #false)) (Val #(W64 0))) (Val #false)) (Val #(W64 2))) (Val #cfg))
      (Val #logger))
  {{ (r : Loc), RET #r; isRep γ i r }}

/-- The handlers' specs as the run loop uses them. -/
theorem handlerSpecs_holds : HandlerSpecs (GF := GF) :=
  handlerSpecs_of replica.Replica.SendMsg.wp_proof replica.Replica.SlowQuorumSize.wp_proof
    state.NOOP.wp_proof dlog_Printf_ok (wp_handlePropose replica.Replica.SendMsg.wp_proof)

/-- The executor goroutine's spec. -/
theorem executeCommandsSpec_holds : ExecuteCommandsSpec (GF := GF) :=
  executeCommandsSpec_of state.Command.Execute.wp_proof replica.Replica.ReplyProposeTS.wp_proof

theorem wp_New : EpaxosNewSpecEp (GF := GF) isReplica :=
  fun γ k i L sl cfg logger c =>
    wp_New_of replica.New.wp_proof rpc.Table.Register.wp_proof
      replica.Replica.ConnectToPeers.wp_proof replica.Replica.ComputeClosestPeers.wp_proof
      replica.Replica.WaitForClientConnections.wp_proof dlog_Printf_ok
      state.Command.String.wp_proof handlerSpecs_holds executeCommandsSpec_holds
      γ k i L sl cfg logger c

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
