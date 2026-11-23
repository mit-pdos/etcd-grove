/-
Ported from dsverify-lab examples/epaxos/proof/Epaxos/Proof/wire/Link.lean (notes/dsv-epaxos.md);
the lab's treemap results are gone (`StateTreemap`, `Interface/Treemap.lean`).

The wire package's results under the names its callers link against: for each spec
`<Fn>.spec : Prop` of `Epaxos/Interface/{Marshal,State,Misc}.lean`, `<Fn>.wp_proof : <Fn>.spec`
(the epaxos per-kind specs as `∀ k`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.StateOps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.StateUnm
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosFixed
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosPreAccept
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosPreAcceptU
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosCommitU
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosTryPreAcceptU
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosAcceptU
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosPrepareReplyU
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosPreAcceptReplyU
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosAcceptM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosCommitM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosTryPreAcceptM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosPrepareReplyM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosPreAcceptReplyM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Varint
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.InitState
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.Nil
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.Noop
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.Execute
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.Conflict
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.ConflictBatch
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.String
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Misc.Dlog
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Misc.IsProxy
public import Proof.bufio.Writer__Flush
public import Proof.bufio.Writer__WriteByte
public import Proof.bufio.Writer__Write
public import Proof.bufio.Reader__ReadByte
public import Proof.bufio.Reader__ReadOk
public import Proof.bufio.NewReaderOk
public import Proof.bufio.NewReaderSize
public import Proof.bufio.NewWriter
public import Proof.bufio.NewWriterSize
public import Proof.bufio.NewWriterSizeRep

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]

/-! ## `state` -/

section
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
  [TH : StateTreemap GF]
theorem state.InitState.wp_proof : state.InitState.spec (GF := GF) := state.InitState.spec_holds
theorem state.NIL.wp_proof : state.NIL.spec (GF := GF) := state.NIL.spec_holds
theorem state.NOOP.wp_proof : state.NOOP.spec (GF := GF) := state.NOOP.spec_holds
theorem state.Command.Execute.wp_proof : state.Command.Execute.spec (GF := GF) :=
  state.Command.Execute.spec_holds
theorem state.Conflict.wp_proof : state.Conflict.spec (GF := GF) := state.Conflict.spec_holds
theorem state.ConflictBatch.wp_proof : state.ConflictBatch.spec (GF := GF) := state.ConflictBatch.spec_holds
theorem state.Command.String.wp_proof : state.Command.String.spec (GF := GF) :=
  state.Command.String.spec_holds
end

/-! ## `dlog`, `config` -/

section
variable [replica.Assumptions]
theorem dlog.Logger.Println.wp_proof : dlog.Logger.Println.spec (GF := GF) := dlog.Logger.Println.spec_holds
theorem dlog.Logger.Printf.wp_proof : dlog.Logger.Printf.spec (GF := GF) := dlog.Logger.Printf.spec_holds
theorem dlog.Logger.Fatal.wp_proof : dlog.Logger.Fatal.spec (GF := GF) := dlog.Logger.Fatal.spec_holds
theorem config.ProxyInfo.IsProxy.wp_proof : config.ProxyInfo.IsProxy.spec (GF := GF) :=
  config.ProxyInfo.IsProxy.spec_holds
end

/-! ## Marshalers -/

section
variable [state.Assumptions] [replica.defs.Assumptions] [epaxos.Assumptions] [bufio.Assumptions]
  [io.Assumptions]

/-- bufio's proofs, the wire proofs' hypothesis `EpBufioDeps` (`Interface/LibDeps.lean`), a local
instance of this section only. -/
theorem epBufioDeps_holds : EpBufioDeps GF where
  flush := EtcdGrove.bufio.Writer.Flush.wp_proof
  writeByte := EtcdGrove.bufio.Writer.WriteByte.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof
  write := EtcdGrove.bufio.Writer.Write.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof
  readByte := EtcdGrove.bufio.Reader.ReadByte.wp_proof
  readOk := EtcdGrove.bufio.Reader.Read.wp_proofOk
  newReaderOk := EtcdGrove.bufio.NewReader.wp_proofOk
    (EtcdGrove.bufio.NewReader.wp_proofE EtcdGrove.bufio.NewReaderSize.wp_proofE)
  newWriter := EtcdGrove.bufio.NewWriter.wp_proof
    (EtcdGrove.bufio.NewWriterSize.wp_proof EtcdGrove.bufio.NewWriterSize.wp_proofRep)

attribute [local instance] epBufioDeps_holds

theorem state.Operation.Marshal.wp_proof : state.Operation.Marshal.spec (GF := GF) :=
  state.Operation.Marshal.spec_holds
theorem state.Operation.Unmarshal.wp_proof : state.Operation.Unmarshal.spec (GF := GF) :=
  state.Operation.Unmarshal.spec_holds
theorem state.Key.Marshal.wp_proof : state.Key.Marshal.spec (GF := GF) := state.Key.Marshal.spec_holds
theorem state.Key.Unmarshal.wp_proof : state.Key.Unmarshal.spec (GF := GF) := state.Key.Unmarshal.spec_holds
theorem state.Value.Marshal.wp_proof : state.Value.Marshal.spec (GF := GF) := state.Value.Marshal.spec_holds
theorem state.Value.Unmarshal.wp_proof : state.Value.Unmarshal.spec (GF := GF) :=
  state.Value.Unmarshal.spec_holds
theorem state.Command.Marshal.wp_proof : state.Command.Marshal.spec (GF := GF) :=
  state.Command.Marshal.spec_holds
theorem state.Command.Unmarshal.wp_proof : state.Command.Unmarshal.spec (GF := GF) :=
  state.Command.Unmarshal.spec_holds

theorem replica.defs.Propose.Marshal.wp_proof : replica.defs.Propose.Marshal.spec (GF := GF) :=
  replica.defs.Propose.Marshal.spec_holds
theorem replica.defs.Propose.Unmarshal.wp_proof : replica.defs.Propose.Unmarshal.spec (GF := GF) :=
  replica.defs.Propose.Unmarshal.spec_holds
theorem replica.defs.ProposeReplyTS.Marshal.wp_proof : replica.defs.ProposeReplyTS.Marshal.spec (GF := GF) :=
  replica.defs.ProposeReplyTS.Marshal.spec_holds
theorem replica.defs.ProposeReplyTS.Unmarshal.wp_proof :
    replica.defs.ProposeReplyTS.Unmarshal.spec (GF := GF) :=
  replica.defs.ProposeReplyTS.Unmarshal.spec_holds
theorem replica.defs.Beacon.Marshal.wp_proof : replica.defs.Beacon.Marshal.spec (GF := GF) :=
  replica.defs.Beacon.Marshal.spec_holds
theorem replica.defs.Beacon.Unmarshal.wp_proof : replica.defs.Beacon.Unmarshal.spec (GF := GF) :=
  replica.defs.Beacon.Unmarshal.spec_holds
theorem replica.defs.BeaconReply.Marshal.wp_proof : replica.defs.BeaconReply.Marshal.spec (GF := GF) :=
  replica.defs.BeaconReply.Marshal.spec_holds
theorem replica.defs.BeaconReply.Unmarshal.wp_proof : replica.defs.BeaconReply.Unmarshal.spec (GF := GF) :=
  replica.defs.BeaconReply.Unmarshal.spec_holds

theorem epaxos.putVarint.wp_proof : epaxos.putVarint.spec (GF := GF) := epaxos.putVarint.spec_holds
theorem epaxos.readVarint.wp_proof : epaxos.readVarint.spec (GF := GF) := epaxos.readVarint.spec_holds

theorem epaxos.Marshal.wp_proof : ∀ k, epaxos.Marshal.spec (GF := GF) k := by
  intro k
  cases k
  · exact epaxos.Marshal.spec_prepare
  · exact epaxos.Marshal.spec_prepareReply
  · exact epaxos.Marshal.spec_preAccept
  · exact epaxos.Marshal.spec_preAcceptReply
  · exact epaxos.Marshal.spec_accept
  · exact epaxos.Marshal.spec_acceptReply
  · exact epaxos.Marshal.spec_commit
  · exact epaxos.Marshal.spec_tryPreAccept
  · exact epaxos.Marshal.spec_tryPreAcceptReply

theorem epaxos.Unmarshal.wp_proof : ∀ k, epaxos.Unmarshal.spec (GF := GF) k := by
  intro k
  cases k
  · exact epaxos.Unmarshal.spec_prepare
  · exact epaxos.Unmarshal.spec_prepareReply
  · exact epaxos.Unmarshal.spec_preAccept
  · exact epaxos.Unmarshal.spec_preAcceptReply
  · exact epaxos.Unmarshal.spec_accept
  · exact epaxos.Unmarshal.spec_acceptReply
  · exact epaxos.Unmarshal.spec_commit
  · exact epaxos.Unmarshal.spec_tryPreAccept
  · exact epaxos.Unmarshal.spec_tryPreAcceptReply

theorem epaxos.New.wp_proof : ∀ k, epaxos.New.spec (GF := GF) k := epaxos.New.spec_all

theorem Serializable.Marshal.wp_proof : Serializable.Marshal.spec (GF := GF) :=
  (Serializable_specs epaxos.Marshal.wp_proof epaxos.Unmarshal.wp_proof epaxos.New.wp_proof).1
theorem Serializable.New.wp_proof : Serializable.New.spec (GF := GF) :=
  (Serializable_specs epaxos.Marshal.wp_proof epaxos.Unmarshal.wp_proof epaxos.New.wp_proof).2.1
theorem Serializable.Unmarshal.wp_proof : Serializable.Unmarshal.spec (GF := GF) :=
  (Serializable_specs epaxos.Marshal.wp_proof epaxos.Unmarshal.wp_proof epaxos.New.wp_proof).2.2

end

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
