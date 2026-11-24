/-
The gryff kit's links (dsv-epaxos's and craq's `Link.lean`, paxos's `Linked.lean`): every proof of
the kit applied to its callees' results. Net's specs (`netN.NetSpecs`: `Conn.Read/Write/Close/
RemoteAddr`, `Listener.Accept`, `Listen`, `Dial`, `DialTimeout`) and dsv-bufio's
(`wire.BufioSpecs`) are built here from their `wp_proof`s (bundles given by `haveI`, never an
`instance`); the RPC layer's codec laws (`gryffCodecLaws`, `gryffRcvLaws`); Net's net/rpc
(`Client.Call`, `SetCodec`, the package-level `Register` on `defaultServer`); `io.ReadFull`'s
every-length form (`lib.io.ReadFull.wp_proofLt`); the kit's model (`Model.wp_proof`); remote's
`Check`/`ServeClient`. `encoding/binary`'s varints (`binaryVarintHyps`, Perennial's proofs). What is not proved stays
a premise (the statement's): the `InitHyp`s, `StringsIndexHyp`, `SortSliceHyp`, `MathPowHyp`, `RandSeedHyp`, `RpcHttpAddr`,
`RpcHttpHyp`, `RpcBootHyp`. `DialHTTP` is Net's `net.rpc.DialHTTP.wp`, over Perennial's proofs of
`strings.Cut`/`TrimLeft`.
-/
module

public import Dsverify.Proof.gryff.examples.gryffnet.KitServer
public import Dsverify.Proof.gryff.examples.gryffnet.KitProof
public import Dsverify.Proof.gryff.examples.gryffnet.KitOp
public import Dsverify.Proof.gryff.examples.gryffnet.ModelProof
public import Dsverify.Proof.gryff.Replica2.Results
public import Dsverify.Proof.gryff.Rpc.CodecProof
public import Dsverify.Proof.gryff.Lib.ReadFullLtProof
public import Net.Proof.net.rpc.putU64
public import Net.Proof.net.rpc.putString
public import Net.Proof.net.rpc.putFrame
public import Net.Proof.net.rpc.getCodec
public import Net.Proof.net.rpc.SetCodec
public import Net.Proof.net.rpc.clientCodec__WriteRequest
public import Net.Proof.net.rpc.Call__done
public import Net.Proof.net.rpc.Client__send
public import Net.Proof.net.rpc.Client__Go
public import Net.Proof.net.rpc.Client__Call
public import Net.Proof.net.rpc.Results
public import Dsverify.Proof.gryff.Wire.Proof.VarintHolds
public import Perennial.Proof.sync.Link
public import Net.Proof.net.Listen
public import Net.Proof.net.Dial
public import Net.Proof.net.DialTimeout
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Conn__RemoteAddr
public import Net.Proof.net.Listener__Accept
public import Proof.bufio.NewWriter
public import Proof.bufio.NewWriterSize
public import Proof.bufio.NewReaderOk
public import Proof.bufio.NewReaderSize
public import Proof.bufio.Reader__ReadOk
public import Proof.bufio.Reader__ReadByte
public import Proof.bufio.Writer__Write
public import Proof.bufio.Writer__WriteByte
public import Proof.bufio.Writer__Flush
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link
public import Proof.bufio.NewWriterSizeRep
public import Net.Proof.net.rpc.Results

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.EtcdGrove.dsvgryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.gryff Perennial.gryff.examples.gryffnet
open Perennial.github_com.mit_pdos.etcd_grove.examples.lib.remote

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- dsv-bufio's specs the wire layer uses, from their proofs. -/
theorem bufioSpecs [bufio.Assumptions] : wire.BufioSpecs GF :=
  ⟨EtcdGrove.bufio.Writer.Write.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof,
    EtcdGrove.bufio.Writer.Flush.wp_proof,
    EtcdGrove.bufio.Writer.WriteByte.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof,
    EtcdGrove.bufio.NewWriter.wp_proof
      (EtcdGrove.bufio.NewWriterSize.wp_proof EtcdGrove.bufio.NewWriterSize.wp_proofRep),
    EtcdGrove.bufio.NewReader.wp_proofOk
      (EtcdGrove.bufio.NewReader.wp_proofE EtcdGrove.bufio.NewReaderSize.wp_proofE),
    EtcdGrove.bufio.Reader.Read.wp_proofOk, EtcdGrove.bufio.Reader.ReadByte.wp_proof⟩

/-- `encoding/binary`'s varint functions over dsv-bufio's reader: Perennial's proofs
(`Wire/Proof/VarintHolds.lean`), so `BinaryVarintHyps` is no premise of the statement. -/
theorem binaryVarintHyps [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions] :
    wire.BinaryVarintHyps GF :=
  haveI := bufioSpecs (GF := GF) (hG := hG)
  wire.binaryVarintHyps_holds

/-- Net's specs N uses, from their proofs. -/
theorem netSpecs [net.Assumptions] [net.FieldAssumptions] : netN.NetSpecs GF :=
  ⟨net.Conn.Read.wp_proof, net.Conn.Write.wp_proof, net.Conn.Close.wp_proof,
    net.Conn.RemoteAddr.wp_proof, net.Listener.Accept.wp_proof, net.Listen.wp_proof,
    net.Dial.wp_proof, net.DialTimeout.wp_proof⟩

/-! Net's net/rpc client and `SetCodec` (`Net/Proof/net/rpc/Results.lean`'s links). `DialHTTP` is
Net's `net.rpc.DialHTTP.wp`, over Perennial's proofs of `strings.Cut`/`TrimLeft`. -/

section rpc
variable [net.rpc.Assumptions] [sync.Assumptions]

theorem SetCodec_wp : net.rpc.SetCodec.spec (GF := GF) (hG := hG) :=
  net.rpc.SetCodec.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock

variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj] [NetProtoGS]

theorem Call_wp : net.rpc.Client.Call.spec (GF := GF) (hG := hG) := net.rpc.Client.Call.wp

end rpc

variable [package_sem' : gryff.examples.gryffnet.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [bvi : go.BasicIntoValInj]

variable [ρ : RemoteGS] in
/-- The orchestrator. -/
theorem wp_Orch [NaInvG GF] : Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof Model.wp_proof EtcdGrove.remote.wp_Check

variable [ρ : RemoteGS] in
/-- Every client machine, from `op`'s proof. -/
theorem wp_Client [NaInvG GF] [bufio.Assumptions] [net.Assumptions]
    [wire.BinaryVarintHyps GF] : Client.spec (GF := GF) (hG := hG) := by
  haveI := bufioSpecs (GF := GF) (hG := hG)
  haveI := netSpecs (GF := GF) (hG := hG)
  exact Client.wp_proof op.wp_proof EtcdGrove.remote.wp_ServeClient

section server
variable [fa : gryff.src.fastrpc.Assumptions] [binA : wire.BinaryVarintHyps GF]
variable [sortA : replica2.SortSliceHyp GF] [strconvA : strconv.Assumptions] [io.Assumptions]
variable [net.Assumptions] [strA : netN.StringsIndexHyp GF] [mathA : lib.MathPowHyp GF]
variable [net.rpc.Assumptions] [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF]
variable [randA : lib.RandSeedHyp GF] [mA : gryff.src.masterlib.Assumptions]
variable [sA : gryff.src.serverlib.Assumptions] [bufio.Assumptions] [sync.Assumptions]
variable [errors.Assumptions]

/-- Every server machine (`DialHTTP`: Net's, see `section rpc`). -/
theorem wp_Server : Server.spec (GF := GF) (hG := hG) := by
  haveI := bufioSpecs (GF := GF) (hG := hG)
  haveI := netSpecs (GF := GF) (hG := hG)
  exact Server.wp_proof lib.io.ReadFull.wp_proofLt gryffCodecLaws gryffRcvLaws Call_wp
    net.rpc.DialHTTP.wp SetCodec_wp (replica2.run.wp lib.io.ReadFull.wp_proofLt) net.rpc.Register.wp

end server

end linked

end Perennial.EtcdGrove.dsvgryff
