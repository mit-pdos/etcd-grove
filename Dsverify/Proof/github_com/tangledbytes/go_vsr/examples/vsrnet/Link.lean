/-
The vr kit's links (notes/dsv-vr.md; the kit's top-level `Link`, namespace `EtcdGrove.dsvvr`): the machines' functions' proofs
(`OrchProof`, `ClientProof`, `ServerProof`) applied to their callees' results (the kit's own
proofs `Conf`, `ModelProof`, `CodecProof`, `KitProof`, `MkClientProof`, `OpProof`, the packages'
`Results.lean`, remote's `Link.lean`, `Net/`'s net proofs), over the library hypotheses that remain
(`JsonHyps` (`JsonHyps.lean`): the `encoding/json` `Decoder` premises; the model's `Encoder` is
`encRepModel`, its `NewEncoder` and `Encode` proved (`Proof/encoding/json/Codec/`); a connection's `io.Reader` is Net's
`net.conn_readerOk` over `net.Conn.Read`'s proof, finding 5); remote's `Check` and `ServeClient` are remote's proofs,
the main tree's `Unmarshal` and `SetCodec` its proofs (`Proof/encoding/json/Results.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ClientProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ServerProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.OrchProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Conf
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ModelProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.CodecProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.KitProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.MkClientProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.OpProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.client.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.events.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrkv.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.time.Results
public import Net.Proof.net.Dial
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Dsverify.Proof.log.slog.Logger
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link
public import Proof.encoding.json.Results
public import Proof.encoding.json.Codec.NewEncoder
public import Proof.encoding.json.Codec.Encoder__Encode_conn
public import Net.Proof.models_lab.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.Registered
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.PayloadEnc
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.log.LogsJson

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

-- (in `EtcdGrove.`, as every `Link.lean`: `etc/proof_roots.py`'s `namespace()` is their common prefix)
namespace EtcdGrove.dsvvr

open github_com.tangledbytes.go_vsr github_com.tangledbytes.go_vsr.examples.vsrnet

open github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS
attribute [local instance] Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.jsonCodec
attribute [local instance] encoding.json.encRepModel

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]
variable [NaInvG GF]

/-- `Encoder.Encode` on a connection, at the model's encoder (`encRepModel`). -/
theorem encEncodeConn : encoding.json.Encoder.Encode_conn.spec (GF := GF) (hG := hG) :=
  encoding.json.Encoder.Encode_conn.wp_proof encoding.json.marshalAny.wp net.Conn.Write.wp_proof

/-- The kit's scanner is `jsoncodec.Scan`'s (`models_lab.jsoncodec.scanOk_scanF`). -/
theorem vsrScanOk :
    ⊢ models_lab.jsoncodec.scanOk (GF := GF) examples.vsrnet.scanF models_lab.jsoncodec.scanFn :=
  models_lab.jsoncodec.scanOk_scanF

/-- The kit's registered codec meets `codecPart vsrnet.jsonCodec`
(`vsrnet.registeredCodecOk_of`, over `jsoncodec`'s helpers' proofs). -/
theorem vsrRegisteredCodecOk : examples.vsrnet.registeredCodecOk (GF := GF) (hG := hG) :=
  examples.vsrnet.registeredCodecOk_of models_lab.jsoncodec.AppendRaw.wp
    models_lab.jsoncodec.AppendQuotedUint.wp models_lab.jsoncodec.AppendString.wp
    models_lab.jsoncodec.At.wp models_lab.jsoncodec.Empty.wp models_lab.jsoncodec.Member.wp
    models_lab.jsoncodec.Next.wp models_lab.jsoncodec.String.wp models_lab.jsoncodec.QuotedUint.wp

/-- `vsrwire.Frame`'s `JSONModelUnmarshal` meets the kit's contract (`vsrnet.frameUnmarshalOk`,
over `jsoncodec`'s helpers' proofs). -/
theorem vsrFrameUnmarshalOk (l : Loc) :
    ⊢ encoding.json.unmarshalAt (examples.vsrnet.jsonCodec (GF := GF)) examples.vsrnet.scanF
      #(methods (go.GoType.PointerType examples.vsrwire.Frame.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType examples.vsrwire.Frame.ty) #l) :=
  examples.vsrnet.frameUnmarshalOk models_lab.jsoncodec.SkipSpace.wp
    models_lab.jsoncodec.ValueEnd.wp models_lab.jsoncodec.At.wp models_lab.jsoncodec.Empty.wp
    models_lab.jsoncodec.Member.wp models_lab.jsoncodec.Next.wp models_lab.jsoncodec.Uint.wp
    models_lab.jsoncodec.Valid.wp l

/-- The specs the payload decoders' proofs take (all proved). -/
theorem vsrDecSpecs : examples.vsrnet.DecSpecs (GF := GF) (hG := hG) :=
  ⟨models_lab.jsoncodec.At.wp, models_lab.jsoncodec.Empty.wp, models_lab.jsoncodec.Member.wp,
    models_lab.jsoncodec.Next.wp, models_lab.jsoncodec.String.wp,
    models_lab.jsoncodec.QuotedUint.wp, models_lab.jsoncodec.SkipSpace.wp,
    models_lab.jsoncodec.ValueEnd.wp, models_lab.jsoncodec.Valid.wp,
    pkg.log.Logs.UnmarshalJSON.wp_proof encoding.json.Unmarshal.wp, vsrRegisteredCodecOk,
    vsrScanOk⟩

/-- The specs the event encoder's proofs take (all proved). -/
theorem vsrEncSpecs : examples.vsrnet.EncSpecs (GF := GF) (hG := hG) :=
  ⟨models_lab.jsoncodec.AppendRaw.wp, models_lab.jsoncodec.AppendUint.wp,
    models_lab.jsoncodec.AppendQuotedUint.wp, models_lab.jsoncodec.AppendString.wp,
    models_lab.jsoncodec.Valid.wp, models_lab.jsoncodec.Nesting.wp,
    models_lab.jsoncodec.AppendCompact.wp, pkg.log.Logs.MarshalJSON.wp_proof encoding.json.Marshal.wp⟩

/-- The kit's types' `JSONModel*` methods meet the kit's contract (round 9). -/
theorem vsrTypeMethods : examples.vsrnet.TypeMethods (GF := GF) (hG := hG) :=
  ⟨examples.vsrnet.eventMarshalOk vsrEncSpecs vsrDecSpecs,
    examples.vsrnet.unmarshalOk_Request vsrDecSpecs, examples.vsrnet.unmarshalOk_Reply vsrDecSpecs,
    examples.vsrnet.unmarshalOk_Prepare vsrDecSpecs,
    examples.vsrnet.unmarshalOk_PrepareOK vsrDecSpecs,
    examples.vsrnet.unmarshalOk_Commit vsrDecSpecs,
    examples.vsrnet.unmarshalOk_StartViewChange vsrDecSpecs,
    examples.vsrnet.unmarshalOk_DoViewChange vsrDecSpecs,
    examples.vsrnet.unmarshalOk_StartView vsrDecSpecs,
    examples.vsrnet.unmarshalOk_GetState vsrDecSpecs,
    examples.vsrnet.unmarshalOk_NewState vsrDecSpecs,
    examples.vsrnet.unmarshalOk_Heartbeat vsrDecSpecs, vsrFrameUnmarshalOk⟩

/-- The kit's JSON facts (`vsrnet.codecOk`) from the premises `j` and the proved parts. -/
theorem vsrCodecOk (j : JsonHyps (GF := GF) (hG := hG)) : examples.vsrnet.codecOk (GF := GF) (hG := hG) :=
  j.codecOk vsrRegisteredCodecOk vsrScanOk vsrTypeMethods

theorem wp_Orch : Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof EtcdGrove.remote.wp_Check CfgAddrs.wp_proof
    (Configure.wp_proof net.Dial.wp_proof net.Conn.Write.wp_proof net.Conn.Close.wp_proof
      net.Conn.Read.wp_proof)
    Model.wp_proof Codec.wp_proof Gen.wp_proof

theorem wp_Server (j : JsonHyps (GF := GF) (hG := hG)) :
    Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof CfgAddrs.wp_proof
    (waitConf.wp_proof net.Listen.wp_proof net.Listener.Accept.wp_proof net.Conn.Write.wp_proof
      net.Conn.Close.wp_proof net.Conn.Read.wp_proof)
    (runReplica.wp_proof log.slog.New.wp_proof log.slog.DiscardHandler.load_proof (vsrCodecOk j)
      (wp_RegisterJSON encoding.json.SetCodec.wp)
      (pkg.network.NewTCP.wp (pkg.events.Event.FromDecoder.wp j.Decode_frame encoding.json.Unmarshal.wp (vsrCodecOk j)))
      (pkg.network.TCP.Run.wp log.slog.Debug.wp_proof j.newDecoder)
      pkg.network.TCP.Recv.wp
      examples.vsrkv.New.wp examples.vsrkv.Store.Handle_value.wp
      pkg.time.NewReal.wp pkg.replica.New.wp
      (pkg.replica.Replica.Run.wp log.slog.Logger.Debug.wp_proof log.slog.Logger.Info.wp_proof
        log.slog.Logger.Warn.wp_proof log.slog.Logger.Error.wp_proof
        (pkg.network.TCP.Send.wp log.slog.Debug.wp_proof j.newDecoder)
        (pkg.events.Event.ToWriter.wp encoding.json.NewEncoder.wp_proof encEncodeConn (vsrCodecOk j)))
      pkg.replica.Replica.Submit.wp)

theorem wp_Client (j : JsonHyps (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof (vsrCodecOk j)
    (Op.wp_proof
      (pkg.client.Client.Request.wp (pkg.network.TCP.Send.wp log.slog.Debug.wp_proof j.newDecoder)
        (fun jc => pkg.events.Event.ToWriter.wp (C := jc) encoding.json.NewEncoder.wp_proof encEncodeConn (vsrCodecOk j)))
      (pkg.client.Client.Submit.wp log.slog.Logger.Error.wp_proof)
      (pkg.client.Client.Run.wp (pkg.network.TCP.Send.wp log.slog.Debug.wp_proof j.newDecoder)
        (fun jc => pkg.events.Event.ToWriter.wp (C := jc) encoding.json.NewEncoder.wp_proof encEncodeConn (vsrCodecOk j))
        log.slog.Logger.Error.wp_proof log.slog.Logger.Debug.wp_proof)
      pkg.network.TCP.Recv.wp pkg.client.Client.CheckResult.wp)
    EtcdGrove.remote.wp_ServeClient
    CfgAddrs.wp_proof
    (waitConf.wp_proof net.Listen.wp_proof net.Listener.Accept.wp_proof net.Conn.Write.wp_proof
      net.Conn.Close.wp_proof net.Conn.Read.wp_proof)
    (mkClient.wp_proof
      (pkg.network.NewTCP.wp (pkg.events.Event.FromDecoder.wp j.Decode_frame encoding.json.Unmarshal.wp
        (vsrCodecOk j)))
      log.slog.New.wp_proof log.slog.DiscardHandler.load_proof (wp_RegisterJSON encoding.json.SetCodec.wp)
      pkg.time.NewReal.wp pkg.client.New.wp)
    Codec.wp_proof

end linked

end EtcdGrove.dsvvr
end Perennial
