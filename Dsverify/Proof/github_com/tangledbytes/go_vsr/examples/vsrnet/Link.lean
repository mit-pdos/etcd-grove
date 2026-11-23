/-
The vr kit's links (notes/dsv-vr.md; the kit's top-level `Link`, namespace `EtcdGrove.dsvvr`): the machines' functions' proofs
(`OrchProof`, `ClientProof`, `ServerProof`) applied to their callees' results (the kit's own
proofs `Conf`, `ModelProof`, `CodecProof`, `KitProof`, `MkClientProof`, `OpProof`, the packages'
`Results.lean`, remote's `Link.lean`, `Net/`'s net proofs), over the library hypotheses that remain
(`LibHyps`: `connReaderOk`, finding 5; `JsonHyps`
(`JsonHyps.lean`): every `encoding/json` premise); remote's `Check` and `ServeClient` are remote's proofs.
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
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.LibHyps
public import Dsverify.Proof.log.slog.Logger
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link

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

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF] [encoding.json.EncoderRep GF]
variable [NaInvG GF]

theorem wp_Orch (h : LibHyps (GF := GF) (hG := hG)) : Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof EtcdGrove.remote.wp_Check CfgAddrs.wp_proof
    (Configure.wp_proof net.Dial.wp_proof net.Conn.Write.wp_proof net.Conn.Close.wp_proof
      h.conn_readerOk)
    Model.wp_proof Codec.wp_proof Gen.wp_proof

theorem wp_Server (h : LibHyps (GF := GF) (hG := hG)) (j : JsonHyps (GF := GF) (hG := hG)) :
    Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof CfgAddrs.wp_proof
    (waitConf.wp_proof net.Listen.wp_proof net.Listener.Accept.wp_proof net.Conn.Write.wp_proof
      net.Conn.Close.wp_proof h.conn_readerOk)
    (runReplica.wp_proof log.slog.New.wp_proof log.slog.DiscardHandler.load_proof j.codecOk
      j.RegisterJSON
      (pkg.network.NewTCP.wp (pkg.events.Event.FromDecoder.wp j.Decode_frame j.Unmarshal j.codecOk))
      (pkg.network.TCP.Run.wp log.slog.Debug.wp_proof j.newDecoder)
      pkg.network.TCP.Recv.wp
      examples.vsrkv.New.wp examples.vsrkv.Store.Handle_value.wp
      pkg.time.NewReal.wp pkg.replica.New.wp
      (pkg.replica.Replica.Run.wp log.slog.Logger.Debug.wp_proof log.slog.Logger.Info.wp_proof
        log.slog.Logger.Warn.wp_proof log.slog.Logger.Error.wp_proof
        (pkg.network.TCP.Send.wp log.slog.Debug.wp_proof j.newDecoder)
        (pkg.events.Event.ToWriter.wp j.NewEncoder j.Encode_conn j.codecOk))
      pkg.replica.Replica.Submit.wp)

theorem wp_Client (h : LibHyps (GF := GF) (hG := hG)) (j : JsonHyps (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof j.codecOk
    (Op.wp_proof
      (pkg.client.Client.Request.wp (pkg.network.TCP.Send.wp log.slog.Debug.wp_proof j.newDecoder)
        (fun jc => pkg.events.Event.ToWriter.wp (C := jc) j.NewEncoder j.Encode_conn j.codecOk))
      (pkg.client.Client.Submit.wp log.slog.Logger.Error.wp_proof)
      (pkg.client.Client.Run.wp (pkg.network.TCP.Send.wp log.slog.Debug.wp_proof j.newDecoder)
        (fun jc => pkg.events.Event.ToWriter.wp (C := jc) j.NewEncoder j.Encode_conn j.codecOk)
        log.slog.Logger.Error.wp_proof log.slog.Logger.Debug.wp_proof)
      pkg.network.TCP.Recv.wp pkg.client.Client.CheckResult.wp)
    EtcdGrove.remote.wp_ServeClient
    CfgAddrs.wp_proof
    (waitConf.wp_proof net.Listen.wp_proof net.Listener.Accept.wp_proof net.Conn.Write.wp_proof
      net.Conn.Close.wp_proof h.conn_readerOk)
    (mkClient.wp_proof
      (pkg.network.NewTCP.wp (pkg.events.Event.FromDecoder.wp j.Decode_frame j.Unmarshal
        j.codecOk))
      log.slog.New.wp_proof log.slog.DiscardHandler.load_proof j.RegisterJSON
      pkg.time.NewReal.wp pkg.client.New.wp)
    Codec.wp_proof

end linked

end EtcdGrove.dsvvr
end Perennial
