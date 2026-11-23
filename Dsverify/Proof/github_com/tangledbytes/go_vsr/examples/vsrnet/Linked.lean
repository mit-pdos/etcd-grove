/-
The vr kit's links (notes/dsv-vr.md), as paxos's `Linked.lean`: the machines' functions' proofs
(`OrchProof`, `ClientProof`, `ServerProof`) applied to their callees' results (the packages'
`Results.lean`, remote's `Link.lean`, `Net/`'s net proofs), over the library hypotheses that remain
(`LibHyps`, one `Prop` bundling them: `log/slog` and `encoding/json`, which have no Lean model
here, and `connReaderOk`, finding 5); remote's `Check` and `ServeClient` are remote's proofs.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Start
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

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

/-- The library hypotheses the kit's machines rest on (no Lean model of `log/slog` or of
`encoding/json` here; `connReaderOk`, finding 5): each a named spec, none an axiom. -/
structure LibHyps : Prop where
  slog_New : log.slog.New.spec (GF := GF) (hG := hG)
  slog_Discard : log.slog.DiscardHandler.load_spec (GF := GF) (hG := hG)
  slog_Debug : log.slog.Debug.spec (GF := GF) (hG := hG)
  slog_LDebug : log.slog.Logger.Debug.spec (GF := GF) (hG := hG)
  slog_LInfo : log.slog.Logger.Info.spec (GF := GF) (hG := hG)
  slog_LWarn : log.slog.Logger.Warn.spec (GF := GF) (hG := hG)
  slog_LError : log.slog.Logger.Error.spec (GF := GF) (hG := hG)
  conn_readerOk : connReaderOk (GF := GF) (hG := hG)
  json_newDecoder : pkg.events.newDecoder.spec (GF := GF) (hG := hG)
  json_Decode_frame : pkg.events.Decoder.Decode_frame.spec (GF := GF) (hG := hG)
  json_Unmarshal : encoding.json.Unmarshal.spec (GF := GF) (hG := hG)
    (jc := examples.vsrnet.jsonCodec)
  json_NewEncoder : encoding.json.NewEncoder.spec (GF := GF) (hG := hG)
  json_Encode : encoding.json.Encoder.Encode_conn.spec (GF := GF) (hG := hG)
    (jc := examples.vsrnet.jsonCodec)
  codec_ok : examples.vsrnet.codecOk (GF := GF) (hG := hG)

theorem wp_Orch (h : LibHyps (GF := GF) (hG := hG)) : Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof h.conn_readerOk EtcdGrove.remote.wp_Check

theorem wp_Server (h : LibHyps (GF := GF) (hG := hG)) : Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof h.slog_New h.slog_Discard h.slog_Debug h.slog_LDebug h.slog_LInfo h.slog_LWarn
    h.slog_LError h.conn_readerOk h.json_newDecoder h.json_Decode_frame h.json_Unmarshal
    h.json_NewEncoder h.json_Encode h.codec_ok

theorem wp_Client (h : LibHyps (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof h.conn_readerOk
    (pkg.network.NewTCP.wp (pkg.events.Event.FromDecoder.wp h.json_Decode_frame h.json_Unmarshal
      h.codec_ok))
    h.slog_New h.slog_Discard h.codec_ok
    (Op.wp_proof
      (pkg.client.Client.Request.wp (pkg.network.TCP.Send.wp h.slog_Debug h.json_newDecoder)
        (fun jc => pkg.events.Event.ToWriter.wp (C := jc) h.json_NewEncoder h.json_Encode h.codec_ok))
      (pkg.client.Client.Submit.wp h.slog_LError)
      (pkg.client.Client.Run.wp (pkg.network.TCP.Send.wp h.slog_Debug h.json_newDecoder)
        (fun jc => pkg.events.Event.ToWriter.wp (C := jc) h.json_NewEncoder h.json_Encode h.codec_ok)
        h.slog_LError h.slog_LDebug))
    EtcdGrove.remote.wp_ServeClient

end linked

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
