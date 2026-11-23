/-
The vr kit's links (notes/dsv-vr.md; the kit's top-level `Link`, namespace `EtcdGrove.dsvvr`): the machines' functions' proofs
(`OrchProof`, `ClientProof`, `ServerProof`) applied to their callees' results (the packages'
`Results.lean`, remote's `Link.lean`, `Net/`'s net proofs), over the library hypotheses that remain
(`LibHyps`: `log/slog`, which has no Lean model here, and `connReaderOk`, finding 5; `JsonHyps`
(`JsonHyps.lean`): every `encoding/json` premise); remote's `Check` and `ServeClient` are remote's proofs.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ClientProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ServerProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.OrchProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.LibHyps
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
  Orch.wp_proof h.conn_readerOk EtcdGrove.remote.wp_Check

theorem wp_Server (h : LibHyps (GF := GF) (hG := hG)) (j : JsonHyps (GF := GF) (hG := hG)) :
    Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof h.slog_New h.slog_Discard h.slog_Debug h.slog_LDebug h.slog_LInfo h.slog_LWarn
    h.slog_LError h.conn_readerOk j.newDecoder j.Decode_frame j.Unmarshal
    j.NewEncoder j.Encode_conn j.codecOk j.RegisterJSON

theorem wp_Client (h : LibHyps (GF := GF) (hG := hG)) (j : JsonHyps (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof h.conn_readerOk
    (pkg.network.NewTCP.wp (pkg.events.Event.FromDecoder.wp j.Decode_frame j.Unmarshal
      j.codecOk))
    h.slog_New h.slog_Discard j.codecOk
    (Op.wp_proof
      (pkg.client.Client.Request.wp (pkg.network.TCP.Send.wp h.slog_Debug j.newDecoder)
        (fun jc => pkg.events.Event.ToWriter.wp (C := jc) j.NewEncoder j.Encode_conn j.codecOk))
      (pkg.client.Client.Submit.wp h.slog_LError)
      (pkg.client.Client.Run.wp (pkg.network.TCP.Send.wp h.slog_Debug j.newDecoder)
        (fun jc => pkg.events.Event.ToWriter.wp (C := jc) j.NewEncoder j.Encode_conn j.codecOk)
        h.slog_LError h.slog_LDebug))
    j.RegisterJSON
    EtcdGrove.remote.wp_ServeClient

end linked

end EtcdGrove.dsvvr
end Perennial
