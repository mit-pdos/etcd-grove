/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: the driver's functions linked to their callees' proofs

Each function's proof (`<F>.wp_proof`) with its callees' linked results: net/rpc's
(`Net/Proof/net/rpc/Results.lean`), net/http's (`Handle.wp`, proved; `Serve.wp_proof_rpc`, an interim axiom), Perennial's.
Written by hand (`etc/gen-link.py` does not cover this part yet); its results are in
`EtcdGrove.rpcdriver`, under the prefix every `Link.lean` shares (`etc/proof_roots.py`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.below
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.isFailMsg
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.counter__take
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.randomArgs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.check
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.dial
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.callOn
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Client
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Server
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Register
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Rcvr
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.CodecProof
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.New
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.Svc__Echo
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.CmdBootLinked
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.server.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.client.Main
public import Net.Proof.net.rpc.Results
public import Net.Proof.net.http.Results
public import Net.Proof.net.rpc.HandleHTTP
public import Net.Proof.net.rpc.Server__HandleHTTP
public import Net.Proof.net.rpc.Accept
public import Net.Proof.net.http.Handle
public import Net.Proof.net.http.Serve
public import Net.Proof.net.Listen
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.strings.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace EtcdGrove.rpcdriver

open github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section link
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
variable [π : NetProtoGS]

theorem wp_below : below.spec (GF := GF) (hG := hG) :=
  below.wp_proof github_com.goose_lang.primitive.wp_RandomUint64

theorem wp_isFailMsg : isFailMsg.spec (GF := GF) (hG := hG) :=
  isFailMsg.wp_proof strings.wp_HasPrefix

theorem wp_take : counter.take.spec (GF := GF) (hG := hG) := counter.take.wp_proof

theorem wp_randomArgs : randomArgs.spec (GF := GF) (hG := hG) :=
  randomArgs.wp_proof wp_below wp_take github_com.goose_lang.primitive.wp_RandomUint64

theorem wp_check : check.spec (GF := GF) (hG := hG) := check.wp_proof wp_isFailMsg

theorem wp_dial : dial.spec (GF := GF) (hG := hG) :=
  dial.wp_proof wp_below net.rpc.Dial.wp
    net.rpc.DialHTTP.wp

theorem wp_callOn : callOn.spec (GF := GF) (hG := hG) :=
  callOn.wp_proof drvCodecLaws wp_below wp_randomArgs wp_check net.rpc.Client.Call.wp
    net.rpc.Client.Go.wp

theorem wp_Client : Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof github_com.goose_lang.primitive.wp_RandomUint64 wp_below wp_dial wp_callOn
    wp_randomArgs net.rpc.Client.Close.wp_closed net.rpc.Client.Call.wp_closed

theorem wp_HandleHTTP : net.rpc.HandleHTTP.spec (GF := GF) (hG := hG) :=
  net.rpc.HandleHTTP.wp_proof
    (net.rpc.Server.HandleHTTP.wp_proof net.http.Handle.wp net.rpc.Server.ServeHTTP.wp)

theorem wp_Accept : net.rpc.Accept.spec (GF := GF) (hG := hG) :=
  net.rpc.Accept.wp_proof net.rpc.Server.Accept.wp

theorem wp_Server : Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof (svcRcv_holds drvCodecLaws service.Svc.Echo.wp_proof) noMethodsRcv_holds
    service.New.wp_proof net.rpc.Register.wp_fresh net.rpc.Register.wp_none wp_HandleHTTP
    net.Listen.wp_proof net.http.Serve.wp_proof_rpc wp_Accept

theorem wp_Register : Register.spec (GF := GF) (hG := hG) :=
  Register.wp_proof net.rpc.SetCodec.wp

end link

end EtcdGrove.rpcdriver
end Perennial
