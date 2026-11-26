/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: the driver's proofs linked

Each function's proof (`<fn>.wp_proof`, over its callees' specs) applied to its callees' linked
proofs: the driver's own, net/http's (`Net/Proof/net/http/Results.lean`; the interim axioms
`ServeMux.ServeHTTP.wp_proof`, `Serve.wp_proof`, `ReadResponse.wp_proof_resp`), net's, bufio's and
Perennial's. A linking module.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.below
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.randomWord
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.randomRequest
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.check
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.session
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Client
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.echo
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.teapotHandler
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Server
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.CmdBootLinked
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client.Main
public import Net.Proof.net.http.Results
public import Net.Proof.net.http.Serve
public import Net.Proof.net.http.ServeMux__ServeHTTP
public import Net.Proof.net.Listen
public import Net.Proof.net.Dial
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Conn__Read
public import Proof.bufio.NewReader
public import Proof.bufio.NewReaderSize
public import Proof.bufio.NewReaderOk
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.io.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace EtcdGrove.httpdriver

open github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section link
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Assumptions]
variable [go.BasicIntoValInj]
variable [π : NetProtoGS] [hπ : net.http.HttpProtoGS]

theorem wp_below : below.spec (GF := GF) (hG := hG) :=
  below.wp_proof github_com.goose_lang.primitive.wp_RandomUint64

theorem wp_randomWord : randomWord.spec (GF := GF) (hG := hG) := randomWord.wp_proof wp_below

theorem wp_randomRequest : randomRequest.spec (GF := GF) (hG := hG) :=
  randomRequest.wp_proof wp_below wp_randomWord strconv.wp_Itoa

theorem wp_check : check.spec (GF := GF) (hG := hG) := check.wp_proof net.http.Header.Get.wp

theorem wp_session : session.spec (GF := GF) (hG := hG) :=
  session.wp_proof wp_below wp_randomRequest wp_check net.Dial.wp_proof net.Conn.Write.wp_proof
    net.Conn.Close.wp_proof net.Conn.Read.wp_proofLc
    (EtcdGrove.bufio.NewReader.wp_proof
      (EtcdGrove.bufio.NewReader.wp_proofE EtcdGrove.bufio.NewReaderSize.wp_proofE))
    net.http.ReadResponse.wp_proof_resp io.wp_ReadAll

theorem wp_Client : Client.spec (GF := GF) (hG := hG) := Client.wp_proof wp_below wp_session

theorem wp_echo : echo.spec (GF := GF) (hG := hG) :=
  echo.wp_proof io.wp_ReadAll
    net.http.Header.Set.wp net.http.Header.Get.wp_ro

theorem wp_teapot : teapotHandler.spec (GF := GF) (hG := hG) := teapotHandler.wp_proof

theorem wp_Server : Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof net.http.NewServeMux.wp net.http.ServeMux.HandleFunc.wp
    net.http.HandlerFunc.ServeHTTP.wp net.http.ServeMux.ServeHTTP.wp_proof net.Listen.wp_proof
    net.http.Serve.wp_proof wp_echo wp_teapot

end link

end EtcdGrove.httpdriver
end Perennial
