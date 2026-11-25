/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the driver's functions linked to their callees' proofs

Each function's proof (`<F>.wp_proof`) with its callees' linked results: grpc's (its interim axioms and
proofs, `Proof/google_golang_org/grpc/`), the context interim axiom
(`context.WithCancelBackground.wp_proof_canceled`), the `StringValue` codec (`wrapperspb.String`'s
proof), net's `Listen`, Perennial's. Written by hand (`etc/gen-link.py` does not cover this part yet); its
results are in `EtcdGrove.grpcdriver`, under the prefix every `Link.lean` shares (`etc/proof_roots.py`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.below
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.randomWord
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.counter__take
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.freshValue
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.errOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.checkErr
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.echo
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.fail
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.meta_
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.canceled
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.serverStream
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.clientStream
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.bidi
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.work
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Client
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Echo
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Fail
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Meta
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__ServerStream
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__ClientStream
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Bidi
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Server
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__unary
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Echo
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Fail
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Meta
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__ServerStream
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__ClientStream
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Bidi
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.NewDriverClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.RegisterDriverServer
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_Echo_Handler
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_Fail_Handler
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_Meta_Handler
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_ServerStream_Handler
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_ClientStream_Handler
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_Bidi_Handler
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.server.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client.Main
public import Proof.google_golang_org.protobuf.types.known.wrapperspb.String
public import Proof.context.WithCancelBackgroundCanceled
public import Proof.google_golang_org.grpc.StaticMethod
public import Proof.google_golang_org.grpc.ClientConn__Invoke
public import Proof.google_golang_org.grpc.ClientConn__NewStream
public import Proof.google_golang_org.grpc.ClientConn__Close
public import Proof.google_golang_org.grpc.GenericClientStream__Send
public import Proof.google_golang_org.grpc.GenericClientStream__Recv
public import Proof.google_golang_org.grpc.GenericClientStream__CloseSend
public import Proof.google_golang_org.grpc.GenericClientStream__Context
public import Proof.google_golang_org.grpc.GenericServerStream__Send
public import Proof.google_golang_org.grpc.GenericServerStream__Recv
public import Proof.google_golang_org.grpc.GenericServerStream__Context
public import Proof.google_golang_org.grpc.NewClient
public import Proof.google_golang_org.grpc.NewServer
public import Proof.google_golang_org.grpc.Server__RegisterService
public import Proof.google_golang_org.grpc.Server__Serve
public import Proof.google_golang_org.grpc.WithTransportCredentials
public import Proof.google_golang_org.grpc.credentials.insecure.NewCredentials
public import Proof.google_golang_org.grpc.status.Code
public import Proof.google_golang_org.grpc.status.Error
public import Proof.google_golang_org.grpc.status.FromError
public import Proof.google_golang_org.grpc.metadata.AppendToOutgoingContext
public import Proof.google_golang_org.grpc.metadata.FromIncomingContext
public import Proof.google_golang_org.grpc.metadata.MD__Get
public import Proof.strings.ToLower
public import Net.Proof.net.Listen
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace EtcdGrove.grpcdriver

open github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section link
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Assumptions]
variable [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]

theorem wp_String :
    google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG) :=
  google_golang_org.protobuf.types.known.wrapperspb.String.wp_proof

theorem wp_below : below.spec (GF := GF) (hG := hG) :=
  below.wp_proof github_com.goose_lang.primitive.wp_RandomUint64

theorem wp_randomWord : randomWord.spec (GF := GF) (hG := hG) := randomWord.wp_proof wp_below

theorem wp_take : counter.take.spec (GF := GF) (hG := hG) := counter.take.wp_proof

theorem wp_freshValue : freshValue.spec (GF := GF) (hG := hG) :=
  freshValue.wp_proof wp_take wp_randomWord _root_.Perennial.strconv.wp_FormatUint

theorem wp_errOk : errOk.spec (GF := GF) (hG := hG) := errOk.wp_proof status.FromError.wp_proof

theorem wp_checkErr : checkErr.spec (GF := GF) (hG := hG) := checkErr.wp_proof wp_errOk

theorem wp_unary : svc.driverClient.unary.spec (GF := GF) (hG := hG) :=
  svc.driverClient.unary.wp_proof grpc.StaticMethod.wp_proof grpc.ClientConn.Invoke.wp_proof

theorem wp_unary_done : svc.driverClient.unary.spec_done (GF := GF) (hG := hG) :=
  svc.driverClient.unary.wp_proof_done grpc.StaticMethod.wp_proof grpc.ClientConn.Invoke.wp_proof

theorem wp_EchoStub : svc.driverClient.Echo.spec (GF := GF) (hG := hG) :=
  svc.driverClient.Echo.wp_proof wp_unary

theorem wp_EchoStub_done : svc.driverClient.Echo.spec_done (GF := GF) (hG := hG) :=
  svc.driverClient.Echo.wp_proof_done wp_unary_done

theorem wp_FailStub : svc.driverClient.Fail.spec (GF := GF) (hG := hG) :=
  svc.driverClient.Fail.wp_proof wp_unary

theorem wp_MetaStub : svc.driverClient.Meta.spec (GF := GF) (hG := hG) :=
  svc.driverClient.Meta.wp_proof wp_unary

theorem wp_ServerStreamStub : svc.driverClient.ServerStream.spec (GF := GF) (hG := hG) :=
  svc.driverClient.ServerStream.wp_proof grpc.StaticMethod.wp_proof grpc.ClientConn.NewStream.wp_proof
    grpc.GenericClientStream.Send.wp_proof grpc.GenericClientStream.Recv.wp_proof
    grpc.GenericClientStream.CloseSend.wp_proof grpc.GenericClientStream.Context.wp_proof

theorem wp_ClientStreamStub : svc.driverClient.ClientStream.spec (GF := GF) (hG := hG) :=
  svc.driverClient.ClientStream.wp_proof grpc.StaticMethod.wp_proof grpc.ClientConn.NewStream.wp_proof
    grpc.GenericClientStream.Send.wp_proof grpc.GenericClientStream.Recv.wp_proof
    grpc.GenericClientStream.CloseSend.wp_proof grpc.GenericClientStream.Context.wp_proof

theorem wp_BidiStub : svc.driverClient.Bidi.spec (GF := GF) (hG := hG) :=
  svc.driverClient.Bidi.wp_proof grpc.StaticMethod.wp_proof grpc.ClientConn.NewStream.wp_proof
    grpc.GenericClientStream.Send.wp_proof grpc.GenericClientStream.Recv.wp_proof
    grpc.GenericClientStream.CloseSend.wp_proof grpc.GenericClientStream.Context.wp_proof

theorem wp_echo : echo.spec (GF := GF) (hG := hG) :=
  echo.wp_proof wp_freshValue wp_checkErr wp_EchoStub wp_String _root_.Perennial.context.wp_Background

theorem wp_fail : fail.spec (GF := GF) (hG := hG) :=
  fail.wp_proof wp_freshValue wp_below wp_checkErr wp_FailStub wp_String
    _root_.Perennial.context.wp_Background

theorem wp_meta : «meta».spec (GF := GF) (hG := hG) :=
  «meta».wp_proof wp_below wp_randomWord wp_checkErr wp_MetaStub wp_String
    _root_.Perennial.context.wp_Background context.WithCancelBackground.wp_proof_canceled
    metadata.AppendToOutgoingContext.wp_proof _root_.Perennial.strings.wp_Join

theorem wp_canceled : canceled.spec (GF := GF) (hG := hG) :=
  canceled.wp_proof wp_freshValue wp_EchoStub_done wp_String _root_.Perennial.context.wp_Background
    context.WithCancelBackground.wp_proof_canceled status.Code.wp_proof

theorem wp_serverStream : serverStream.spec (GF := GF) (hG := hG) :=
  serverStream.wp_proof wp_randomWord wp_checkErr wp_ServerStreamStub wp_String
    _root_.Perennial.context.wp_Background _root_.Perennial.strings.wp_HasPrefix

theorem wp_clientStream : clientStream.spec (GF := GF) (hG := hG) :=
  clientStream.wp_proof wp_randomWord wp_checkErr wp_ClientStreamStub wp_String
    _root_.Perennial.context.wp_Background

theorem wp_bidi : bidi.spec (GF := GF) (hG := hG) :=
  bidi.wp_proof wp_randomWord wp_checkErr wp_BidiStub wp_String
    _root_.Perennial.context.wp_Background _root_.Perennial.strings.wp_HasPrefix

theorem wp_work : work.spec (GF := GF) (hG := hG) :=
  work.wp_proof wp_below wp_echo wp_fail wp_meta wp_canceled wp_serverStream wp_clientStream wp_bidi

theorem wp_Client : Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof github_com.goose_lang.primitive.wp_RandomUint64 wp_below wp_work wp_freshValue
    wp_EchoStub_done svc.NewDriverClient.wp_proof wp_String _root_.Perennial.context.wp_Background
    insecure.NewCredentials.wp_proof grpc.WithTransportCredentials.wp_proof grpc.NewClient.wp_proof
    grpc.ClientConn.Close.wp_proof status.Code.wp_proof

theorem wp_sEcho : server.Echo.spec (GF := GF) (hG := hG) :=
  server.Echo.wp_proof _root_.Perennial.strconv.wp_FormatUint wp_String

theorem wp_sFail : server.Fail.spec (GF := GF) (hG := hG) :=
  server.Fail.wp_proof _root_.Perennial.strings.wp_HasPrefix status.Error.wp_proof

theorem wp_sMeta : server.Meta.spec (GF := GF) (hG := hG) :=
  server.Meta.wp_proof metadata.FromIncomingContext.wp_proof
    (metadata.MD.Get.wp_proof _root_.Perennial.EtcdGrove.strings.ToLower.wp_proof) _root_.Perennial.strings.wp_Join
    wp_String

theorem wp_sServerStream : server.ServerStream.spec (GF := GF) (hG := hG) :=
  server.ServerStream.wp_proof wp_String

theorem wp_sClientStream : server.ClientStream.spec (GF := GF) (hG := hG) :=
  server.ClientStream.wp_proof wp_String

theorem wp_sBidi : server.Bidi.spec (GF := GF) (hG := hG) := server.Bidi.wp_proof

theorem wp_Server : Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof grpc.NewServer.wp_proof
    (svc.RegisterDriverServer.wp_proof grpc.Server.RegisterService.wp_proof)
    _root_.Perennial.net.Listen.wp_proof grpc.Server.Serve.wp_proof
    wp_sEcho wp_sFail wp_sMeta wp_sServerStream wp_sClientStream wp_sBidi
    svc._Driver_Echo_Handler.wp_proof svc._Driver_Fail_Handler.wp_proof
    svc._Driver_Meta_Handler.wp_proof
    (svc._Driver_ServerStream_Handler.wp_proof grpc.GenericServerStream.Recv.wp_proof
      grpc.GenericServerStream.Send.wp_proof grpc.GenericServerStream.Context.wp_proof)
    (svc._Driver_ClientStream_Handler.wp_proof grpc.GenericServerStream.Recv.wp_proof
      grpc.GenericServerStream.Send.wp_proof grpc.GenericServerStream.Context.wp_proof)
    (svc._Driver_Bidi_Handler.wp_proof grpc.GenericServerStream.Recv.wp_proof
      grpc.GenericServerStream.Send.wp_proof grpc.GenericServerStream.Context.wp_proof)

end link

end EtcdGrove.grpcdriver
end Perennial
