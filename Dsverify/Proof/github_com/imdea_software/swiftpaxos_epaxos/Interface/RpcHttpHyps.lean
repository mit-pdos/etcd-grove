/-
**Hypotheses: net/rpc over HTTP** (notes/dsv-epaxos.md, "Hypotheses"). The master and the
replicas serve net/rpc over HTTP (`rpc.Register` on `DefaultServer`, `rpc.HandleHTTP`,
`http.Serve(l, nil)`) and dial it with `rpc.DialHTTP` (the fork's `master.go`, the kit's
`register` and `serve`). `Net/`'s model proves net/rpc's raw server and client
(origin/models-rpc-server: `NewServer`, `Server.Register`, `ServeConn`, `Accept`, `Dial`), not
these. Upamanyu's branch `models-rpc-http` (stacked on models-rpc-server; #24, 2026-11-23) will
prove them; this file states them, **with his names and shapes**, as the class `RpcHttpHyp GF`, a
premise every theorem using them takes (and, like the `InitHyp`s, a visible premise of
`epaxos_remote_robust`; never an `instance`). To be discharged by models-rpc-http.

The names (relative to this kit's namespace, so that sibling kits' copies do not clash):

* `rpcAddrP W a hs hsAns`: address `a` serves net/rpc in world `W` behind a handshake: on each
  connection the client-to-server bytes are `hs ++ reqsWire _` and the server-to-client bytes
  `hsAns ++ ansWire _`. Raw net/rpc is `rpcAddrP W a [] []` (`rpcAddrP_raw`: `Net/`'s `rpcAddr`).
  Over HTTP `hs = connectReq path` (`CONNECT <path> HTTP/1.0\n\n`, what the model's
  `DialHTTPPath` writes before its frames) and `hsAns = connectAns`
  (`HTTP/1.0 200 Connected to Go RPC\n\n`, what `Server.ServeHTTP` writes after the hijack).
  The handshake is part of the protocol: a hypothesis that `DialHTTP` returns `isClient` over
  plain `rpcAddr` (frames from byte 0) would be false of the model. `rpcAddrP`'s `hs` part also
  states that a client sends nothing after `CONNECT` until it has read the answer (Go's
  `DialHTTPPath` waits; the kit's clients do not pipeline).
* `handlerOk W a path h`: the net/http handler `h`, handed a `CONNECT path` request on a
  connection of `a`, serves `W`'s frames after the handshake.
* `muxHas W a path`: `DefaultServeMux` routes `path` to such a handler (persistent).
* `defaultServer γ`: `rpc.DefaultServer` is a server with names `γ` (the package-level
  `Register`/`HandleHTTP` act on it).
* Specs: `rpc.DialHTTPPath.spec`, `rpc.DialHTTP.spec` (at `DefaultRPCPath`, `/_goRPC_`),
  `rpc.Server.ServeHTTP.spec` (a handler for any path), `rpc.Server.HandleHTTP.spec`,
  `rpc.HandleHTTP.spec` (the debug path is never requested: `rpcAddrP`'s handshake names the rpc
  path), `rpc.Register.spec` (the package-level one, on `DefaultServer`), `http.Serve.spec`
  (with handler `nil`: `DefaultServeMux`), `http.ServeMux.ServeHTTP.spec`.
  `http.ListenAndServe.spec` is not stated: the kit does not call it.
-/
module

public import Net.Spec.net.rpc.Dial
public import Net.Spec.net.rpc.Server__Accept
public import Net.Spec.net.rpc.Server__Register
public import Dsverify.Proof.net.rpc.Init
public import Dsverify.Proof.net.http.Init

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Net Perennial.net.rpc

/-- The bytes of a Go string constant. -/
def strBytes (s : String) : List w8 := s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

/-- The handshake `DialHTTPPath(network, address, path)` writes. -/
def connectReq (path : GoString) : List w8 :=
  strBytes "CONNECT " ++ path ++ strBytes " HTTP/1.0\n\n"

/-- The answer's head `Server.ServeHTTP` writes after the hijack. -/
def connectAns : List w8 := strBytes "HTTP/1.0 200 Connected to Go RPC\n\n"

/-- `rpc.DefaultRPCPath`. -/
def defaultRPCPath : GoString := strBytes "/_goRPC_"

section hyp
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [log.Assumptions] [net.http.Assumptions]

/-- **Hypothesis** (the file header): net/rpc over HTTP, as models-rpc-http will state it. -/
class RpcHttpHyp (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics]
    [net.rpc.Assumptions] [net.FieldAssumptions] [NetProtoGS] [log.Assumptions]
    [net.http.Assumptions] where
  rpcAddrP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcAddrP_persistent : ∀ W a hs hsAns, Persistent (rpcAddrP W a hs hsAns)
  /-- Raw net/rpc is the empty handshake. -/
  rpcAddrP_raw : ∀ W a, rpcAddrP W a [] [] ⊣⊢ rpcAddr (Gg := hG.goose_globalGS) W a
  handlerOk : RpcWorld GF → GoString → GoString → GoInterface → IProp GF
  handlerOk_persistent : ∀ W a path h, Persistent (handlerOk W a path h)
  muxHas : RpcWorld GF → GoString → GoString → IProp GF
  muxHas_persistent : ∀ W a path, Persistent (muxHas W a path)
  defaultServer : GName → IProp GF
  defaultServer_persistent : ∀ γ, Persistent (defaultServer γ)
  /-- `net/rpc`'s initialized package has its `DefaultServer`. -/
  defaultServer_init :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ⊢ ∃ γ, defaultServer γ
  /-- `rpc.DialHTTPPath(nw, a, path)`: writes `connectReq path`, reads the answer through
  `http.ReadResponse` (status `200 Connected to Go RPC`, else an error), then `NewClient`. -/
  DialHTTPPath_spec : ∀ (nw : GoString), net.tcpNet nw → ∀ (W : RpcWorld GF) (a path : GoString),
    {{ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗
        rpcAddrP W a (connectReq path) connectAns }}
      (App (App (App (Val (@! net.rpc.DialHTTPPath)) (Val #nw)) (Val #a)) (Val #path))
    {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
        (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }}
  /-- `rpc.DialHTTP(nw, a)`: `DialHTTPPath` at `DefaultRPCPath`. -/
  DialHTTP_spec : ∀ (nw : GoString), net.tcpNet nw → ∀ (W : RpcWorld GF) (a : GoString),
    {{ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗
        rpcAddrP W a (connectReq defaultRPCPath) connectAns }}
      (App (App (Val (@! net.rpc.DialHTTP)) (Val #nw)) (Val #a))
    {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
        (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }}
  /-- `(*Server).ServeHTTP` as a net/http handler: on `CONNECT` it hijacks, writes
  `connectAns` and runs `ServeConn` on the frames (otherwise it answers 405). -/
  Server_ServeHTTP_spec : ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF)
      (a path : GoString),
    ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isServer s γs ∗ srvServes γs C W a ∗ srvEnv ∗ codecSet C ⊢
      handlerOk W a path (interface.mkOk (go.GoType.PointerType net.rpc.Server.ty) #s)
  /-- `(*Server).HandleHTTP(rpcPath, debugPath)`: registers the server at `rpcPath` on
  `DefaultServeMux` (the debug path is never requested). -/
  Server_HandleHTTP_spec : ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF)
      (a rpcPath debugPath : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        isServer s γs ∗ srvServes γs C W a ∗ srvEnv ∗ codecSet C }}
      (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"HandleHTTP"))
        (Val #rpcPath)) (Val #debugPath))
    {{ RET #(); muxHas W a rpcPath }}
  /-- `rpc.HandleHTTP()`: `DefaultServer.HandleHTTP(DefaultRPCPath, DefaultDebugPath)`. -/
  HandleHTTP_spec : ∀ (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        defaultServer γs ∗ srvServes γs C W a ∗ srvEnv ∗ codecSet C }}
      (App (Val (@! net.rpc.HandleHTTP)) (Val #()))
    {{ RET #(); muxHas W a defaultRPCPath }}
  /-- `rpc.Register(rcvr)`: `DefaultServer.Register(rcvr)` (as `Server.Register.spec`). -/
  Register_spec : ∀ (γ : GName) (C : CodecSpec GF) (rcvr : GoInterface) (S : MethodSpec GF)
      (nm : GoString) (c : w8) (rest : GoString),
    nm = c :: rest → uint.Z (W8 0x41) ≤ uint.Z c ∧ uint.Z c ≤ uint.Z (W8 0x5A) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ defaultServer γ ∗ codecSet C ∗
        C.rcv rcvr (rcvrIs C rcvr S nm false) }}
      (App (Val (@! net.rpc.Register)) (Val #rcvr))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ svcReg γ C nm S) ∨ ⌜err ≠ interface.nil⌝ }}
  /-- `(*ServeMux).ServeHTTP` on `DefaultServeMux`: a handler of every path it routes. -/
  ServeMux_ServeHTTP_spec : ∀ (W : RpcWorld GF) (a path : GoString),
    muxHas W a path ⊢
      handlerOk W a path (interface.mkOk (go.GoType.PointerType net.http.ServeMux.ty)
        #(globalAddr net.http.DefaultServeMux))
  /-- `http.Serve(lis, nil)`: the net/http server on `DefaultServeMux`, up to each connection's
  hijack, over `rpcAddrP`'s address protocol (answers no non-`CONNECT` request a client of
  `rpcAddrP` never sends). It returns only on a listener error. -/
  Serve_spec : ∀ (W : RpcWorld GF) (a path : GoString) (lis : GoInterface) (l : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        rpcAddrP W a (connectReq path) connectAns ∗ muxHas W a path ∗
        net.isListener (GF := GF) lis l ∗ netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a ∗
        lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l a }}
      (App (App (Val (@! net.http.Serve)) (Val #lis)) (Val #interface.nil))
    {{ (err : GoInterface), RET #err; True }}

end hyp

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
