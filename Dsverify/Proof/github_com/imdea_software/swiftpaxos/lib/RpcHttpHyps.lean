/-
**Hypotheses: net/rpc over HTTP** (notes/dsv-swiftpaxos.md, "Hypotheses"). The master and the
replicas serve net/rpc over HTTP (`rpc.Register` on `DefaultServer`, `rpc.HandleHTTP`,
`http.Serve(l, nil)`; the fork's `master/master.go`, the kit's `Server`), and the client and the
master dial with `rpc.DialHTTP`. `Net/`'s model proves raw net/rpc (models-rpc-server, merged:
`NewServer`, `Server.Register`, `ServeConn`, `Accept`, `Dial`, the client), not these.
Upamanyu's branch `models-rpc-http` (#24) is proving them; this file states them as the class
`RpcHttpHyp GF` **with his names and shapes** (copied from dsv-epaxos's
`Interface/RpcHttpHyps.lean`, namespaced to this kit so the kits' copies do not clash). It is a
premise every theorem using them takes and a visible premise of `swiftpaxos_remote_robust`; no
`instance` of it exists.

The names (see dsv-epaxos's file for each): `rpcAddrP W a hs hsAns` (address `a` serves `W`'s
net/rpc behind the handshake `hs`/`hsAns`; raw net/rpc is `rpcAddrP W a [] []`, `rpcAddrP_raw`;
over HTTP `connectReq path`/`connectAns`), `handlerOk`, `defaultServer`, `DialHTTPPath_spec`,
`DialHTTP_spec`, `Server_ServeHTTP_spec`, `Server_HandleHTTP_spec`, `HandleHTTP_spec`,
`Register_spec`, `ServeMux_ServeHTTP_spec`, `Serve_spec`.

**Changed against dsv-epaxos's copy: wildcard listeners.** The master listens at `":7001"`, a
wildcard, which in `Net/`'s model takes a connection dialed to *any* valid address with port 7001
(D21), and `lis_set_proto` gives all those addresses one pair of protocols. `Net/`'s rpc
protocols are per address (`reqProto W a` names `a` in `isRpcConn W a`), so `rpcAddr`/`rpcAddrP`
of the addresses a wildcard takes cannot be made by `lis_set_proto`. Hence (a finding for
models-rpc-http, notes "Design findings"):
* `rpcLisP W la hs hsAns` (persistent): every valid address listener address `la` takes serves `W`
  behind the handshake (`rpcLisP_addr`), and the right to listen at `la` with those protocols. It
  is made once from `lisUnset la` at the boot (`rpcLisP_set`); for a valid `la` it is one address.
* `muxHas W A path`: `DefaultServeMux` routes `path` to a handler serving `W` at every address of
  the set `A` (for a wildcard `lisAccepts la`). `HandleHTTP` asks `srvServes` at each of them
  (vacuous at an address where `W` lists no service).
* `Serve_spec` is over a listener at `la` with `rpcLisP` and `muxHas W (lisAccepts la)`.
-/
module

public import Net.Spec.net.rpc.Dial
public import Net.Spec.net.rpc.Server__Accept
public import Net.Spec.net.rpc.Server__Register
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net Perennial.net.rpc Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has

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

/-- **Hypothesis** (the file header): net/rpc over HTTP, as models-rpc-http will state it. -/
class RpcHttpHyp [go_gctx : GoGlobalContext] (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF]
    [go.Semantics] [SwiftNetPkgState GF] [net.rpc.Assumptions] [net.FieldAssumptions]
    [log.Assumptions] [net.http.Assumptions] where
  rpcAddrP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcAddrP_persistent : ∀ W a hs hsAns, Persistent (rpcAddrP W a hs hsAns)
  /-- Raw net/rpc is the empty handshake. -/
  rpcAddrP_raw : ∀ W a, rpcAddrP W a [] [] ⊣⊢ rpcAddr (Gg := hG.goose_globalGS) W a
  /-- A listener address's rpc protocols (the file header). -/
  rpcLisP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcLisP_persistent : ∀ W la hs hsAns, Persistent (rpcLisP W la hs hsAns)
  rpcLisP_addr : ∀ W la hs hsAns a, addrOk a = true → lisAccepts la a →
    rpcLisP W la hs hsAns ⊢ rpcAddrP W a hs hsAns
  /-- The boot sets them once, from the addresses `la` takes, unset. -/
  rpcLisP_set : ∀ (E : CoPset) (W : RpcWorld GF) (la : GoString) (hs hsAns : List w8),
    listenOk la = true →
    regCtx (Gg := hG.goose_globalGS) -∗ inv regN' (regInv (Gg := hG.goose_globalGS) W) -∗
      lisUnset (Gg := hG.goose_globalGS) la ={E}=∗ rpcLisP W la hs hsAns
  handlerOk : RpcWorld GF → (GoString → Prop) → GoString → GoInterface → IProp GF
  handlerOk_persistent : ∀ W A path h, Persistent (handlerOk W A path h)
  muxHas : RpcWorld GF → (GoString → Prop) → GoString → IProp GF
  muxHas_persistent : ∀ W A path, Persistent (muxHas W A path)
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
      (A : GoString → Prop) (path : GoString),
    ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isServer s γs ∗ (□ ∀ a, ⌜A a⌝ → srvServes γs C W a) ∗ srvEnv ∗
        codecSet C ⊢
      handlerOk W A path (interface.mkOk (go.GoType.PointerType net.rpc.Server.ty) #s)
  /-- `(*Server).HandleHTTP(rpcPath, debugPath)`: registers the server at `rpcPath` on
  `DefaultServeMux` (the debug path is never requested). -/
  Server_HandleHTTP_spec : ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF)
      (A : GoString → Prop) (rpcPath debugPath : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        isServer s γs ∗ (□ ∀ a, ⌜A a⌝ → srvServes γs C W a) ∗ srvEnv ∗ codecSet C }}
      (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"HandleHTTP"))
        (Val #rpcPath)) (Val #debugPath))
    {{ RET #(); muxHas W A rpcPath }}
  /-- `rpc.HandleHTTP()`: `DefaultServer.HandleHTTP(DefaultRPCPath, DefaultDebugPath)`. -/
  HandleHTTP_spec : ∀ (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (A : GoString → Prop),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        defaultServer γs ∗ (□ ∀ a, ⌜A a⌝ → srvServes γs C W a) ∗ srvEnv ∗ codecSet C }}
      (App (Val (@! net.rpc.HandleHTTP)) (Val #()))
    {{ RET #(); muxHas W A defaultRPCPath }}
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
  ServeMux_ServeHTTP_spec : ∀ (W : RpcWorld GF) (A : GoString → Prop) (path : GoString),
    muxHas W A path ⊢
      handlerOk W A path (interface.mkOk (go.GoType.PointerType net.http.ServeMux.ty)
        #(globalAddr net.http.DefaultServeMux))
  /-- `http.Serve(lis, nil)`: the net/http server on `DefaultServeMux`, up to each connection's
  hijack, over the listener address's rpc protocols (it answers no non-`CONNECT` request, which
  a client of `rpcAddrP` never sends). It returns only on a listener error. -/
  Serve_spec : ∀ (W : RpcWorld GF) (la path : GoString) (lis : GoInterface) (l : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        rpcLisP W la (connectReq path) connectAns ∗ muxHas W (lisAccepts la) path ∗
        net.isListener (GF := GF) lis l ∗ netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
        lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l la }}
      (App (App (Val (@! net.http.Serve)) (Val #lis)) (Val #interface.nil))
    {{ (err : GoInterface), RET #err; True }}

attribute [instance] RpcHttpHyp.rpcAddrP_persistent RpcHttpHyp.rpcLisP_persistent
  RpcHttpHyp.handlerOk_persistent RpcHttpHyp.muxHas_persistent
  RpcHttpHyp.defaultServer_persistent

end hyp

section use
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [SwiftNetPkgState GF] [net.rpc.Assumptions] [net.FieldAssumptions]
variable [log.Assumptions] [net.http.Assumptions] [H : RpcHttpHyp GF]

/-- What `rpc.DialHTTP("tcp", a)` needs (persistent): the client's bounds and package state, and
`a` serving `W` over HTTP at `DefaultRPCPath`. -/
def rpcHttp (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗
    H.rpcAddrP W a (connectReq defaultRPCPath) connectAns)

instance rpcHttp_persistent (W : RpcWorld GF) (a : GoString) :
    Persistent (rpcHttp (GF := GF) W a) := by
  unfold rpcHttp; infer_instance

/-- `rpc.DialHTTP("tcp", a)` (`DialHTTP_spec` at `"tcp"`). -/
theorem DialHTTP_tcp (W : RpcWorld GF) (a : GoString) :
    {{ rpcHttp W a }}
      (App (App (Val (@! net.rpc.DialHTTP)) (Val #(go!"tcp"))) (Val #a))
    {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
        (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }} := by
  iintro %Φ Hp HΦ
  unfold rpcHttp
  iapply H.DialHTTP_spec go!"tcp" net.tcpNet_tcp W a $$ Hp HΦ

end use

end Perennial.github_com.imdea_software.swiftpaxos
