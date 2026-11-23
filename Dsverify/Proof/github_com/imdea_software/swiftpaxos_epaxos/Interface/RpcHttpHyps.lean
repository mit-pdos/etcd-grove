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
* `rpcLisP W la hs hsAns` (persistent; Upamanyu's answer A1 on #24): every valid address the
  listener address `la` takes (`lisAccepts`: `la` itself, or every valid address with its port
  for a wildcard such as the master's `":7501"`) serves `W` behind the handshake
  (`rpcLisP_addr`), with the right to listen at `la` (`rpcLisP_lis`); set once at the boot from
  `lisUnset la` (`rpcLisP_set`).
* `muxOwner R` (exclusive): the right to register paths at `DefaultServeMux`, `R` those
  registered (`http.Handle` panics on a path registered twice); a machine's `muxOwner []` is a
  boot resource of net/http's initialization (`rpcBootRes`, as dsv-craq's `RpcBoot`).
* `muxHas W A path` (persistent): `DefaultServeMux` routes `path` to a handler serving `W` at
  every address of the set `A`.
* `defaultServer γ`: `rpc.DefaultServer` is a server with names `γ` (the package-level
  `Register`/`HandleHTTP` act on it).
* Specs: `rpc.DialHTTPPath.spec`, `rpc.DialHTTP.spec` (at `DefaultRPCPath`, `/_goRPC_`; the
  client fields, kept until models-rpc-http is on lean), `rpc.HandleHTTP.spec` (with
  `muxOwner`; the debug path is never requested), `rpc.Register.spec` (the package-level one,
  on `DefaultServer`), `http.Serve.spec` (with handler `nil`: `DefaultServeMux`, over a
  listener at `la` with `rpcLisP`). Not stated (the kit does not call them, or only through
  these): `Server.ServeHTTP`, `Server.HandleHTTP`, `ServeMux.ServeHTTP`, `ListenAndServe`.
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

/-- `rpc.DefaultDebugPath`. -/
def defaultDebugPath : GoString := strBytes "/debug/rpc"

section hyp
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [log.Assumptions] [net.http.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **Hypothesis** (the file header), its addresses' part: the protocols of the rpc addresses,
over the global state only (every machine's heap sees the same ones). -/
class RpcHttpAddr (GF : BundledGFunctors) [Gg : GooseGlobalGS HasLC.hasLC GF] [NetProtoGS] where
  rpcAddrP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcAddrP_persistent : ∀ W a hs hsAns, Persistent (rpcAddrP W a hs hsAns)
  /-- Raw net/rpc is the empty handshake. -/
  rpcAddrP_raw : ∀ W a, rpcAddrP W a [] [] ⊣⊢ rpcAddr (Gg := Gg) W a
  /-- A listener address's rpc protocols (the file header). -/
  rpcLisP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcLisP_persistent : ∀ W la hs hsAns, Persistent (rpcLisP W la hs hsAns)
  rpcLisP_addr : ∀ W la hs hsAns a, addrOk a = true → lisAccepts la a →
    rpcLisP W la hs hsAns ⊢ rpcAddrP W a hs hsAns
  /-- The right to listen at `la` (`net.Listen.spec`'s update; models-rpc-http's
  `rpcLisP_lis`). -/
  rpcLisP_lis : ∀ W la hs hsAns,
    rpcLisP W la hs hsAns ⊢
      |={⊤,∅}=> lisToks (extGlobalGS netExt (G := Gg)) la ∗
        (lisToks (extGlobalGS netExt (G := Gg)) la ={∅,⊤}=∗ True)
  /-- Its listener address is one `Listen` takes (models-rpc-http's `rpcLisP_ok`). -/
  rpcLisP_ok : ∀ W la hs hsAns, rpcLisP W la hs hsAns ⊢ ⌜listenOk la = true⌝
  /-- The boot sets them once, from the addresses `la` takes, unset. (models-rpc-http
  e6b232b2f6's `rpcLisP_set` also asks that the world give every address `la` takes the
  handshake `hs`/`hsAns` (`RpcWorld.hs`, `.hsAns`, fields lean's `RpcWorld` does not have yet);
  on that merge the start builds its world with `hs := fun _ => connectReq defaultRPCPath`,
  `hsAns := fun _ => connectAns`, which meets it at every `la`.) -/
  rpcLisP_set : ∀ (E : CoPset) (W : RpcWorld GF) (la : GoString) (hs hsAns : List w8),
    listenOk la = true →
    regCtx (Gg := Gg) -∗ inv regN' (regInv (Gg := Gg) W) -∗
      lisUnset (Gg := Gg) la ={E}=∗ rpcLisP W la hs hsAns

attribute [instance] RpcHttpAddr.rpcAddrP_persistent RpcHttpAddr.rpcLisP_persistent

/-- **Hypothesis** (the file header): net/rpc over HTTP, as models-rpc-http will state it
(the specs, per machine heap, over the addresses' part `RpcHttpAddr`). -/
class RpcHttpHyp (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics]
    [net.rpc.Assumptions] [net.FieldAssumptions] [NetProtoGS] [log.Assumptions]
    [net.http.Assumptions] [RpcHttpAddr GF] where
  /-- The right to register paths at `DefaultServeMux`, `R` those registered (exclusive: a
  second registration of a path panics). A machine's comes from net/http's initialization (a
  boot resource, `rpcBootRes`). -/
  muxOwner : List GoString → IProp GF
  /-- `DefaultServeMux` routes `path` to a handler serving `W` at every address of `A`. -/
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
        RpcHttpAddr.rpcAddrP W a (connectReq path) connectAns }}
      (App (App (App (Val (@! net.rpc.DialHTTPPath)) (Val #nw)) (Val #a)) (Val #path))
    {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
        (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }}
  /-- `rpc.DialHTTP(nw, a)`: `DialHTTPPath` at `DefaultRPCPath`. -/
  DialHTTP_spec : ∀ (nw : GoString), net.tcpNet nw → ∀ (W : RpcWorld GF) (a : GoString),
    {{ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗
        RpcHttpAddr.rpcAddrP W a (connectReq defaultRPCPath) connectAns }}
      (App (App (Val (@! net.rpc.DialHTTP)) (Val #nw)) (Val #a))
    {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
        (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }}
  /-- `rpc.HandleHTTP()`: `DefaultServer.HandleHTTP(DefaultRPCPath, DefaultDebugPath)`, i.e.
  `http.Handle` of both paths on `DefaultServeMux` (which panics on a path already registered:
  hence `muxOwner`); the debug path is never requested (`rpcAddrP`'s handshake names the rpc
  path). Its server serves `W` at every address of `A`. -/
  HandleHTTP_spec : ∀ (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (A : GoString → Prop)
      (R : List GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        muxOwner R ∗ ⌜defaultRPCPath ∉ R ∧ defaultDebugPath ∉ R⌝ ∗
        defaultServer γs ∗ (□ ∀ a, ⌜A a⌝ → srvServes γs C W a) ∗ srvEnv ∗ codecSet C }}
      (App (Val (@! net.rpc.HandleHTTP)) (Val #()))
    {{ RET #(); muxOwner (defaultDebugPath :: defaultRPCPath :: R) ∗
        muxHas W A defaultRPCPath }}
  /-- `rpc.Register(rcvr)`: `DefaultServer.Register(rcvr)` (as `Server.Register.spec`; a
  second registration of a name is an error). -/
  Register_spec : ∀ (γ : GName) (C : CodecSpec GF) (rcvr : GoInterface) (S : MethodSpec GF)
      (nm : GoString) (c : w8) (rest : GoString),
    nm = c :: rest → uint.Z (W8 0x41) ≤ uint.Z c ∧ uint.Z c ≤ uint.Z (W8 0x5A) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ defaultServer γ ∗ codecSet C ∗
        C.rcv rcvr (rcvrIs C rcvr S nm false) }}
      (App (Val (@! net.rpc.Register)) (Val #rcvr))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ svcReg γ C nm S) ∨ ⌜err ≠ interface.nil⌝ }}
  /-- `http.Serve(lis, nil)`: the net/http server on `DefaultServeMux`, up to each connection's
  hijack, over the listener address's rpc protocols (it answers no non-`CONNECT` request, which
  a client of `rpcAddrP` never sends). It returns only on a listener error. -/
  Serve_spec : ∀ (W : RpcWorld GF) (la path : GoString) (lis : GoInterface) (l : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        RpcHttpAddr.rpcLisP W la (connectReq path) connectAns ∗ muxHas W (lisAccepts la) path ∗
        net.isListener (GF := GF) lis l ∗
        netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
        lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l la }}
      (App (App (Val (@! net.http.Serve)) (Val #lis)) (Val #interface.nil))
    {{ (err : GoInterface), RET #err; True }}

attribute [instance]
  RpcHttpHyp.muxHas_persistent RpcHttpHyp.defaultServer_persistent

end hyp

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
