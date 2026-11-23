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
net/rpc behind the handshake `hs`/`hsAns`; over HTTP `connectReq path`/`connectAns`; every world
of the stand-in is HTTP's, `worldHs_http`), `muxOwner`, `muxHas`, `defaultServer`,
`DialHTTPPath_spec`, `DialHTTP_spec` (models-rpc-http's preconditions verbatim: `httpEnv`, net/rpc's
`connected`; `dialEnv`), `HandleHTTP_spec` (with `muxOwner`), `Register_spec`, `Serve_spec`. Not
stated (the kit does not call them, or only through these): `Server.ServeHTTP`,
`Server.HandleHTTP`, `ServeMux.ServeHTTP` (reviewed against dsv-epaxos `75c9efff2f` and
models-rpc-http `e6b232b2f6`, 2026-11-23).

**Changed against dsv-epaxos's copy: wildcard listeners.** The master listens at `":7001"`, a
wildcard, which in `Net/`'s model takes a connection dialed to *any* valid address with port 7001
(D21), and `lis_set_proto` gives all those addresses one pair of protocols. `Net/`'s rpc
protocols are per address (`reqProto W a` names `a` in `isRpcConn W a`), so `rpcAddr`/`rpcAddrP`
of the addresses a wildcard takes cannot be made by `lis_set_proto`. Hence (a finding for
models-rpc-http, notes "Design findings"):
* `rpcLisP W la hs hsAns` (persistent): every valid address listener address `la` takes serves `W`
  behind the handshake (`rpcLisP_addr`), the right to listen at `la` (`rpcLisP_lis`: `Listen.spec`'s
  update) and `listenOk la` (`rpcLisP_ok`). It is made once from `lisUnset la` at the boot
  (`rpcLisP_set`, in a world giving every address `la` takes that handshake). These are the exact
  shapes of models-rpc-http `e6b232b2f6` (`Net/Proof/net/rpc/Proto.lean`, over `lisProtoD`); when it
  lands, the fields are replaced by its definitions and theorems.
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
public import Dsverify.Proof.net.rpc.Init
public import Dsverify.Proof.net.http.Init
public import Proof.bufio.PkgInit
public import Perennial.Proof.io.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.strconv.Base

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

/-- `rpc.DefaultDebugPath`. -/
def defaultDebugPath : GoString := strBytes "/debug/rpc"

/-- The status `DialHTTPPath` requires (net/rpc's `connected`; models-rpc-http's
`net.rpc.connectedStatus`). -/
def connectedStatus : GoString := strBytes "200 Connected to Go RPC"

section env
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The package state `DialHTTP(Path)`'s read of the answer needs (`http.ReadResponse`):
models-rpc-http's `net.http.httpEnv` (`Net/Proof/net/http/Defs.lean`), verbatim (dsv-epaxos's). -/
def httpEnv : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
    isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗
    ∃ nb : net.http.noBody, globalAddr net.http.NoBody ↦□ nb)

/-- A dialer's package state: models-rpc-http's `DialHTTP(Path).spec` premises besides the
address (`httpEnv`, net/rpc's `connected`). net/http and net/rpc have no initialization proof
(their `isPkgInit` facts are `True` here), so a machine's boot gives it (the boot resource, as
dsv-epaxos's `rpcBootRes`). -/
def dialEnv : IProp GF :=
  iprop(httpEnv ∗ globalAddr net.rpc.connected ↦□ connectedStatus)

instance httpEnv_persistent : Persistent (httpEnv (GF := GF)) := by
  unfold httpEnv; infer_instance

instance dialEnv_persistent : Persistent (dialEnv (GF := GF)) := by
  unfold dialEnv; infer_instance

end env

section hyp

/-- **Hypothesis** (the file header): net/rpc over HTTP, as models-rpc-http will state it. -/
class RpcHttpHyp [go_gctx : GoGlobalContext] (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF]
    [go.Semantics] [SwiftNetPkgState GF] [net.rpc.Assumptions] [net.FieldAssumptions]
    [log.Assumptions] [net.http.Assumptions] where
  rpcAddrP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcAddrP_persistent : ∀ W a hs hsAns, Persistent (rpcAddrP W a hs hsAns)
  /-- The world's handshake at an address, the dialer's and the acceptor's answer: models-rpc-http's
  `RpcWorld.hs`/`RpcWorld.hsAns` (fields that `lean`'s `RpcWorld` does not have yet). -/
  worldHs : RpcWorld GF → GoString → List w8
  worldHsAns : RpcWorld GF → GoString → List w8
  /-- Every world of the stand-in is net/rpc over HTTP at `DefaultRPCPath` at every address: the
  stand-in for the world models-rpc-http's start builds, `{ W with hs := fun _ => connectReq
  defaultRPCPath, hsAns := fun _ => connectAns }` (the kit serves and dials only that). -/
  worldHs_http : ∀ W a, worldHs W a = connectReq defaultRPCPath ∧ worldHsAns W a = connectAns
  /-- A listener address's rpc protocols (the file header). -/
  rpcLisP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcLisP_persistent : ∀ W la hs hsAns, Persistent (rpcLisP W la hs hsAns)
  rpcLisP_addr : ∀ W la hs hsAns a, addrOk a = true → lisAccepts la a →
    rpcLisP W la hs hsAns ⊢ rpcAddrP W a hs hsAns
  /-- They include the right to listen at `la` (`net.Listen.spec`'s update; models-rpc-http
  `e6b232b2f6`'s `rpcLisP_lis`). -/
  rpcLisP_lis : ∀ W la hs hsAns,
    rpcLisP W la hs hsAns ⊢
      |={⊤,∅}=> lisToks (NG (Gg := hG.goose_globalGS)) la ∗
        (lisToks (NG (Gg := hG.goose_globalGS)) la ={∅,⊤}=∗ True)
  /-- `la` is a listener address (models-rpc-http's `rpcLisP_ok`). -/
  rpcLisP_ok : ∀ W la hs hsAns, rpcLisP W la hs hsAns ⊢ ⌜listenOk la = true⌝
  /-- The boot sets them once, from the addresses `la` takes, unset, in a world that gives every
  address `la` takes the handshake `hs`/`hsAns` (models-rpc-http's `rpcLisP_set`). -/
  rpcLisP_set : ∀ (E : CoPset) (W : RpcWorld GF) (la : GoString) (hs hsAns : List w8),
    listenOk la = true →
    (∀ a, addrOk a = true ∧ lisAccepts la a → worldHs W a = hs ∧ worldHsAns W a = hsAns) →
    regCtx (Gg := hG.goose_globalGS) -∗ inv regN' (regInv (Gg := hG.goose_globalGS) W) -∗
      lisUnset (Gg := hG.goose_globalGS) la ={E}=∗ rpcLisP W la hs hsAns
  /-- The right to register paths at `DefaultServeMux`, `R` those registered (exclusive: a
  second registration of a path panics). A machine's comes from net/http's initialization (a
  boot resource). -/
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
    {{ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ httpEnv ∗
        globalAddr net.rpc.connected ↦□ connectedStatus ∗
        rpcAddrP W a (connectReq path) connectAns }}
      (App (App (App (Val (@! net.rpc.DialHTTPPath)) (Val #nw)) (Val #a)) (Val #path))
    {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
        (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }}
  /-- `rpc.DialHTTP(nw, a)`: `DialHTTPPath` at `DefaultRPCPath`. -/
  DialHTTP_spec : ∀ (nw : GoString), net.tcpNet nw → ∀ (W : RpcWorld GF) (a : GoString),
    {{ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ httpEnv ∗
        globalAddr net.rpc.connected ↦□ connectedStatus ∗
        rpcAddrP W a (connectReq defaultRPCPath) connectAns }}
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
        rpcLisP W la (connectReq path) connectAns ∗ muxHas W (lisAccepts la) path ∗
        net.isListener (GF := GF) lis l ∗ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
        lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l la }}
      (App (App (Val (@! net.http.Serve)) (Val #lis)) (Val #interface.nil))
    {{ (err : GoInterface), RET #err; True }}

attribute [instance] RpcHttpHyp.rpcAddrP_persistent RpcHttpHyp.rpcLisP_persistent
  RpcHttpHyp.muxHas_persistent
  RpcHttpHyp.defaultServer_persistent

end hyp

section use
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [SwiftNetPkgState GF] [net.rpc.Assumptions] [net.FieldAssumptions]
variable [log.Assumptions] [net.http.Assumptions] [H : RpcHttpHyp GF]

/-- What `rpc.DialHTTP("tcp", a)` needs (persistent): the client's bounds and package state
(`dialEnv`: models-rpc-http's `httpEnv` and net/rpc's `connected`), and `a` serving `W` over HTTP
at `DefaultRPCPath`. -/
def rpcHttp (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ dialEnv ∗
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
  iunfold rpcHttp at Hp
  icases Hp with ⟨%Hb, #Hc, Hd, #Ha⟩
  iunfold dialEnv at Hd
  icases Hd with ⟨#He, #Hcon⟩
  iapply H.DialHTTP_spec go!"tcp" net.tcpNet_tcp W a $$ [] HΦ
  iframe Hc He Hcon Ha
  ipureintro; exact Hb

/-- A method spec that also accepts error answers: `Net/`'s server answers a request whose
arguments do not decode with an error (`srvServes` asks `errOk` of each service). A caller's `Φ`
of the form `⌜msg ≠ []⌝ ∨ …` meets the second half. -/
def withErr (S : MethodSpec GF) : MethodSpec GF := fun m args Φ =>
  iprop(S m args Φ ∧ ∀ msg : GoString, ⌜msg ≠ []⌝ -∗ Φ [] msg)

theorem withErr_errOk (S : MethodSpec GF) : ⊢ errOk (withErr S) := by
  unfold errOk withErr
  iintro !> %m %args %Φ %msg %Hmsg HS
  icases HS with ⟨-, Herr⟩
  imodintro
  iapply Herr $$ %msg %Hmsg

end use

end Perennial.github_com.imdea_software.swiftpaxos
