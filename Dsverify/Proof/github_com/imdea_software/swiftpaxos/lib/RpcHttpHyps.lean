/-
**net/rpc over HTTP, the kit's view** (notes/dsv-swiftpaxos.md, "net/rpc over HTTP"). The master and
the replicas serve net/rpc over HTTP on `DefaultServer` (`rpc.Register`, `rpc.HandleHTTP`,
`http.Serve(l, nil)`; the fork's `master/master.go`, the kit's `Server`), and the client and the
master dial with `rpc.DialHTTP`. Every one of those calls is `Net/`'s spec, used as it is:
`RpcHttpHyp GF` bundles them (`DialHTTP.spec`, `HandleHTTP.spec`, `Register.spec_fresh`,
`http.Serve.spec_rpc`), so that the proofs take one premise; `Link.lean`'s `netRpcHttpHyp` gives it
from `Net/`'s proofs, and the statement has no premise for it.

**Wildcard listeners.** The master listens at `":7001"`, a wildcard, which in `Net/`'s model takes
a connection dialed to *any* valid address with port 7001 (D21). `RpcHttpAddr` (below; Net's,
`netRpcHttpAddr`, `RpcHttpAddrNet.lean`) gives a listener address's rpc protocols, `rpcLisP W la hs
hsAns` (persistent): every valid address `la` takes serves `W` behind the handshake
(`rpcLisP_addr`), the right to listen at `la` (`rpcLisP_lis`) and `listenOk la` (`rpcLisP_ok`); made
once from `lisUnset la` at the boot (`rpcLisP_set`). They are Net's (`rpcAddrP_net`, `rpcLisP_net`,
`worldHs_net`).
-/
module

public import Net.Spec.net.rpc.Dial
public import Net.Spec.net.rpc.Server__Accept
public import Net.Spec.net.rpc.Server__Register
public import Net.Spec.net.rpc.DialHTTP
public import Net.Spec.net.rpc.HandleHTTP
public import Net.Spec.net.rpc.Register
public import Net.Spec.net.http.Serve
public import Net.Proof.net.http.MuxDefs
public import Net.Proof.net.rpc.HTTPPaths
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Net.Proof.net.rpc.Init
public import Net.Proof.net.http.Init
public import Proof.bufio.PkgInit
public import Perennial.Proof.io.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net Perennial.net.rpc Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has
  GooseGlobalGS.gooseInvGS

/-- The handshake `DialHTTPPath(network, address, path)` writes (Net's). -/
abbrev connectReq (path : GoString) : List w8 := net.rpc.connectReq path

/-- The answer's head `Server.ServeHTTP` writes after the hijack (Net's). -/
abbrev connectAns : List w8 := net.rpc.connectAns

/-- `rpc.DefaultRPCPath` (Net's). -/
abbrev defaultRPCPath : GoString := net.rpc.defaultRPCPath

/-- `rpc.DefaultDebugPath` (Net's). -/
abbrev defaultDebugPath : GoString := net.rpc.defaultDebugPath

/-- The status `DialHTTPPath` requires (net/rpc's `connected`, Net's). -/
abbrev connectedStatus : GoString := net.rpc.connectedStatus

section env
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [net.http.Assumptions]

/-- A machine's net/rpc-over-HTTP package state: net/http's server variables (`httpSrvEnv`, which
`Serve.spec_rpc` takes and which holds `DialHTTP.spec`'s `httpEnv`, `httpSrvEnv_env`) and net/rpc's
`connected`; a machine's boot gives it (`rpcBootRes`). -/
def dialEnv : IProp GF :=
  iprop(net.http.httpSrvEnv ∗ globalAddr net.rpc.connected ↦□ connectedStatus)

instance dialEnv_persistent : Persistent (dialEnv (GF := GF)) := by
  unfold dialEnv; infer_instance

/-- `DialHTTP.spec`'s `httpEnv`, from net/http's server variables. -/
theorem httpSrvEnv_env : net.http.httpSrvEnv (GF := GF) ⊢ net.http.httpEnv (GF := GF) := by
  iintro #H
  iunfold net.http.httpSrvEnv at H
  icases H with ⟨#He, -⟩
  iexact He

end env

section hyp

/-- The rpc addresses' and listeners' protocols, over the global state only (every machine's heap
sees the same ones): Net's (`netRpcHttpAddr`, `RpcHttpAddrNet.lean`), which the statement gives the
proofs; the proofs are generic in it (the file header). -/
class RpcHttpAddr (GF : BundledGFunctors) [Gg : GooseGlobalGS HasLC.hasLC GF] [SwiftNetPkgState GF] where
  rpcAddrP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcAddrP_persistent : ∀ W a hs hsAns, Persistent (rpcAddrP W a hs hsAns)
  /-- The world's handshake at an address, the dialer's and the acceptor's answer: models-rpc-http's
  `RpcWorld.hs`/`RpcWorld.hsAns` (fields that `lean`'s `RpcWorld` does not have yet). -/
  worldHs : RpcWorld GF → GoString → List w8
  worldHsAns : RpcWorld GF → GoString → List w8
  /-- The world `W` over HTTP at `DefaultRPCPath`: models-rpc-http's `{ W with hs := fun _ =>
  connectReq defaultRPCPath, hsAns := fun _ => connectAns }` (Upamanyu's EPaxos review, 1: a law
  fixing `worldHs` for every world had no true instance). The kit's world is `httpW` of the raw
  world the start allocates. -/
  httpW : RpcWorld GF → RpcWorld GF
  httpW_hs : ∀ W a, worldHs (httpW W) a = connectReq defaultRPCPath
  httpW_hsAns : ∀ W a, worldHsAns (httpW W) a = connectAns
  httpW_SS : ∀ W, (httpW W).SS = W.SS
  /-- Its connection registry is `W`'s (models-rpc-http's `{W with hs, hsAns}` keeps `reg`;
  dsv-epaxos's `httpW_reg`): the start allocates `regInv` of the kit's world from `W`'s name. -/
  httpW_reg : ∀ W, (httpW W).reg = W.reg
  /-- A listener address's rpc protocols (the file header). -/
  rpcLisP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcLisP_persistent : ∀ W la hs hsAns, Persistent (rpcLisP W la hs hsAns)
  rpcLisP_addr : ∀ W la hs hsAns a, addrOk a = true → lisAccepts la a →
    rpcLisP W la hs hsAns ⊢ rpcAddrP W a hs hsAns
  /-- They include the right to listen at `la` (`net.Listen.spec`'s update; models-rpc-http
  `e6b232b2f6`'s `rpcLisP_lis`). -/
  rpcLisP_lis : ∀ W la hs hsAns,
    rpcLisP W la hs hsAns ⊢
      |={⊤,∅}=> lisToks (extGlobalGS netExt (G := Gg)) la ∗
        (lisToks (extGlobalGS netExt (G := Gg)) la ={∅,⊤}=∗ True)
  /-- `la` is a listener address (models-rpc-http's `rpcLisP_ok`). -/
  rpcLisP_ok : ∀ W la hs hsAns, rpcLisP W la hs hsAns ⊢ ⌜listenOk la = true⌝
  /-- The boot sets them once, from the addresses `la` takes, unset, in a world that gives every
  address `la` takes the handshake `hs`/`hsAns` (models-rpc-http's `rpcLisP_set`). -/
  rpcLisP_set : ∀ (E : CoPset) (W : RpcWorld GF) (la : GoString) (hs hsAns : List w8),
    listenOk la = true →
    (∀ a, addrOk a = true ∧ lisAccepts la a → worldHs W a = hs ∧ worldHsAns W a = hsAns) →
    regCtx (Gg := Gg) -∗ inv regN' (regInv (Gg := Gg) W) -∗
      lisUnset (Gg := Gg) la ={E}=∗ rpcLisP W la hs hsAns
  /-- They are Net's: an address's (`DialHTTP.spec`'s), a listener address's (`Serve.spec_rpc`'s),
  and the world's handshake (`HandleHTTP.spec`'s). -/
  rpcAddrP_net : ∀ W a hs hsAns, rpcAddrP W a hs hsAns ⊢ net.rpc.rpcAddrP (Gg := Gg) W a hs hsAns
  rpcLisP_net : ∀ W la hs hsAns, rpcLisP W la hs hsAns ⊢ net.rpc.rpcLisP (Gg := Gg) W la hs hsAns
  worldHs_net : ∀ W a, worldHs W a = W.hs a
  worldHsAns_net : ∀ W a, worldHsAns W a = W.hsAns a

attribute [instance] RpcHttpAddr.rpcAddrP_persistent RpcHttpAddr.rpcLisP_persistent

/-- `Net/`'s specs of the net/rpc-over-HTTP calls the kit makes (the file header), bundled: the
proofs take this one premise; `Link.lean`'s `netRpcHttpHyp` gives it from `Net/`'s proofs. -/
class RpcHttpHyp [go_gctx : GoGlobalContext] (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF]
    [go.Semantics] [SwiftNetPkgState GF] [net.rpc.Assumptions]
    [log.Assumptions] [net.http.Assumptions] : Prop where
  DialHTTP_spec : net.rpc.DialHTTP.spec (GF := GF) (hG := hG)
  HandleHTTP_spec : net.rpc.HandleHTTP.spec (GF := GF) (hG := hG)
  Register_spec : net.rpc.Register.spec_fresh (GF := GF) (hG := hG)
  Serve_spec : net.http.Serve.spec_rpc (GF := GF) (hG := hG)

section mux
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go.Semantics] [net.http.Assumptions]

/-- The right to register paths on `DefaultServeMux`, `R` those registered (Net's `muxOwn`). A
machine's comes from net/http's first initialization (a boot resource). -/
abbrev muxOwner (R : List GoString) : IProp GF :=
  net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) R

end mux

end hyp

section use
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [SwiftNetPkgState GF] [net.rpc.Assumptions]
variable [log.Assumptions] [net.http.Assumptions] [RpcHttpAddr GF] [H : RpcHttpHyp GF]

/-- What `rpc.DialHTTP("tcp", a)` needs (persistent): the client's bounds and package state
(`dialEnv`: net/http's `httpSrvEnv` and net/rpc's `connected`), and `a` serving `W` over HTTP
at `DefaultRPCPath`. -/
def rpcHttp (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ dialEnv ∗
    RpcHttpAddr.rpcAddrP W a (connectReq defaultRPCPath) connectAns)

instance rpcHttp_persistent (W : RpcWorld GF) (a : GoString) :
    Persistent (rpcHttp (GF := GF) W a) := by
  unfold rpcHttp; infer_instance

/-- `rpc.DialHTTP("tcp", a)` (`DialHTTP_spec` at `"tcp"`). -/
theorem DialHTTP_tcp (W : RpcWorld GF) (a : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ rpcHttp W a }}
      (App (App (Val (@! net.rpc.DialHTTP)) (Val #(go!"tcp"))) (Val #a))
    {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
        (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }} := by
  iintro %Φ ⟨#Hnet, Hp⟩ HΦ
  iunfold rpcHttp at Hp
  icases Hp with ⟨%Hb, #Hc, Hd, #Ha⟩
  iunfold dialEnv at Hd
  icases Hd with ⟨#Hse, #Hcon⟩
  ihave #He := httpSrvEnv_env $$ Hse
  ihave #Ha' := RpcHttpAddr.rpcAddrP_net W a _ _ $$ Ha
  iapply H.DialHTTP_spec go!"tcp" net.tcpNet_tcp W a $$ [] HΦ
  iframe Hnet Hc He Hcon Ha'
  ipureintro; exact Hb

/-- A listener address's rpc protocols over HTTP give, at every valid address it takes, the world's
HTTP handshake (what `HandleHTTP.spec` asks of the served addresses). -/
theorem rpcLisP_hs (W : RpcWorld GF) (la a : GoString) (h : addrOk a = true ∧ lisAccepts la a) :
    RpcHttpAddr.rpcLisP W la (connectReq defaultRPCPath) connectAns ⊢
      ⌜W.hs a ≠ [] ∧ W.hsAns a = connectAns⌝ := by
  iintro #H
  ihave #H' := RpcHttpAddr.rpcLisP_net W la _ _ $$ H
  iunfold net.rpc.rpcLisP at H'
  icases H' with ⟨-, -, %Hhs⟩
  ipureintro
  obtain ⟨h1, h2⟩ := Hhs a h
  refine ⟨?_, h2⟩
  rw [h1]
  simp [net.rpc.connectReq]

/-- A method spec that also accepts error answers: `Net/`'s server answers a request whose
arguments do not decode with an error (`srvServes` asks `errOk` of each service, for the server's
own messages, `srvErrMsg`, which are not empty). A caller's `Φ`
of the form `⌜msg ≠ []⌝ ∨ …` meets the second half. -/
def withErr (S : MethodSpec GF) : MethodSpec GF := fun m args Φ =>
  iprop(S m args Φ ∧ ∀ msg : GoString, ⌜msg ≠ []⌝ -∗ Φ [] msg)

theorem withErr_errOk (S : MethodSpec GF) : ⊢ errOk (withErr S) := by
  unfold errOk withErr
  iintro !> %m %args %Φ %msg %Hmsg HS
  icases HS with ⟨-, Herr⟩
  imodintro
  iapply Herr $$ %msg %(net.rpc.srvErrMsg_ne msg Hmsg)

end use

end Perennial.github_com.imdea_software.swiftpaxos
