/-
**net/rpc over HTTP, the kit's view** (notes/dsv-epaxos.md, "Hypotheses"). The master and the
replicas serve net/rpc over HTTP on `DefaultServer` (`rpc.Register`, `rpc.HandleHTTP`,
`http.Serve(l, nil)`; the fork's `master.go`, the kit's `serve`) and dial it with `rpc.DialHTTP`
(the kit's `register`, the master's run loop). Every one of those calls is `Net/`'s spec, used as
it is: `RpcHttpHyp GF` bundles them (`DialHTTP.spec`, `HandleHTTP.spec`, `Register.spec_fresh`,
`http.Serve.spec_rpc`), so that the proofs take one premise; `Link.lean`'s `netRpcHttpHyp` gives
it from `Net/`'s proofs, and the statement has no premise for it.

`RpcHttpAddr` (below; Net's, `netRpcHttpAddr`, `RpcHttpAddrNet.lean`) gives the addresses' and
listeners' rpc protocols: `rpcAddrP W a hs hsAns` (address `a` serves `W`'s net/rpc behind the
handshake `hs`/`hsAns`; over HTTP `connectReq defaultRPCPath`/`connectAns`), `rpcLisP W la hs
hsAns` (persistent: every valid address the listener address `la` takes, `lisAccepts`, serves `W`
behind the handshake, `rpcLisP_addr`, with the right to listen at `la`, `rpcLisP_lis`; set once at
the boot from `lisUnset la`, `rpcLisP_set`), and the HTTP world `httpW W` (`W` with HTTP's
handshake at every address). They are Net's (`rpcAddrP_net`, `rpcLisP_net`, `worldHs_net`).
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
public import Net.Proof.net.rpc.Init
public import Net.Proof.net.http.Init
public import Proof.bufio.PkgInit
public import Perennial.Proof.io.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Net Perennial.net.rpc

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

section hyp
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [log.Assumptions] [net.http.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The package state `DialHTTP`'s read of the answer needs (`http.ReadResponse`): net/http's
`httpEnv`. -/
abbrev httpEnv : IProp GF := net.http.httpEnv (GF := GF)

/-- A dialer's package state: `DialHTTP.spec`'s premises besides the address (net/http's
`httpEnv`, net/rpc's `connected`), which a server machine's boot gives (`rpcBootRes`). -/
def dialEnv : IProp GF :=
  iprop(httpEnv ∗ globalAddr net.rpc.connected ↦□ connectedStatus)

instance dialEnv_persistent : Persistent (dialEnv (GF := GF)) := by
  unfold dialEnv; infer_instance

/-- The rpc addresses' and listeners' protocols, over the global state only (every machine's heap
sees the same ones): Net's (`netRpcHttpAddr`, `RpcHttpAddrNet.lean`), which the statement gives the
proofs; the proofs are generic in it (the file header). -/
class RpcHttpAddr (GF : BundledGFunctors) [Gg : GooseGlobalGS HasLC.hasLC GF] [NetProtoGS] where
  rpcAddrP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcAddrP_persistent : ∀ W a hs hsAns, Persistent (rpcAddrP W a hs hsAns)
  /-- The world's handshake at an address, the dialer's and the acceptor's answer: stand-ins
  for models-rpc-http's `RpcWorld.hs`/`RpcWorld.hsAns` (fields lean's `RpcWorld` does not have
  yet; dsv-swiftpaxos's `worldHs`/`worldHsAns`). -/
  worldHs : RpcWorld GF → GoString → List w8
  worldHsAns : RpcWorld GF → GoString → List w8
  /-- The world `W` served over HTTP at `DefaultRPCPath` at every address: the world
  models-rpc-http's start builds, `{ W with hs := fun _ => connectReq defaultRPCPath, hsAns :=
  fun _ => connectAns }` (the kit serves and dials only that). Its laws: the handshake at every
  address is HTTP's (`httpW_hs`, `httpW_hsAns`), and the services and the connection registry are
  `W`'s (`httpW_SS`, `httpW_reg`); a raw world (`hs = []`, models-rpc-http's default) keeps its
  own `worldHs`, so `rpcLisP_set`'s premise holds only of the worlds `httpW` builds. -/
  httpW : RpcWorld GF → RpcWorld GF
  httpW_hs : ∀ W a, worldHs (httpW W) a = connectReq defaultRPCPath
  httpW_hsAns : ∀ W a, worldHsAns (httpW W) a = connectAns
  httpW_SS : ∀ W, (httpW W).SS = W.SS
  httpW_reg : ∀ W, (httpW W).reg = W.reg
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
  /-- The boot sets them once, from the addresses `la` takes, unset, in a world that gives every
  address `la` takes the handshake `hs`/`hsAns` (models-rpc-http e6b232b2f6's `rpcLisP_set`,
  `Net/Proof/net/rpc/Proto.lean`, with `W.hs`/`W.hsAns` as `worldHs W`/`worldHsAns W`). -/
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
class RpcHttpHyp (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics]
    [net.rpc.Assumptions] [net.FieldAssumptions] [NetProtoGS] [log.Assumptions]
    [net.http.Assumptions] : Prop where
  DialHTTP_spec : net.rpc.DialHTTP.spec (GF := GF) (hG := hG)
  HandleHTTP_spec : net.rpc.HandleHTTP.spec (GF := GF) (hG := hG)
  Register_spec : net.rpc.Register.spec_fresh (GF := GF) (hG := hG)
  Serve_spec : net.http.Serve.spec_rpc (GF := GF) (hG := hG)

/-- The right to register paths on `DefaultServeMux`, `R` those registered (Net's `muxOwn`). A
machine's comes from net/http's first initialization (a boot resource). -/
abbrev muxOwner (R : List GoString) : IProp GF :=
  net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) R

/-- net/rpc's `DefaultServer` with an owned, empty registry (what `Register.spec_fresh` takes). A
machine's comes from net/rpc's first initialization (`DefaultServer = NewServer()`, a boot
resource). -/
def defaultSrvFresh : IProp GF :=
  iprop(∃ γs γf : GName, net.rpc.defaultServerO γs γf ∗ net.rpc.svcOwn γf ∅)

/-- `rpc.DialHTTP("tcp", a)` over the kit's `httpEnv` and `RpcHttpAddr`'s `rpcAddrP`. -/
theorem DialHTTP_kit [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF] (W : RpcWorld GF) (a : GoString) :
    {{ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ httpEnv ∗
        globalAddr net.rpc.connected ↦□ connectedStatus ∗
        RpcHttpAddr.rpcAddrP W a (connectReq defaultRPCPath) connectAns }}
      (App (App (Val (@! net.rpc.DialHTTP)) (Val #(go!"tcp"))) (Val #a))
    {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
        (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }} := by
  iintro %Φ ⟨%Hb, #Hc, #He, #Hcon, #Ha⟩ HΦ
  ihave #Ha' := RpcHttpAddr.rpcAddrP_net W a _ _ $$ Ha
  iapply H.DialHTTP_spec go!"tcp" net.tcpNet_tcp W a $$ [] HΦ
  iframe Hc He Hcon Ha'
  ipureintro; exact Hb

/-- A listener address's rpc protocols over HTTP give, at every valid address it takes, the world's
HTTP handshake (what `HandleHTTP.spec` asks of the served addresses). -/
theorem rpcLisP_hs [RA : RpcHttpAddr GF] (W : RpcWorld GF) (la a : GoString)
    (h : addrOk a = true ∧ lisAccepts la a) :
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

end hyp

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
