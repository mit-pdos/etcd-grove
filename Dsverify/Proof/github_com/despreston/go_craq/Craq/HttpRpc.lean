/-
**net/rpc over HTTP** (notes/dsv-craq.md, H2-H4), over `Net/`'s `models-rpc-http` shapes verbatim:
the world `net.rpc.RpcWorld` (its fields `hs`/`hsAns`: the handshake a dialer of an address writes
and the acceptor's answer), `net.rpc.rpcAddrP W a hs hsAns` (address `a` serves `W` behind that
handshake: `Net/Proof/net/rpc/Proto.lean`), `net.rpc.connectReq`, `net.rpc.connectAns`,
`net.rpc.defaultRPCPath`, `net.rpc.connectedStatus`, Net's `net.rpc.isClient` (whose invariant is
over `W.hs a ++ reqsWire _`) and Net's `net.rpc.DialHTTP.spec`.

**The client side is proved** (models-rpc-http's `net.rpc.DialHTTP.wp`, over `DialHTTPPath.wp` and
net/http's `ReadResponse.wp`): go-craq's clients dial with `rpc.DialHTTP("tcp", a)`, through
`Craq/Hyps.lean`'s `RpcClientSpecs.dialHTTP`, whose instance `examples/craqnet/Link.lean` makes
from Net's proof. Its precondition, besides `httpRpcAddr W a`, is a machine's environment
(`rpcEnv`, `Craq/Codec.lean`: `receiptBound ≤ 2 ^ 64`, net/rpc's `srvEnv` (so `cliEnv`), net/http's
`httpEnv`, `connected ↦□ connectedStatus`), which each machine's boot supplies (`rpcBootRes`).

**The server side** (`RpcHttpServe`, a premise of `craq_remote_robust`, never an instance) is what
Net does not prove yet: net/http's server (`http.ListenAndServe` up to the hijack, `DefaultServeMux`),
`rpc.HandleHTTP` and the package-level `rpc.RegisterName` on `DefaultServer`, in the shapes of the
other kits' (dsv-epaxos's `RpcHttpHyp`, dsv-gryff's): `muxOwner R` (exclusive: the right to register
paths at `DefaultServeMux`, `R` those registered; `http.Handle` panics on a path registered twice),
`muxHas W A path` (persistent: the mux routes `path` to a handler serving `W` at the addresses `A`),
`defaultServer γ` (persistent: `rpc.DefaultServer` is a server with registry `γ`). A machine's
`muxOwner []` and `∃ γ, defaultServer γ` come from its initialization (`rpcBootRes`). Net's net/rpc
server (`Server.ServeHTTP.spec`, `ServeCodec`) needs the machine's thread bound
`threadBound ≤ 2 ^ 31` (its `sync.WaitGroup`'s counter is an `int32`), so `HandleHTTP` and
`ListenAndServe` ask for it too.
-/
module

public import Net.Proof.net.rpc.ClientDefs
public import Net.Proof.net.rpc.ServerDefs
public import Net.Proof.net.http.Defs
public import Net.Proof.models_lab.Errors
public import Dsverify.Proof.net.rpc.Init
public import Dsverify.Proof.net.http.Init

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

/-- An address serving net/rpc over HTTP at `DefaultRPCPath`, as go-craq's servers do: Net's
`rpcAddrP` behind the CONNECT handshake (`connectReq defaultRPCPath`, answered `connectAns`). -/
abbrev httpRpcAddr [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [NetProtoGS]
    (W : net.rpc.RpcWorld GF) (a : GoString) : IProp GF :=
  net.rpc.rpcAddrP (Gg := Gg) W a (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns

/-- **H2, H3** (the file header): net/rpc's server over HTTP on `DefaultServer` and
`DefaultServeMux`. -/
class RpcHttpServe [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] [net.rpc.Assumptions]
    [net.FieldAssumptions] [NetProtoGS] where
  /-- The right to register paths at `DefaultServeMux`, `R` those registered (exclusive). A
  machine's `muxOwner []` comes from net/http's initialization (`rpcBootRes`). -/
  muxOwner : List GoString → IProp GF
  /-- `DefaultServeMux` routes `path` to a handler serving `W` at every address of `A`. -/
  muxHas : net.rpc.RpcWorld GF → (GoString → Prop) → GoString → IProp GF
  muxHas_persistent : ∀ W A path, Persistent (muxHas W A path)
  /-- `rpc.DefaultServer` is a server with registry `γ`; a machine's comes from net/rpc's
  initialization, `DefaultServer = NewServer()` (`rpcBootRes`). -/
  defaultServer : GName → IProp GF
  defaultServer_persistent : ∀ γ, Persistent (defaultServer γ)
  /-- `rpc.RegisterName(name, rcvr)`: `DefaultServer.RegisterName(name, rcvr)` (Net's
  `Server.RegisterName.spec`; a second registration of a name is an error). -/
  RegisterName : ∀ (C : net.rpc.CodecSpec GF) (name : GoString) (rcvr : GoInterface)
      (S : net.rpc.MethodSpec GF) (nm : GoString) (np : Bool) (γ : GName),
    name ≠ [] →
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ defaultServer γ ∗ net.rpc.codecSet C ∗
        C.rcv rcvr (net.rpc.rcvrIs C rcvr S nm np) }}
      (App (App (Val (@! net.rpc.RegisterName)) (Val #name)) (Val #rcvr))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ net.rpc.svcReg γ C name S) ∨ ⌜err ≠ interface.nil⌝ }}
  /-- `rpc.HandleHTTP()`: `DefaultServer.HandleHTTP(DefaultRPCPath, DefaultDebugPath)`, i.e.
  `http.Handle` of both paths on `DefaultServeMux` (hence `muxOwner`); the debug path is never
  requested (`rpcAddrP`'s handshake names the rpc path). Its server (registry `γs`) serves `W` at
  every address of `A`; on a connection it hijacks, writes `connectAns` (`connected`) and runs
  `ServeConn` (Net's `Server.ServeHTTP.spec`, which needs `threadBound ≤ 2 ^ 31`). -/
  HandleHTTP : ∀ (γs : GName) (C : net.rpc.CodecSpec GF) (W : net.rpc.RpcWorld GF)
      (A : GoString → Prop) (R : List GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        muxOwner R ∗ ⌜net.rpc.defaultRPCPath ∉ R ∧ go!"/debug/rpc" ∉ R⌝ ∗
        defaultServer γs ∗ (□ ∀ a, ⌜A a⌝ → net.rpc.srvServes γs C W a) ∗ net.rpc.srvEnv ∗
        net.rpc.codecSet C ∗ globalAddr net.rpc.connected ↦□ net.rpc.connectedStatus }}
      (App (Val (@! net.rpc.HandleHTTP)) (Val #()))
    {{ RET #(); muxOwner (go!"/debug/rpc" :: net.rpc.defaultRPCPath :: R) ∗
        muxHas W A net.rpc.defaultRPCPath }}
  /-- `http.ListenAndServe(a, nil)`: listens at the valid address `a` and serves its connections
  with `DefaultServeMux`, up to each connection's hijack (it answers no non-`CONNECT` request,
  which a dialer of `rpcAddrP` never sends). -/
  ListenAndServe : ∀ (W : net.rpc.RpcWorld GF) (A : GoString → Prop) (a : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        ⌜addrOk a = true ∧ A a⌝ ∗ httpRpcAddr W a ∗ muxHas W A net.rpc.defaultRPCPath }}
      (App (App (Val (@! net.http.ListenAndServe)) (Val #a)) (Val #interface.nil))
    {{ (err : GoInterface), RET #err; True }}

attribute [instance] RpcHttpServe.muxHas_persistent RpcHttpServe.defaultServer_persistent

end github_com.despreston.go_craq

end Perennial
