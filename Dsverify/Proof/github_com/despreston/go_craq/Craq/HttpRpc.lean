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

**The server side** is `Net/`'s but for `http.ListenAndServe`: `rpc.HandleHTTP` is Net's proved
`net.rpc.HandleHTTP.spec` (over net/http's `Handle`), `DefaultServeMux`'s right to register paths
is net/http's `muxOwn` (`muxOwner R`, exclusive, `R` those registered; from net/http's first
initialization), and `rpc.DefaultServer` with an owned, empty registry (`defaultSrvFresh`) comes
from net/rpc's first initialization (Net's `net.rpc.wp_init_first`); the package-level
`rpc.RegisterName` of a fresh name is Net's proved `net.rpc.RegisterName.spec_fresh`. What Net does
not prove is `http.ListenAndServe(a, nil)` (Net proves `http.Serve` on a listener, not
`ListenAndServe`'s own `Listen`): `RpcHttpServe`, a premise of `craq_remote_robust`, never an
instance, written over Net's `muxRpc` (the mux routes `DefaultRPCPath` to `HandleHTTP`'s handler,
serving `W` at the addresses `A`). Net's net/rpc server (`Server.ServeHTTP.spec`, `ServeCodec`)
needs the machine's thread bound `threadBound ≤ 2 ^ 31` (its `sync.WaitGroup`'s counter is an
`int32`), so `ListenAndServe` asks for it too.
-/
module

public import Net.Proof.net.rpc.ClientDefs
public import Net.Proof.net.rpc.ServerDefs
public import Net.Proof.net.http.Defs
public import Net.Proof.net.http.MuxDefs
public import Net.Proof.models_lab.Errors
public import Net.Proof.net.rpc.Init
public import Net.Proof.net.http.Init

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

/-- `DefaultServeMux`'s right to register paths, `R` those registered (exclusive; net/http's
`muxOwn`). -/
abbrev muxOwner [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] [net.http.Assumptions]
    (R : List GoString) : IProp GF :=
  net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) R

/-- `DefaultServer` with an owned, empty registry (what net/rpc's first initialization makes;
`RegisterName.spec_fresh` registers on it). -/
def defaultSrvFresh [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] [net.rpc.Assumptions]
    [net.FieldAssumptions] [NetProtoGS] : IProp GF :=
  iprop(∃ γs γf, net.rpc.defaultServerO γs γf ∗ net.rpc.svcOwn γf ∅)

/-- **H3** (the file header): `http.ListenAndServe(a, nil)` listens at the valid address `a` and
serves its connections with `DefaultServeMux`, up to each connection's hijack (it answers no
non-`CONNECT` request, which a dialer of `rpcAddrP` never sends); the mux routes `DefaultRPCPath`
to an rpc handler at every address of `A` (`muxRpc`, from `HandleHTTP`). -/
class RpcHttpServe [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] [net.http.Assumptions]
    [NetProtoGS] : Prop where
  ListenAndServe : ∀ (W : net.rpc.RpcWorld GF) (A : GoString → Prop) (a : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        ⌜addrOk a = true ∧ A a⌝ ∗ httpRpcAddr W a ∗
        net.http.muxRpc (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) W A
          net.rpc.defaultRPCPath }}
      (App (App (Val (@! net.http.ListenAndServe)) (Val #a)) (Val #interface.nil))
    {{ (err : GoInterface), RET #err; True }}

/-- An address of `httpRpcAddr` speaks HTTP's `CONNECT` handshake (what `HandleHTTP.spec` asks of
the served addresses). -/
theorem httpRpcAddr_hs [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [NetProtoGS]
    (W : net.rpc.RpcWorld GF) (a : GoString) :
    httpRpcAddr (Gg := Gg) W a ⊢ ⌜W.hs a ≠ [] ∧ W.hsAns a = net.rpc.connectAns⌝ := by
  unfold httpRpcAddr net.rpc.rpcAddrP
  iintro ⟨-, -, %Hhs⟩
  ipureintro
  refine ⟨?_, Hhs.2⟩
  rw [Hhs.1]
  simp [net.rpc.connectReq]

end github_com.despreston.go_craq

end Perennial
