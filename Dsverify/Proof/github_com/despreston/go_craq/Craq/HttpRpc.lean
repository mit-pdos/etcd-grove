/-
**Hypothesis H4 (net/rpc over HTTP, client side)**, stated so that it is true of the models and
named after the shapes Net's piece will have (upamanyus, #24, 2026-11-23: branch
`models-rpc-http`, stacked on `models-rpc-server`; notes/dsv-craq.md, H4). It awaits that piece.

go-craq's clients dial with `rpc.DialHTTP`: `DialHTTPPath` (models/net/rpc/client.go) writes the
CONNECT request `connectReq path` (`CONNECT <path> HTTP/1.0\n\n`), reads the server's answer
(`connectedAns`, `HTTP/1.0 200 Connected to Go RPC\n\n`) through `http.ReadResponse`, then runs
`NewClient(conn)` on the same connection. Net's piece will have **`rpcAddrP W a hs hsAns`**: an
address whose connections carry `hs ++ reqsWire` from client to server and `hsAns ++ ansWire`
back (raw net/rpc is `rpcAddr W a = rpcAddrP W a [] []`), with Net's `isClient` stated over the
connection's frame part, unchanged in name and use. Until it lands:

* `RpcHttpAddr GF`: the predicate `rpcAddrP` (persistent), abstract.
* `RpcHttpDial GF`: `rpc.DialHTTPPath.spec` over `rpcAddrP W a (connectReq path) connectedAns`
  (Net's `isClient`, or the dial's error), and `rpc.DialHTTP.spec`, its instance at
  `DefaultRPCPath` (`/_goRPC_`).

They are classes in `Type` (the predicate is data), taken as instance variables; no instance of
them exists. With `rpcAddrP` abstract they say something only together with the server side and
the addresses' allocation (notes/dsv-craq.md, H2-H4), which the kit's statement will take as
premises with them.
-/
module

public import Net.Proof.net.rpc.ClientDefs
public import Net.Proof.models_lab.Errors
public import Dsverify.Proof.net.rpc.Init
public import Net.Proof.net.rpc.ServerDefs
public import Dsverify.Proof.net.http.Init

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

/-- `CONNECT <path> HTTP/1.0\n\n`: the client's handshake. -/
def connectReq (path : GoString) : List w8 := go!"CONNECT " ++ path ++ go!" HTTP/1.0\n\n"

/-- `HTTP/1.0 200 Connected to Go RPC\n\n`: the server's answer to it. -/
def connectedAns : List w8 := go!"HTTP/1.0 200 Connected to Go RPC\n\n"

/-- net/rpc's `DefaultRPCPath`. -/
def defaultRPCPath : GoString := go!"/_goRPC_"

/-- **H4, the addresses** (see the file header). -/
class RpcHttpAddr [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    (GF : BundledGFunctors) [GooseGlobalGS HasLC.hasLC GF] where
  /-- Address `a` serves world `W`'s net/rpc after the handshake `hs`, answered by `hsAns`. -/
  rpcAddrP : net.rpc.RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcAddrP_pers : ∀ W a hs hsAns, Persistent (rpcAddrP W a hs hsAns)

instance rpcAddrP_persistent [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    {GF : BundledGFunctors} [GooseGlobalGS HasLC.hasLC GF] [ra : RpcHttpAddr GF]
    (W : net.rpc.RpcWorld GF) (a : GoString) (hs hsAns : List w8) :
    Persistent (RpcHttpAddr.rpcAddrP W a hs hsAns) :=
  ra.rpcAddrP_pers W a hs hsAns

/-- An address serving net/rpc over HTTP at `DefaultRPCPath`, as go-craq's servers do. -/
abbrev httpRpcAddr [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    {GF : BundledGFunctors} [GooseGlobalGS HasLC.hasLC GF] [RpcHttpAddr GF]
    (W : net.rpc.RpcWorld GF) (a : GoString) : IProp GF :=
  RpcHttpAddr.rpcAddrP W a (connectReq defaultRPCPath) connectedAns

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ra : RpcHttpAddr (GF := GF)]

/-- `DialHTTPPath(network, a, path)`: Net's `rpc.DialHTTPPath.spec` (expected). -/
abbrev rpc.DialHTTPPath.spec : Prop :=
  ∀ (W : net.rpc.RpcWorld GF) (network a path : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗
      RpcHttpAddr.rpcAddrP (GF := GF) W a (connectReq path) connectedAns }}
    (App (App (App (Val (@! net.rpc.DialHTTPPath)) (Val #network)) (Val #a)) (Val #path))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ net.rpc.isClient c W a) ∨
      (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }}

/-- `DialHTTP("tcp", a)`: Net's `rpc.DialHTTP.spec` (expected), `DialHTTPPath`'s instance at
`DefaultRPCPath`. -/
abbrev rpc.DialHTTP.spec : Prop :=
  ∀ (W : net.rpc.RpcWorld GF) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ httpRpcAddr (GF := GF) W a }}
    (App (App (Val (@! net.rpc.DialHTTP)) (Val #go!"tcp")) (Val #a))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ net.rpc.isClient c W a) ∨
      (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }}

end specs

/-- **H4, the dial** (see the file header). -/
class RpcHttpDial [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] [net.rpc.Assumptions]
    [net.FieldAssumptions] [NetProtoGS] [ra : RpcHttpAddr GF] where
  DialHTTPPath : rpc.DialHTTPPath.spec (GF := GF)
  DialHTTP : rpc.DialHTTP.spec (GF := GF)

/-! ## The server side (H2, H3)

Net's expected `rpc.Server.ServeHTTP.spec` (as a handler of net/http's: on `CONNECT` it hijacks,
writes `connectedAns` and runs `ServeConn` on the frame part), `rpc.HandleHTTP.spec` (the
`DefaultServer` at `DefaultRPCPath` on `DefaultServeMux`; the debug path is never requested) and
`http.ListenAndServe.spec` (the net/http server up to the hijack, over `rpcAddrP`, the handlers
given as `handlerOk` per path); and the package-level `rpc.RegisterName` (the `DefaultServer`'s
`Server.RegisterName`, proved on models-rpc-server, with net/rpc's package variable). The mux's
vocabulary (`muxOwner R`: the right to register paths at `DefaultServeMux`, `R` those registered,
exclusive; `muxRoute p h`: it routes `p` to `h`, persistent) and `handlerOk h p W a` are abstract
here, as the lab's `Harness/Proof/net/{http,rpc}`. **Open**: where a machine's `muxOwner []`
comes from (net/http's initialization, H1: Net's piece decides); without it, and without the
allocation of `rpcAddrP`, these say nothing. -/

/-- The `*Server` `s` as an `http.Handler`. -/
abbrev serverHandler [GooseExts] [GoGlobalContext] (s : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType net.rpc.Server.ty) #s

/-- **H2, H3** (the section header). -/
class RpcHttpServe [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] [net.rpc.Assumptions]
    [net.FieldAssumptions] [NetProtoGS] [ra : RpcHttpAddr GF] where
  muxOwner : List GoString → IProp GF
  muxRoute : GoString → GoInterface → IProp GF
  muxRoute_pers : ∀ p h, Persistent (muxRoute p h)
  handlerOk : GoInterface → GoString → net.rpc.RpcWorld GF → GoString → IProp GF
  handlerOk_pers : ∀ h p W a, Persistent (handlerOk h p W a)
  /-- `rpc.RegisterName(name, rcvr)`: `Server.RegisterName.spec` on the `DefaultServer`. -/
  RegisterName : ∀ (C : net.rpc.CodecSpec GF) (name : GoString) (rcvr : GoInterface)
      (S : net.rpc.MethodSpec GF) (nm : GoString) (np : Bool),
    name ≠ [] →
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ net.rpc.codecSet C ∗
        C.rcv rcvr (net.rpc.rcvrIs C rcvr S nm np) }}
      (App (App (Val (@! net.rpc.RegisterName)) (Val #name)) (Val #rcvr))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ (s : Loc) (γ : GName),
          globalAddr net.rpc.DefaultServer ↦□ s ∗ net.rpc.isServer s γ ∗
          net.rpc.svcReg γ C name S) ∨ ⌜err ≠ interface.nil⌝ }}
  /-- `rpc.HandleHTTP()`: Net's `rpc.HandleHTTP.spec` (expected). -/
  HandleHTTP : ∀ (R : List GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ muxOwner R ∗
        ⌜defaultRPCPath ∉ R ∧ go!"/debug/rpc" ∉ R⌝ }}
      (App (Val (@! net.rpc.HandleHTTP)) (Val #()))
    {{ RET #(); muxOwner (go!"/debug/rpc" :: defaultRPCPath :: R) ∗
        ∃ s : Loc, globalAddr net.rpc.DefaultServer ↦□ s ∗
          muxRoute defaultRPCPath (serverHandler s) }}
  /-- The `*Server` handles `DefaultRPCPath` of `a` (Net's `rpc.Server.ServeHTTP.spec`, as a
  handler), given its registrations serve `a`. -/
  ServeHTTP : ∀ (s : Loc) (γ : GName) (C : net.rpc.CodecSpec GF) (W : net.rpc.RpcWorld GF)
      (a : GoString),
    net.rpc.isServer s γ ∗ net.rpc.srvServes γ C W a ∗ net.rpc.srvEnv ∗ net.rpc.codecSet C ⊢
      handlerOk (serverHandler s) defaultRPCPath W a
  /-- `http.ListenAndServe(a, nil)`: Net's `http.ListenAndServe.spec` (expected): it serves `a`'s
  connections, routing `p` to `h`, and returns only with `Listen`'s error. -/
  ListenAndServe : ∀ (W : net.rpc.RpcWorld GF) (a p : GoString) (h : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ ⌜addrOk a = true⌝ ∗
        httpRpcAddr W a ∗ muxRoute p h ∗ handlerOk h p W a }}
      (App (App (Val (@! net.http.ListenAndServe)) (Val #a)) (Val #interface.nil))
    {{ (err : GoInterface), RET #err; ⌜err ≠ interface.nil⌝ }}

end github_com.despreston.go_craq

end Perennial
