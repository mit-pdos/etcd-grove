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
public import Dsverify.Proof.net.rpc.Base

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

end github_com.despreston.go_craq

end Perennial
