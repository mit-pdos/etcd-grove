/-
**Hypotheses: net/rpc's server over HTTP** (notes/dsv-gryff.md, "Hypotheses"). The master serves
net/rpc over HTTP on a server of its own (`rpc.NewServer`, `Server.Register`,
`Server.HandleHTTP(DefaultRPCPath, DefaultDebugPath)`, `http.Serve(l, nil)`; `masterlib/master.go`)
and each replica on `DefaultServer` (`rpc.Register`, `rpc.HandleHTTP`, `http.Serve(l, nil)`;
`kit.go`, `serverlib/server.go`). `Net/` proves raw net/rpc (models-rpc-server: `NewServer`,
`Server.Register`, `ServeConn`, `Accept`) and, merged here from models-rpc-http, the client over
HTTP (`rpcAddrP`, `connectReq`, `connectAns`, `defaultRPCPath`, `DialHTTP.spec`,
`DialHTTPPath.spec`, the latter over `http.ReadResponse.spec`): those are used as they are, not
restated. The server side is upamanyus's next item on `models-rpc-http`; this file states it as
ONE class `RpcHttpHyp GF` with his intended names and shapes (#24; dsv-swiftpaxos's
`lib/RpcHttpHyps.lean`), a premise of every theorem using it and a visible premise of
`gryff_remote_robust`; no `instance` of it exists.

**Wildcard listeners** (answer A1 on #24): the master listens at `":7501"`, a replica's net/rpc at
`":850x"`, wildcards, which in `Net/`'s model take a connection dialed to any valid address with
that port. `rpcLisP W la hs hsAns` (persistent): every valid address `la` takes serves `W` behind
the handshake (`rpcLisP_addr`), and the right to listen at `la` (`rpcLisP_lis`); made once from
`lisUnset la` at the start (`rpcLisP_set`). `muxHas W A path`: a mux routes `path` to a handler
serving `W` at every address of `A` (for a wildcard listener, `lisAccepts la`).

**Error answers** (A2/C3): `srvServes` asks `errOk` of each service, today "every non-empty
message"; the kit's services accept them (`Rpc/Defs.lean`'s `withErr`). When upamanyus restricts
`errOk` to the server's own messages (`srvErrMsg`), `withErr` shrinks accordingly. **Client.Call's
errors** (C1): today a non-`ServerError` error comes with `models_lab.errAny`; it is to become
`∃ msg, errMsg err msg ∗ ⌜msg ≠ []⌝` (no use here needs more than `errAny`).

**The codec's per-machine boot resource** (C2, `rpcBootRes`): `rpc.SetCodec` (the kit's
`Register()`) needs `codecUnset` (exclusive: the other half of `codec`'s points-to, at `nil`) and
`codecMu`'s mutex, and the server reads `invalidRequest`; they come from net/rpc's package
initialization **once per machine**, as a resource the machine's boot hands to `main` (like the
replicas' prophecy, `cmd/server*/Boot.lean`). `Net/` does not give it yet (its net/rpc
initialization is names only), so the boot proofs take it from the class `RpcBootHyp` (net/rpc's initializer, run where
neither net/http nor net/rpc is initialized, leaves `rpcBootRes` and `muxFree DefaultRPCPath`; a
hypothesis of the deployment's boot, visible in the statement). It is not
persistent and never made by an update (`|==> codecFresh` would be unsound).
-/
module

public import Net.Spec.net.rpc.DialHTTP
public import Net.Spec.net.rpc.Server__Accept
public import Net.Spec.net.rpc.Server__Register
public import Net.Spec.net.rpc.SetCodec
public import Net.Proof.net.rpc.ServerDefs
public import Net.Code.net.http
public import Dsverify.Proof.net.rpc.Base
public import Dsverify.Proof.net.http.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Net Perennial.net.rpc

attribute [local instance] GooseGlobalGS.gooseInvGS

section hyp

/-- **Hypothesis** (the file header): net/rpc's server over HTTP, as models-rpc-http will state
it. -/
class RpcHttpHyp [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    [go_gctx : GoGlobalContext] (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF]
    [go.Semantics] [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] where
  /-- A listener address's rpc protocols (the file header). -/
  rpcLisP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcLisP_persistent : ∀ W la hs hsAns, Persistent (rpcLisP W la hs hsAns)
  rpcLisP_addr : ∀ W la hs hsAns a, addrOk a = true → lisAccepts la a →
    rpcLisP W la hs hsAns ⊢ rpcAddrP (Gg := hG.goose_globalGS) W a hs hsAns
  /-- They include the right to listen at `la` with some protocols (`Listen.spec`'s). -/
  rpcLisP_lis : ∀ W la hs hsAns,
    rpcLisP W la hs hsAns ⊢ ∃ P Q, lisProto (Gg := hG.goose_globalGS) la P Q
  /-- The start sets them once, from the addresses `la` takes, unset. -/
  rpcLisP_set : ∀ (E : CoPset) (W : RpcWorld GF) (la : GoString) (hs hsAns : List w8),
    listenOk la = true → (∀ a, lisAccepts la a → W.hs a = hs ∧ W.hsAns a = hsAns) →
    regCtx (Gg := hG.goose_globalGS) -∗ inv regN' (regInv (Gg := hG.goose_globalGS) W) -∗
      lisUnset (Gg := hG.goose_globalGS) la ={E}=∗ rpcLisP W la hs hsAns
  /-- `h` is a net/http handler of `path` serving `W` at the addresses `A`. -/
  handlerOk : RpcWorld GF → (GoString → Prop) → GoString → GoInterface → IProp GF
  handlerOk_persistent : ∀ W A path h, Persistent (handlerOk W A path h)
  /-- `DefaultServeMux` routes `path` to a handler serving `W` at the addresses `A`. -/
  muxHas : RpcWorld GF → (GoString → Prop) → GoString → IProp GF
  muxHas_persistent : ∀ W A path, Persistent (muxHas W A path)
  /-- `rpc.DefaultServer` is a server with the registry `γ`. -/
  defaultServer : GName → IProp GF
  defaultServer_persistent : ∀ γ, Persistent (defaultServer γ)
  /-- net/rpc's initialized package has its `DefaultServer` (`NewServer()`). -/
  defaultServer_init :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ⊢ ∃ γ, defaultServer γ
  /-- `(*Server).ServeHTTP` as a net/http handler: on `CONNECT` it hijacks, writes
  `connectAns` and runs `ServeConn` on the frames (otherwise it answers 405). -/
  Server_ServeHTTP_spec : ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF)
      (A : GoString → Prop) (path : GoString),
    ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isServer s γs ∗ (□ ∀ a, ⌜A a⌝ → srvServes γs C W a) ∗ srvEnv ∗
        codecSet C ⊢
      handlerOk W A path (interface.mkOk (go.GoType.PointerType net.rpc.Server.ty) #s)
  /-- `(*Server).HandleHTTP(rpcPath, debugPath)`: registers the server at `rpcPath` on
  `DefaultServeMux` (the debug path is never requested). Go panics if `rpcPath` is registered
  twice on the mux: the premise `muxFree` is that it is not. -/
  muxFree : GoString → IProp GF
  Server_HandleHTTP_spec : ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF)
      (A : GoString → Prop) (debugPath : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        muxFree defaultRPCPath ∗
        isServer s γs ∗ (□ ∀ a, ⌜A a⌝ → srvServes γs C W a) ∗ srvEnv ∗ codecSet C }}
      (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"HandleHTTP"))
        (Val #defaultRPCPath)) (Val #debugPath))
    {{ RET #(); muxHas W A defaultRPCPath }}
  /-- `rpc.HandleHTTP()`: `DefaultServer.HandleHTTP(DefaultRPCPath, DefaultDebugPath)`. -/
  HandleHTTP_spec : ∀ (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (A : GoString → Prop),
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        muxFree defaultRPCPath ∗
        defaultServer γs ∗ (□ ∀ a, ⌜A a⌝ → srvServes γs C W a) ∗ srvEnv ∗ codecSet C }}
      (App (Val (@! net.rpc.HandleHTTP)) (Val #()))
    {{ RET #(); muxHas W A defaultRPCPath }}
  /-- `rpc.Register(rcvr)`: `DefaultServer.Register(rcvr)` (as `Server.Register.spec`: a
  second registration of a name returns an error). -/
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
        net.isListener (GF := GF) lis l ∗ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
        lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l la }}
      (App (App (Val (@! net.http.Serve)) (Val #lis)) (Val #interface.nil))
    {{ (err : GoInterface), RET #err; True }}

attribute [instance] RpcHttpHyp.rpcLisP_persistent RpcHttpHyp.handlerOk_persistent
  RpcHttpHyp.muxHas_persistent RpcHttpHyp.defaultServer_persistent

end hyp

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- **The codec's per-machine boot resource** (C2, the file header): what net/rpc's package
initialization leaves on a machine for `SetCodec` and the server: `codecMu`'s mutex, the
exclusive `codecUnset`, and the placeholder `invalidRequest`. -/
def rpcBootRes : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    sync.isMutex (globalAddr net.rpc.codecMu) (codecInv (GF := GF)) ∗ codecUnset (GF := GF) ∗
    globalAddr net.rpc.invalidRequest ↦□ ())

/-- `g`, but `False` at net/http and net/rpc (neither initialized yet). -/
def gNoRpc {PROP : Type _} [BI PROP] (g : GoString → PROP) : GoString → PROP := fun p =>
  if p = pkg_id.net.rpc ∨ p = pkg_id.net.http then iprop(False) else g p

/-- **Hypothesis** (C2): net/rpc's initializer, run on a machine where neither net/http nor
net/rpc is initialized yet (`gNoRpc g`), leaves the machine's boot resource `rpcBootRes`, and
`DefaultServeMux` without a handler at `DefaultRPCPath` (`muxFree`, which `HandleHTTP` consumes:
Go panics on a second registration of a path). Owned, not persistent: a machine's boot proof gets
it once, at its packages' initialization (as the replicas get their prophecy,
`cmd/server*/Boot.lean`). Taken by the deployment's boot proofs and visible in the statement;
never an instance. -/
class RpcBootHyp (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics]
    [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [H : RpcHttpHyp GF] : Prop where
  wp_init_own : ∀ (g : GoString → IProp GF), GetIsPkgInitProp pkg_id.net.rpc g →
    {{ ownInitializing (gNoRpc g) }} (App (Val net.rpc.initialize') (Val #()))
    {{ RET #(); ownInitializing g ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗
        rpcBootRes (GF := GF) ∗ H.muxFree defaultRPCPath }}

end boot

end Perennial.gryff
