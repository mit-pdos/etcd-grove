/-
**Hypotheses: net/rpc's server over HTTP** (notes/dsv-gryff.md, "Hypotheses"). The master serves
net/rpc over HTTP on a server of its own (`rpc.NewServer`, `Server.Register`,
`Server.HandleHTTP(DefaultRPCPath, DefaultDebugPath)`, `http.Serve(l, nil)`; `masterlib/master.go`)
and each replica on `DefaultServer` (`rpc.Register`, `rpc.HandleHTTP`, `http.Serve(l, nil)`;
`kit.go`, `serverlib/server.go`). `Net/` proves raw net/rpc (models-rpc-server: `NewServer`,
`Server.Register`, `ServeConn`, `Accept`; rpc-defaultserver: `defaultServer`, the package-level
`Register` and `RegisterName`) and, from models-rpc-http, the client over HTTP (`rpcAddrP`, `connectReq`, `connectAns`, `defaultRPCPath`, `DialHTTP.spec`,
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

**Error answers** (A2/C3): `srvServes` asks `errOk` of each service: the server's own messages
(`srvErrMsg`, Net's restriction, landed); the kit's services accept every non-empty message
(`Rpc/Defs.lean`'s `withErr`), a superset (`Server/RpcEnv.lean`'s `withErr_errOk`). **Client.Call's
errors** (C1): today a non-`ServerError` error comes with `models_lab.errAny`; it is to become
`∃ msg, errMsg err msg ∗ ⌜msg ≠ []⌝` (no use here needs more than `errAny`).

**The codec's per-machine boot resource** (C2, `rpcBootRes`): `rpc.SetCodec` (the kit's
`Register()`) needs `codecUnset` (exclusive: the other half of `codec`'s points-to, at `nil`) and
`codecMu`'s mutex, and the server reads `invalidRequest`; they come from net/rpc's package
initialization **once per machine**, as a resource the machine's boot hands to `main` (like the
replicas' prophecy, `cmd/server*/Boot.lean`). `Net/` does not give it yet (its net/rpc
initialization is names only), so the boot proofs take it from the class `RpcBootHyp`: net/rpc's
initializer, run where net/rpc is not initialized, leaves `rpcInitRes` (`rpcBootRes`,
`DefaultServer`, the package variables its client and server read); net/http's, where net/http is
not initialized, leaves `httpInitRes` (`muxFree DefaultRPCPath`, `httpEnv`). A hypothesis of the
deployment's boot (`cmd/server*/Boot.lean`), visible in the statement. Not persistent and never
made by an update (`|==> codecFresh` would be unsound), and never derived from `isPkgInit` (which
is `True` for these names-only packages; Upamanyu's review of dsv-epaxos).
-/
module

public import Net.Spec.net.rpc.DialHTTP
public import Net.Spec.net.rpc.Server__Accept
public import Net.Spec.net.rpc.Server__Register
public import Net.Spec.net.rpc.NewServer
public import Net.Spec.net.rpc.SetCodec
public import Net.Proof.net.rpc.ServerDefs
public import Net.Code.net.http
public import Dsverify.Proof.net.rpc.Init
public import Dsverify.Proof.net.http.Init

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Net Perennial.net.rpc

attribute [local instance] GooseGlobalGS.gooseInvGS

section hyp

/-- The listeners' part: the protocols of the rpc listener addresses, over the global state only
(every machine's heap sees the same ones; the start sets them before any machine runs). As
dsv-epaxos's `RpcHttpAddr`. No longer a hypothesis: Net proves it (`netRpcHttpAddr` below), and the
statement instantiates it so; the proofs stay generic in it. -/
class RpcHttpAddr [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    (GF : BundledGFunctors) [Gg : GooseGlobalGS HasLC.hasLC GF] [π : NetProtoGS] where
  /-- A listener address's rpc protocols (the file header). -/
  rpcLisP : RpcWorld GF → GoString → List w8 → List w8 → IProp GF
  rpcLisP_persistent : ∀ W la hs hsAns, Persistent (rpcLisP W la hs hsAns)
  rpcLisP_addr : ∀ W la hs hsAns a, addrOk a = true → lisAccepts la a →
    rpcLisP W la hs hsAns ⊢ rpcAddrP (Gg := Gg) W a hs hsAns
  /-- The right to listen at `la` (`net.Listen.spec`'s update; models-rpc-http `e6b232b2f6`'s
  shape). -/
  rpcLisP_lis : ∀ W la hs hsAns,
    rpcLisP W la hs hsAns ⊢
      |={⊤,∅}=> lisToks (extGlobalGS netExt (G := Gg)) la ∗
        (lisToks (extGlobalGS netExt (G := Gg)) la ={∅,⊤}=∗ True)
  rpcLisP_ok : ∀ W la hs hsAns, rpcLisP W la hs hsAns ⊢ ⌜listenOk la = true⌝
  /-- The start sets them once, from the addresses `la` takes, unset (`e6b232b2f6`'s premises;
  `W.hs`/`W.hsAns` are `RpcWorld`'s fields, merged from models-rpc-http, so a world with HTTP's
  handshake at every address `la` takes is built as `{ W with hs := …, hsAns := … }`). -/
  rpcLisP_set : ∀ (E : CoPset) (W : RpcWorld GF) (la : GoString) (hs hsAns : List w8),
    listenOk la = true →
    (∀ a, addrOk a = true ∧ lisAccepts la a → W.hs a = hs ∧ W.hsAns a = hsAns) →
    regCtx (Gg := Gg) -∗ inv regN' (regInv (Gg := Gg) W) -∗
      lisUnset (Gg := Gg) la ={E}=∗ rpcLisP W la hs hsAns

attribute [instance] RpcHttpAddr.rpcLisP_persistent

/-- **`RpcHttpAddr` holds: Net's listeners' rpc protocols** (models-rpc-http, landed:
`Net/Proof/net/rpc/Proto.lean`'s `rpcLisP` and its proved laws `rpcLisP_addr`, `rpcLisP_lis`,
`rpcLisP_ok`, `rpcLisP_set`). A `def`, not an `instance`: the statement gives it to the theorems
taking `[RpcHttpAddr GF]` (so `RpcHttpAddr` is no premise of the statement any more). -/
def netRpcHttpAddr [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [Gg : GooseGlobalGS HasLC.hasLC GF] [π : NetProtoGS] :
    RpcHttpAddr GF where
  rpcLisP := net.rpc.rpcLisP (Gg := Gg)
  rpcLisP_persistent := fun W la hs hsAns => net.rpc.rpcLisP_persistent W la hs hsAns
  rpcLisP_addr := fun W la hs hsAns a hok hacc => net.rpc.rpcLisP_addr W la hs hsAns a hok hacc
  rpcLisP_lis := fun W la hs hsAns => net.rpc.rpcLisP_lis W la hs hsAns
  rpcLisP_ok := fun W la hs hsAns => net.rpc.rpcLisP_ok W la hs hsAns
  rpcLisP_set := fun E W la hs hsAns hla hhs => net.rpc.rpcLisP_set E W la hs hsAns hla hhs

/-- **Hypothesis** (the file header): net/rpc's server over HTTP, as models-rpc-http will state
it (per machine heap, over the listeners' part `RpcHttpAddr`). -/
class RpcHttpHyp [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    [go_gctx : GoGlobalContext] (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF]
    [go.Semantics] [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
    [RA : RpcHttpAddr GF] where
  /-- `h` is a net/http handler of `path` serving `W` at the addresses `A`. -/
  handlerOk : RpcWorld GF → (GoString → Prop) → GoString → GoInterface → IProp GF
  handlerOk_persistent : ∀ W A path h, Persistent (handlerOk W A path h)
  /-- `DefaultServeMux` routes `path` to a handler serving `W` at the addresses `A`. -/
  muxHas : RpcWorld GF → (GoString → Prop) → GoString → IProp GF
  muxHas_persistent : ∀ W A path, Persistent (muxHas W A path)
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
  /-- A server `NewServer` made has no service yet (`γ`'s service map is empty: Net's
  `NewServer.spec` gives `isServer` only, so a first `Register` on it could not be shown to
  succeed: a finding for models-rpc-server). -/
  srvFresh : GName → IProp GF
  NewServer_fresh_spec :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
      (App (Val (@! net.rpc.NewServer)) (Val #()))
    {{ (s : Loc), RET #s; ∃ γ : GName, isServer s γ ∗ srvFresh γ }}
  /-- `s.Register(rcvr)` on a fresh server (`Server.Register.spec`'s, without its error case:
  net/rpc's `register` fails only for a name that is not exported, a receiver with no suitable
  method, or a name already registered, none of which a fresh server and `rcvrIs` allow). -/
  Server_Register_fresh_spec : ∀ (s : Loc) (γ : GName) (C : CodecSpec GF) (rcvr : GoInterface)
      (S : MethodSpec GF) (nm : GoString) (c : w8) (rest : GoString),
    nm = c :: rest → uint.Z (W8 0x41) ≤ uint.Z c ∧ uint.Z c ≤ uint.Z (W8 0x5A) →
    {{ isServer s γ ∗ srvFresh γ ∗ codecSet C ∗ C.rcv rcvr (rcvrIs C rcvr S nm false) }}
      (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"Register")) (Val #rcvr))
    {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ svcReg γ C nm S }}
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
        RA.rpcLisP W la (connectReq path) connectAns ∗ muxHas W (lisAccepts la) path ∗
        net.isListener (GF := GF) lis l ∗ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
        lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l la }}
      (App (App (Val (@! net.http.Serve)) (Val #lis)) (Val #interface.nil))
    {{ (err : GoInterface), RET #err; True }}

attribute [instance] RpcHttpHyp.handlerOk_persistent
  RpcHttpHyp.muxHas_persistent

end hyp

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [RA : RpcHttpAddr GF]

/-- **The codec's per-machine boot resource** (C2, the file header): what net/rpc's package
initialization leaves on a machine for `SetCodec` and the server: `codecMu`'s mutex, the
exclusive `codecUnset`, and the placeholder `invalidRequest`. -/
def rpcBootRes : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    sync.isMutex (globalAddr net.rpc.codecMu) (codecInv (GF := GF)) ∗ codecUnset (GF := GF) ∗
    globalAddr net.rpc.invalidRequest ↦□ ())

/-- `g`, but `False` at the package `q` (not initialized yet). -/
def gNoPkg {PROP : Type _} [BI PROP] (q : GoString) (g : GoString → PROP) : GoString → PROP :=
  fun p => if p = q then iprop(False) else g p

/-- What net/rpc's initializer leaves on a machine: the codec state (`rpcBootRes`), its
`DefaultServer` (`DefaultServer = NewServer()`, a server with registry `γs`), and the package
variables its client and server read (`cliEnv`: `io`'s and `sync`'s facts, `io.EOF`,
`ErrUnexpectedEOF`, `ErrDeadlineExceeded`, `errFrame`, `ErrShutdown`, `debugLog = false`;
`connected = "200 Connected to Go RPC"`). -/
def rpcInitRes : IProp GF :=
  iprop(rpcBootRes (GF := GF) ∗ (∃ γs, net.rpc.defaultServer γs) ∗ net.rpc.cliEnv ∗
    globalAddr net.rpc.connected ↦□ net.rpc.connectedStatus)

/-- What net/http's initializer leaves on a machine: `DefaultServeMux` with no handler at
`DefaultRPCPath` (`muxFree`, which `HandleHTTP` consumes: Go panics on a second registration of a
path) and its imports `bufio` and `io` initialized (`httpEnv`). -/
def httpInitRes [H : RpcHttpHyp GF] : IProp GF :=
  iprop(H.muxFree defaultRPCPath ∗ net.http.httpEnv)

/-- A server machine's boot resources: what net/http's and net/rpc's initializers leave. -/
def serverBoot [H : RpcHttpHyp GF] : IProp GF :=
  iprop(httpInitRes (GF := GF) ∗ rpcInitRes (GF := GF))

/-- **Hypothesis** (C2; Upamanyu's review of dsv-epaxos on #24: `DefaultServer` and net/rpc's and
net/http's package variables come from a machine's boot, never from an `isPkgInit` fact, which is
`True` for these names-only packages): net/rpc's initializer, run on a machine where net/rpc is
not initialized yet (`gNoPkg net/rpc g`), leaves `rpcInitRes`; net/http's, where net/http is not
initialized yet, leaves `httpInitRes`. Owned, not persistent: a machine's boot proof gets them
once, at its packages' initialization (`cmd/server*/Boot.lean`, as the replicas' prophecy). Taken
by the deployment's boot proofs and visible in the statement; never an instance.

**Every package the initializers reach is named** (dsv-inithyp-fix; as swiftpaxos's `RpcFirstInit`):
the table before (`gNoPkg q g`) and after (`g`) agree beyond the package `q`, and the premise
`GetIsPkgInitProp q g` is the shared `Dsverify/Proof/net/{rpc,http}/Init.lean`'s condition, which
since dsv-inithyp-fix constrains the initializer's whole import closure (`build_get_is_pkg_init_wf`
over the `PkgInfo` imports, models-rpc-http's
`mime/multipart` and `net/http/internal/ascii` included). So the table holds each such package's fact before
and after, and a table with `False` at an import (say `bufio`), which would make the post
`ownInitializing g` need `□ False`, does not meet the premise. The programs' tables
(`HYP_IMPORTS` default `'all'`, `etc/dsv/gryff.py`) hold that closure and prove the conditions. -/
class RpcBootHyp (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics]
    [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF] : Prop where
  wp_init_own : ∀ (g : GoString → IProp GF), GetIsPkgInitProp pkg_id.net.rpc g →
    {{ ownInitializing (gNoPkg pkg_id.net.rpc g) }} (App (Val net.rpc.initialize') (Val #()))
    {{ RET #(); ownInitializing g ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗
        rpcInitRes (GF := GF) }}
  wp_http_own : ∀ (g : GoString → IProp GF), GetIsPkgInitProp pkg_id.net.http g →
    {{ ownInitializing (gNoPkg pkg_id.net.http g) }} (App (Val net.http.initialize') (Val #()))
    {{ RET #(); ownInitializing g ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
        httpInitRes (GF := GF) }}

end boot

end Perennial.gryff
