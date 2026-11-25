/-
**net/rpc's server over HTTP, the kit's view** (notes/dsv-gryff.md, "net/rpc over HTTP"). The master
serves net/rpc over HTTP on a server of its own (`rpc.NewServer`, `Server.Register`,
`Server.HandleHTTP(DefaultRPCPath, DefaultDebugPath)`, `http.Serve(l, nil)`; `masterlib/master.go`)
and each replica on `DefaultServer` (`rpc.Register`, `rpc.HandleHTTP`, `http.Serve(l, nil)`;
`kit.go`, `serverlib/server.go`). Every one of those calls is `Net/`'s spec, used as it is
(`NewServer.spec_owned`, `Server.Register.spec_fresh`, `Register.spec_fresh`,
`Server.HandleHTTP.spec`, `HandleHTTP.spec`, `http.Serve.spec_rpc`, `DialHTTP.spec`), taken by the
proofs as a premise and linked at the top (`examples/gryffnet/Link.lean`).

**Wildcard listeners**: the master listens at `":7501"`, a replica's net/rpc at `":850x"`,
wildcards, which in `Net/`'s model take a connection dialed to any valid address with that port.
`rpcLisP W la hs hsAns` (persistent; Net's, `netRpcHttpAddr`): every valid address `la` takes
serves `W` behind the handshake (`rpcLisP_addr`), and the right to listen at `la` (`rpcLisP_lis`);
made once from `lisUnset la` at the start (`rpcLisP_set`).

**Error answers**: `srvServes` asks `errOk` of each service: the server's own messages
(`srvErrMsg`); the kit's services accept every non-empty message (`Rpc/Defs.lean`'s `withErr`), a
superset (`Server/RpcEnv.lean`'s `withErr_errOk`).

**A machine's boot resources** (`serverBoot`): net/http's and net/rpc's initializers, run the first
time on a machine, leave owned state (`Net/Proof/net/{http,rpc}/InitFirst.lean`, Net's interim
axioms `wp_init_first`): the right to register on `DefaultServeMux` (`muxOwn`), the codec registry
at `nil` (`codecUnset`, which `rpc.SetCodec`, the kit's `Register()`, takes) and `DefaultServer`'s
owned, empty registry; with their package facts (`httpEnv`, `rpcInit`) they make `httpInitRes` and
`rpcInitRes` (`httpInitRes_of_first`, `rpcInitRes_of_first`), which a server machine's boot
(`cmd/server*/Boot.lean`) hands to `main`.
-/
module

public import Net.Spec.net.rpc.DialHTTP
public import Net.Spec.net.rpc.Server__Accept
public import Net.Spec.net.rpc.Server__Register
public import Net.Spec.net.rpc.NewServer
public import Net.Spec.net.rpc.SetCodec
public import Net.Proof.net.rpc.ServerDefs
public import Net.Code.net.http
public import Net.Proof.net.rpc.InitFirst
public import Net.Proof.net.http.MuxDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Net Perennial.net.rpc

attribute [local instance] GooseGlobalGS.gooseInvGS

section hyp

/-- The listeners' part: the protocols of the rpc listener addresses, over the global state only
(every machine's heap sees the same ones; the start sets them before any machine runs). As
dsv-epaxos's `RpcHttpAddr`. Net proves it (`netRpcHttpAddr` below), which the top-level proof
instantiates; the proofs are generic in it. -/
class RpcHttpAddr [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
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
  /-- They are Net's listeners' protocols, which net/http's `Serve.spec_rpc` takes. -/
  rpcLisP_net : ∀ W la hs hsAns,
    rpcLisP W la hs hsAns ⊢ net.rpc.rpcLisP (Gg := Gg) W la hs hsAns

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
  rpcLisP_net := fun _ _ _ _ => .rfl

end hyp

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.http.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- **The codec's per-machine boot resource** (the file header): what net/rpc's package
initialization leaves on a machine for `SetCodec` and the server: `codecMu`'s mutex, the
exclusive `codecUnset`, and the placeholder `invalidRequest`. -/
def rpcBootRes : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    sync.isMutex (globalAddr net.rpc.codecMu) (codecInv (GF := GF)) ∗ codecUnset (GF := GF) ∗
    globalAddr net.rpc.invalidRequest ↦□ ())

/-- What net/rpc's first initialization leaves on a machine: the codec state (`rpcBootRes`), its
`DefaultServer` with an owned, empty registry (`defaultServerO γs γf ∗ svcOwn γf ∅`), and the
package variables its client and server read (`cliEnv`; `connected`). -/
def rpcInitRes : IProp GF :=
  iprop(rpcBootRes (GF := GF) ∗
    (∃ γs γf, net.rpc.defaultServerO γs γf ∗ net.rpc.svcOwn γf (∅ : GMap GoString Unit)) ∗
    net.rpc.cliEnv ∗ globalAddr net.rpc.connected ↦□ net.rpc.connectedStatus)

/-- What net/http's first initialization leaves on a machine: the right to register on
`DefaultServeMux`, nothing registered (`muxOwn`), and the package variables its server reads
(`httpSrvEnv`: its package fact `httpEnv` and what the first initialization leaves; until 2026-11-25
`httpEnv` alone). -/
def httpInitRes : IProp GF :=
  iprop(net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) [] ∗
    net.http.httpSrvEnv)

/-- A server machine's boot resources: what net/http's and net/rpc's first initializations leave. -/
def serverBoot : IProp GF :=
  iprop(httpInitRes (GF := GF) ∗ rpcInitRes (GF := GF))

/-- net/rpc's first initialization's results (its fact `rpcInit` and `rpcFirstRes`,
`Net/Proof/net/rpc/InitFirst.lean`) give `rpcInitRes`. -/
theorem rpcInitRes_of_first :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ net.rpc.rpcFirstRes (GF := GF) ⊢
      rpcInitRes (GF := GF) := by
  iintro ⟨#Hpk, Hf⟩
  ihave #Hi := net.rpc.rpcInit_access $$ Hpk
  unfold net.rpc.rpcInit
  icases Hi with ⟨-, #Hse, #Hcon, #Hmu⟩
  unfold net.rpc.rpcFirstRes
  icases Hf with ⟨Hun, %γs, %γf, #Hds, Hown⟩
  unfold rpcInitRes rpcBootRes
  unfold net.rpc.srvEnv
  icases Hse with ⟨#Hce, #Hinv⟩
  ihave #Hce2 := Hce
  iunfold net.rpc.cliEnv at Hce2
  icases Hce2 with ⟨%eof, %ueof, %ed, #Hio, #Hsync, -⟩
  iframe Hun Hsync Hmu Hinv Hce Hcon
  iexists γs, γf
  iframe Hds Hown

/-- net/http's first initialization's results (`net.http.wp_init_first_mux`'s) give `httpInitRes`. -/
theorem httpInitRes_of_first :
    net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) [] ∗
      net.http.httpSrvEnv (GF := GF) ⊢
      httpInitRes (GF := GF) := by
  iintro ⟨Hmux, #He⟩
  unfold httpInitRes
  iframe Hmux He

/-- `muxRpc` holds of fewer addresses. -/
theorem muxRpc_mono (m : Loc) (W : net.rpc.RpcWorld GF) (A A' : GoString → Prop) (p : GoString)
    (h : ∀ a, A' a → A a) :
    net.http.muxRpc (GF := GF) (hG := hG) m W A p ⊢ net.http.muxRpc (GF := GF) (hG := hG) m W A' p := by
  unfold net.http.muxRpc
  iintro ⟨%hh, #Hr, #Hh⟩
  iexists hh
  iframe Hr
  imodintro
  iintro %a %ha
  iapply Hh
  ipureintro; exact h a ha

end boot

end Perennial.gryff
