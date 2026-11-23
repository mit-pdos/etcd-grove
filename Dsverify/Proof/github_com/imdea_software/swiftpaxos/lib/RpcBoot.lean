/-
**Hypothesis: net/rpc's first initialization** (notes/dsv-swiftpaxos.md, "State (twelfth
session)", the boot, source (b)). net/rpc's and net/http's initializers are `InitHyp`s here
(`Dsverify/Proof/net/{rpc,http}/Init.lean`): they establish the packages' facts (`True`), and
keep nothing. A machine's net/rpc state, though, is owned and made by those initializers the
first time they run: the codec registry at `nil` (`codecFresh`: `codecMu`'s mutex and `codec`'s
other half), the client's and server's package variables (`net.rpc.srvEnv`, which includes
`cliEnv`), what `DialHTTP` reads (`dialEnv`), net/http's `DefaultServeMux` with nothing registered
(`RpcHttpHyp.muxOwner []`) and net/rpc's `DefaultServer = NewServer()` (`∃ γs,
RpcHttpHyp.defaultServer γs`).

`RpcFirstInit` states that: net/rpc's initializer, run on a machine where neither net/rpc nor
net/http is initialized yet (the initialization table `g` is `False` at both), ends in a table
`g'` that agrees with `g` elsewhere and meets net/rpc's and net/http's `GetIsPkgInitProp` (as
their `InitHyp`s'), and returns those resources. This is what Go does: a package's initializer
runs once per process, its first run allocates the package's variables (net/http's
`DefaultServeMux`, net/rpc's `DefaultServer`, the error variables), and it does not panic
(`InitHyp`'s trust).

**Status: a visible premise, approved by the coordinator (2026-11-23).** It is a premise of
`swiftpaxos_remote_robust`, per machine heap, and never an instance. It is the same kind of
premise as dsv-epaxos's landed `RpcBoot` (a whole command's initializer returning `rpcBootRes`),
scoped to net/rpc's initializer only: the kit's own packages' first runs (`concurrent-map`,
`client`, `swift`, `swiftnet`, the commands) are proved (`examples/swiftnet/Boot.lean`). It stands
in for the per-machine net/rpc boot resource Upamanyu said `Net/` will provide; when `Net/` has it,
this premise goes.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps
public import Dsverify.Proof.net.rpc.Init
public import Dsverify.Proof.net.http.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section hyp
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [SwiftNetPkgState GF] [net.rpc.Assumptions] [net.FieldAssumptions]
variable [log.Assumptions] [net.http.Assumptions] [RpcHttpAddr GF]

/-- A machine's net/rpc boot resources (dsv-epaxos's `rpcBootRes`, with `cliEnv` through
`srvEnv`): see the file header. -/
def rpcBootRes [H : RpcHttpHyp GF] : IProp GF :=
  iprop(sync.isMutex (globalAddr net.rpc.codecMu) net.rpc.codecInv ∗ net.rpc.codecUnset ∗
    net.rpc.srvEnv ∗ H.muxOwner [] ∗ (∃ γs, H.defaultServer γs) ∗ dialEnv)

/-- **Hypothesis** (the file header): net/rpc's first initialization. -/
class RpcFirstInit [H : RpcHttpHyp GF] : Prop where
  wp_init_first : ∀ (g g' : GoString → IProp GF),
    (g pkg_id.net.rpc ⊢ False) → (g pkg_id.net.http ⊢ False) →
    GetIsPkgInitProp pkg_id.net.rpc g' → GetIsPkgInitProp pkg_id.net.http g' →
    (∀ p, p ≠ pkg_id.net.rpc → p ≠ pkg_id.net.http → g' p = g p) →
    {{ ownInitializing g }} (App (Val net.rpc.initialize') (Val #()))
    {{ RET #(); ownInitializing g' ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ rpcBootRes }}

end hyp

end Perennial.github_com.imdea_software.swiftpaxos
