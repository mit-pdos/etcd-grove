/-
**net/rpc's first initialization on a machine** (notes/dsv-swiftpaxos.md, the boot). A machine's
net/rpc state is owned and made by net/rpc's and net/http's initializers the first time they run:
the codec registry at `nil` (`codecMu`'s mutex and `codec`'s other half, `codecUnset`), the client's
and server's package variables (`net.rpc.srvEnv`, which includes `cliEnv`), what `DialHTTP` reads
(`dialEnv`), net/http's `DefaultServeMux` with nothing registered (`muxOwner []`) and net/rpc's
`DefaultServer = NewServer()` with an owned, empty registry (`defaultServerO γs γf ∗ svcOwn γf ∅`,
which `Register.spec_fresh` takes): `rpcBootRes`.

`wp_rpc_first` (and the class `RpcFirstInit`, its shape for the kit's boot): net/rpc's initializer, run on a machine where neither net/rpc nor net/http is
initialized yet (the initialization table `g` is `False` at both: in the kit's commands net/rpc's
initializer is the first to reach net/http's), ends in a table `g'` that agrees with `g` elsewhere
and meets net/rpc's `GetIsPkgInitProp`, and returns those resources. Proved from `Net/`'s
`net.rpc.wp_init_first_http` (net/rpc's initializer, proved; net/http's first run inside it, Net's
interim axiom `net.http.wp_init_first`, on a machine of at most `2 ^ 30` threads), given
`NewServer`'s spec with an owned registry (which the linking modules pass).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps
public import Net.Proof.net.rpc.InitFirst
public import Net.Proof.net.http.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section boot
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [SwiftNetPkgState GF] [net.rpc.Assumptions] [net.FieldAssumptions]
variable [log.Assumptions] [net.http.Assumptions]

/-- A machine's net/rpc boot resources (see the file header). -/
def rpcBootRes : IProp GF :=
  iprop(sync.isMutex (globalAddr net.rpc.codecMu) net.rpc.codecInv ∗ net.rpc.codecUnset ∗
    net.rpc.srvEnv ∗ muxOwner [] ∗
    (∃ γs γf : GName, net.rpc.defaultServerO γs γf ∗ net.rpc.svcOwn γf ∅) ∗ dialEnv ∗
    isPkgInit (PROP := IProp GF) pkg_id.net.http)

/-- **net/rpc's first initialization** (see the file header). -/
theorem wp_rpc_first (wp_NewServer : net.rpc.NewServer.spec_owned (GF := GF) (hG := hG))
    (hT : threadBound GF ≤ 2 ^ 30) (g g' : GoString → IProp GF)
    (hr : g pkg_id.net.rpc ⊢ iprop(False)) (hh : g pkg_id.net.http ⊢ iprop(False))
    (Hr : GetIsPkgInitProp pkg_id.net.rpc g')
    (hsame : ∀ p, p ≠ pkg_id.net.rpc → p ≠ pkg_id.net.http → g' p = g p) :
    {{ ownInitializing g }} (App (Val net.rpc.initialize') (Val #()))
    {{ RET #(); ownInitializing g' ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ rpcBootRes }} := by
  iintro %Φ Hown HΦ
  iapply (net.rpc.wp_init_first_http wp_NewServer g g' hr hh Hr hsame) $$ [Hown]
  · iframe Hown; ipureintro; exact hT
  iintro !> ⟨Hown, #Hpk, Hres, #Hht, Hmux⟩
  iapply HΦ
  iframe Hown Hpk
  ihave #Hri := net.rpc.rpcInit_access $$ Hpk
  ihave #He := net.http.httpEnv_access $$ Hht
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, #Hsrv, #Hcon, #Hmu⟩
  iunfold net.rpc.rpcFirstRes at Hres
  icases Hres with ⟨Hcu, Hds⟩
  iunfold rpcBootRes
  iframe Hmu Hcu Hsrv Hmux Hds Hht
  iunfold dialEnv
  iframe He Hcon

/-- net/rpc's first initialization in the shape the kit's boot (`BootLinked.lean`) takes, as a
class: the top-level proof gives it from `wp_rpc_first` on a machine of at most `2 ^ 30` threads
(`Proof/.../TopLevelRobustness.lean`); not a premise of the statement. -/
class RpcFirstInit : Prop where
  wp_init_first : ∀ (g g' : GoString → IProp GF),
    (g pkg_id.net.rpc ⊢ False) → (g pkg_id.net.http ⊢ False) →
    GetIsPkgInitProp pkg_id.net.rpc g' → GetIsPkgInitProp pkg_id.net.http g' →
    (∀ p, p ≠ pkg_id.net.rpc → p ≠ pkg_id.net.http → g' p = g p) →
    {{ ownInitializing g }} (App (Val net.rpc.initialize') (Val #()))
    {{ RET #(); ownInitializing g' ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ rpcBootRes }}

/-- `RpcFirstInit` holds on a machine of at most `2 ^ 30` threads. -/
theorem rpcFirstInit_of (wp_NewServer : net.rpc.NewServer.spec_owned (GF := GF) (hG := hG))
    (hT : threadBound GF ≤ 2 ^ 30) : RpcFirstInit (GF := GF) :=
  ⟨fun g g' hr hh Hr _ hs => wp_rpc_first wp_NewServer hT g g' hr hh Hr hs⟩

end boot

end Perennial.github_com.imdea_software.swiftpaxos
