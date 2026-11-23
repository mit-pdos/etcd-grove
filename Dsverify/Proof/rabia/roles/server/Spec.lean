/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/Spec.lean`, run `rabia-r1wake-1`.)

`rabia/roles/server`'s specs (interface, stage 1b).

**`ServerInit`, the constructor hub** (`HUBS.md`): from server `k`'s share without its configuration
address (`serverCore`; stage 2: at the configuration `cf`, `cfgIs`, `k < n`), it makes
the channels, resets the ledger's slots, allocates server `k`'s local ghost names (`SrvNames`), the
split of its keys (`isSrvKeys`) and the slots' invariant (`slotsInv_alloc`), and builds the three
layers; its postcondition `serverBuilt` names each layer through its slots only: the proxy's
`proxyInitOk`/`proxyRO`, the network's `networkInitOk`, the consensus layer's `consExecRes`,
`consHandlerRes`, `consStatsRO`, and the shared `srvChans`, `ledgerRO`, `slotsInv`.
`Prologue` connects (`serverReady`: the routines' resources), `ServerMain` starts the six routines
and waits on `Done` (never closed: it does not return), `TerminalLogger` (started by `Prologue`)
never returns either.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.network.Spec
public import Dsverify.Proof.rabia.roles.server.layers.proxy.Spec
public import Dsverify.Proof.rabia.internal.system.Spec
public import Dsverify.Proof.rabia.internal.logger.Spec
public import Dsverify.GeneratedProof.rabia.roles.server
public import Dsverify.Proof.rabia.roles.server.Base
public import Dsverify.Proof.rabia.Core.PkgState
public import Perennial.Proof.sync.WaitGroupDefs

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.roles.server.layers.network rabia.roles.server.layers.consensus
  rabia.roles.server.layers.proxy rabia

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

/-- The server `s`'s read-only fields (persistent): its id, `Done`, its layers. -/
def serverRO (k : Nat) (ch : SrvChans) (s p n c : Loc) : IProp GF :=
  iprop(structFieldRef Server go!"SvrId" s ↦□ (W32 k) ∗ structFieldRef Server go!"Done" s ↦□ ch.done ∗
    structFieldRef Server go!"Proxy" s ↦□ p ∗ structFieldRef Server go!"Network" s ↦□ n ∗
    structFieldRef Server go!"Consensus" s ↦□ c)

/-- The wait group's namespace. -/
def srvWgN (k : Nat) : Namespace := ndot (ndot rabiaR "srv_wg") (toString k)

/-- The server's own state (its wait group, its other fields): the wait group `Wg` (read-only
field), its invariant, its counter (zero) and its waiters' token. -/
def serverOwn (γ : Names) (k : Nat) (s : Loc) : IProp GF :=
  iprop(∃ (wg : Loc) (γw : sync.WaitGroupNames), structFieldRef Server go!"Wg" s ↦□ wg ∗
    sync.isWaitGroup wg γw (srvWgN k) ∗ sync.ownWaitGroup γw (W32 0) ∗
    sync.ownWaitGroupWaiters γw 0)

/-- Server `k` built (`ServerInit`'s postcondition): each layer's built state, by its slots. -/
def serverBuilt (γ : Names) (cf : RCfg) (k : Nat) (s : Loc) : IProp GF :=
  iprop(∃ (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (p n c : Loc) (ledger : GoSlice),
    serverRO k ch s p n c ∗ serverOwn γ k s ∗
    srvChans γ cf k γl ch ∗ ledgerRO γl ledger ∗ slotsInv γ cf k γl γc ∗
    proxyInitOk γ cf k γl γc ch p ∗ proxyRO γ k p ∗
    networkInitOk γ cf k γl ch n ∗
    consExecRes γ cf k γl γc ch c ∗ consHandlerRes γ cf k γl γc ch c ∗ consStatsRO c)

/-- Server `k` connected (`Prologue`'s postcondition): the six routines' resources. -/
def serverReady (γ : Names) (cf : RCfg) (k : Nat) (s : Loc) : IProp GF :=
  iprop(∃ (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (p n c : Loc),
    serverRO k ch s p n c ∗ serverOwn γ k s ∗ srvChans γ cf k γl ch ∗
    proxyCmdRes γ cf k γl ch p ∗ proxyKvsRes γ cf k γl γc p ∗
    networkRouterRes γ cf k γl ch n ∗ networkSerRes γ cf k γl n ∗
    consExecRes γ cf k γl γc ch c ∗ consHandlerRes γ cf k γl γc ch c)

/-- The terminal logger's resources (persistent). -/
def serverLogRes (γ : Names) (cf : RCfg) (k : Nat) (s : Loc) : IProp GF :=
  iprop(∃ (γl : SrvNames) (ch : SrvChans) (p n c : Loc),
    serverRO k ch s p n c ∗ srvChans γ cf k γl ch ∗ proxyRO γ k p ∗ consStatsRO c)

end defs

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.Assumptions]

/-- `ServerInit(k, proxyAddr k, netAddr k)`: server `k` built from its share. -/
abbrev ServerInit.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (id : w32), id.toNat = k → k < cf.n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server ∗ confRO cf ∗ cfgIs γ.rab cf ∗
      serverCore γ k }}
    (App (App (App (Val (@! ServerInit)) (Val #id)) (Val #(proxyAddr k))) (Val #(netAddr k)))
  {{ (s : Loc), RET #s; serverBuilt γ cf k s }}

/-- `s.Prologue()`: the signal listener, the network layer connected, the proxy accepting, the
terminal logger. -/
abbrev Server.Prologue.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗
      serverBuilt γ cf k s }}
    (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"Prologue")) (Val #()))
  {{ RET #(); serverReady γ cf k s }}

/-- `s.ServerMain()`: the six routines; waits on `Done`: never returns. -/
abbrev Server.ServerMain.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗
      serverReady γ cf k s }}
    (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"ServerMain")) (Val #()))
  {{ RET #(); False }}

/-- `s.TerminalLogger()`: never returns. -/
abbrev Server.TerminalLogger.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server ∗ confRO cf ∗ serverLogRes γ cf k s }}
    (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"TerminalLogger")) (Val #()))
  {{ RET #(); False }}

end spec

end Perennial.rabia.roles.server
