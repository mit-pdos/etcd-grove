/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/proxy/Spec.lean`, run `rabia-r1wake-1`.)

`rabia/roles/server/layers/proxy`'s specs (interface, stage 1b).

The proxy layer of server `k`: `ProxyInit` (its endpoint `ProxyTcpInit`, the store), `Prologue`
(the endpoint's `Connect`), and its two routines, which never return (`Done` is never closed):
`CmdReceiver` (stage 2: the client requests received are batched, up to `batchSize` of them (or
fewer, at the batch timeout), into a new object `(k, ProSeq)`: `newObj`'s batch, sent to the
network layer as a client request with its permit) and `KVSExecutor` (executes the decided
slots in order, reading each decision through the consensus layer's slots' invariant,
`readDecision`, executes a decided batch's requests in order and replies to each request's
client if it is connected here).

What it takes (`proxyBootRes`, from `ServerInit`): its part of server `k`'s keys, the permits'
authority, the receipts of its clients' requests. `proxyRO` (persistent): its endpoint, for the
terminal logger.
-/
module

public import Dsverify.Proof.rabia.internal.tcp.Spec
public import Dsverify.Proof.rabia.roles.server.layers.consensus.Spec
public import Dsverify.GeneratedProof.rabia.roles.server.layers.proxy
public import Dsverify.Proof.rabia.Core.PkgState
public import Dsverify.Proof.rabia.roles.server.layers.proxy.Base

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.proxy

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia.roles.server.layers.consensus rabia

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

/-- What server `k`'s proxy needs at its start (`ServerInit` gives it). -/
def proxyBootRes (γ : Names) (k : Nat) (γl : SrvNames) : IProp GF :=
  iprop(keysPart γl true [] ∗ isSrvKeys γ k γl ∗ crAuth γl ∅ ∗
    [∗list] c ∈ List.range nC, [∗list] n ∈ List.range opBudget, pRcpt γl c n)

/-- The proxy `p`'s endpoint (persistent). -/
def proxyRO (γ : Names) (k : Nat) (p : Loc) : IProp GF :=
  iprop(∃ t : Loc, structFieldRef Proxy go!"TCP" p ↦□ t ∗ proxyTcpRO γ k t)

/-- The proxy's store `m` reads as the model's store `s` (a missing key reads `""`). -/
def StoreRel (m : GMap GoString GoString) (s : (kv GoString GoString).State) : Prop :=
  ∀ key, (m.lookup key).getD [] = (s key).getD []

/-- The proxy `p`'s read-only fields (persistent): its server's id `k`, its channels, its
endpoint `t`, its store's map `kv`, its ledger, and the function fields set for the in-memory
store (`StorageMode` 0). -/
def proxyFields (k : Nat) (ch : SrvChans) (p : Loc) (wg t : Loc) (kv : GoMap)
    (ledger : GoSlice) : IProp GF :=
  iprop(∃ id : w32, ⌜id.toNat = k⌝ ∗ structFieldRef Proxy go!"SvrId" p ↦□ id ∗
    structFieldRef Proxy go!"Wg" p ↦□ wg ∗ structFieldRef Proxy go!"Done" p ↦□ ch.done ∗
    structFieldRef Proxy go!"ClientsIn" p ↦□ ch.c2p ∗ structFieldRef Proxy go!"ToNet" p ↦□ ch.p2n ∗
    structFieldRef Proxy go!"NetIn" p ↦□ ch.n2p ∗ structFieldRef Proxy go!"TCP" p ↦□ t ∗
    structFieldRef Proxy go!"KVStore" p ↦□ kv ∗
    structFieldRef Proxy go!"executeCmdFunc" p ↦□
      methods (go.GoType.PointerType Proxy.ty) go!"naiveExecuteCmd" #p ∗
    structFieldRef Proxy go!"executeAndReplyFunc" p ↦□
      methods (go.GoType.PointerType Proxy.ty) go!"singleExecuteAndReply" #p ∗
    structFieldRef Proxy go!"Ledger" p ↦□ ledger)

/-- The proxy `p` after `ProxyInit`. -/
def proxyInitOk (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (p : Loc) :
    IProp GF :=
  iprop(∃ (wg t : Loc) (kv : GoMap) (ledger : GoSlice) (cd : Loc), ⌜k < cf.n⌝ ∗
    proxyFields k ch p wg t kv ledger ∗
    structFieldRef Proxy go!"CurrSeq" p ↦ (W32 0) ∗ structFieldRef Proxy go!"CurrDec" p ↦ cd ∗
    ownMap kv (DFrac.own 1) (∅ : GMap GoString GoString) ∗
    proxyTcpRO γ k t ∗ proxyTcpOwn γ cf k γl t ∗
    srvChans γ cf k γl ch ∗ ledgerRO γl ledger ∗ slotsInv γ cf k γl γc ∗
    isSrvKeys γ k γl ∗ keysPart γl true [] ∗ crAuth γl ∅)

/-- `CmdReceiver`'s resources after `Prologue`. -/
def proxyCmdRes (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (ch : SrvChans) (p : Loc) : IProp GF :=
  iprop(∃ (wg t : Loc) (kv : GoMap) (ledger : GoSlice), ⌜k < cf.n⌝ ∗
    proxyFields k ch p wg t kv ledger ∗ srvChans γ cf k γl ch ∗
    isSrvKeys γ k γl ∗ keysPart γl true [] ∗ crAuth γl ∅)

/-- `KVSExecutor`'s resources after `Prologue`. -/
def proxyKvsRes (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (p : Loc) : IProp GF :=
  iprop(∃ (ch : SrvChans) (wg t : Loc) (kv : GoMap) (ledger : GoSlice) (cd : Loc),
    proxyFields k ch p wg t kv ledger ∗
    structFieldRef Proxy go!"CurrSeq" p ↦ (W32 0) ∗ structFieldRef Proxy go!"CurrDec" p ↦ cd ∗
    ownMap kv (DFrac.own 1) (∅ : GMap GoString GoString) ∗
    isChanBag (V := Unit) γl.done ch.done doneP ∗ ledgerRO γl ledger ∗ slotsInv γ cf k γl γc ∗
    proxyTcpRO γ k t)

instance proxyFields_persistent (k : Nat) (ch : SrvChans) (p wg t : Loc) (kv : GoMap)
    (ledger : GoSlice) : Persistent (proxyFields (GF := GF) k ch p wg t kv ledger) := by
  unfold proxyFields; infer_instance

instance proxyRO_persistent (γ : Names) (k : Nat) (p : Loc) :
    Persistent (proxyRO (GF := GF) γ k p) := by unfold proxyRO; infer_instance

end defs

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.layers.proxy.Assumptions]

/-- `ProxyInit(k, done, wg, proxyAddr k, ClientsToProxy, ProxyToNet, NetToProxy, ledger)`. -/
abbrev ProxyInit.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (id : w32) (wg : Loc)
    (ledger : GoSlice), id.toNat = k → k < cf.n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.proxy ∗ confRO cf ∗
      srvChans γ cf k γl ch ∗ ledgerRO γl ledger ∗ slotsInv γ cf k γl γc ∗ shared γ ∗
      proxyBootRes γ k γl }}
    (App (App (App (App (App (App (App (App (Val (@! ProxyInit)) (Val #id)) (Val #ch.done))
      (Val #wg)) (Val #(proxyAddr k))) (Val #ch.c2p)) (Val #ch.p2n)) (Val #ch.n2p))
      (Val #ledger))
  {{ (p : Loc), RET #p; proxyInitOk γ cf k γl γc ch p ∗ proxyRO γ k p }}

/-- `p.Prologue()`: accepting clients in the background; the routines' resources. -/
abbrev Proxy.Prologue.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.proxy ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗
      proxyInitOk γ cf k γl γc ch p }}
    (App (Val (p @!! go.GoType.PointerType Proxy.ty @!! go!"Prologue")) (Val #()))
  {{ RET #(); proxyCmdRes γ cf k γl ch p ∗ proxyKvsRes γ cf k γl γc p }}

/-- `p.CmdReceiver()`: never returns. -/
abbrev Proxy.CmdReceiver.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (ch : SrvChans) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.proxy ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗
      proxyCmdRes γ cf k γl ch p }}
    (App (Val (p @!! go.GoType.PointerType Proxy.ty @!! go!"CmdReceiver")) (Val #()))
  {{ RET #(); False }}

/-- `p.KVSExecutor()`: never returns. -/
abbrev Proxy.KVSExecutor.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.proxy ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗
      proxyKvsRes γ cf k γl γc p }}
    (App (Val (p @!! go.GoType.PointerType Proxy.ty @!! go!"KVSExecutor")) (Val #()))
  {{ RET #(); False }}

end spec

end Perennial.rabia.roles.server.layers.proxy
