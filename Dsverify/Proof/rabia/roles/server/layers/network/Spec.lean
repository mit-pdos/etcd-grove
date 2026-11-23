/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/network/Spec.lean`, run `rabia-r1wake-1`.)

`rabia/roles/server/layers/network`'s specs (interface, stage 1b).

The network layer of server `k`: `NetworkInit` (its endpoint `NetTCPInit` and its `ToSerializer`
channel), `Prologue` (the endpoint's `Connect`), and its two routines, which never return (`Done`
is never closed): `MsgRouter` (the proxy's client requests and the executor's messages to the
serializer, the handler's replies to their servers' send channels, the received messages to the
handler or, replies, to the executor) and `MsgSerializer` (each message appended to `B_k`, its
encoding sent to every server's send channel).

What it takes (`networkBootRes`, from `ServerInit`): the router's consumer and producer tokens of
its SPSC channels, the handler's log it keeps (`hlog`), half of `B_k`'s authority (the
serializer's), the receive routines' push logs and receipts (for the endpoint). Its built states
(`networkInitOk`, then `networkRouterRes`, `networkSerRes`) are this package's, as are its own
channel `ToSerializer` and its log (`toSerP`, `serLb`; allocated by `NetworkInit`).
-/
module

public import Dsverify.Proof.rabia.internal.tcp.Spec
public import Dsverify.GeneratedProof.rabia.roles.server.layers.network
public import Dsverify.Proof.rabia.Core.PkgState
public import Dsverify.Proof.rabia.roles.server.layers.network.Base

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.network

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

/-- `l` is a prefix of the router's forwards to the serializer, log `γs` (persistent; `true`:
`E_k`'s next, `false`: a client request). -/
def serLb (γs : GName) (l : List Bool) : IProp GF := monoListLbOwn γs l
def serAuth (γs : GName) (l : List Bool) : IProp GF := monoListAuthOwn γs 1 l

/-- `ToSerializer` (router → serializer, SPSC): the `i`-th forward (log `γs`) is the next of `E_k`
(in order: the log counts them) or a client request with its permit. -/
def toSerP (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γs : GName) (i : Int) (v : Msg) : IProp GF :=
  iprop(∃ (m : MsgV) (bl : List Bool), msgRep v m ∗ bmsgOk γ cf k m ∗ serLb γs bl ∗
    ⌜bl.length = i.toNat + 1⌝ ∗
    (if bl[i.toNat]? = some true then
      iprop(∃ l : List MsgV, exLb γl l ∗
        ⌜l[((bl.take i.toNat).filter id).length]? = some m ∧ ExLogOk l⌝)
    else iprop(∃ o : ObjV, ⌜m.ty = tyClientRequest ∧ m.obj = some o⌝ ∗ crTok γl o.proSeq.toNat)))

/-- What server `k`'s network layer needs at its start (`ServerInit` gives it). -/
def networkBootRes (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) : IProp GF :=
  iprop(spscConsumer γl.e2n ([] : List Msg) ∗ spscProducer γl.n2h ([] : List Msg) ∗
    hAuth γl [] ∗ monoListAuthOwn (γ.net.bcast k) (1 : Qp).half ([] : List MsgV) ∗
    [∗list] X ∈ List.range cf.n, pushAuth γl X [] ∗ rcptAuth γl X ∅)

/-- The fields of the network layer's struct `nv` that the routines read (server `k`'s channels). -/
def netFieldsOk (cf : RCfg) (k : Nat) (ch : SrvChans) (nv : Network) : Prop :=
  k < cf.n ∧ nv.Done' = ch.done ∧ nv.ProxyIn' = ch.p2n ∧ nv.MsgHandlerIn' = ch.h2n ∧
    nv.ConExecutorIn' = ch.e2n ∧ nv.ToMsgHandler' = ch.n2h ∧ nv.ToConExecutor' = ch.n2e

/-- The router's loop state: the pushes received from each server (`P`, with their push logs'
lower bounds; the receive channel's consumer counts are their lengths), the executor's messages
received (`E`), the forwards to the serializer (`T`, log `bl`: `true` for the executor's), the
forwards to the handler (`H`, log `hl`: every broadcast received from `X` was forwarded), the
send channels' producer-1 tokens. -/
def routerLoop (cf : RCfg) (γl : SrvNames) (γr : OrdNames) (γts : SpscNames) (γsl : GName)
    (γs : List OrdNames) : IProp GF :=
  iprop(∃ (P : List (List MsgV)) (E T H : List Msg) (bl : List Bool) (hl : List (Nat × Nat)),
    ordCons γr (P.map List.length) ∗ ⌜P.length = cf.n⌝ ∗
    □ (∀ (X : Nat) (px : List MsgV), ⌜P[X]? = some px⌝ -∗ pushLb γl X px) ∗
    spscConsumer γl.e2n E ∗ spscProducer γts T ∗ serAuth γsl bl ∗
    ⌜bl.length = T.length ∧ (bl.filter id).length = E.length⌝ ∗
    spscProducer γl.n2h H ∗ hAuth γl hl ∗
    ⌜hl.length = H.length ∧
      ∀ (X : Nat) (px : List MsgV), P[X]? = some px → ∀ j < (bcastPart px).length, (X, j) ∈ hl⌝ ∗
    [∗list] γo ∈ γs, ∃ c, ordProd γo 1 c)

/-- The serializer's loop state: the forwards received (`R`, log `bl`), the executor's messages
among them (`Ex`, a prefix of `E_k`), `B_k` (half its authority): its client requests with their
permits, its other messages `Ex`; the send channels' producer-0 tokens (`B_k`'s length each). -/
def serLoop (γ : Names) (k : Nat) (γl : SrvNames) (γts : SpscNames) (γsl : GName)
    (γs : List OrdNames) : IProp GF :=
  iprop(∃ (R : List Msg) (bl : List Bool) (Ex B : List MsgV),
    spscConsumer γts R ∗ serLb γsl bl ∗
    ⌜bl.length = R.length ∧ (bl.filter id).length = Ex.length⌝ ∗
    exLb γl Ex ∗ ⌜ExLogOk Ex⌝ ∗
    monoListAuthOwn (γ.net.bcast k) (1 : Qp).half B ∗
    ⌜RoundsOrdered B ∧ B.filter (fun m => decide (m.ty ≠ tyClientRequest)) = Ex⌝ ∗
    ([∗list] m ∈ B.filter (fun m => decide (m.ty = tyClientRequest)),
      ∃ o : ObjV, ⌜m.obj = some o⌝ ∗ crTok γl o.proSeq.toNat) ∗
    [∗list] γo ∈ γs, ordProd γo 0 B.length)

/-- The network layer `n` after `NetworkInit`. -/
def networkInitOk (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (ch : SrvChans) (n : Loc) : IProp GF :=
  iprop(∃ (nv : Network) (γr : OrdNames) (γts : SpscNames) (γsl : GName),
    ⌜netFieldsOk cf k ch nv⌝ ∗ n ↦ nv ∗ srvChans γ cf k γl ch ∗
    rabia.internal.tcp.netTcpRecv γ cf k γl γr nv.TCP' ∗ ordCons γr (List.replicate cf.n 0) ∗ rabia.internal.tcp.netTcpOwn γ cf k γl γr nv.TCP' ∗
    networkBootRes γ cf k γl ∗
    isSpsc γts nv.ToSerializer' (toSerP γ cf k γl γsl) (fun _ => iprop(False)) ∗
    spscProducer γts ([] : List Msg) ∗ spscConsumer γts ([] : List Msg) ∗ serAuth γsl [] ∗
    serLb γsl [])

/-- The router's resources after `Prologue`. -/
def networkRouterRes (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (ch : SrvChans) (n : Loc) : IProp GF :=
  iprop(∃ (nv : Network) (γr : OrdNames) (γts : SpscNames) (γsl : GName) (γs : List OrdNames),
    ⌜netFieldsOk cf k ch nv⌝ ∗ n ↦□ nv ∗ srvChans γ cf k γl ch ∗
    rabia.internal.tcp.netTcpRecv γ cf k γl γr nv.TCP' ∗ rabia.internal.tcp.netTcpSend γ cf k γs nv.TCP' ∗
    isSpsc γts nv.ToSerializer' (toSerP γ cf k γl γsl) (fun _ => iprop(False)) ∗
    routerLoop cf γl γr γts γsl γs)

/-- The serializer's resources after `Prologue`. -/
def networkSerRes (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (n : Loc) : IProp GF :=
  iprop(∃ (nv : Network) (γts : SpscNames) (γsl : GName) (γs : List OrdNames),
    ⌜k < cf.n⌝ ∗ n ↦□ nv ∗ rabia.internal.tcp.netTcpSend γ cf k γs nv.TCP' ∗
    isSpsc γts nv.ToSerializer' (toSerP γ cf k γl γsl) (fun _ => iprop(False)) ∗
    serLoop γ k γl γts γsl γs)

end defs

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.layers.network.Assumptions]

/-- `NetworkInit(k, done, wg, netAddr k, NetToProxy, ProxyToNet, MsgHandlerToNet,
ConExecutorToNet, NetToMsgHandler, NetToConExecutor)`. -/
abbrev NetworkInit.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (ch : SrvChans) (id : w32) (wg : Loc),
  id.toNat = k → k < cf.n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.network ∗ confRO cf ∗
      srvChans γ cf k γl ch ∗ shared γ ∗ networkBootRes γ cf k γl }}
    (App (App (App (App (App (App (App (App (App (App (Val (@! NetworkInit)) (Val #id))
      (Val #ch.done)) (Val #wg)) (Val #(netAddr k))) (Val #ch.n2p)) (Val #ch.p2n)) (Val #ch.h2n))
      (Val #ch.e2n)) (Val #ch.n2h)) (Val #ch.n2e))
  {{ (n : Loc), RET #n; networkInitOk γ cf k γl ch n }}

/-- `n.Prologue()`: connected to every server; the routines' resources. -/
abbrev Network.Prologue.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (ch : SrvChans) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.network ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗
      networkInitOk γ cf k γl ch n }}
    (App (Val (n @!! go.GoType.PointerType Network.ty @!! go!"Prologue")) (Val #()))
  {{ RET #(); networkRouterRes γ cf k γl ch n ∗ networkSerRes γ cf k γl n }}

/-- `n.MsgRouter()`: never returns. -/
abbrev Network.MsgRouter.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (ch : SrvChans) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.network ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗
      networkRouterRes γ cf k γl ch n }}
    (App (Val (n @!! go.GoType.PointerType Network.ty @!! go!"MsgRouter")) (Val #()))
  {{ RET #(); False }}

/-- `n.MsgSerializer()`: never returns. -/
abbrev Network.MsgSerializer.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.network ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗
      networkSerRes γ cf k γl n }}
    (App (Val (n @!! go.GoType.PointerType Network.ty @!! go!"MsgSerializer")) (Val #()))
  {{ RET #(); False }}

end spec

end Perennial.rabia.roles.server.layers.network
