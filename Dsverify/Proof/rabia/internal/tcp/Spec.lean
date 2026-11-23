/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/Spec.lean`, run `rabia-r1wake-1`.)

`rabia/internal/tcp`'s specs used by other packages (interface, stage 1b).

* **Client endpoint** (`ClientTCP`, the kit's `New` and `Op`): `ClientTcpInit` makes the endpoint
  of client `c` with its two channels set up (`clientChans`: the send channel an SPSC of `c`'s
  requests in order, `clSendP`; the receive channel a bag of replies to `c`, `repP`) and the rest
  of the endpoint (`clientOwn`, this package's); `Connect` dials in the background (to proxy `c mod n`), from the
  client's right to establish its connection (`estabTok`: `connect` sets `estab` once its
  handshake write succeeds, before its send routine starts); it does not block.
* **Proxy endpoint** (`ProxyTCP`, the proxy layer): `ProxyTcpInit` listens on the proxy's address
  (its token) and keeps the client channel (`ClientsToProxy`, `c2pP`) and the request receipts
  (`pRcpt`); `Connect` accepts in the background (N7: a client's newer connection replaces its
  entry; each accepted connection gets its own routines); `ClientSendChan(c)` is client `c`'s
  reply channel (`repP`) or `nil`; `NumConns` a number. `proxyTcpRO` (persistent) is the client
  table's lock and the endpoint's read-only fields. The receipts of client `c`'s requests go to the
  receive routine of `c`'s established connection, the only connection that carries requests
  (`proxyP`), read by one routine (each connection is accepted once).
* **Network endpoint** (`NetTCP`, the network layer): `NetTCPInit` listens on the network
  address and makes `RecvChan` (`recvP`, ordered, `n` producers: the receive routine of the
  connection from each server; the consumer's token goes to the router); `Connect` (from the push
  logs' and receipts' authorities) dials every server and accepts from each (N7: a peer's newer
  connection replaces its entry, counted once), then starts one receive routine per peer (so the
  receipts of `B_X` are minted by one routine) and the send routines, and returns the send
  channels (`sendP`, ordered, 2 producers: the serializer's broadcasts and the router's replies;
  the producers' tokens).
-/
module

public import Dsverify.Proof.rabia.Core.Chans
public import Dsverify.GeneratedProof.rabia.internal.tcp
public import Dsverify.Proof.rabia.internal.config.Spec
public import Dsverify.Proof.rabia.Core.PkgState
public import Dsverify.Proof.rabia.internal.tcp.Defs
public import Dsverify.Proof.rabia.internal.tcp.Base

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia

/-- The client endpoint's channels' ghost names. -/
structure ClNames where
  send : SpscNames
  recv : ChanNames

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

/-- The open listener `li` (id `l`) at `a`, owned (`net.Listen`'s result). -/
def ownListener (li : GoInterface) (l : w64) (a : GoString) : IProp GF :=
  iprop(net.isListener li l ∗ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
    netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a)

/-- Client `c`'s endpoint `t`: its channel fields (read-only) with their idioms (persistent). -/
def clientChans (γ : Names) (c : Nat) (γc : ClNames) (t : Loc) : IProp GF :=
  iprop(∃ sc rc : GoChan, structFieldRef ClientTCP go!"SendChan" t ↦□ sc ∗
    structFieldRef ClientTCP go!"RecvChan" t ↦□ rc ∗
    isSpsc γc.send sc (clSendP γ c) (fun _ => iprop(False)) ∗ isChanBag γc.recv rc (repP γ c))

/-- The rest of client `c`'s endpoint `t` for proxy address `addr`, before `Connect`: its other
fields and the send channel's consumer token. -/
def clientOwn (γ : Names) (c : Nat) (γc : ClNames) (t : Loc) (addr : GoString) : IProp GF :=
  iprop(∃ (wg : Loc) (done : GoChan) (cn rd wr : Loc),
    structFieldRef ClientTCP go!"Id" t ↦□ (BitVec.ofNat 32 c : w32) ∗
    structFieldRef ClientTCP go!"Wg" t ↦□ wg ∗ wgCtr wg 2 ∗
    structFieldRef ClientTCP go!"Done" t ↦□ done ∗ doneChan done ∗
    structFieldRef ClientTCP go!"ProxyAddr" t ↦□ addr ∗
    structFieldRef ClientTCP go!"Conn" t ↦ cn ∗ structFieldRef ClientTCP go!"Reader" t ↦ rd ∗
    structFieldRef ClientTCP go!"Writer" t ↦ wr ∗ spscConsumer γc.send ([] : List Command) ∗
    clientChans γ c γc t)

/-- Proxy `k`'s endpoint `p`, read-only parts (persistent): the client table's lock and its
invariant (each connected client's reply channel, `repP`). -/
def proxyTcpRO (γ : Names) (k : Nat) (p : Loc) : IProp GF :=
  iprop(∃ (scs cns rds wrs : GoSlice), structFieldRef ProxyTCP go!"SendChan" p ↦□ scs ∗
    structFieldRef ProxyTCP go!"Conns" p ↦□ cns ∗ structFieldRef ProxyTCP go!"Readers" p ↦□ rds ∗
    structFieldRef ProxyTCP go!"Writers" p ↦□ wrs ∗
    sync.isMutex (structFieldRef ProxyTCP go!"ConnsLock" p) (tableInv γ scs cns rds wrs))

/-- The rest of proxy `k`'s endpoint `p` before `Connect`: its listener, the client channel and
the request receipts. -/
def proxyTcpOwn (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (p : Loc) : IProp GF :=
  iprop(∃ (li : GoInterface) (l : w64) (toProxy done : GoChan) (wg : Loc), ⌜k < cf.n⌝ ∗
    structFieldRef ProxyTCP go!"Listener" p ↦□ li ∗ ownListener li l (proxyAddr k) ∗
    structFieldRef ProxyTCP go!"RecvChan" p ↦□ toProxy ∗ isChanBag γl.c2p toProxy (c2pP γ cf k γl) ∗
    structFieldRef ProxyTCP go!"Done" p ↦□ done ∗ doneChan done ∗
    structFieldRef ProxyTCP go!"Wg" p ↦□ wg ∗ wgCtr wg (2 * nC) ∗
    [∗list] c ∈ List.range nC, [∗list] n ∈ List.range opBudget, pRcpt γl c n)

/-- Server `k`'s network endpoint `t`'s receive channel `RecvChan` (persistent). -/
def netTcpRecv (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γr : OrdNames) (t : Loc) :
    IProp GF :=
  iprop(∃ rc : GoChan, structFieldRef NetTCP go!"RecvChan" t ↦□ rc ∗
    isOrdChan (V := Msg) γr rc cf.n (recvP γ cf k γl))

/-- Server `k`'s network endpoint `t`'s send channels `SendChan[j]`, `j < n`, with ghost names
`γs` (persistent). -/
def netTcpSend (γ : Names) (cf : RCfg) (k : Nat) (γs : List OrdNames) (t : Loc) : IProp GF :=
  iprop(∃ (ssl : GoSlice) (chs : List GoChan), structFieldRef NetTCP go!"SendChan" t ↦□ ssl ∗
    ssl ↦*□ chs ∗ ⌜chs.length = cf.n ∧ γs.length = cf.n⌝ ∗
    [∗list] j ↦ ch ∈ chs, ∃ γo, ⌜γs[j]? = some γo⌝ ∗
      isOrdChan (V := GoSlice) γo ch 2 (sendP γ cf k j))

/-- The rest of server `k`'s network endpoint `t` before `Connect` (its listener, the receive
channel's producers' tokens `γr`). -/
def netTcpOwn (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γr : OrdNames) (t : Loc) :
    IProp GF :=
  iprop(∃ (li : GoInterface) (l : w64) (done : GoChan) (wg : Loc) (scs rcs sns rds wrs : GoSlice)
      (chs : List GoChan) (ss rs ws : List Loc), ⌜k < cf.n⌝ ∗
    structFieldRef NetTCP go!"Id" t ↦□ (BitVec.ofNat 32 k : w32) ∗
    structFieldRef NetTCP go!"Listener" t ↦□ li ∗
    ownListener li l (netAddr k) ∗
    structFieldRef NetTCP go!"Done" t ↦□ done ∗ doneChan done ∗
    structFieldRef NetTCP go!"Wg" t ↦□ wg ∗ wgCtr wg (2 * cf.n) ∗
    structFieldRef NetTCP go!"SendChan" t ↦□ scs ∗ scs ↦* chs ∗
    structFieldRef NetTCP go!"RecvConn" t ↦□ rcs ∗ rcs ↦* List.replicate cf.n null ∗
    structFieldRef NetTCP go!"SendConn" t ↦□ sns ∗ sns ↦* ss ∗
    structFieldRef NetTCP go!"Readers" t ↦□ rds ∗ rds ↦* rs ∗
    structFieldRef NetTCP go!"Writers" t ↦□ wrs ∗ wrs ↦* ws ∗
    ⌜chs.length = cf.n ∧ ss.length = cf.n ∧ rs.length = cf.n ∧ ws.length = cf.n⌝ ∗
    [∗list] i ∈ List.range cf.n, ordProd γr i 0)

instance proxyTcpRO_persistent (γ : Names) (k : Nat) (p : Loc) :
    Persistent (proxyTcpRO (GF := GF) γ k p) := by unfold proxyTcpRO; infer_instance
instance clientChans_persistent (γ : Names) (c : Nat) (γc : ClNames) (t : Loc) :
    Persistent (clientChans (GF := GF) γ c γc t) := by unfold clientChans; infer_instance
instance netTcpRecv_persistent (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γr : OrdNames)
    (t : Loc) : Persistent (netTcpRecv (GF := GF) γ cf k γl γr t) := by
  unfold netTcpRecv; infer_instance
instance netTcpSend_persistent (γ : Names) (cf : RCfg) (k : Nat) (γs : List OrdNames) (t : Loc) :
    Persistent (netTcpSend (GF := GF) γ cf k γs t) := by unfold netTcpSend; infer_instance

end defs

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.internal.tcp.Assumptions]

/-- `ClientTcpInit(c, addr)`: client `c`'s endpoint, its channels set up (no request sent yet). -/
abbrev ClientTcpInit.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (c : w32) (addr : GoString), c.toNat < nC →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ confRO cf }}
    (App (App (Val (@! ClientTcpInit)) (Val #c)) (Val #addr))
  {{ (t : Loc), RET #t; ∃ γc : ClNames, clientChans γ c.toNat γc t ∗
      spscProducer γc.send ([] : List Command) ∗ clientOwn γ c.toNat γc t addr }}

/-- `t.Connect()` of client `c`'s endpoint at its proxy (server `c mod n`'s): it dials in the
background, from the client's right to establish its connection there. -/
abbrev ClientTCP.Connect.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (c : Nat) (γc : ClNames) (t : Loc), c < nC →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗ clientOwn γ c γc t (proxyAddr (c % cf.n)) ∗
      estabTok γ c (c % cf.n) }}
    (App (Val (t @!! go.GoType.PointerType ClientTCP.ty @!! go!"Connect")) (Val #()))
  {{ RET #(); True }}

/-- `ProxyTcpInit(k, addr, toProxy)` of proxy `k`: it listens on its address (retrying until it
succeeds); the client channel is `ClientsToProxy`; the receipts of its clients' requests. -/
abbrev ProxyTcpInit.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (id : w32) (toProxy : GoChan),
    id.toNat = k → k < cf.n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ confRO cf ∗
      shared γ ∗ isChanBag γl.c2p toProxy (c2pP γ cf k γl) ∗
      [∗list] c ∈ List.range nC, [∗list] n ∈ List.range opBudget, pRcpt γl c n }}
    (App (App (App (Val (@! ProxyTcpInit)) (Val #id)) (Val #(proxyAddr k))) (Val #toProxy))
  {{ (p : Loc), RET #p; proxyTcpRO γ k p ∗ proxyTcpOwn γ cf k γl p }}

/-- `p.Connect()`: accepts the clients' connections in the background. -/
abbrev ProxyTCP.Connect.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗ proxyTcpRO γ k p ∗ proxyTcpOwn γ cf k γl p }}
    (App (Val (p @!! go.GoType.PointerType ProxyTCP.ty @!! go!"Connect")) (Val #()))
  {{ RET #(); True }}

/-- `p.ClientSendChan(c)`: client `c`'s reply channel, or `nil` (not connected here). -/
abbrev ProxyTCP.ClientSendChan.spec : Prop :=
  ∀ (γ : Names) (k : Nat) (p : Loc) (cid : w32), cid.toNat < nC →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ proxyTcpRO γ k p }}
    (App (Val (p @!! go.GoType.PointerType ProxyTCP.ty @!! go!"ClientSendChan")) (Val #cid))
  {{ (ch : GoChan), RET #ch;
      ⌜ch = chan.nil⌝ ∨ ∃ γch : ChanNames, isChanBag γch ch (repP γ cid.toNat) }}

/-- `p.NumConns()`: some number. -/
abbrev ProxyTCP.NumConns.spec : Prop :=
  ∀ (γ : Names) (k : Nat) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ proxyTcpRO γ k p }}
    (App (Val (p @!! go.GoType.PointerType ProxyTCP.ty @!! go!"NumConns")) (Val #()))
  {{ (n : w64), RET #n; True }}

/-- `NetTCPInit(k, addr)` of server `k`: it listens on its network address (retrying until it
succeeds); its receive channel, the consumer's token. -/
abbrev NetTCPInit.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (id : w32), id.toNat = k → k < cf.n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ confRO cf ∗ shared γ }}
    (App (App (Val (@! NetTCPInit)) (Val #id)) (Val #(netAddr k)))
  {{ (t : Loc), RET #t; ∃ γr : OrdNames, netTcpRecv γ cf k γl γr t ∗
      ordCons γr (List.replicate cf.n 0) ∗ netTcpOwn γ cf k γl γr t }}

/-- `t.Connect()` of server `k`'s network endpoint: it returns once connected to every server
(itself included) and accepting from every server; the send channels and their producers' tokens
(producer 0 the serializer's, 1 the router's). -/
abbrev NetTCP.Connect.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γr : OrdNames) (t : Loc), k < cf.n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗ netTcpRecv γ cf k γl γr t ∗ netTcpOwn γ cf k γl γr t ∗
      [∗list] X ∈ List.range cf.n, pushAuth γl X [] ∗ rcptAuth γl X ∅ }}
    (App (Val (t @!! go.GoType.PointerType NetTCP.ty @!! go!"Connect")) (Val #()))
  {{ RET #(); ∃ γs : List OrdNames, netTcpSend γ cf k γs t ∗
      [∗list] γo ∈ γs, ordProd γo 0 0 ∗ ordProd γo 1 0 }}

end spec

end Perennial.rabia.internal.tcp
