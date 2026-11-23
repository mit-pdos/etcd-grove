/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/Rabia/Chans.lean`, run `rabia-r1wake-1`.)

Server `k`'s channels and local ghost state shared by its layers (interface, stage 1b): the
element predicate of every channel between two packages (`notes/stage1b-design.md`, the channels'
table), the record of its local ghost names (`SrvNames`, allocated by `ServerInit`), and the
persistent predicates the layers share (`srvChans`: every such channel with its idiom; `ledgerRO`:
the ledger's slots; `isSrvKeys`: the split of server `k`'s written keys between its proxy and its
consensus layer). A layer's own channels and ghost state are its package's (the network's
`ToSerializer` and its log: network's `Spec.lean`; the slots' queues, their logs, the frozen
rounds: consensus's `Spec.lean`).

The per-sender order and the receipts (the design's "Why the order", "Why the receipts"):
* `rcpt X j` (exclusive): the receipt of `B_X[j]`, minted by the receive routine of server `X`'s
  connection, of which there is one: the network endpoint starts its receive routines after
  `accepting`, one per peer (the table's entry for `X` once `accepting` is done, N7: some
  connection on which `X`'s handshake arrived whole; any stream from `X` carries a prefix of `B_X`,
  `netP`, so each broadcast is pushed at most once, whichever connection it is);
* `push X` (mono-list): the messages that receive routine pushed on `RecvChan`, in order; their
  broadcasts are a prefix of `B_X`;
* `hlog` (mono-list of `(X, j)`): what the router forwarded to the handler, in order;
* `exlog` (mono-list): the executor's messages `E_k`, in order (`ExLogOk`);
* `crp q` (exclusive): the permit of the proxy's object `q` (its client request goes once into
  `B_k`);
* `prc (c, n)` (exclusive): the proxy's receipt of client `c`'s request `n` (each request is put
  in one object: `newObj`'s `robj r ∉ K`; and a proxy makes fewer than `2^32` objects); minted by
  the receive routine of the client's established connection (`proxyP`: requests travel only
  there; one receive routine per accepted connection);
* `kp`, `ke`: the proxy's and the consensus layer's halves of their parts of server `k`'s keys.
-/
module

public import Dsverify.Proof.rabia.Core.Proto
public import Dsverify.Proof.rabia.internal.ledger.Spec
public import Dsverify.Proof.rabia.Lib.OrdChan
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Spsc

@[expose] public section

noncomputable section

namespace Perennial.rabia

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.ledger

/-! ## Names -/

/-- A ledger slot: its location, its ghost name (`slotSt`), its queue. -/
structure SlotV where
  loc : Loc
  γ : GName
  q : GoChan

/-- The server's channels (the `Server` struct's fields). -/
structure SrvChans where
  done : GoChan
  c2p : GoChan
  p2n : GoChan
  n2p : GoChan
  h2n : GoChan
  e2n : GoChan
  n2h : GoChan
  n2e : GoChan

/-- Server `k`'s local ghost names (`ServerInit` allocates them). -/
structure SrvNames where
  /-- `Done` (bag, nothing is sent) -/
  done : ChanNames
  /-- `ClientsToProxy` (bag) -/
  c2p : ChanNames
  /-- `ProxyToNet` (bag) -/
  p2n : ChanNames
  /-- `NetToProxy` (bag, nothing is sent) -/
  n2p : ChanNames
  /-- `MsgHandlerToNet` (bag) -/
  h2n : ChanNames
  /-- `ConExecutorToNet` (SPSC) -/
  e2n : SpscNames
  /-- `NetToMsgHandler` (SPSC) -/
  n2h : SpscNames
  /-- `NetToConExecutor` (bag) -/
  n2e : ChanNames
  /-- per sender `X`: the receipts of `B_X`'s elements (ghost map `Nat ↦ ()`) -/
  rcpt : Nat → GName
  /-- per sender `X`: its receive routine's pushes (mono-list of `MsgV`) -/
  push : Nat → GName
  /-- the router's forwards to the handler (mono-list of `Nat × Nat`) -/
  hlog : GName
  /-- the executor's messages `E_k` (mono-list of `MsgV`) -/
  exlog : GName
  /-- the client requests' permits (ghost map `Nat ↦ ()`) -/
  crp : GName
  /-- the proxy's receipts of requests (ghost map `Nat × Nat ↦ ()`) -/
  prc : GName
  /-- the proxy's part of server `k`'s keys (ghost variable, halves) -/
  kp : GName
  /-- the consensus layer's part of server `k`'s keys (ghost variable, halves) -/
  ke : GName
  /-- the ledger's slots -/
  slots : List SlotV

/-- The ledger's length (`Conf.LenLedger`). -/
def lenLedger : Nat := 10000

/-- The keys of a proxy's objects (`pobj`, `robj`): the proxy's part of its server's keys. -/
def model.FKey.isObj : FKey → Bool
  | .pobj _ => true
  | .robj _ _ => true
  | _ => false

/-- A side's part of server `k`'s keys: `true` the proxy's (object keys), `false` the consensus
layer's. -/
def SrvNames.keysName (γl : SrvNames) (side : Bool) : GName := if side then γl.kp else γl.ke

def srvKeysN (k : Nat) : Namespace := ndot (ndot rabiaR "keys") (toString k)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-! ## Local ghost state -/

/-- The receipt of `B_X[j]` (exclusive). -/
def rcpt (γl : SrvNames) (X j : Nat) : IProp GF := ghostMapElem (γl.rcpt X) j (.own 1) ()
/-- The receipts of `B_X` minted so far (the receive routine of the connection from `X`). -/
def rcptAuth (γl : SrvNames) (X : Nat) (J : GMap Nat Unit) : IProp GF :=
  ghostMapAuth (γl.rcpt X) 1 J

/-- `l` is a prefix of what the receive routine of `X`'s connection pushed (persistent). -/
def pushLb (γl : SrvNames) (X : Nat) (l : List MsgV) : IProp GF := monoListLbOwn (γl.push X) l
def pushAuth (γl : SrvNames) (X : Nat) (l : List MsgV) : IProp GF :=
  monoListAuthOwn (γl.push X) 1 l

/-- `l` is a prefix of the router's forwards to the handler (persistent). -/
def hLb (γl : SrvNames) (l : List (Nat × Nat)) : IProp GF := monoListLbOwn γl.hlog l
def hAuth (γl : SrvNames) (l : List (Nat × Nat)) : IProp GF := monoListAuthOwn γl.hlog 1 l

/-- `l` is a prefix of the executor's messages `E_k` (persistent). -/
def exLb (γl : SrvNames) (l : List MsgV) : IProp GF := monoListLbOwn γl.exlog l
def exAuth (γl : SrvNames) (l : List MsgV) : IProp GF := monoListAuthOwn γl.exlog 1 l

/-- The permit of the proxy's object `q` (exclusive). -/
def crTok (γl : SrvNames) (q : Nat) : IProp GF := ghostMapElem γl.crp q (.own 1) ()
/-- The permits minted so far (the proxy's command receiver). -/
def crAuth (γl : SrvNames) (Q : GMap Nat Unit) : IProp GF := ghostMapAuth γl.crp 1 Q

/-- The proxy's receipt of client `c`'s request `n` (exclusive). -/
def pRcpt (γl : SrvNames) (c n : Nat) : IProp GF := ghostMapElem γl.prc (c, n) (.own 1) ()

/-- A side's part of server `k`'s keys (its writer's half; `side`: `true` the proxy). -/
def keysPart (γl : SrvNames) (side : Bool) (K : List FKey) : IProp GF :=
  ghostVar (γl.keysName side) (1 : Qp).half K

/-- Server `k`'s keys, split: the proxy's part (objects' keys) and the consensus layer's (the
others), each half with its writer (namespace `srvKeysN k`). -/
def srvKeysInv (γ : Names) (k : Nat) (γl : SrvNames) : IProp GF :=
  iprop(∃ (K Kp Ke : List FKey), keysOf γ.rab (.srv k) K ∗ ⌜K.Perm (Kp ++ Ke)⌝ ∗
    ghostVar γl.kp (1 : Qp).half Kp ∗ ghostVar γl.ke (1 : Qp).half Ke ∗
    ⌜(∀ key ∈ Kp, key.isObj = true) ∧ ∀ key ∈ Ke, key.isObj = false⌝)

/-! ## The channels' element predicates -/

/-- `Done`: nothing is sent (nobody closes it either). -/
def doneP : Unit → IProp GF := fun _ => iprop(False)

/-- `ClientsToProxy` (the proxy's receive routines → `CmdReceiver`): a request of a client of
proxy `k` (`c % n = k`, `proxyP`), within the budget, with its receipt. -/
def c2pP (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (v : Command) : IProp GF :=
  iprop(∃ (c : Nat) (q : CmdV), ⌜c < nC ∧ c % cf.n = k ∧ q.cliSeq.toNat < opBudget ∧
      (encCmd q).length ≤ cmdBound⌝ ∗
    cmdRep v q ∗ reqOk γ c q ∗ pRcpt γl c q.cliSeq.toNat)

/-- `ProxyToNet` (`CmdReceiver` → router): proxy `k`'s client request message, with its object's
permit. -/
def p2nP (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (v : Msg) : IProp GF :=
  iprop(∃ (m : MsgV) (o : ObjV), ⌜m.ty = tyClientRequest ∧ m.obj = some o⌝ ∗ msgRep v m ∗
    bmsgOk γ cf k m ∗ crTok γl o.proSeq.toNat)

/-- `NetToProxy`: nothing is sent. -/
def n2pP : Msg → IProp GF := fun _ => iprop(False)

/-- `ConExecutorToNet` (executor → router, SPSC): the `i`-th is `E_k[i]`, with its facts. -/
def e2nP (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (i : Int) (v : Msg) : IProp GF :=
  iprop(∃ (m : MsgV) (l : List MsgV), msgRep v m ∗ bmsgOk γ cf k m ∗ exLb γl l ∗
    ⌜l[i.toNat]? = some m ∧ ExLogOk l⌝)

/-- `MsgHandlerToNet` (handler → router): a `ProposalReply` to a server (`Phase`). -/
def h2nP (γ : Names) (cf : RCfg) (v : Msg) : IProp GF :=
  iprop(∃ (m : MsgV) (j : Nat), ⌜j < cf.n⌝ ∗ msgRep v m ∗ replyOk γ cf j m)

/-- `NetTCP.SendChan[j]` (ordered, 2 producers → `SendHandler(j)`): the serializer's (producer 0)
`n`-th is `B_k[n]`'s encoding; the router's (producer 1) a `ProposalReply` to `j`'s encoding. -/
def sendP (γ : Names) (cf : RCfg) (k j : Nat) : Nat → Nat → GoSlice → IProp GF := fun p n v =>
  if p = 0 then
    iprop(∃ (l : List MsgV) (m : MsgV), bcastLb γ k l ∗ ⌜l[n]? = some m⌝ ∗ v ↦*□ encMsg m)
  else
    iprop(∃ m : MsgV, v ↦*□ encMsg m ∗ replyOk γ cf j m)

/-- `NetTCP.RecvChan` (ordered, `n` producers `RecvHandler(X)` → router): `X`'s `n`-th push is its
push log's `n`-th, whose broadcasts are a prefix of `B_X`; a broadcast comes with its facts and
its receipt (its index in `B_X`), a `ProposalReply` is one to `k`. -/
def recvP (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) : Nat → Nat → Msg → IProp GF :=
  fun X n v =>
  iprop(∃ (m : MsgV) (l : List MsgV), msgRep v m ∗ pushLb γl X l ∗
    ⌜l.length = n + 1 ∧ l[n]? = some m⌝ ∗ bcastLb γ X (bcastPart l) ∗
    (if m.ty = tyProposalReply then replyOk γ cf k m
     else iprop(bmsgOk γ cf X m ∗ rcpt γl X ((bcastPart l).length - 1))))

/-- `NetToMsgHandler` (router → handler, SPSC): the `i`-th is `B_X[j]` for a server `X`, with its
facts and receipt, and the router forwarded `X`'s broadcasts before `j` earlier (the handler's
per-sender order). -/
def n2hP (γ : Names) (cf : RCfg) (γl : SrvNames) (i : Int) (v : Msg) : IProp GF :=
  iprop(∃ (m : MsgV) (X j : Nat) (l : List MsgV) (hl : List (Nat × Nat)),
    ⌜X < cf.n ∧ l[j]? = some m ∧ hl.length = i.toNat + 1 ∧ hl[i.toNat]? = some (X, j) ∧
      ∀ j' < j, (X, j') ∈ hl.take i.toNat⌝ ∗
    msgRep v m ∗ bcastLb γ X l ∗ bmsgOk γ cf X m ∗ rcpt γl X j ∗ hLb γl hl)

/-- `NetToConExecutor` (router → executor): a `ProposalReply` to `k`. -/
def n2eP (γ : Names) (cf : RCfg) (k : Nat) (v : Msg) : IProp GF :=
  iprop(∃ m : MsgV, msgRep v m ∗ replyOk γ cf k m)

/-- The client endpoint's `SendChan` (`Op` → `SendHandler`, SPSC): the `i`-th is client `c`'s
request `i`, within the budget. -/
def clSendP (γ : Names) (c : Nat) (i : Int) (v : Command) : IProp GF :=
  iprop(∃ q : CmdV, ⌜q.cliSeq.toNat = i.toNat ∧ i.toNat < opBudget ∧ 0 ≤ i⌝ ∗ cmdRep v q ∗
    reqOk γ c q)

/-- The client endpoint's `RecvChan` (`RecvHandler` → `Op`) and the proxy's `SendChan[c]`
(`KVSExecutor` → `SendHandler(c)`): a reply to client `c`. -/
def repP (γ : Names) (c : Nat) (v : Command) : IProp GF :=
  iprop(∃ q : CmdV, cmdRep v q ∗ repOk γ c q)

/-! ## The persistent predicates the layers share -/

/-- Server `k`'s channels with their idioms, at configuration `cf` (persistent). -/
def srvChans (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (ch : SrvChans) : IProp GF :=
  iprop(isChanBag (V := Unit) γl.done ch.done doneP ∗
    isChanBag γl.c2p ch.c2p (c2pP γ cf k γl) ∗ isChanBag γl.p2n ch.p2n (p2nP γ cf k γl) ∗
    isChanBag γl.n2p ch.n2p n2pP ∗ isChanBag γl.h2n ch.h2n (h2nP γ cf) ∗
    isSpsc γl.e2n ch.e2n (e2nP γ cf k γl) (fun _ => iprop(False)) ∗
    isSpsc γl.n2h ch.n2h (n2hP γ cf γl) (fun _ => iprop(False)) ∗
    isChanBag γl.n2e ch.n2e (n2eP γ cf k))

/-- The ledger `ledger` holds the slots `γl.slots` (persistent): `LenLedger` of them, each with
its lock and queue. -/
def ledgerRO (γl : SrvNames) (ledger : GoSlice) : IProp GF :=
  iprop(ledger ↦*□ γl.slots.map (·.loc) ∗ ⌜γl.slots.length = lenLedger⌝ ∗
    [∗list] e ∈ γl.slots, isSlot e.loc e.γ e.q)

/-- The split of server `k`'s keys, allocated (persistent). -/
def isSrvKeys (γ : Names) (k : Nat) (γl : SrvNames) : IProp GF :=
  inv (srvKeysN k) (srvKeysInv γ k γl)

instance srvChans_persistent (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (ch : SrvChans) :
    Persistent (srvChans (GF := GF) γ cf k γl ch) := by unfold srvChans; infer_instance
instance ledgerRO_persistent (γl : SrvNames) (ledger : GoSlice) :
    Persistent (ledgerRO (GF := GF) γl ledger) := by unfold ledgerRO; infer_instance

end defs

/-! ## The laws of the keys' split (statements; proved in Prove) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- Allocation, from server `k`'s (empty) key set and the two parts' fresh ghost variables. -/
theorem srvKeys_alloc (γ : Names) (k : Nat) (γl : SrvNames) (E : CoPset) :
    keysOf (GF := GF) γ.rab (.srv k) [] ∗ ghostVar γl.kp 1 ([] : List FKey) ∗
      ghostVar γl.ke 1 ([] : List FKey) ⊢
      |={E}=> isSrvKeys γ k γl ∗ keysPart γl true [] ∗ keysPart γl false [] := by
  iintro ⟨Hk, Hp, He⟩
  icases ghostVar_split γl.kp ([] : List FKey) (1 : Qp).half (1 : Qp).half $$ [Hp] with ⟨Hp1, Hp2⟩
  · rw [Qp.half_add_half]; iexact Hp
  icases ghostVar_split γl.ke ([] : List FKey) (1 : Qp).half (1 : Qp).half $$ [He] with ⟨He1, He2⟩
  · rw [Qp.half_add_half]; iexact He
  imod inv_alloc (srvKeysN k) E (srvKeysInv γ k γl) $$ [Hk Hp1 He1] with #Hinv
  · inext
    unfold srvKeysInv
    iexists [], [], []
    iframe
    ipureintro
    exact ⟨List.Perm.refl _, by simp, by simp⟩
  imodintro
  unfold isSrvKeys keysPart SrvNames.keysName
  iframe Hinv
  simp only [↓reduceIte, Bool.false_eq_true]
  iframe

/-- A side's access (`side`: `true` the proxy, `false` the consensus layer): server `k`'s keys,
where the other side's part has only the other kind of keys; it puts back keys that extend its own
part with keys of its kind. -/
theorem srvKeys_acc (γ : Names) (k : Nat) (γl : SrvNames) (side : Bool) (E : CoPset)
    (hE : ↑(srvKeysN k) ⊆ E) (Ks : List FKey) :
    isSrvKeys (GF := GF) γ k γl ∗ keysPart γl side Ks ⊢
      |={E, E \ ↑(srvKeysN k)}=> ∃ K Ko, keysOf γ.rab (.srv k) K ∗
        ⌜K.Perm (Ks ++ Ko) ∧ ∀ key ∈ Ko, key.isObj = !side⌝ ∗
        ∀ K' Ks', keysOf γ.rab (.srv k) K' ∗
          ⌜K'.Perm (Ks' ++ Ko) ∧ ∀ key ∈ Ks', key.isObj = side⌝ ={E \ ↑(srvKeysN k), E}=∗
          keysPart γl side Ks' := by
  unfold isSrvKeys keysPart
  cases side <;> simp only [SrvNames.keysName, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    Bool.not_true]
  · iintro ⟨#Hinv, Hp⟩
    imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
    unfold srvKeysInv
    icases Hi with ⟨%K, %Kp, %Ke, >HK, >%hperm, >Hkp, >Hke, >%hkinds⟩
    ihave %heq := ghostVar_agree γl.ke Ks _ Ke _ $$ Hp Hke
    subst heq
    imodintro
    iexists K, Kp
    iframe HK
    isplitr
    · ipureintro; exact ⟨hperm.trans List.perm_append_comm, hkinds.1⟩
    iintro %K' %Ks' ⟨HK', %hK'⟩
    imod ghostVar_update_halves Ks' γl.ke Ks Ks $$ Hp Hke with ⟨Hp, Hke⟩
    imod Hclose $$ [HK' Hkp Hke] with -
    · inext
      iexists K', Kp, Ks'
      iframe
      ipureintro
      exact ⟨hK'.1.trans List.perm_append_comm, hkinds.1, hK'.2⟩
    imodintro
    iexact Hp
  · iintro ⟨#Hinv, Hp⟩
    imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
    unfold srvKeysInv
    icases Hi with ⟨%K, %Kp, %Ke, >HK, >%hperm, >Hkp, >Hke, >%hkinds⟩
    ihave %heq := ghostVar_agree γl.kp Ks _ Kp _ $$ Hp Hkp
    subst heq
    imodintro
    iexists K, Ke
    iframe HK
    isplitr
    · ipureintro; exact ⟨hperm, hkinds.2⟩
    iintro %K' %Ks' ⟨HK', %hK'⟩
    imod ghostVar_update_halves Ks' γl.kp Ks Ks $$ Hp Hkp with ⟨Hp, Hkp⟩
    imod Hclose $$ [HK' Hkp Hke] with -
    · inext
      iexists K', Ks', Ke
      iframe
      ipureintro
      exact ⟨hK'.1, hK'.2, hkinds.2⟩
    imodintro
    iexact Hp

end laws

end Perennial.rabia
