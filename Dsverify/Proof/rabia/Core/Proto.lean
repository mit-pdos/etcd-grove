/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/Rabia/Proto.lean`, run `rabia-r1wake-1`,
onto `GooseLang/Ext/Net/Proto.lean`'s vocabulary: connections are numbers, `addrTok` is
persistent; the kit's addresses are `127.0.0.1:76nn`; the namespaces are below `rabiaR`.)

The network's protocols and the nodes' shares (interface, stages 1 and 2).

* **Messages' facts** (persistent): `objOk` (a consensus object carries a batch of registered
  requests, in order, as proxy `ProId` made it), `bmsgOk γ X m` (a message of server `X`'s broadcast log: each type's
  fact, `Protocol.lean`'s keys), `replyOk` (a `ProposalReply` to server `k`), `reqOk` (a client's
  request), `repOk` (a proxy's reply: the request was decided at a slot and the result is its
  command's on the store of the slots before).
* **Broadcast logs**: server `X`'s serializer appends every message it broadcasts to `B_X` (a
  mono-list, `bcastInv`: each element `bmsgOk`, the rounds of a slot in order, each key once);
  a stream to a server carries a prefix of `B_X`, in order (`bcastLb`).
* **Established connections** (`estab`): client `c`'s connection to its proxy on which its
  handshake write succeeded (one-shot, set by the client's `connect` once: `estabTok`). A client
  writes requests only there (it redials only while its handshake write fails, and its send routine
  starts after), so `proxyP` carries requests only on the established connection: the proxy's
  receive routine of that connection (one per accepted connection) is the only one that reads
  them, whatever the acceptor's table holds (N7: a duplicate handshake replaces the old entry).
  A server's network layer needs no such fact: its receive routines start after `accepting`, one
  per peer (the table's last entry), and a peer writes messages only on its last connection.
* **Protocols** (`addrP`, `addrQ`): what the dialers and acceptors of each address of
  `protoAddrs` write (the configuration `cf` the orchestrator recorded, `cfgIs`, is taken
  existentially by the protocols, set at the start before it is chosen; `cfgP`/`cfgQ` the
  configuration exchange on port 9000).
* **Machines** (remote's deployment, `kit.go`): twelve machines on one host, addresses
  `127.0.0.1:76nn` (`kitAddr`); the orchestrator records and sends the configuration (`cfgP` on
  the server machines' and the client machines' configuration addresses, `protoAddrs`) and runs
  `remote.Check`; client machine `c` serves remote's calls at `cliAddr c` (protocols remote's); the
  shares `orchCore`, `cliCore c`, `serverShare k`.
-/
module

public import Dsverify.Proof.rabia.Core.Ghost
public import GooseLang.Ext.Net.Proto
public import Perennial.Ghost.MonoList

@[expose] public section

noncomputable section

namespace Perennial.rabia

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net

/-! ## Addresses -/

/-- The number of server machines (the configuration's `n` of them run a server). -/
def maxS : Nat := 5

/-- The two decimal digits of `n < 100`. -/
def digits2 (n : Nat) : GoString :=
  [BitVec.ofNat 8 (48 + n / 10), BitVec.ofNat 8 (48 + n % 10)]

/-- The kit's address with port `76nn` (`n < 100`): `127.0.0.1:76nn` (`kit.go`'s address lists;
all the machines on one host, remote's deployment, as dsv-paxos's `74xx`). -/
def kitAddr (n : Nat) : GoString := go!"127.0.0.1:76" ++ digits2 n

/-- Server `k`'s proxy address (`ProxyAddrs()[k]`), network address (`NetAddrs()[k]`) and
configuration address (`ServerConfAddrs()[k]`) (`k < maxS`). -/
def proxyAddr (k : Nat) : GoString := kitAddr (1 + k)
def netAddr (k : Nat) : GoString := kitAddr (11 + k)
def cfgAddr (k : Nat) : GoString := kitAddr (21 + k)

/-- Client machine `c`'s address for the orchestrator's calls (`ClientAddrs()[c]`, remote's
`ServeClient`; its protocols are remote's) and its configuration address (`ClientConfAddrs()[c]`)
(`c < nC`). -/
def cliAddr (c : Nat) : GoString := kitAddr (31 + c)
def cliCfgAddr (c : Nat) : GoString := kitAddr (41 + c)

/-- The handshake of a dialer with id `i` (`Command{CliId: i}`). -/
def hsCmd (i : Nat) : CmdV := { cliId := BitVec.ofNat 32 i, cliSeq := 0, svrSeq := 0, commands := [] }
def hsBytes (i : Nat) : List w8 := frame (encCmd (hsCmd i))

/-- The number of clients. -/
def nC : Nat := 6

/-- A message's round by its type and phase (`0` the proposal, `2p` the state of phase `p ≥ 1`,
`2p + 1` the vote of phase `p`); also the round a slot-queue notification stands for. -/
def roundOf (m : MsgV) : Option Nat :=
  if m.ty = tyProposal then some 0
  else if m.ty = tyState then some (2 * m.phase.toNat)
  else if m.ty = tyVote then some (2 * m.phase.toNat + 1)
  else none

/-- A message's slot and round: the consensus messages a server sends in order for each slot. -/
def msgRound (m : MsgV) : Option (Nat × Nat) :=
  (roundOf m).map fun r => ((m.obj.map (·.svrSeq.toNat)).getD 0, r)

/-- The rounds of each slot are in order in a broadcast log, and each round once. -/
def RoundsOrdered (l : List MsgV) : Prop :=
  (∀ (i : Nat) (m : MsgV) (s r : Nat), l[i]? = some m → msgRound m = some (s, r + 1) →
    ∃ j < i, ∃ m', l[j]? = some m' ∧ msgRound m' = some (s, r)) ∧
  (∀ (i j : Nat) (m m' : MsgV) (sr : Nat × Nat), l[i]? = some m → l[j]? = some m' → msgRound m = some sr →
    msgRound m' = some sr → i = j) ∧
  (∀ (i j : Nat) (m m' : MsgV) (o o' : ObjV), l[i]? = some m → l[j]? = some m' → m.ty = tyClientRequest →
    m'.ty = tyClientRequest → m.obj = some o → m'.obj = some o' → o.proSeq = o'.proSeq → i = j)

/-- An executor's log `E_k` (a prefix of it): its rounds in order, no client request. -/
def ExLogOk (l : List MsgV) : Prop := RoundsOrdered l ∧ ∀ m ∈ l, m.ty ≠ tyClientRequest

/-- The broadcast part of a sequence of messages (all but `ProposalReply`s). -/
def bcastPart (l : List MsgV) : List MsgV := l.filter (·.ty ≠ tyProposalReply)

/-! ## Names -/

/-- The network's ghost names (`start` allocates them). -/
structure NetNames where
  /-- server `X`'s broadcast log `B_X` (a mono-list of messages) -/
  bcast : Nat → GName
  /-- the clients' established connections: a ghost map `(c, k) ↦ Option Nat` (`none` unset,
  exclusive, the client's; `some cid` set, persistent) -/
  estab : GName

/-- All the shared names. -/
structure Names where
  rab : RabiaNames
  net : NetNames

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS GooseGlobalGS.gooseAllG

instance : Pos.Countable ObjV :=
  countableOfLeftInverse
    (B := w32 × w32 × w32 × Bool × List w32 × List w32 × List GoString)
    (fun o => (o.proId, o.proSeq, o.svrSeq, o.isNull, o.cliIds, o.cliSeqs, o.commands))
    (fun (a, b, c, d, e, f, g) => ⟨a, b, c, d, e, f, g⟩)
    (fun _ => rfl)
instance : Pos.Countable MsgV :=
  countableOfLeftInverse (B := w32 × w32 × w32 × Option ObjV)
    (fun m => (m.ty, m.phase, m.value, m.obj))
    (fun (a, b, c, d) => ⟨a, b, c, d⟩)
    (fun _ => rfl)


/-! ## Messages' facts -/

/-- A bound on the commands a server handles: every command reached the servers through a proxy,
which reads a request's frame into 409600 bytes (a longer frame is a read error, N6). -/
def cmdBound : Nat := 409600

/-- A consensus object made of its slot only (a State's or Vote's `Obj`; with `isNull`, a NULL
decision's). -/
def model.ObjV.slotOnly (o : ObjV) (null : Bool) : Prop :=
  o = { proId := 0, proSeq := 0, svrSeq := o.svrSeq, isNull := null, cliIds := [], cliSeqs := [],
        commands := [] }

/-- A consensus object carrying a batch `rs` of registered requests (`1 ≤ |rs| ≤ batchSize`,
each with its one command, in order), made by proxy `ProId < n` as its object `ProSeq`. -/
def objOk (γ : Names) (cf : RCfg) (o : ObjV) : IProp GF :=
  iprop(∃ rs : List ReqId, fact γ.rab (.pobj (o.proId.toNat, o.proSeq.toNat)) (.reqs rs) ∗
    regFacts γ.rab rs o.commands ∗
    ⌜o.isNull = false ∧ o.cliIds = rs.map (fun r => BitVec.ofNat 32 r.1) ∧
      o.cliSeqs = rs.map (fun r => BitVec.ofNat 32 r.2) ∧ 1 ≤ rs.length ∧
      rs.length ≤ cf.batchSize ∧ (∀ r ∈ rs, r.1 < nC ∧ r.2 < 2 ^ 32) ∧ o.proId.toNat < cf.n ∧
      ∀ cmd ∈ o.commands, ∃ i, cmd = cmdOf i ∧ inputOk i ∧ cmd.length < cmdBound⌝)

/-- A decision message's object for decision `d` of slot `s`. -/
def decObjOk (γ : Names) (cf : RCfg) (s : Nat) (d : DVal) (o : ObjV) : IProp GF :=
  match d with
  | .null => iprop(⌜o.isNull = true ∧ o.svrSeq.toNat = s ∧ o.slotOnly true⌝)
  | .obj id => iprop(⌜(o.proId.toNat, o.proSeq.toNat) = id ∧ o.svrSeq.toNat = s⌝ ∗ objOk γ cf o)

/-- A message of server `X`'s broadcast log, with its type's facts. -/
def bmsgOk (γ : Names) (cf : RCfg) (X : Nat) (m : MsgV) : IProp GF :=
  if m.ty = tyClientRequest then
    iprop(∃ o, ⌜m.obj = some o ∧ o.proId.toNat = X⌝ ∗ objOk γ cf o)
  else if m.ty = tyProposal then
    iprop(∃ o, ⌜m.obj = some o ∧ m.phase = 0⌝ ∗ objOk γ cf o ∗
      fact γ.rab (.prop X o.svrSeq.toNat) (.obj (o.proId.toNat, o.proSeq.toNat)))
  else if m.ty = tyState then
    iprop(∃ o, ⌜m.obj = some o ∧ m.phase.toNat ≥ 1 ∧ o.slotOnly false⌝ ∗
      fact γ.rab (.st X o.svrSeq.toNat m.phase.toNat) (.bit m.value.toNat))
  else if m.ty = tyVote then
    iprop(∃ o, ⌜m.obj = some o ∧ o.slotOnly false⌝ ∗
      fact γ.rab (.vt X o.svrSeq.toNat m.phase.toNat) (.bit m.value.toNat))
  else if m.ty = tyProposalRequest then
    iprop(⌜m.phase.toNat = X ∧ m.obj = none⌝ ∗ ∃ b, fact γ.rab (.preq X m.value.toNat) (.bit b))
  else if m.ty = tyDecision then
    iprop(∃ o d, ⌜m.obj = some o⌝ ∗ fact γ.rab (.dec o.svrSeq.toNat) (.dval d) ∗
      decObjOk γ cf o.svrSeq.toNat d o)
  else iprop(False)

/-- A `ProposalReply` to server `k`: the requested slot's object with the proposals of a majority
`W` of the servers (`Majority`). -/
def replyOk (γ : Names) (cf : RCfg) (k : Nat) (m : MsgV) : IProp GF :=
  iprop(∃ (o : ObjV) (W : List Nat) (b : Nat), ⌜m.ty = tyProposalReply ∧ m.phase.toNat = k ∧ m.obj = some o ∧
      o.svrSeq = m.value ∧ W.Nodup ∧ (∀ X ∈ W, X < cf.n) ∧ W.length ≥ cf.maj⌝ ∗ objOk γ cf o ∗
    ([∗list] X ∈ W, fact γ.rab (.prop X m.value.toNat) (.obj (o.proId.toNat, o.proSeq.toNat))) ∗
    fact γ.rab (.preq k m.value.toNat) (.bit b))

/-- Client `c`'s request (`Op`'s `Command`): registered. -/
def reqOk (γ : Names) (c : Nat) (q : CmdV) : IProp GF :=
  iprop(∃ cmd, ⌜q.cliId = BitVec.ofNat 32 c ∧ q.commands = [cmd] ∧ q.svrSeq = 0 ∧
      ∃ i, cmd = cmdOf i ∧ inputOk i⌝ ∗
    fact γ.rab (.reg (c, q.cliSeq.toNat)) (.cmd cmd))

/-- A proxy's reply to client `c`: its request is `rs[j]` of the object decided at slot `s`, the
result its command's (`bc[j]`) on the store of the slots before `s` (`cmds`) and the requests
before it in the batch (`bc.take j`). -/
def repOk (γ : Names) (c : Nat) (q : CmdV) : IProp GF :=
  iprop(∃ (s : Nat) (id : ObjId) (rs : List ReqId) (bc : List GoString) (j : Nat) (res : GoString)
      (cmds : List GoString) (cmd : GoString),
    ⌜q.cliId = BitVec.ofNat 32 c ∧ q.commands = [res] ∧ rs[j]? = some (c, q.cliSeq.toNat) ∧
      bc[j]? = some cmd ∧ res = (execCmd (stateOfCmds (cmds ++ bc.take j)) cmd).2⌝ ∗
    fact γ.rab (.dec s) (.dval (.obj id)) ∗ fact γ.rab (.pobj id) (.reqs rs) ∗
    regFacts γ.rab rs bc ∗ prefixFacts γ.rab s cmds)

/-! ## Broadcast logs and established connections -/

/-- `l` is a prefix of server `X`'s broadcast log (persistent). -/
def bcastLb (γ : Names) (X : Nat) (l : List MsgV) : IProp GF := monoListLbOwn (γ.net.bcast X) l

/-- Server `X`'s broadcast log: half its authority (the other half is the serializer's), every
element with its facts at the recorded configuration (once the log is not empty), the rounds in
order (namespace `bcastN X`). -/
def bcastInv (γ : Names) (X : Nat) : IProp GF :=
  iprop(∃ l, monoListAuthOwn (γ.net.bcast X) (1 : Qp).half l ∗
    (⌜l = []⌝ ∨ ∃ cf, cfgIs γ.rab cf ∗ [∗list] m ∈ l, bmsgOk γ cf X m) ∗ ⌜RoundsOrdered l⌝)

def bcastN (X : Nat) : Namespace := ndot (ndot rabiaR "bcast") (toString X)

/-- Client `c`'s established connection to proxy `k` is `cid` (persistent). -/
def estab (γ : Names) (c k : Nat) (cid : Nat) : IProp GF :=
  ghostMapElem γ.net.estab (c, k) .discard (some cid)

/-- The established connections' map's authority (a client sets its entry through it, once: its
element `estabTok` is exclusive until set, then persistent). -/
def estabInv (γ : Names) : IProp GF :=
  iprop(∃ m : GMap (Nat × Nat) (Option Nat), ghostMapAuth γ.net.estab 1 m)

def estabN : Namespace := ndot rabiaR "estab"

/-- Client `c` has not established its connection to proxy `k` (exclusive: `connect` sets it). -/
def estabTok (γ : Names) (c k : Nat) : IProp GF :=
  ghostMapElem γ.net.estab (c, k) (.own 1) (none : Option Nat)

/-! ## Protocols -/

/-- What a server writes to server `k`'s network address (at the recorded configuration): its
handshake, then its messages to `k`: a prefix of its broadcast log, in order, with
`ProposalReply`s to `k` interleaved. (Nothing written yet is allowed outright: a buffered writer
is made over the connection before anything is known of it, `bufio.NewWriterSize`'s `□ Q W`.) -/
def netP (γ : Names) (k : Nat) : Proto GF := fun cid W =>
  iprop(⌜W = []⌝ ∨ ∃ (cf : RCfg) (X : Nat) (fs : List MsgV), cfgIs γ.rab cf ∗
    ⌜X < cf.n ∧ W <+: hsBytes X ++ frames (fs.map encMsg) ∧
      ∀ m ∈ fs, (encMsg m).length < 2 ^ 32⌝ ∗
    bcastLb γ X (bcastPart fs) ∗
    [∗list] m ∈ fs.filter (·.ty = tyProposalReply), replyOk γ cf k m)

/-- The client operations' budget (SF1: each client runs fewer than `2^29` operations, so the
requests a proxy receives, at most `nC * 2^29 < 2^32`, get distinct 32-bit `ProSeq`s). -/
def opBudget : Nat := 2 ^ 29

/-- What a client writes to server `k`'s proxy (`k = c mod n` at the recorded configuration): its
handshake, then, on its established connection only, its registered requests in increasing
sequence numbers (`Op` numbers them `cl.next`; the endpoint writes them in order and skips one whose
command cannot be framed, G12/N8), within the budget; every frame's payload is below `2^32`.
(Nothing written yet is allowed outright, as `netP`.) -/
def proxyP (γ : Names) (k : Nat) : Proto GF := fun cid W =>
  iprop(⌜W = []⌝ ∨ ∃ (cf : RCfg) (c : Nat) (qs : List CmdV), cfgIs γ.rab cf ∗ ⌜c < nC ∧ c % cf.n = k ∧
      W <+: hsBytes c ++ frames (qs.map encCmd) ∧
      qs.length ≤ opBudget ∧ qs.Pairwise (fun a b => a.cliSeq.toNat < b.cliSeq.toNat) ∧
      ∀ q ∈ qs, q.cliSeq.toNat < opBudget ∧ (encCmd q).length < 2 ^ 32⌝ ∗
    (⌜qs = []⌝ ∨ estab γ c k cid) ∗ [∗list] q ∈ qs, reqOk γ c q)

/-- What server `k`'s proxy writes to a client: replies to the client of the connection's
handshake (a client id `c < nC`); every frame's payload is below `2^32`. (Nothing written yet is
allowed outright, as `netP`: the proxy makes its writer before it reads the handshake.) -/
def proxyQ (γ : Names) (_k : Nat) : Proto GF := fun cid W =>
  iprop(⌜W = []⌝ ∨ ∃ (c : Nat) (rs : List CmdV), sentLb (Gg := G) cid false (hsBytes c) ∗
    ⌜c < nC ∧ W <+: frames (rs.map encCmd) ∧ ∀ q ∈ rs, (encCmd q).length < 2 ^ 32⌝ ∗
    [∗list] q ∈ rs, repOk γ c q)

/-- What the orchestrator writes to a node's configuration address (a server node's or a client
node's): a prefix of the recorded configuration's encoding (`sendConf`). -/
def cfgP (γ : Names) : Proto GF := fun _ W =>
  iprop(∃ cf : RCfg, cfgIs γ.rab cf ∗ ⌜W <+: cf.enc⌝)

/-- What a node's configuration listener writes back: a prefix of the acknowledgment
(`awaitConf`'s `confAck`). -/
def cfgQ : Proto GF := fun _ W => iprop(⌜W <+: [(0x6b : w8)]⌝)

/-- Nothing is written (the network layers' acceptors; the client node's address). -/
def noneP : Proto GF := fun _ W => iprop(⌜W = []⌝)

/-- The dialers' protocol of each address whose protocols the start sets (`protoAddrs`: each
server node's proxy, network and configuration addresses; each client node's configuration
address). -/
def addrP (γ : Names) (a : GoString) : Proto GF :=
  (List.range maxS).foldr (fun k P =>
    if a = proxyAddr k then proxyP γ k else if a = netAddr k then netP γ k
    else if a = cfgAddr k then cfgP γ else P)
    ((List.range nC).foldr (fun c P => if a = cliCfgAddr c then cfgP γ else P) noneP)

/-- The acceptors' protocol of each address of `protoAddrs`. -/
def addrQ (γ : Names) (a : GoString) : Proto GF :=
  (List.range maxS).foldr (fun k P =>
    if a = proxyAddr k then proxyQ γ k else if a = cfgAddr k then cfgQ else P)
    ((List.range nC).foldr (fun c P => if a = cliCfgAddr c then cfgQ else P) noneP)

/-! ## The shared invariants and the shares -/

/-- The 15 server addresses, node by node. -/
def serverAddrs : List GoString :=
  (List.range maxS).flatMap fun k => [proxyAddr k, netAddr k, cfgAddr k]

/-- The addresses whose protocols the start sets: the server addresses and the client nodes'
configuration addresses (the client nodes' `:7000` keep theirs unset: their claims of
`config.Conf`; their request addresses are the harness's). -/
def protoAddrs : List GoString := serverAddrs ++ (List.range nC).map cliCfgAddr

/-- Everything shared, persistent: the facts' invariant, the broadcast logs', the established
connections', the protocols of `protoAddrs`. -/
def shared (γ : Names) : IProp GF :=
  iprop(isRabia γ.rab ∗ ([∗list] X ∈ List.range maxS, inv (bcastN X) (bcastInv γ X)) ∗
    inv estabN (estabInv γ) ∗
    [∗list] a ∈ protoAddrs, addrProto (Gg := G) a (addrP γ a) (addrQ γ a))

/-- The orchestrator's (node 0's) part: the shared state and its key set (empty: it records the
configuration). The key-value state's half (`kvState`'s) is not here: the start hands it to
remote's pending library (`Core/Start.lean`). -/
def orchCore (γ : Names) : IProp GF :=
  iprop(shared γ ∗ keysOf γ.rab .orch [])

/-- Client node `c`'s part (`c < nC`): the shared state, client `c`'s key set (empty), the right
to establish its connection to every server node's proxy (it connects to server `c mod n`'s, `n`
chosen later), its configuration address's token (`awaitConf` listens there). -/
def cliCore (γ : Names) (c : Nat) : IProp GF :=
  iprop(shared γ ∗ keysOf γ.rab (.cli c) [] ∗
    ([∗list] k ∈ List.range maxS, estabTok γ c k) ∗ addrTok (GF := GF) (cliCfgAddr c))

/-- Server `k`'s part without its configuration address (what `ServerInit` takes): the
shared state, its proxy and network addresses' tokens, its key set (empty), half of its broadcast
log (empty). -/
def serverCore (γ : Names) (k : Nat) : IProp GF :=
  iprop(shared γ ∗ addrTok (GF := GF) (proxyAddr k) ∗ addrTok (GF := GF) (netAddr k) ∗
    keysOf γ.rab (.srv k) [] ∗ monoListAuthOwn (γ.net.bcast k) (1 : Qp).half ([] : List MsgV))

/-- Server node `k`'s share (`k < maxS`, node `7 + k`): `serverCore` and its configuration
address's token (`awaitConf` listens there). -/
def serverShare (γ : Names) (k : Nat) : IProp GF :=
  iprop(serverCore γ k ∗ addrTok (GF := GF) (cfgAddr k))

instance shared_persistent (γ : Names) : Persistent (shared (GF := GF) γ) := by
  unfold shared isRabia; infer_instance

end defs

/-! ## The address laws (stage 3; statements, proved in Prove) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-! ### Address facts (internal: hosts split from ports, no kernel `decide` on whole addresses) -/

theorem digits2_inj {i j : Nat} (hi : i < 100) (hj : j < 100) (h : digits2 i = digits2 j) :
    i = j := by
  unfold digits2 at h
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨h1, h2⟩ := h
  have e1 := congrArg BitVec.toNat h1
  have e2 := congrArg BitVec.toNat h2
  simp only [BitVec.toNat_ofNat] at e1 e2
  omega

theorem kitAddr_inj {i j : Nat} (hi : i < 100) (hj : j < 100) (h : kitAddr i = kitAddr j) :
    i = j :=
  digits2_inj hi hj (List.append_cancel_left h)

theorem kitAddr_ne {i j : Nat} (hi : i < 100) (hj : j < 100) (h : i ≠ j) : kitAddr i ≠ kitAddr j :=
  fun e => h (kitAddr_inj hi hj e)

theorem maxS_cases' (k : Nat) (hk : k < maxS) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
  unfold maxS at hk; omega

theorem nC_cases (c : Nat) (hc : c < nC) :
    c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by
  unfold nC at hc; omega

theorem range_maxS' : List.range maxS = [0, 1, 2, 3, 4] := by simp [maxS, List.range_succ]
theorem range_nC : List.range nC = [0, 1, 2, 3, 4, 5] := by simp [nC, List.range_succ]

/- The address tables' entries: each condition decided by `kitAddr_ne` (the port's digits), no
`simp`/`split` on the `ite`s. -/
macro "addr_pick" : tactic => `(tactic| (
  repeat (first
    | (refine (ite_eq_right_of_eq_false _ _ (eq_false ?_)).trans ?_
       · exact kitAddr_ne (by decide) (by decide) (by decide))
    | exact ite_eq_left_of_eq_true _ _ (eq_true rfl))))

section tables
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

theorem addrP_proxy (γ : Names) (k : Nat) (hk : k < maxS) :
    addrP (GF := GF) γ (proxyAddr k) = proxyP γ k := by
  unfold addrP; rw [range_maxS', range_nC]; simp only [List.foldr_cons, List.foldr_nil]
  rcases maxS_cases' k hk with rfl | rfl | rfl | rfl | rfl <;> addr_pick

theorem addrQ_proxy (γ : Names) (k : Nat) (hk : k < maxS) :
    addrQ (GF := GF) γ (proxyAddr k) = proxyQ γ k := by
  unfold addrQ; rw [range_maxS', range_nC]; simp only [List.foldr_cons, List.foldr_nil]
  rcases maxS_cases' k hk with rfl | rfl | rfl | rfl | rfl <;> addr_pick

theorem addrP_net (γ : Names) (k : Nat) (hk : k < maxS) :
    addrP (GF := GF) γ (netAddr k) = netP γ k := by
  unfold addrP; rw [range_maxS', range_nC]; simp only [List.foldr_cons, List.foldr_nil]
  rcases maxS_cases' k hk with rfl | rfl | rfl | rfl | rfl <;> addr_pick

theorem addrQ_net (γ : Names) (k : Nat) (hk : k < maxS) :
    addrQ (GF := GF) γ (netAddr k) = noneP := by
  unfold addrQ; rw [range_maxS', range_nC]; simp only [List.foldr_cons, List.foldr_nil]
  rcases maxS_cases' k hk with rfl | rfl | rfl | rfl | rfl <;> addr_pick <;> rfl

theorem addrP_cfg (γ : Names) (k : Nat) (hk : k < maxS) :
    addrP (GF := GF) γ (cfgAddr k) = cfgP γ := by
  unfold addrP; rw [range_maxS', range_nC]; simp only [List.foldr_cons, List.foldr_nil]
  rcases maxS_cases' k hk with rfl | rfl | rfl | rfl | rfl <;> addr_pick

theorem addrQ_cfg (γ : Names) (k : Nat) (hk : k < maxS) :
    addrQ (GF := GF) γ (cfgAddr k) = cfgQ := by
  unfold addrQ; rw [range_maxS', range_nC]; simp only [List.foldr_cons, List.foldr_nil]
  rcases maxS_cases' k hk with rfl | rfl | rfl | rfl | rfl <;> addr_pick

theorem addrP_cliCfg (γ : Names) (c : Nat) (hc : c < nC) :
    addrP (GF := GF) γ (cliCfgAddr c) = cfgP γ := by
  unfold addrP; rw [range_maxS', range_nC]; simp only [List.foldr_cons, List.foldr_nil]
  rcases nC_cases c hc with rfl | rfl | rfl | rfl | rfl | rfl <;> addr_pick

theorem addrQ_cliCfg (γ : Names) (c : Nat) (hc : c < nC) :
    addrQ (GF := GF) γ (cliCfgAddr c) = cfgQ := by
  unfold addrQ; rw [range_maxS', range_nC]; simp only [List.foldr_cons, List.foldr_nil]
  rcases nC_cases c hc with rfl | rfl | rfl | rfl | rfl | rfl <;> addr_pick

end tables

theorem protoAddrs_proxy (k : Nat) (hk : k < maxS) :
    protoAddrs[3 * k]? = some (proxyAddr k) := by
  rcases maxS_cases' k hk with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem protoAddrs_net (k : Nat) (hk : k < maxS) :
    protoAddrs[3 * k + 1]? = some (netAddr k) := by
  rcases maxS_cases' k hk with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem protoAddrs_cfg (k : Nat) (hk : k < maxS) :
    protoAddrs[3 * k + 2]? = some (cfgAddr k) := by
  rcases maxS_cases' k hk with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem protoAddrs_cliCfg (c : Nat) (hc : c < nC) :
    protoAddrs[15 + c]? = some (cliCfgAddr c) := by
  rcases nC_cases c hc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Server `k`'s proxy address's protocols. -/
theorem shared_proxyProto (γ : Names) (k : Nat) (hk : k < maxS) :
    shared (GF := GF) γ ⊢ addrProto (Gg := G) (proxyAddr k) (proxyP γ k) (proxyQ γ k) := by
  unfold shared
  iintro ⟨-, -, -, #Ha⟩
  rw [← addrP_proxy γ k hk, ← addrQ_proxy γ k hk]
  iapply (BigSepL.bigSepL_lookup (protoAddrs_proxy k hk)) $$ Ha

/-- Server `k`'s network address's protocols. -/
theorem shared_netProto (γ : Names) (k : Nat) (hk : k < maxS) :
    shared (GF := GF) γ ⊢ addrProto (Gg := G) (netAddr k) (netP γ k) noneP := by
  unfold shared
  iintro ⟨-, -, -, #Ha⟩
  rw [← addrP_net γ k hk, ← addrQ_net γ k hk]
  iapply (BigSepL.bigSepL_lookup (protoAddrs_net k hk)) $$ Ha

/-- Server `k`'s configuration address's protocols. -/
theorem shared_cfgProto (γ : Names) (k : Nat) (hk : k < maxS) :
    shared (GF := GF) γ ⊢ addrProto (Gg := G) (cfgAddr k) (cfgP γ) cfgQ := by
  unfold shared
  iintro ⟨-, -, -, #Ha⟩
  rw [← addrP_cfg γ k hk, ← addrQ_cfg γ k hk]
  iapply (BigSepL.bigSepL_lookup (protoAddrs_cfg k hk)) $$ Ha

/-- Client node `c`'s configuration address's protocols. -/
theorem shared_cliCfgProto (γ : Names) (c : Nat) (hc : c < nC) :
    shared (GF := GF) γ ⊢ addrProto (Gg := G) (cliCfgAddr c) (cfgP γ) cfgQ := by
  unfold shared
  iintro ⟨-, -, -, #Ha⟩
  rw [← addrP_cliCfg γ c hc, ← addrQ_cliCfg γ c hc]
  iapply (BigSepL.bigSepL_lookup (protoAddrs_cliCfg c hc)) $$ Ha

end laws

end Perennial.rabia
