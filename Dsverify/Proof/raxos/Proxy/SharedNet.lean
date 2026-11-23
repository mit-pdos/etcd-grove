/-
Package `proxy`: the network side of the proxy's shared state (`sharedNet`, part of
`proxySharedDef`; persistent), used by `Proxy.NetworkInit` (`Net*.lean`).

**What `NewProxy` must establish** (all persistent once made; the lemmas at the end help):
* `pr.serverAddress ↦□ "0.0.0.0:" ++ decStr (7606 + k)` (`proxy.go`: the wildcard host, replica `k`'s proxy port);
* `pr.incomingClientReaders ↦□ rm` and the invariant `inv netN (netOwn pr rm ∨ addrTok (proxyAddr k))`
  holding, on the left, the accept routine's exclusive state: the `Listener` field and the readers'
  map `rm ↦$ M` (`netOwn_inv_alloc`). The routine (`waitForConnections`) Listens with the caller's
  `addrTok`, then swaps it for `netOwn` (a second caller cannot: the token is exclusive);
* `pr.outgoingClientWriters ↦□ wm` and `isMutex pr.clientWritersMutex (writersR γ k BM γw wm)`
  (initially `wm ↦$ ∅`);
* `pr.buffioWriterMutexes ↦□ bm`, `bm ↦$□ BM` with keys `21..26` (the clients), each mutex
  `isMutex mu (peerR γ k (cOf p) (γw p))` (`peerR_alloc` makes the ghost name and the body);
* `pr.clientAddrList ↦□ cm`, `cm ↦$□ CM` with `CM !! (21 + c) = some (clientAddr c)`, c < 6;
* `pr.rpcTable ↦□ rt`, `rt ↦$□ RT` with `RT !! 1 = some rp1`, `rp1 ↦□ {1, *ClientBatch cb0}`.

**The writers' design.** A writer `w` to client `c` (made by `connectToClient`) is owned by
`wSlot γ k c w`: a `bufio.Writer` over the connection's dialer end (`EtcdGrove.bufio.ownBufWriter`
of origin/dsv-bufio, size 4096, `NewWriter`'s), written with client `c`'s
port's protocol (`clientInProto γ c`); while healthy (no sticky error) what it holds is the
handshake and whole answer frames, each fit (learned from the answer's `Marshal` into a
`msgBuffer`, before its code byte is written: P4). When published in the writers' map it is put in a per-writer invariant
`inv wN (wSlot γ k w ∨ claimed)`; the first sender holding the peer's mutex claims it into the
mutex's body `peerR` (a ghost map `γw p` of the claimed writers, `claimed` being its persistent
element, so a later sender finds it there).
-/
module

public import Dsverify.Proof.raxos.Proxy.StateDefs
public import Proof.bufio.Own

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

def netN : Namespace := ndot raxosN "net"
def wN : Namespace := ndot raxosN "writer"

/-- The bytes a healthy writer to a client from proxy `k` holds: the handshake, then the answer
frames `L`. -/
def ansStream (k : Nat) (L : List Batch) : List w8 :=
  hs k ++ (L.map frame).flatten

/-- The client of a peer name (`21 + c` ↦ `c`). -/
def cOf (p : w64) : Nat := uint.nat p - 21

theorem cOf_peer (cl : Nat) (hcl : cl < 6) : cOf (W64 (21 + cl)) = cl := by
  rcases cl with _ | _ | _ | _ | _ | _ | cl <;> first | rfl | omega

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- Writer `w` to client `c`, of proxy `k` (exclusive). -/
def wSlot (γ : QNames) (k c : Nat) (w : Loc) : IProp GF :=
  iprop(∃ (wi : GoInterfaceOk) (cid : Nat) (Ew : GoInterface → IProp GF) (sent pend : List w8)
      (err : GoInterface),
    EtcdGrove.bufio.ownBufWriter w wi (sendTok cid false (clientInProto γ c)) (clientInProto γ c cid)
      Ew 4096 sent pend err ∗
    (⌜err ≠ interface.nil⌝ ∨ ∃ L : List Batch,
      ⌜sent ++ pend = ansStream k L ∧ ∀ b ∈ L, batchFit b⌝ ∗
      [∗list] b ∈ L, ∃ r, ⌜b.cmds = [r]⌝ ∗ opAns γ b.id r))

/-- The body of a peer's writer mutex: the writers claimed so far (ghost map `γp`). -/
def peerR (γ : QNames) (k c : Nat) (γp : GName) : IProp GF :=
  iprop(∃ C : GMap Loc Unit, ghostMapAuth γp 1 C ∗ [∗map] w ↦ _u ∈ C, wSlot γ k c w)

/-- Writer `w` was published for peer `p` (persistent): the peer has a mutex, and the writer is
unclaimed or claimed by that mutex's body. -/
def wPub (γ : QNames) (k : Nat) (BM : GMap w64 Loc) (γw : w64 → GName) (p : w64) (w : Loc) :
    IProp GF :=
  iprop(∃ mu : Loc, ⌜BM !! p = some mu⌝ ∗
    inv wN iprop(wSlot γ k (cOf p) w ∨ ghostMapElem (γw p) w DFrac.discard ()))

/-- The body of `clientWritersMutex`: the writers' map, each writer published. -/
def writersR (γ : QNames) (k : Nat) (BM : GMap w64 Loc) (γw : w64 → GName) (wm : Loc) :
    IProp GF :=
  iprop(∃ W : GMap w64 Loc, wm ↦$ W ∗ [∗map] p ↦ w ∈ W, wPub γ k BM γw p w)

/-- The accept routine's exclusive state: the `Listener` field and the readers' map. -/
def netOwn (pr rm : Loc) : IProp GF :=
  iprop(∃ (lv : GoInterface) (M : GMap w64 Loc), pr.[Proxy, go!"Listener"] ↦ lv ∗ rm ↦$ M)

/-- The network side's shared state (persistent): see the file header. -/
def sharedNet (γ : QNames) (k : Nat) (pr : Loc) : IProp GF :=
  iprop(∃ (rm wm bm cm rt rp1 cb0 : Loc) (BM : GMap w64 Loc) (γw : w64 → GName)
      (CM : GMap w64 GoString) (RT : GMap w8 Loc),
    pr.[Proxy, go!"serverAddress"] ↦□ (go!"0.0.0.0:" ++ decStr (7606 + k)) ∗
    pr.[Proxy, go!"incomingClientReaders"] ↦□ rm ∗
    inv netN iprop(netOwn pr rm ∨ addrTok (proxyAddr k)) ∗
    pr.[Proxy, go!"outgoingClientWriters"] ↦□ wm ∗
    sync.isMutex (pr.[Proxy, go!"clientWritersMutex"]) (writersR γ k BM γw wm) ∗
    pr.[Proxy, go!"buffioWriterMutexes"] ↦□ bm ∗ bm ↦$□ BM ∗
    ⌜∀ c : Nat, c < 6 → (BM !! W64 (21 + c)).isSome⌝ ∗
    ([∗map] p ↦ mu ∈ BM, sync.isMutex mu (peerR γ k (cOf p) (γw p))) ∗
    pr.[Proxy, go!"clientAddrList"] ↦□ cm ∗ cm ↦$□ CM ∗
    ⌜∀ c : Nat, c < 6 → CM !! W64 (21 + c) = some (clientAddr c)⌝ ∗
    pr.[Proxy, go!"rpcTable"] ↦□ rt ∗ rt ↦$□ RT ∗ ⌜RT !! W8 1 = some rp1⌝ ∗
    rp1 ↦□ (raxos.common.RPCPair.mk (W8 1)
      (interface.mkOk (go.GoType.PointerType raxos.proto.client.ClientBatch.ty) #cb0)))

instance wPub_persistent (γ : QNames) (k : Nat) (BM : GMap w64 Loc) (γw : w64 → GName) (p : w64)
    (w : Loc) : Persistent (wPub (GF := GF) γ k BM γw p w) := by
  unfold wPub; infer_instance


set_option synthInstance.maxSize 2048 in
instance sharedNet_persistent (γ : QNames) (k : Nat) (pr : Loc) :
    Persistent (sharedNet (GF := GF) γ k pr) := by
  unfold sharedNet; infer_instance

/-- For `NewProxy`: a peer mutex's body, with a fresh ghost name. -/
theorem peerR_alloc (γ : QNames) (k c : Nat) : ⊢ |==> ∃ γp, peerR (GF := GF) γ k c γp := by
  imod ghost_map_alloc_empty (K := Loc) (V := Unit) with ⟨%γp, Ha⟩
  imodintro
  iexists γp
  unfold peerR
  iexists ∅
  isplitl [Ha]
  · iexact Ha
  iapply BigSepM.bigSepM_empty.2
  itrivial

/-- For `NewProxy`: the accept routine's invariant, from its state. -/
theorem netOwn_inv_alloc (k : Nat) (pr rm : Loc) (lv : GoInterface) (E : CoPset) :
    ⊢ (pr.[Proxy, go!"Listener"] ↦ lv : IProp GF) -∗ rm ↦$ (∅ : GMap w64 Loc) ={E}=∗
      inv netN iprop(netOwn pr rm ∨ addrTok (proxyAddr k)) := by
  iintro Hl Hm
  imod inv_alloc netN E iprop(netOwn pr rm ∨ addrTok (proxyAddr k)) $$ [Hl Hm] with #Hi
  · inext; ileft; unfold netOwn; iexists lv, ∅; iframe Hl Hm
  imodintro; iexact Hi

end defs

end Perennial.raxos
