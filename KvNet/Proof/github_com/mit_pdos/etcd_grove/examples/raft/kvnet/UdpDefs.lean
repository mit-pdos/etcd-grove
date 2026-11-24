/-
# kvudp's transport: its ghost state and representation predicates (2026-11-24)

`notes/kvudp-proof-plan.md`. The UDP transport (`udptransport.go`, `nodeudp.go`) sends each raft
message as fragment datagrams named `(from, boot, seq)`; the receiver reassembles a message from the
fragments of one name. What makes that sound is that **a name is never reused**: the ghost state
records, for each name used, the one body sent under it (`udpMsgAt k body`, persistent agreement),
and each datagram on the network carries the fact of the fragment it is (`udpDgOk`).

**The ghost state** (`UdpNames`, four ghost maps, allocated once at the top level):
* `msgs : MsgKey ↦ List w8`, persistent elements `udpMsgAt k body`: the message named `k` is `body`.
* `toks : MsgKey ↦ Bool`, exclusive elements `udpSeqTok k`: the right to record `k` (a sequence
  number `nextSeq` handed out, not yet recorded).
* `ctrs : (from, boot) ↦ w64`, exclusive elements `udpCtr from boot c`: the process `(from, boot)`
  has used its sequence numbers up to `c` (`udpNet.seq`, under its mutex).
* `his : from ↦ w64`, exclusive elements `udpHi from hi`: replica `from`'s boot numbers handed out so
  far are at most `hi`; the element lives in the replica's boot file invariant (`UdpBootDefs.lean`),
  which ties it to the boot counter's durable file.

`udpMsgInv γu` (one invariant) holds the four authorities and `UdpMsgOk`: every recorded or
reserved name `(f, b, s)` has `s ≤ ctrs (f, b)`; a reserved name is not recorded; every counter
`(f, b)` has `b ≤ his f`. So a fresh counter `(f, hi + 1)` (`nextBoot`) and a fresh token
`(f, b, c + 1)` (`nextSeq`) are fresh names.

**The datagram protocol**: `udpDgOk F γu d` (persistent): `d` parses (`parseDg`) as an ack (no claim)
or as a fragment, the `index`-th chunk of the body recorded under its name, which is a message's
encoding with its fact (`udpBodyOk`: as a TCP frame carries, `Proto.lean`'s `framesOk`).
`udpAddrInv F γu a` (one invariant per cluster address): `udpSent a ms` with `udpDgOk` of every
datagram in `ms`. The sender proves `udpDgOk` of what it sends, which is at most `maxDatagramN` bytes
(`parseDg_length`), so what arrives (`Udp.Intact`) is exactly what was sent, and the receiver gets
`udpDgOk` of it.

**The representation predicates**:
* `isUdpPeerAddr F γu pid p` (persistent): `p` is the `*UDPAddr` of a valid address with its invariant.
* `isUdpNet F γu u id boot` (persistent): the process's endpoint: its fields, socket (`udpConnAt`) at
  its own address with that address's invariant, the address map, the boot number, the ghost
  invariant, and its mutex, whose invariant `udpNetLockInv` holds the sequence counter (with its ghost
  counter) and the snapshot waiters (`ackWaitOwn`: each waiter's channel, with the right to close it).
* `isUdpCore F γu t γ N id n` (persistent): a started transport's fixed fields (endpoint, node, stats,
  stop channel), as TCP's `isTransportCore`; `isUdpPeers F t`: its peers, each with its queue, a bag of
  `qElem F pid` (TCP's queue element: the message with its fact).
* `ownReassembler F γu r` (exclusive, the receiver's): the reassembler's maps; every chunk held in a
  message in progress is the chunk of the body recorded under the message's name (`ownPartial`).
* `recvElem F id x`: a message completed, queued to its sender's stepper: what `Node.stepPeer` takes.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TransportDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpWire
public import KvNet.Proof.net.UdpBase
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

/-- A message's name: its sender, its process's boot number, its sequence number there. -/
abbrev MsgKey := w64 × w64 × w64

/-- kvudp's ghost names (see the file header). -/
structure UdpNames where
  msgs : GName
  toks : GName
  ctrs : GName
  his : GName

/-- The names' invariant's namespace. -/
def udpMsgN : Namespace := nroot .@ "kvudp" .@ "msgs"
/-- The addresses' invariants' namespace (one namespace: no proof opens two at once). -/
def udpSentN : Namespace := nroot .@ "kvudp" .@ "sent"

/-- **The names' facts** (see the file header). -/
def UdpMsgOk (M : GMap MsgKey (List w8)) (T : GMap MsgKey Bool) (C : GMap (w64 × w64) w64)
    (H : GMap w64 w64) : Prop :=
  (∀ k : MsgKey, ((M !! k).isSome ∨ (T !! k).isSome) →
    ∃ c, C !! (k.1, k.2.1) = some c ∧ uint.nat k.2.2 ≤ uint.nat c) ∧
  (∀ k : MsgKey, (T !! k).isSome → M !! k = none) ∧
  (∀ (fb : w64 × w64) (c : w64), C !! fb = some c →
    ∃ hi, H !! fb.1 = some hi ∧ uint.nat fb.2 ≤ uint.nat hi)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

/-! ## The ghost state -/

/-- The message named `k` is `body` (persistent). -/
def udpMsgAt (γu : UdpNames) (k : MsgKey) (body : List w8) : IProp GF :=
  ghostMapElem γu.msgs k DFrac.discard body

/-- The right to record the name `k`, once (exclusive). -/
def udpSeqTok (γu : UdpNames) (k : MsgKey) : IProp GF :=
  ghostMapElem γu.toks k (DFrac.own 1) true

/-- The process `(f, b)` has used its sequence numbers up to `c` (exclusive). -/
def udpCtr (γu : UdpNames) (f b c : w64) : IProp GF :=
  ghostMapElem γu.ctrs ((f, b) : w64 × w64) (DFrac.own 1) c

/-- Replica `f`'s boot numbers handed out are at most `hi` (exclusive). -/
def udpHi (γu : UdpNames) (f hi : w64) : IProp GF :=
  ghostMapElem γu.his f (DFrac.own 1) hi

instance udpMsgAt_persistent γu k body : Persistent (udpMsgAt (GF := GF) γu k body) := by
  unfold udpMsgAt; infer_instance

/-- **The names' invariant** (see the file header). -/
def udpMsgInv (γu : UdpNames) : IProp GF :=
  inv udpMsgN iprop(∃ (M : GMap MsgKey (List w8)) (T : GMap MsgKey Bool) (C : GMap (w64 × w64) w64)
      (H : GMap w64 w64),
    ghostMapAuth γu.msgs 1 M ∗ ghostMapAuth γu.toks 1 T ∗ ghostMapAuth γu.ctrs 1 C ∗
    ghostMapAuth γu.his 1 H ∗ ⌜UdpMsgOk M T C H⌝)

instance udpMsgInv_persistent γu : Persistent (udpMsgInv (GF := GF) γu) := by
  unfold udpMsgInv; infer_instance

/-! ## The datagram protocol -/

/-- A message body: a message's encoding (`putMsg`'s), with its fact. -/
def udpBodyOk (F : KvFacts GF) (body : List w8) : IProp GF :=
  iprop(∃ (src : w64) (st : MsgSt), ⌜body = encMsg st ∧ body.length < 2 ^ 63⌝ ∗ F.msgOk src st)

instance udpBodyOk_persistent F body : Persistent (udpBodyOk (GF := GF) F body) := by
  unfold udpBodyOk; infer_instance

/-- A fragment's fact: it is a chunk of the body recorded under its name. -/
def udpFragOk (F : KvFacts GF) (γu : UdpNames) (dg : DgM) : IProp GF :=
  iprop(∃ body, udpMsgAt γu dg.key body ∗ udpBodyOk F body ∗ ⌜FragOf body dg⌝)

instance udpFragOk_persistent F γu dg : Persistent (udpFragOk (GF := GF) F γu dg) := by
  unfold udpFragOk; infer_instance

/-- The fact of a parsed datagram: none for an ack, `udpFragOk` for a fragment. -/
def udpDgMOk (F : KvFacts GF) (γu : UdpNames) (dg : DgM) : IProp GF :=
  iprop(⌜dg.kind = kindAckB⌝ ∨ (⌜dg.kind = kindFragmentB⌝ ∗ udpFragOk F γu dg))

instance udpDgMOk_persistent F γu dg : Persistent (udpDgMOk (GF := GF) F γu dg) := by
  unfold udpDgMOk; infer_instance

/-- **A datagram of the protocol** (see the file header): it parses, with its fact. -/
def udpDgOk (F : KvFacts GF) (γu : UdpNames) (d : List w8) : IProp GF :=
  iprop(∃ dg, ⌜parseDg d = some dg⌝ ∗ udpDgMOk F γu dg)

instance udpDgOk_persistent F γu d : Persistent (udpDgOk (GF := GF) F γu d) := by
  unfold udpDgOk; infer_instance

/-- **The datagrams sent to the address `a`** (see the file header). -/
def udpAddrInv (F : KvFacts GF) (γu : UdpNames) (a : GoString) : IProp GF :=
  inv udpSentN iprop(∃ ms, udpSent (extGlobalGS udpExt (G := hG.goose_globalGS)) a ms ∗
    [∗list] d ∈ ms, udpDgOk F γu d)

instance udpAddrInv_persistent F γu a : Persistent (udpAddrInv (GF := GF) F γu a) := by
  unfold udpAddrInv; infer_instance

/-- **What a cluster's UDP side starts from, for every process** (persistent): the names' invariant,
and every valid address of the address map `M` with its invariant (`openUDP`'s; `udpNet.newTransport`
needs nothing per address: the endpoint has them). -/
def udpAddrsInv (F : KvFacts GF) (γu : UdpNames) (M : GMap w64 GoString) : IProp GF :=
  iprop(udpMsgInv γu ∗ □ ∀ (pid : w64) (a : GoString), ⌜M !! pid = some a ∧ addrOk a = true⌝ -∗
    udpAddrInv F γu a)

instance udpAddrsInv_persistent F γu M : Persistent (udpAddrsInv (GF := GF) F γu M) := by
  unfold udpAddrsInv; infer_instance

/-! ## The endpoint (`udpNet`) -/

/-- A replica's `*UDPAddr` in the endpoint's map: a valid address, with its invariant. -/
def isUdpPeerAddr (F : KvFacts GF) (γu : UdpNames) (p : Loc) : IProp GF :=
  iprop(∃ (ip : List w8) (port : w64) (a : GoString), net.udpAddrAt p ip port ∗
    ⌜ValidDest ip port a⌝ ∗ udpAddrInv F γu a)

instance isUdpPeerAddr_persistent F γu p : Persistent (isUdpPeerAddr (GF := GF) F γu p) := by
  unfold isUdpPeerAddr; infer_instance

/-- A snapshot waiting for its ack (`ackWait`), as the endpoint's map holds it: its receiver, its
channel and the right to close it (`acked`'s). -/
def ackWaitOwn (w : Loc) : IProp GF :=
  iprop(∃ (to : w64) (ch : Loc) (γch : ChanNames),
    w.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ackWait, go!"to"] ↦□ to ∗
    w.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ackWait, go!"done"] ↦□ ch ∗
    ownBroadcastChan ch γch iprop(True) .Pending)

/-- **The endpoint's mutex's invariant**: the last sequence number used, with the process's ghost
counter, and the snapshot waiters. -/
def udpNetLockInv (γu : UdpNames) (u : Loc) (id boot : w64) : IProp GF :=
  iprop(∃ (sq : w64) (km : Loc) (K : GMap w64 Loc),
    u.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet, go!"seq"] ↦ sq ∗ udpCtr γu id boot sq ∗
    u.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet, go!"acks"] ↦ km ∗ km ↦$ K ∗
    [∗map] _s ↦ w ∈ K, ackWaitOwn w)

/-- **The process's endpoint** `u` of replica `id`, boot number `boot` (see the file header). -/
def isUdpNet (F : KvFacts GF) (γu : UdpNames) (u : Loc) (id boot : w64) : IProp GF :=
  iprop(∃ (c : Loc) (s : w64) (a : GoString) (am : Loc) (A : GMap w64 Loc),
    u.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet, go!"id"] ↦□ id ∗
    u.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet, go!"conn"] ↦□ c ∗
    net.udpConnAt c s a ∗ udpAddrInv F γu a ∗
    u.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet, go!"addrs"] ↦□ am ∗ am ↦$□ A ∗
    ([∗map] _pid ↦ p ∈ A, isUdpPeerAddr F γu p) ∗
    u.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet, go!"boot"] ↦□ boot ∗
    udpMsgInv γu ∗
    sync.isMutex (u.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet, go!"mu"])
      (udpNetLockInv γu u id boot))

instance isUdpNet_persistent F γu u id boot : Persistent (isUdpNet (GF := GF) F γu u id boot) := by
  unfold isUdpNet; infer_instance

/-- Datagrams to send (`writeAll`'s `ds`, `fragments`' result made read-only): each a byte slice
(read-only) of the protocol. -/
def udpDgsOk (F : KvFacts GF) (γu : UdpNames) (ds : List GoSlice) : IProp GF :=
  iprop([∗list] d ∈ ds, ∃ bs : List w8, d ↦*□ bs ∗ udpDgOk F γu bs)

instance udpDgsOk_persistent F γu ds : Persistent (udpDgsOk (GF := GF) F γu ds) := by
  unfold udpDgsOk; infer_instance

/-! ## The transport (`udpTransport`) -/

/-- A peer's sender `p`, its id and its queue (a bag of TCP's `qElem F pid`). -/
def isUdpPeer (F : KvFacts GF) (p : Loc) (pid : w64) : IProp GF :=
  iprop(p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpPeer, go!"id"] ↦□ pid ∗
    ∃ (ch : Loc) (γq : ChanNames),
      p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpPeer, go!"queue"] ↦□ ch ∗
      isChanBag (V := Loc) γq ch (qElem F pid))

instance isUdpPeer_persistent F p pid : Persistent (isUdpPeer (GF := GF) F p pid) := by
  unfold isUdpPeer; infer_instance

/-- The transport's peers map, read-only. -/
def isUdpPeers (F : KvFacts GF) (t : Loc) : IProp GF :=
  iprop(∃ (pm : Loc) (M : GMap w64 Loc),
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport, go!"peers"] ↦□ pm ∗
    pm ↦$□ M ∗ [∗map] pid ↦ p ∈ M, isUdpPeer F p pid)

instance isUdpPeers_persistent F t : Persistent (isUdpPeers (GF := GF) F t) := by
  unfold isUdpPeers; infer_instance

/-- The transport's endpoint and stop channel (set by `newTransport`). -/
def isUdpBase (F : KvFacts GF) (γu : UdpNames) (t : Loc) (id : w64) (sc : Loc) (γsc : ChanNames) :
    IProp GF :=
  iprop(∃ (u : Loc) (boot : w64) (sts : Loc),
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport, go!"u"] ↦□ u ∗
    isUdpNet F γu u id boot ∗
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport, go!"stats"] ↦□ sts ∗
    isStats sts ∗
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport, go!"stopc"] ↦□ sc ∗
    ownBroadcastChan sc γsc iprop(True) .Unknown ∗ isUdpPeers F t)

instance isUdpBase_persistent F γu t id sc γsc :
    Persistent (isUdpBase (GF := GF) F γu t id sc γsc) := by
  unfold isUdpBase; infer_instance

/-- **A started transport** `t` of replica `id` on the node `n` (see the file header). -/
def isUdpCore (F : KvFacts GF) (γu : UdpNames) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64)
    (n : NodeH) : IProp GF :=
  iprop(∃ (sc : Loc) (γsc : ChanNames), isUdpBase F γu t id sc γsc ∗
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport, go!"node"] ↦□
      interface.mkOk (go.GoType.PointerType node.ty) #n.loc ∗
    isNode n γ N id ∗ ⌜Cluster.trace γ = none⌝)

instance isUdpCore_persistent F γu t γ N id n : Persistent (isUdpCore (GF := GF) F γu t γ N id n) := by
  unfold isUdpCore; infer_instance

/-! ## The receiving side -/

/-- A chunk of a message in progress, at index `i` of `n` chunks: none yet (nil), or the chunk of the
body recorded under the message's name `k`. -/
def chunkSlot (F : KvFacts GF) (γu : UdpNames) (k : MsgKey) (n i : Nat) (c : GoSlice) : IProp GF :=
  iprop(⌜c = slice.nil⌝ ∨ ∃ (bs : List w8) (body : List w8), c ↦* bs ∗ udpMsgAt γu k body ∗
    udpBodyOk F body ∗ ⌜nChunks body = n ∧ bs = chunkAt body i⌝)

/-- **A message in progress** `p`, of the sender `src` (see the file header): its name, its chunks
(`have` of them arrived). -/
def ownPartial (F : KvFacts GF) (γu : UdpNames) (src : w64) (p : Loc) : IProp GF :=
  iprop(∃ (id : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.msgID) (cs : GoSlice)
      (chs : List GoSlice) (hv tp : w32) (got : List Bool),
    p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.«partial», go!"id"] ↦ id ∗
    p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.«partial», go!"chunks"] ↦ cs ∗
    p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.«partial», go!"have"] ↦ hv ∗
    p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.«partial», go!"top"] ↦ tp ∗
    cs ↦* chs ∗ ⌜got.length = chs.length ∧ uint.nat hv = (got.filter id).length⌝ ∗
    [∗list] i ↦ c ∈ chs,
      chunkSlot F γu (src, id.boot', id.seq') chs.length i c ∗ ⌜(got[i]? = some true) ↔ c ≠ slice.nil⌝)

/-- **The reassembler** `r`, the receiver's (see the file header). -/
def ownReassembler (F : KvFacts GF) (γu : UdpNames) (r : Loc) : IProp GF :=
  iprop(∃ (pm dm lm sts : Loc) (P D : GMap w64 GoSlice)
      (Ls : GMap w64 github_com.mit_pdos.etcd_grove.examples.raft.kvnet.msgID),
    r.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.reassembler, go!"pending"] ↦□ pm ∗
    r.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.reassembler, go!"done"] ↦□ dm ∗
    r.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.reassembler, go!"last"] ↦□ lm ∗
    r.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.reassembler, go!"stats"] ↦□ sts ∗
    isStats sts ∗ pm ↦$ P ∗ dm ↦$ D ∗ lm ↦$ Ls ∗
    ([∗map] src ↦ sl ∈ P, ∃ ps : List Loc, sl ↦* ps ∗ ownSliceCap Loc sl (DFrac.own 1) ∗
      [∗list] p ∈ ps, ownPartial F γu src p) ∗
    ([∗map] _src ↦ sl ∈ D, ∃ ds : List github_com.mit_pdos.etcd_grove.examples.raft.kvnet.doneMsg,
      sl ↦* ds ∗ ownSliceCap github_com.mit_pdos.etcd_grove.examples.raft.kvnet.doneMsg sl (DFrac.own 1)))

/-- A fragment as `getDatagram` returns it, owned: the Go struct `d` holds the model `dg`, its chunk
slice (owned) holding `dg.chunk`. -/
def dgOwn (d : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.datagram) (dg : DgM) : IProp GF :=
  iprop(⌜d.kind' = dg.kind ∧ d.from' = dg.src ∧ d.to' = dg.dst ∧ d.boot' = dg.boot ∧ d.seq' = dg.seq ∧
      d.index' = dg.index ∧ d.total' = dg.total⌝ ∗ d.chunk' ↦* dg.chunk)

/-- **A message completed, queued to its sender's stepper** (`received`): owned, read back by
`getMsg`, addressed to `id`, with its fact: what `Node.stepPeer` takes. -/
def recvElem (F : KvFacts GF) (id : w64) (x : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.received) :
    IProp GF :=
  iprop(∃ (src : w64) (st : MsgSt),
    msgPtsC x.m' (DFrac.own 1) (DFrac.own 1) true { st with resps := [] } ∗ F.msgOk src st ∗
    ⌜st.msg.To' = id⌝)

end defs

/-- `received` is countable (a channel's element type: `isChanBag`'s). -/
instance received_countable [GooseExts] :
    Pos.Countable github_com.mit_pdos.etcd_grove.examples.raft.kvnet.received :=
  Pos.Countable.ofInjective (fun x => Pos.Countable.encode (x.m', x.from', x.boot', x.seq', x.snap'))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h; subst h1 h2 h3 h4 h5; rfl)

end raft_kvnet
end EtcdGrove
end Perennial
