/-
kvnet's server side (`transport.go`, `node.go`), its vocabulary over the wire protocol
(`Proto.lean`, `notes/kvnet-protocol.md`): what a replica's transport, node and stats are, for
the specs of `Transport.*`, `Node.serve`/`serveClient`/`handle`.

* `isStats s` (persistent): the counters' mutex, guarding the array (`Stats.add` increments one).
* `isPeerAddr F p pid` (persistent): a peer's sender `p`: its id `pid`, its address, valid, with the
  address's protocols (`addrProto a (kvP F pid) (kvQ F pid)`), its queue channel.
* `stepLaw F γ N id` (persistent), **the seam to raft's message layer**: a message a peer frame
  carried (`F.msgOk src st`, `MsgWf`), read back by `getMsg` (`msgPtsC … { st with resps := [] }`)
  and addressed to `id`, is one `node.Step` takes (`stepIn`). Its proof is raft's `stepIn_intro`
  (with `msgCredits`, `snapLocalMsg`, the sent token) at `F`'s instance, after decision B.
* `isTransportCore F t γ N id n` (persistent): the transport's id, its node (`isNode n γ N id`, the
  interface over `*node` at `n`, untraced: `node.ReportSnapshot`'s premise), its stats, and its stop channel (2026-11-24, G5: `stop` closes it,
  the senders return; `isTransportStop`, whose closer `transportStopper` `newTransport` gives).
* `qElem F pid m` (the peer queue's element, `Transport.enqueue`/`runPeer`): a message for the peer
  `pid` (`msgPtsC`, at any fractions), with its fact `F.msgOk src st` and a length a frame can carry:
  what `runPeer` needs for `putMsg`, `peer_send` and `writeFrame`, and `dropped` for the message.
  The queue is a bag channel of them (`isChanBag`, Perennial's idiom: no order, never closed).
* `isPeer F p pid a` (persistent): `isPeerAddr` and the queue's channel, a bag of `qElem F pid`.
* `isPeers F t` (persistent): the transport's peers map, read-only, each value a peer (`isPeer`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Proto
public import KvNet.Proof.go_etcd_io.raft.v3.InvNode
public import KvNet.Proof.go_etcd_io.raft.v3.InvPb
public import Perennial.Proof.sync
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- The counters, guarded by their mutex. -/
def statsInv (s : Loc) : IProp GF :=
  iprop(∃ a : GoArray w64 24,
    s.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats, go!"c"] ↦ a)

/-- A stats object: its mutex (see the file header). -/
def isStats (s : Loc) : IProp GF :=
  sync.isMutex (s.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats, go!"mu"]) (statsInv s)

instance isStats_persistent (s : Loc) : Persistent (isStats (GF := GF) s) := by
  unfold isStats; infer_instance

/-- **The step law** (see the file header): the seam to raft's message layer. -/
def stepLaw (F : KvFacts GF) (γ : Cluster) (N : Namespace) (id : w64) : IProp GF :=
  iprop(□ ∀ (src : w64) (st : MsgSt) (ml : Loc), ⌜st.msg.To' = id⌝ -∗ F.msgOk src st -∗
    msgPtsC ml (DFrac.own 1) (DFrac.own 1) true { st with resps := [] } ={⊤}=∗ stepIn γ N id ml)

instance stepLaw_persistent F γ N id : Persistent (stepLaw (GF := GF) F γ N id) := by
  unfold stepLaw; infer_instance

/-- The transport's stop channel `sc` (named `γsc`), closed by `stop` (persistent). -/
def isTransportStop (t : Loc) (sc : Loc) (γsc : ChanNames) : IProp GF :=
  iprop(t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport, go!"stopc"] ↦□ sc ∗
    ownBroadcastChan sc γsc iprop(True) .Unknown)

instance isTransportStop_persistent t sc γsc : Persistent (isTransportStop (GF := GF) t sc γsc) := by
  unfold isTransportStop; infer_instance

/-- The right to close the transport's stop channel, once (exclusive): `stop`'s. -/
def transportStopper (sc : Loc) (γsc : ChanNames) : IProp GF :=
  ownBroadcastChan sc γsc iprop(True) .Pending

/-- The transport's fixed fields, its node and stats, and its stop channel (see the file header). -/
def isTransportCore (F : KvFacts GF) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH) :
    IProp GF :=
  iprop(∃ (sp sc : Loc) (γsc : ChanNames),
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport, go!"id"] ↦□ id ∗
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport, go!"node"] ↦□
      interface.mkOk (go.GoType.PointerType node.ty) #n.loc ∗
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport, go!"stats"] ↦□ sp ∗
    isStats sp ∗ isNode n γ N id ∗ ⌜Cluster.trace γ = none⌝ ∗ isTransportStop t sc γsc)

/-- A peer's sender `p` (see the file header): its id, its address with its protocols. -/
def isPeerAddr (F : KvFacts GF) (p : Loc) (pid : w64) (a : GoString) : IProp GF :=
  iprop(p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.peer, go!"id"] ↦□ pid ∗
    p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.peer, go!"addr"] ↦□ a ∗
    addrProto a (kvP F pid) (kvQ F pid) ∗ ⌜addrOk a = true⌝)

instance isPeerAddr_persistent F p pid a : Persistent (isPeerAddr (GF := GF) F p pid a) := by
  unfold isPeerAddr; infer_instance

instance isTransportCore_persistent F t γ N id n :
    Persistent (isTransportCore (GF := GF) F t γ N id n) := by
  unfold isTransportCore; infer_instance

/-! ## The server's accessors (the acceptor's end, `true`), from the library's laws -/

/-- Closes of an end of a library connection (`close_au`). -/
theorem cAcc_of_connIs (cn : Nat) (s : Bool) : connIs cn ⊢ cAcc (GF := GF) cn s := by
  iintro #Hc
  unfold cAcc
  imodintro
  imod close_au cn s $$ Hc with ⟨%st, %d, Hend, Hdir, Hcl⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %res %st' %d' %Ho Hend Hdir
  imod Hcl $$ %res %st' %d' %Ho Hend Hdir with -
  imodintro
  itrivial

/-- Reads at the end `s` of `cn`, after `R0` (`read_au`): `readFull`/`readFrame`'s accessor for the
reader predicate `fun got => recvTokL cn s P (R0 ++ got)`. -/
theorem rAcc_of_recvTokL (cn : Nat) (s : Bool) (P : Net.Proto GF) (R0 : List w8) :
    ⊢ rAcc (GF := GF) cn s (fun got => recvTokL cn s P (R0 ++ got)) := by
  unfold rAcc
  imodintro
  iintro %got %m Hg
  imod read_au cn s P (R0 ++ got) m $$ Hg with ⟨%st, %d, Hend, Hdir, Hcl⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %r %d' %Ho Hend Hdir
  imod Hcl $$ %r %d' %Ho Hend Hdir with ⟨H, -⟩
  imodintro
  rw [List.append_assoc]
  iexact H

/-- A queued message for the peer `pid` (see the file header). -/
def qElem (F : KvFacts GF) (pid : w64) (m : Loc) : IProp GF :=
  iprop(∃ (dq dqe : DFrac) (cap : Bool) (st : MsgSt) (src : w64),
    msgPtsC m dq dqe cap st ∗ F.msgOk src st ∗
    ⌜st.msg.To' = pid⌝)

/-- A peer's sender with its queue (see the file header). -/
def isPeer (F : KvFacts GF) (p : Loc) (pid : w64) (a : GoString) : IProp GF :=
  iprop(isPeerAddr F p pid a ∗ ∃ (ch : Loc) (γq : ChanNames),
    p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.peer, go!"queue"] ↦□ ch ∗
    isChanBag (V := Loc) γq ch (qElem F pid))

instance isPeer_persistent F p pid a : Persistent (isPeer (GF := GF) F p pid a) := by
  unfold isPeer; infer_instance

/-- The transport's peers (see the file header). -/
def isPeers (F : KvFacts GF) (t : Loc) : IProp GF :=
  iprop(∃ (pm : Loc) (M : GMap w64 Loc),
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport, go!"peers"] ↦□ pm ∗
    pm ↦$□ M ∗ [∗map] pid ↦ p ∈ M, ∃ a, isPeer F p pid a)

instance isPeers_persistent F t : Persistent (isPeers (GF := GF) F t) := by
  unfold isPeers; infer_instance

/-- A nonblocking send of `v` on a bag channel, with `P v` (the select's send case: it fires only
when the value fits in the buffer or a receiver waits). -/
theorem queue_nb_send_au {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (v : V) (Φ : IProp GF) :
    ⊢ isChanBag γ ch P -∗ P v -∗ Φ -∗ nonblockingSendAuInner γ v Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingSendAuInner
  iintro ⟨#Hch, #Hinv⟩ HP HΦ
  iapply ncfupd_of_fupd
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iexists s
  iframe Hoc0
  rcases s with buff | _ | _ | _ | _ | _ | _
  all_goals dsimp only
  case Buffered =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hi HP] with -
    · inext; iexists .Buffered (buff ++ [v])
      dsimp only
      iframe Hoc
      iapply BigSepL.bigSepL_append.2
      iframe Hi
      iapply BigSepL.bigSepL_singleton.2
      iexact HP
    imodintro
    iexact HΦ
  case RcvPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HP] with -
    · inext; iexists .SndCommit v; iframe
    imodintro
    iexact HΦ
  all_goals first | itrivial | (iexfalso; iexact Hi)

end defs

end raft_kvnet
end EtcdGrove
end Perennial
