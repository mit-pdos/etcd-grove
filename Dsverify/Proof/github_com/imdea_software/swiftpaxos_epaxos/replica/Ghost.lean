/-
The replica framework's internal ghost structure (package-internal; `notes/prove-replica.md`).

* **Names.** The framework's own names `FwNames` (the lock's keys for the peer cells and the
  readers slice, the two deposit phases) are fixed once per replica at `γ.rep.dials id id`
  (`fwNames`, persistent, agreeing): the replica's own dial variable, which `peerConn` never uses
  (`peerConn γ i i _` carries `i < i`), handed to the replica with `dialTok γ id id`
  (HUB-REQUEST 1).
* **Deposits.** While `ConnectToPeers` dials, the peer cells (`Peers`, `PeerWriters`, `Alive`,
  `Latencies` and the slots) are owned outside `r.M` (the dial loop's indices below `id`, the
  listener goroutine's above), then deposited in an invariant (`depInv`) when dialing is done
  (phase 1); `PeerReaders` likewise once the reader goroutines are started (`rdepInv`, phase 2).
  `r.M`'s `fwCore` holds each part or its key; a lock holder that knows the phase trades the key
  for the part (`fwCore_peers_acc`, `fwCore_readers_acc`, in `Epaxos/Interface/Replica.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Registry
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.RpcTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.ConnBuf

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The framework's internal names: the key of the peer cells, the key of the readers slice,
the phase of the peer deposit, the phase of the readers deposit. -/
abbrev FwNames := GName × GName × GName × GName

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- Replica `id`'s framework names are `ns` (persistent, agreeing). -/
def fwNames (γ : EpNames) (id : Nat) (ns : FwNames) : IProp GF :=
  dghostVar (A := Option FwNames) (γ.rep.dials id id) DFrac.discard (some ns)

instance fwNames_persistent (γ : EpNames) (id : Nat) (ns : FwNames) :
    Persistent (fwNames (GF := GF) γ id ns) := by unfold fwNames; infer_instance
instance fwNames_timeless (γ : EpNames) (id : Nat) (ns : FwNames) :
    Timeless (fwNames (GF := GF) γ id ns) := by unfold fwNames; infer_instance

theorem fwNames_agree (γ : EpNames) (id : Nat) (ns ns' : FwNames) :
    fwNames (GF := GF) γ id ns -∗ fwNames γ id ns' -∗ ⌜ns = ns'⌝ := by
  unfold fwNames
  iintro H1 H2
  ihave %H := dghostVar_agree $$ H1 H2
  ipureintro; exact Option.some.inj H

/-- Fix the framework's names, from the replica's own dial token. -/
theorem dialTok_fwNames (γ : EpNames) (id : Nat) (ns : FwNames) :
    dialTok (GF := GF) γ id id ==∗ fwNames γ id ns := by
  rw [dialTok_unseal]; unfold dialTokDef fwNames dghostVar
  iintro H
  haveI : CMRA.Exclusive (DFracAgree.mk (DFrac.own (1 : Qp)) (encodeO (none : Option w64))) :=
    DFracAgree.mk_exclusive
  imod own_update _ _ (DFracAgree.mk (DFrac.own 1) (encodeO (some ns)))
    (.exclusive (DFracAgree.mk_valid.mpr DFrac.valid_own_one)) $$ H with H
  iapply own_update _ _ _ DFracAgree.persist $$ H

/-- A half gives the index facts of all its list. -/
theorem sentHalf_all (γ : EpNames) (f t : Nat) (ms : List Msg) :
    sentHalf (GF := GF) γ f t ms ⊢ sentHalf γ f t ms ∗ [∗list] k ↦ m ∈ ms, msgSent γ f t k m := by
  rw [sentHalf_unseal, msgSent_unseal]; unfold sentHalfDef msgSentDef
  iintro H
  ihave #Hlb := monoListLbOwn_get $$ H
  iframe H
  iapply (BigSepL.bigSepL_intro (P := iprop(□ monoListLbOwn (GF := GF) (γ.rep.sent f t) ms))
    (fun k m hk => by
      iintro #H
      iapply monoListIdxOwn_get k m hk $$ H))
  iexact Hlb

/-- A phase variable at `n` (half, or discarded). -/
abbrev phaseHalf (γp : GName) (n : Nat) : IProp GF :=
  dghostVar γp (DFrac.own (1 : Qp).half) n
abbrev phaseDone (γp : GName) : IProp GF :=
  dghostVar γp DFrac.discard (1 : Nat)

/-- Phase 1 (the peer cells deposited) of replica `id`'s framework (persistent). -/
def fwPhase1 (γ : EpNames) (id : Nat) : IProp GF :=
  iprop(∃ ns : FwNames, fwNames γ id ns ∗ phaseDone ns.2.2.1)

/-- Phase 2 (the readers slice deposited) (persistent). -/
def fwPhase2 (γ : EpNames) (id : Nat) : IProp GF :=
  iprop(∃ ns : FwNames, fwNames γ id ns ∗ phaseDone ns.2.2.2)

instance fwPhase1_persistent (γ : EpNames) (id : Nat) : Persistent (fwPhase1 (GF := GF) γ id) := by
  unfold fwPhase1; infer_instance
instance fwPhase2_persistent (γ : EpNames) (id : Nat) : Persistent (fwPhase2 (GF := GF) γ id) := by
  unfold fwPhase2; infer_instance

/-- The namespace of the framework's deposits (under the framework's `fwN = epN.replica`). -/
def fwDepN : Namespace := ndot (ndot epN "replica") "dep"

/-- A deposit of `P` with key `γk` and phase `γp`: before the phase, its half at 0 (the depositor
holds the other); after it, `P` or the key (the lock holder that took `P` left its key). -/
def depInv (γk γp : GName) (P : IProp GF) : IProp GF :=
  iprop(phaseHalf γp 0 ∨ (phaseDone γp ∗ (P ∨ token γk)))

/-- A deposit, allocated: the depositor's half and the lock's key. -/
theorem dep_alloc (P : IProp GF) (E : CoPset) :
    ⊢ |={E}=> ∃ γk γp, inv fwDepN (depInv γk γp P) ∗ phaseHalf γp 0 ∗ token γk := by
  imod token_alloc (GF := GF) with ⟨%γk, Hk⟩
  imod dghostVar_alloc (GF := GF) (0 : Nat) with ⟨%γp, Hp⟩
  icases dghostVar_split γp (0 : Nat) (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) $$ [Hp]
    with ⟨Hp1, Hp2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hp
  imod inv_alloc fwDepN E (depInv γk γp P) $$ [Hp1] with #Hi
  · inext; unfold depInv; ileft; iexact Hp1
  imodintro
  iexists γk, γp
  iframe
  iexact Hi

/-- The depositor deposits `P`: the phase is done (persistent). -/
theorem dep_deposit (γk γp : GName) (P : IProp GF) (E : CoPset) (hE : ↑fwDepN ⊆ E) :
    ⊢ inv fwDepN (depInv γk γp P) -∗ phaseHalf γp 0 -∗ P ={E}=∗ phaseDone γp := by
  iintro #Hi Hh HP
  iinv Hi with Hd Hclose
  unfold depInv
  icases Hd with (>Hh' | ⟨>#Hd, _⟩)
  · icombine Hh Hh' as Hp
    imod dghostVar_update (1 : Nat) γp (0 : Nat) $$ [Hp] with Hp
    · iexact Hp
    imod dghostVar_persist $$ Hp with #Hp
    imod Hclose $$ [HP] with -
    · inext; iright; iframe Hp; ileft; iexact HP
    imodintro; iexact Hp
  · icombine Hh Hd gives %H
    exact absurd H.2 (by decide)

/-- After the phase, a lock holder trades the key (or `P` itself) for `P`. -/
theorem dep_take (γk γp : GName) (P : IProp GF) (E : CoPset) (hE : ↑fwDepN ⊆ E) :
    ⊢ inv fwDepN (depInv γk γp P) -∗ phaseDone γp -∗ (P ∨ token γk) -∗ £ 1 ={E}=∗ P := by
  iintro #Hi #Hd HP Hlc
  icases HP with (HP | Hk)
  · imodintro; iexact HP
  iinv Hi with Hc Hclose
  imod lc_fupd_elim_later (E := E \ ↑fwDepN) $$ Hlc Hc with Hc
  unfold depInv
  icases Hc with (Hh | ⟨_, (HP | Hk')⟩)
  · icombine Hh Hd gives %H
    exact absurd H.2 (by decide)
  · imod Hclose $$ [Hk] with -
    · inext; iright; iframe Hd; iright; iexact Hk
    imodintro; iexact HP
  · iexfalso; iapply token_exclusive $$ Hk Hk'

end ghost

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

/-- The protocol replica `id` writes with on its connection with peer `j` (`peerP`). -/
def peerPX (γ : EpNames) (id : Nat) (L : List GoString) (j : Nat) (side : Bool) :
    Proto GF :=
  if side then repAccP γ (L.getD id []) else repDialP γ (L.getD j [])

/-- The protocol replica `id` reads with on its connection with peer `j`. -/
def peerPin (γ : EpNames) (id : Nat) (L : List GoString) (j : Nat) (side : Bool) :
    Proto GF :=
  if side then repDialP γ (L.getD id []) else repAccP γ (L.getD j [])

theorem peerPX_ppc (γ : EpNames) (id : Nat) (L : List GoString) (j : Nat) (side : Bool) :
    ProtoPrefixClosed (peerPX (GF := GF) γ id L j side) := by
  unfold peerPX; split
  · exact repAccP_ppc γ _
  · exact repDialP_ppc γ _

/-- The end `side` of connection `cid` is the `*TCPConn` in `c` (`net.connAt`, some addresses),
with `ErrDeadlineExceeded`'s and `io.EOF`'s values (its errors' evidence). -/
def connIn (c : GoInterface) (cid : Nat) (side : Bool) (t : Loc) (la ra ed eof : GoInterface) :
    IProp GF :=
  iprop(⌜c = interface.ok (net.connIface t)⌝ ∗ (∃ a : GoString, net.connAt t cid side a la ra) ∗
    globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ globalAddr io.EOF ↦□ eof)

instance connIn_persistent (c : GoInterface) (cid : Nat) (side : Bool) (t : Loc)
    (la ra ed eof : GoInterface) : Persistent (connIn (GF := GF) c cid side t la ra ed eof) := by
  unfold connIn; infer_instance

/-- The dialer of a connection between `id` and `j` at end `side` of `id`. -/
abbrev dialerOf (id j : Nat) (side : Bool) : Nat := if side then j else id

/-- Peer `j`'s connection `c` (`cid`, end `side`) at replica `id`, with its writer `w` and the
framework's sent list `ms` (`peerSlot`'s connected arm), and, for an accepted connection, the
acceptor's fresh token (a second acceptance of the same connection is refuted), and the
connection's role (what the writer's protocol needs for the stream's next messages). -/
def slotConn (γ : EpNames) (id : Nat) (L : List GoString) (j : Nat) (c : GoInterface) (w : Loc)
    (ms : List Msg) (cid : Nat) (side : Bool) : IProp GF :=
  iprop(∃ (sent pend : List w8) (err : GoInterface) (ws : List Msg) (t : Loc)
      (la ra ed eof : GoInterface),
    connIn c cid side t la ra ed eof ∗
    peerConn γ (if side then j else id) (if side then id else j) cid ∗
    roleElem γ cid (.peer (W64 (dialerOf id j side))) ∗
    wrOwn w (connWr t cid side la ra ed (peerPX γ id L j side) (peerPX_ppc γ id L j side) 4096)
      sent pend err ∗
    ⌜protoMsgs ws = ms ∧ (∀ m ∈ ws, m.wf) ∧ (err = interface.nil →
      sent ++ pend = streamHdr (if side then j else id) side ++ ws.flatMap encMsg)⌝ ∗
    (if side then connFresh cid true else iprop(True)))

/-- What only the reader goroutine of peer `j` at replica `id` uses (and only one is ever
started: `j` has at most one connection to `id`): the right to mint the delivery tokens of `j`'s
stream from 0, and the cell `Ewma[j]` (`ew` the slice `Ewma`; written without `r.M` by that
reader only). -/
def lisStart (γ : EpNames) (id : Nat) (ew : GoSlice) (j : Nat) : IProp GF :=
  iprop(delivFrom γ id j 0 ∗ ⌜(j : Int) < sint.Z ew.len⌝ ∗
    ∃ v : w64, typedPointsto (sliceIndexRef w64 (j : Int) ew) v (DFrac.own 1))

/-- Peer `j`'s slot at replica `id` (the body of `fwCore`'s slots): `peerSlot`, with the
acceptor's fresh token of an accepted connection, and the reader's start resources until a
connection is installed. -/
def peerSlotX (γ : EpNames) (id : Nat) (L : List GoString) (ew : GoSlice) (j : Nat) (c : GoInterface)
    (w : Loc) : IProp GF :=
  iprop(∃ ms : List Msg, sentHalf γ id j ms ∗
    ((⌜w = null⌝ ∗ ⌜id < j → c = interface.nil⌝ ∗ ⌜ms = []⌝ ∗ lisStart γ id ew j) ∨
      ∃ (cid : Nat) (side : Bool), slotConn γ id L j c w ms cid side))

/-- What the reader goroutine of peer `j`'s connection (`cid`, end `side`) at replica `id`
starts from: the connection's role, its reader `rd` past the header of the stream it reads
(written by the other end), the right to mint the delivery tokens, `Ewma[j]`. -/
def lisRes (γ : EpNames) (id : Nat) (L : List GoString) (ew : GoSlice) (j : Nat) (c : GoInterface)
    (cid : Nat) (side : Bool) (rd : Loc) : IProp GF :=
  iprop(∃ (t : Loc) (la ra ed eof : GoInterface), connIn c cid side t la ra ed eof ∗
    ⌜if side then id < j else j < id⌝ ∗
    roleElem γ cid (.peer (W64 (dialerOf id j side))) ∗
    rdOwn rd (connRd t cid side eof la ra ed (peerPin γ id L j side))
      (streamHdr (dialerOf id j side) (!side)) ∗
    lisStart γ id ew j)

/-- Peer `j`'s slot while connecting (before the readers are started): `peerSlotX`, and, once
connected, the reader's resources. -/
def pendSlot (γ : EpNames) (id : Nat) (L : List GoString) (ew : GoSlice) (j : Nat) (c : GoInterface)
    (rd w : Loc) : IProp GF :=
  iprop(∃ ms : List Msg, sentHalf γ id j ms ∗
    ((⌜w = null ∧ rd = null⌝ ∗ ⌜id < j → c = interface.nil⌝ ∗ ⌜ms = []⌝ ∗ lisStart γ id ew j) ∨
      ∃ (cid : Nat) (side : Bool), slotConn γ id L j c w ms cid side ∗
        lisRes γ id L ew j c cid side rd))

/-- The peer cells of replica `id` (whole slices `Peers`, `PeerWriters`, `Alive`, `Latencies`)
and the slots (`ew` is `Ewma`, whose cells the slots hold until their readers start). -/
def fwPeers (γ : EpNames) (id : Nat) (L : List GoString) (peers writers alive lat ew : GoSlice) :
    IProp GF :=
  iprop(∃ (cs : List GoInterface) (ws : List Loc) (als : List Bool) (ls : List w64),
    peers ↦* cs ∗ writers ↦* ws ∗ alive ↦* als ∗ lat ↦* ls ∗
    ⌜cs.length = L.length ∧ ws.length = L.length ∧ als.length = L.length ∧
      ls.length = L.length⌝ ∗
    [∗list] j ∈ List.range L.length, if j = id then iprop(True) else
      peerSlotX γ id L ew j (cs.getD j interface.nil) (ws.getD j null))

/-- Replica `id`'s client writer `w` of connection `cid` (the body of `fwCore`'s client writers):
`clientSlot`, with the connection's role (a client op's: what the reply's protocol needs). -/
def clientSlotX (γ : EpNames) (id : Nat) (L : List GoString) (w : Loc) (cid : Nat) :
    IProp GF :=
  iprop(∃ (c : GoInterface) (sent pend : List w8) (err : GoInterface) (t : Loc)
      (la ra ed eof : GoInterface),
    connIn c cid true t la ra ed eof ∗
    wrOwn w (connWr t cid true la ra ed (repAccP γ (L.getD id [])) (repAccP_ppc γ _) 4096)
      sent pend err ∗
    (⌜sent ++ pend = []⌝ ∨ ghostMapElem (γ.rep.replies id) w (DFrac.own 1) ()) ∗
    ∃ (cl : w64) (i : KvI), roleElem γ cid (.client cl i))

/-- The readers slice. -/
def fwReaders (L : List GoString) (readers : GoSlice) : IProp GF :=
  iprop(∃ rs : List Loc, readers ↦* rs ∗ ⌜rs.length = L.length⌝)

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
