/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/WaitPeers.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N1: `waitForPeerConnections(done)` (the accepting goroutine of `ConnectToPeers`)

Listens on the replica's port (retrying), then accepts connections until each higher peer has
connected (a peer's newest connection is kept; `connected` counts each peer once): a client's
handshake hands the connection to `serveClient` (its frozen spec); a peer's fills the peer's slot
(`slotOwn`, with the reader and writer bridges of `ConnLaws`). The listener and the slots go back
to `ConnectToPeers` through `done` (`doneRes`).
-/
module

public import Dsverify.Proof.gryff.Replica2.Specs
public import Dsverify.Proof.gryff.N.ConnLaws
public import Dsverify.Proof.gryff.N.ConnDefs
public import Dsverify.Proof.gryff.N.StrIndex
public import Dsverify.Proof.gryff.Server.LogErr
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.N.NetSpecs
public import Dsverify.Proof.gryff.Lib.ReadFullLt
public import Dsverify.Proof.gryff.Lib.NetAddr
public import Perennial.Proof.time.Link
public import Perennial.Proof.encoding.binary.Results

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.replica2

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [net.Assumptions] [net.FieldAssumptions] [nS : NetSpecs GF] [strA : StringsIndexHyp GF]


/-- The higher peers. -/
def above (k : Fin 3) : Fin 3 → Bool := fun j => decide (k < j)

/-- How many slots are filled. -/
def cnt (cs : Fin 3 → Bool) : Nat := (cs 0).toNat + (cs 1).toNat + (cs 2).toNat

/-- The accept loop's exit: every higher slot is filled. -/
theorem cnt_full (k : Fin 3) (cs : Fin 3 → Bool) (h : ∀ j, cs j = true → k < j)
    (hc : 3 ≤ k.val + 1 + cnt cs) : ∀ j, above k j = true → cs j = true := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  unfold cnt at hc
  intro j hj
  unfold above at hj
  simp only [decide_eq_true_eq] at hj
  obtain ⟨k, hk⟩ := k
  obtain ⟨j, hj3⟩ := j
  simp only [Fin.lt_def] at h0 h1 h2 hj
  rcases k with _ | _ | _ | k <;> rcases j with _ | _ | _ | j <;>
    cases e0 : cs 0 <;> cases e1 : cs 1 <;> cases e2 : cs 2 <;>
    simp_all [Fin.lt_def] <;> omega

theorem set3 (cs : Fin 3 → Bool) (q : Fin 3) :
    [cs 0, cs 1, cs 2].set ((q.val : Int).toNat) true =
      [upd cs q true 0, upd cs q true 1, upd cs q true 2] := by
  obtain ⟨q, hq⟩ := q
  rcases q with _ | _ | _ | q
  all_goals first | omega | (simp [upd])

theorem cnt_upd (cs : Fin 3 → Bool) (q : Fin 3) (h : cs q = false) :
    cnt (upd cs q true) = cnt cs + 1 := by
  obtain ⟨q, hq⟩ := q
  unfold cnt upd
  rcases q with _ | _ | _ | q
  all_goals first | omega | (simp_all <;> omega)

theorem slots_congr (γ : GryffNames GF) (k : Fin 3) (S : PeerSlices) (P : Fin 3 → Bool)
    (cs cs' : Fin 3 → Bool) (h : ∀ j, P j = true → cs j = cs' j) :
    slots (hG := hG) γ k S P cs ⊢ slots γ k S P cs' := by
  unfold slots
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  iintro ⟨H0, H1, H2⟩
  isplitl [H0]
  · cases hp : P 0
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]; itrivial
    · simp only [hp, ↓reduceIte]; rw [← h0 hp]; iexact H0
  isplitl [H1]
  · cases hp : P 1
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]; itrivial
    · simp only [hp, ↓reduceIte]; rw [← h1 hp]; iexact H1
  · cases hp : P 2
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]; itrivial
    · simp only [hp, ↓reduceIte]; rw [← h2 hp]; iexact H2

theorem logArg_int (n : w64) : ⊢ logArg (hG := hG) (interface.mkOk go.int #n) := by
  iapply logArg_wf
  intro ii h
  exact fmt.ArgsWf.cons_int _ _ _ (.int n) .nil ii (by rw [← h]; simp)

theorem logArg_int32 (n : w32) : ⊢ logArg (hG := hG) (interface.mkOk go.int32 #n) := by
  iapply logArg_wf
  intro ii h
  exact fmt.ArgsWf.cons_int _ _ _ (.int32 n) .nil ii (by rw [← h]; simp)

theorem set_two {α : Type} (a b c : α) : [a, b].set (sint.nat (W64 (0 + 1))) c = [a, c] := by
  rw [show sint.nat (W64 (0 + 1)) = 1 from by decide]; rfl


/-- What `waitForPeerConnections` hands back through `done`: the listener (at the wildcard
`la` of the replica's port) and the higher peers' slots, filled. Port: `Net/`'s listener
(`isListener`, `netLisOn`, its state `netLis`, owned). -/
def doneRes (γ : GryffNames GF) (k : Fin 3) (gR : Loc) (S : PeerSlices) (la : GoString) :
    IProp GF :=
  iprop(∃ (li : GoInterface) (l : w64) (o : Bool),
    gR.[src.genericsmr.Replica, go!"Listener"] ↦ li ∗ Perennial.net.isListener li l ∗
    netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
    netLis (extLocalGS netExt (L := hG.goose_localGS)) l la o ∗
    slots γ k S (above k) (fun _ => true))

theorem replicaAddrs_colon {ip port : GoString} (ha : ip ++ go!":" ++ port ∈ replicaAddrs) :
    (58#8 : w8) ∉ ip := by
  generalize hA : ip ++ go!":" ++ port = A at ha
  have hlen : A.length = 14 := by
    simp only [replicaAddrs, portAddr, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> rfl
  have hone : ∀ i, i < 14 → A[i]? = some (58#8 : w8) → i = 9 := by
    simp only [replicaAddrs, portAddr, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> decide
  have hi : A[ip.length]? = some (58#8 : w8) := by rw [← hA]; simp
  have hl : ip.length < 14 := by rw [← hlen, ← hA]; simp
  have h9 := hone _ hl hi
  have hip : ip = A.take 9 := by rw [← h9, ← hA]; simp
  rw [hip]
  simp only [replicaAddrs, portAddr, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> decide

/-- The wildcard `waitForPeerConnections` listens at: `":" ++ port`. -/
theorem lisAddrOf_split {ip port : GoString} (ha : ip ++ go!":" ++ port ∈ replicaAddrs) :
    lisAddrOf (ip ++ go!":" ++ port) = go!":" ++ port := by
  unfold lisAddrOf
  have hc : (W8 58) ∉ ip := replicaAddrs_colon ha
  rw [List.append_assoc, List.idxOf_append, if_neg hc]
  simp

theorem lisAddr_listenOk {ip port : GoString} (ha : ip ++ go!":" ++ port ∈ replicaAddrs) :
    listenOk (go!":" ++ port) = true := by
  generalize hA : ip ++ go!":" ++ port = A at ha
  have hp : port = A.drop (ip.length + 1) := by rw [← hA]; simp
  have hipl : ip.length = 9 := by
    have h := replicaAddrs_colon (ip := ip) (port := port) (by rw [hA]; exact ha)
    have hlen : A.length = 14 := by
      simp only [replicaAddrs, portAddr, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> rfl
    have hi : A[ip.length]? = some (58#8 : w8) := by rw [← hA]; simp
    have hl : ip.length < 14 := by rw [← hlen, ← hA]; simp
    have hone : ∀ i, i < 14 → A[i]? = some (58#8 : w8) → i = 9 := by
      simp only [replicaAddrs, portAddr, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> decide
    exact hone _ hl hi
  rw [hp, hipl]
  simp only [replicaAddrs, portAddr, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> decide

/-- `poll.ErrDeadlineExceeded`'s value, from `internal/poll`'s initialization (as
`examples/net/wire/Pkg.lean`'s `ed_of_poll`). -/
theorem ed_of_poll' :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢
      ∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll).trans ?_
  show iprop((∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrNoDeadline) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrDeadlineExceeded) e DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr internal.poll.ErrFileClosing)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard)) ⊢ _
  iintro ⟨-, ⟨%ed, #Hd⟩, -⟩
  iexists ed
  iexact Hd

theorem logArgs_of_wf (xs : List GoInterface) (h : fmt.ArgsWf xs) :
    ⊢ ([∗list] x ∈ xs, logArg (hG := hG) x) := by
  induction xs with
  | nil => iintro; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons x xs ih =>
    iintro
    iapply BigSepL.bigSepL_cons.2
    isplitl
    · iapply logArg_wf
      intro ii hii
      exact h ii (by rw [← hii]; simp)
    · iapply ih
      intro ii hii
      exact h ii (List.mem_cons_of_mem _ hii)

/-- A `net` error result is a non-nil error with an `Error()` (an `*OpError`). -/
theorem resErr_errAny (k : NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    Perennial.net.resErr (GF := GF) (some k) op src addr ed nm err ⊢
      ⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err := by
  unfold Perennial.net.resErr Perennial.net.opErr
  iintro ⟨%e, ⟨%pe, %nw, ⟨%Herr, -⟩, #Hpe⟩, -⟩
  subst Herr
  isplitr
  · ipureintro; simp [interface.mkOk]
  iapply opErrPtr_errAny $$ Hpe

/-- `bufio.NewReader(conn)` of a connection (`wire.wp_NewReader` at the conn's interface value). -/
theorem wp_NewReader_conn (tc : Loc) (eof la ra ed : GoInterface) (I : List w8 → IProp GF)
    (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗
        _root_.Perennial.io.readerOk (Perennial.net.connIface tc) (fun _ m => 0 < m) I
          (Perennial.net.connReadE eof la ra ed) ∗ I R }}
      (App (Val (@! bufio.NewReader))
        (Val #(interface.mkOk (go.GoType.PointerType Perennial.net.TCPConn.ty) #tc)))
    {{ (br : Loc), RET #br; wire.ownReader br (connRSt tc eof la ra ed) I R }} :=
  wire.wp_NewReader (connRSt tc eof la ra ed) I R (Perennial.net.connIface_ne_bufioReader tc)

/-- `bufio.NewWriter(conn)` of a connection (`wire.wp_NewWriter` at the conn's interface value). -/
theorem wp_NewWriter_conn (tc : Loc) (la ra ed : GoInterface) (J Q : List w8 → IProp GF)
    (W : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗
        wire.writerOk ⟨Perennial.net.connIface tc, Perennial.net.connWriteE la ra ed, 4096⟩ J Q ∗
        J W ∗ □ Q W }}
      (App (Val (@! bufio.NewWriter))
        (Val #(interface.mkOk (go.GoType.PointerType Perennial.net.TCPConn.ty) #tc)))
    {{ (bw : Loc), RET #bw;
        wire.ownWriter bw ⟨Perennial.net.connIface tc, Perennial.net.connWriteE la ra ed, 4096⟩ J Q W []
          interface.nil }} :=
  wire.wp_NewWriter ⟨Perennial.net.connIface tc, Perennial.net.connWriteE la ra ed, 4096⟩ J Q W rfl
    (Perennial.net.connIface_ne_bufioWriter tc)

/-- `serveClient`'s spec (`Replica2/SpecsN.lean`'s `Replica.serveClient.wp`, proved in
`N/Serve.lean`), as a premise: the accept loops hand client connections to it. -/
def serveClientSpec (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR : Loc) : Prop :=
  ∀ (conn : GoInterface) (rd : Loc) (hs : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ clientConnIn γ ρ k conn rd hs ∗
        ⌜hs < peerMark⌝ }}
      (App (App (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"serveClient"))
        (Val #conn)) (Val #rd)) (Val #hs))
    {{ RET #(); True }}

/-- An accepted connection whose client handshake `hs` was read: `clientConnIn`. -/
theorem clientConnIn_intro (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (t : Loc) (c : Nat)
    (a a0 : GoString) (la ra ed eof : GoInterface) (rd : Loc) (hs : w32)
    (hc : hs < peerMark) (ha0 : a0 ∈ replicaAddrs) :
    Perennial.net.connAt t c true a la ra ∗ globalAddr io.EOF ↦□ eof ∗
      wire.readerOk (connRSt t eof la ra ed)
        (recvTokL (Gg := hG.goose_globalGS) c true (gryffWireP γ a0)) ∗
      wire.ownReader rd (connRSt t eof la ra ed)
        (recvTokL (Gg := hG.goose_globalGS) c true (gryffWireP γ a0)) (u32Le hs) ∗
      wire.writerOk ⟨Perennial.net.connIface t, Perennial.net.connWriteE la ra ed, 4096⟩
        (sendTok c true (gryffWireQ γ a0)) (gryffWireQ γ a0 c) ∗
      sendTok c true (gryffWireQ γ a0) [] ∗ connFresh c true ∗ □ protoInvs γ ⊢
      |={⊤}=> clientConnIn γ ρ k (interface.mkOk (go.GoType.PointerType Perennial.net.TCPConn.ty) #t)
        rd hs := by
  iintro ⟨#Hc, #Heof, #Hrok, Hown, #Hwok, Hsend, Hfresh, #Hinv⟩
  have key := ownReader_sentLb rd (connRSt t eof la ra ed) c true (gryffWireP γ a0) (u32Le hs)
  simp only [Bool.not_true] at key
  ihave ⟨Hown, #Hlb⟩ := key $$ Hown
  imod ownReader_protoNow rd (connRSt t eof la ra ed) c true (gryffWireP γ a0) (u32Le hs) ⊤
    $$ Hown with ⟨Hown, #Hp⟩
  ihave #Hcc := acc_client_conn γ a0 c hs hc $$ Hp
  ihave #Hbr := acc_client_reader γ a0 c hs hc rd (connRSt t eof la ra ed)
  ihave #Hwb := acc_client_writer γ a0 c hs hc $$ Hlb
  imodintro
  unfold clientConnIn
  iexists t, c, a, a0, la, ra, ed, eof, recvTokL (Gg := hG.goose_globalGS) c true (gryffWireP γ a0)
  unfold connRSt
  iframe Hc Heof Hrok Hown Hwok Hsend Hfresh Hcc Hinv
  isplitr
  · ipureintro; exact ⟨rfl, ha0⟩
  iframe Hbr Hwb

set_option goose.wp.extras true

theorem waitForPeerConnections_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3)
    (r gR : Loc) (S : PeerSlices) (pal : GoSlice) (nodes : List GoString) (ip port : GoString)
    (ch : Loc) (γd : ChanNames) (ws : List w64)
    (hn : nodes.length = 3 ∧ nodes[k.val]? = some (ip ++ go!":" ++ port))
    (ha : ip ++ go!":" ++ port ∈ replicaAddrs)
    (hS : sliceShape S.pS 3 ∧ sliceShape S.rS 3 ∧ sliceShape S.wS 3 ∧ sliceShape S.aS 3)
    (wp_serve : serveClientSpec γ ρ k r gR)
    (wp_rfl : lib.io.ReadFull.specLt (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
        gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
        gR.[src.genericsmr.Replica, go!"N"] ↦□ W64 3 ∗
        gR.[src.genericsmr.Replica, go!"PeerAddrList"] ↦□ pal ∗ pal ↦*□ nodes ∗
        □ portId γ (ip ++ go!":" ++ port) (W32 (k.val : Int)) ∗
        lisProto (lisAddrOf (ip ++ go!":" ++ port)) (gryffWireP γ (ip ++ go!":" ++ port))
          (gryffWireQ γ (ip ++ go!":" ++ port)) ∗
        gR.[src.genericsmr.Replica, go!"Listener"] ↦ interface.nil ∗
        gR.[src.genericsmr.Replica, go!"Peers"] ↦□ S.pS ∗
        gR.[src.genericsmr.Replica, go!"PeerReaders"] ↦□ S.rS ∗
        gR.[src.genericsmr.Replica, go!"PeerWriters"] ↦□ S.wS ∗
        gR.[src.genericsmr.Replica, go!"Alive"] ↦□ S.aS ∗
        slots γ k S (above k) (fun _ => false) ∗
        isChanBag γd ch (fun _ : Bool => doneRes γ k gR S (lisAddrOf (ip ++ go!":" ++ port))) ∗
        □ protoInvs γ ∗ predIdIs γ.proto k ws }}
      (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!!
        go!"waitForPeerConnections")) (Val #ch))
    {{ RET #(); True }} := by
  have hla := lisAddrOf_split ha
  rw [hla]
  wp_start as ⟨#Hrep, #HgR, #HId, #HN, #Hpal, #Hnodes, #Hport, #Hlp, Hlis,
    #HpS, #HrS, #HwS, #HaS, Hslots, #Hdone, #Hsh, #Hpred⟩
  have hk3 := k.isLt
  have hidx : sint.Z (W64 (sint.Z (rid32 k))) = (k.val : Int) := by unfold rid32; word
  have hlok := lisAddr_listenOk ha
  ihave %Hpall := ownSlice_len _ _ _ $$ Hnodes
  have hpal : sint.Z pal.len = 3 := by have := Hpall.1; rw [hn.1] at this; word
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
  wp_apply wp_load_slice_index pal (sint.Z (W64 (sint.Z (rid32 k)))) nodes _ (ip ++ go!":" ++ port)
    (by omega) $$ [Hnodes] as -
  · iframe Hnodes; ipureintro; rw [hidx]; simpa using hn.2
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
  wp_apply wp_load_slice_index pal (sint.Z (W64 (sint.Z (rid32 k)))) nodes _ (ip ++ go!":" ++ port)
    (by omega) $$ [Hnodes] as -
  · iframe Hnodes; ipureintro; rw [hidx]; simpa using hn.2
  have h14 : (ip ++ go!":" ++ port).length = 14 := by
    simp only [replicaAddrs, portAddr, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h <;> rw [h] <;> rfl
  wp_apply wp_Index (ip ++ go!":" ++ port) (58#8) ip port rfl (replicaAddrs_colon ha)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %_
  have hl2 : ip.length + port.length < 14 := by
    simp only [List.length_append, List.length_singleton] at h14; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by
    simp only [List.length_append, List.length_singleton]; constructor <;> try constructor
    all_goals word))]
  have hdrop : List.take (sint.nat (W64 ((ip ++ go!":" ++ port).length : Int)) -
      sint.nat (W64 (ip.length : Int))) (List.drop (sint.nat (W64 (ip.length : Int)))
        (ip ++ go!":" ++ port)) = go!":" ++ port := by
    have h1 : sint.nat (W64 (ip.length : Int)) = ip.length := by word
    have h2 : sint.nat (W64 ((ip ++ go!":" ++ port).length : Int)) =
        (ip ++ go!":" ++ port).length := by
      simp only [List.length_append, List.length_singleton]; word
    rw [h1, h2]; simp
  rw [hdrop]
  ihave #Hlog : isPkgInit (PROP := IProp GF) pkg_id.log $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hnet : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · iPkgInit
  ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
  · iPkgInit
  ihave ⟨%ed, #Hed⟩ := ed_of_poll' $$ Hpoll
  ihave #Hdl : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog := replica.dlog_init_access $$ Hdl
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  ihave #Hla := logArgs_of_wf _ (.cons_string _ _ .nil)
  wp_apply log.wp_Printf_logArg _ _ _ _ $$ [$Hsl1 $Hla] as -
  -- listen (retrying)
  wp_apply (nS.listen go!"tcp" Perennial.net.tcpNet_tcp (go!":" ++ port)) $$ [] as %lv %err0 Hl
  · isplitr
    · ipureintro; exact hlok
    iapply listen_lis_au $$ Hlp
  ihave IHL : iprop(∃ (lv' e' : GoInterface),
      "Hlis" ∷ gR.[src.genericsmr.Replica, go!"Listener"] ↦ lv' ∗
      "err" ∷ err_ptr ↦ e' ∗
      "Hl" ∷ ((⌜e' = interface.nil⌝ ∗ ∃ l, Perennial.net.isListener lv' l ∗
          netLis (extLocalGS netExt (L := hG.goose_localGS)) l (go!":" ++ port) true ∗
          netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l (go!":" ++ port)) ∨
        (⌜e' ≠ interface.nil⌝ ∗ models_lab.errAny e'))) $$ [Hlis err Hl]
  · iexists lv, err0; iframe
    icases Hl with (⟨%He, Hl⟩ | ⟨%x, -, #Hre⟩)
    · ileft; iframe Hl; ipureintro; exact He
    · iright; iapply resErr_errAny $$ Hre
  wp_for IHL
  icases Hl with (⟨%He, %l, #Hli, Hnl, #Hon⟩ | ⟨%He, #HeA⟩)
  rotate_left
  · obtain ⟨i, rfl⟩ : ∃ i, e' = interface.ok i := by
      cases e' with
      | nil => exact absurd rfl He
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (by simp)]
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    ihave #Hla1 := logArgs_of_wf [interface.mkOk go.int32 #(rid32 k)]
      (.cons_int _ _ _ (.int32 _) .nil)
    wp_apply log.wp_Printf_logArg _ _ _ _ $$ [$Hsl2] as -
    · iintro !>
      rw [show ([interface.mkOk go.int32 #(rid32 k), GoInterface.nil] : List GoInterface).set
          (sint.nat (W64 (0 + 1))) (GoInterface.ok i) =
          [interface.mkOk go.int32 #(rid32 k), GoInterface.ok i] from by
        rw [show sint.nat (W64 (0 + 1)) = 1 from by decide]; rfl]
      iapply BigSepL.bigSepL_cons.2
      ihave ⟨#Ha, -⟩ := BigSepL.bigSepL_cons.1 $$ Hla1
      iframe Ha
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_err $$ HeA
    wp_apply time.wp_Sleep
    wp_apply (nS.listen go!"tcp" Perennial.net.tcpNet_tcp (go!":" ++ port)) $$ [] as %lv2 %err2 Hl
    · isplitr
      · ipureintro; exact hlok
      iapply listen_lis_au $$ Hlp
    wp_for_post
    iframe
    iexists lv2, err2
    iframe
    icases Hl with (⟨%He, Hl⟩ | ⟨%x, -, #Hre⟩)
    · ileft; iframe Hl; ipureintro; exact He
    · iright; iapply resErr_errAny $$ Hre
  subst He
  wp_auto
  rw [if_neg (by simpa using (show (#false : val) ≠ #true from fun h => absurd (go.intoVal_inj h) (by decide))), if_pos (by simp)]
  wp_auto
  ihave #Hioi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hioi with ⟨-, -, -, -, #HEOFv, -⟩
  ihave #HEOF := HEOFv
  iunfold _root_.Perennial.errors.newVar at HEOF
  icases HEOF with ⟨%xeof, #Heof, -⟩
  generalize interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xeof = eof
  iunfold Perennial.net.isListener at Hli
  icases Hli with ⟨%tl, %xl, %Hlv, #Hlat⟩
  subst Hlv
  wp_apply (wp_slice_make2 (V := Bool) _) as %cS ⟨HcS, -⟩
  · ipureintro; decide
  have e0 : arrayIndexRef w8 (sint.Z (W64 0)) b_ptr = b_ptr := go.arrayIndexRef_0 _ _
  have e4 : (W64 4 - W64 0 : w64) = W64 4 := rfl
  rw [e0, e4] at *
  ihave Hb := slice_array b_ptr _ _ (by decide) $$ b
  ihave IH : iprop(∃ (iv : w32) (cs : Fin 3 → Bool) (bb : List w8) (o : Bool),
      "i" ∷ i_ptr ↦ iv ∗ "HcS" ∷ cS ↦* [cs 0, cs 1, cs 2] ∗
      "%Hcs" ∷ ⌜(∀ j, cs j = true → k < j) ∧ sint.Z iv = k.val + 1 + cnt cs⌝ ∗
      "Hslots" ∷ slots γ k S (above k) cs ∗
      "Hb" ∷ slice.mk b_ptr (W64 4) (W64 4) ↦* bb ∗ "%Hbb" ∷ ⌜bb.length = 4⌝ ∗
      "Hnl" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l (go!":" ++ port) o ∗
      "Hlis" ∷ gR.[src.genericsmr.Replica, go!"Listener"] ↦
        interface.mkOk (go.GoType.PointerType Perennial.net.TCPListener.ty) #tl)
      $$ [i HcS Hslots Hb Hlis Hnl]
  · iexists _, (fun _ => false), _, true
    iframe
    isplitr
    · ipureintro
      refine ⟨fun j h => absurd h (by simp), ?_⟩
      unfold cnt rid32
      simp only [Bool.toNat_false, Nat.add_zero]
      clear hdrop
      word
    ipureintro; rfl
  wp_for IH
  wp_if_destruct
  rotate_left
  · -- every higher peer connected: hand back through `done`
    have h3 : sint.Z (W32 (sint.Z (W64 3))) = 3 := by decide
    have hfull := cnt_full k cs Hcs.1 (by have := Hcs.2; omega)
    wp_apply (wp_bag_send γd ch true (fun _ : Bool => doneRes γ k gR S (go!":" ++ port)))
      $$ [Hlis Hslots Hnl]
    · iframe Hdone
      unfold doneRes
      iexists _, l, o
      iframe Hlis Hon Hnl
      isplitr
      · iunfold Perennial.net.isListener
        iexists tl, xl
        iframe Hlat
        ipureintro; rfl
      iapply slots_congr _ _ _ _ _ _ hfull $$ Hslots
    iapply HΦ; itrivial
  -- an iteration: accept
  wp_apply (nS.accept tl l xl (go!":" ++ port) (fun _ =>
      netLis (extLocalGS netExt (L := hG.goose_localGS)) l (go!":" ++ port) o)
      (fun a cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l (go!":" ++ port) o ∗
        connEnd cn true (gryffWireQ γ (ip ++ go!":" ++ port)) (gryffWireP γ (ip ++ go!":" ++ port))
          [] [] ∗ connFresh cn true))) $$ [Hnl] as %cv %aerr Hres
  · iframe Hlat Hon
    iapply accept_lis_au $$ Hlp Hnl
  icases Hres with (⟨%Haerr, %cid, %a, %Hacc, #Hcc, Hnl, Hend, Hfresh⟩ | ⟨%kk, Hnl, #Hre⟩)
  rotate_left
  · -- `Accept` failed
    ihave ⟨%Hne, #HeA⟩ := resErr_errAny _ _ _ _ _ _ _ $$ Hre
    obtain ⟨ie, rfl⟩ : ∃ ie, aerr = interface.ok ie := by
      cases aerr with
      | nil => exact absurd rfl Hne
      | ok ie => exact ⟨ie, rfl⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %sl3 ⟨Hsl3, -⟩
    wp_apply log.wp_Println_logArg _ _ _ $$ [$Hsl3] as -
    · iintro !>
      rw [set_two]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply logArg_string
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_err $$ HeA
    wp_for_post
    iframe
    iexists iv, cs, bb, o
    iframe
    ipureintro; exact ⟨Hcs, Hbb⟩
  subst Haerr
  iunfold Perennial.net.isConn at Hcc
  icases Hcc with ⟨%tc, %la, %ra, %Hcv, #Hown⟩
  subst Hcv
  ihave #Hown' := Hown
  iunfold Perennial.net.connAt at Hown'
  icases Hown' with ⟨%nwc, -, -, -, #Hra, -⟩
  iunfold Perennial.net.netAddr at Hra
  icases Hra with ⟨%rap, %rav, %Hrap, -⟩
  subst Hrap
  wp_auto
  wp_apply (nS.remoteAddr tc cid true a _ _) $$ [$Hown]
  try wp_auto
  wp_apply lib.wp_TCPAddr_String rap as %ras -
  generalize hra : interface.mkOk (go.GoType.PointerType Perennial.net.TCPAddr.ty) #rap = ra
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %sl4 ⟨-, -⟩
  wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
  -- the handshake
  iunfold connEnd at Hend
  icases Hend with ⟨Hsend, Hrecv⟩
  ihave Hrecv := recvTok_L $$ Hrecv
  wp_apply lib.wp_connReadFull nS.read wp_rfl tc cid true a la ra ed _ [] _ bb
    $$ [$Hio $Hown $Hed $Hrecv $Hb] as %n %rerr ⟨%data, %Hdata, Hb, Hrecv, #Hre⟩
  obtain ⟨hn, hdl, hnil⟩ := Hdata
  cases rerr with
  | ok ei =>
    -- the handshake was not read whole: close, next
    wp_auto
    icases Hre with (%Hc | #HeA)
    · cases Hc
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %sl5 ⟨Hsl5, -⟩
    wp_apply log.wp_Printf_logArg _ _ _ _ $$ [$Hsl5] as -
    · iintro !>
      rw [set_two]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply logArg_err $$ HeA
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_int
    ihave #Hci := sendTok_connIs $$ Hsend
    wp_apply (nS.close tc cid true a la ra (fun _ => iprop(True))) $$ [] as %cerr -
    · iframe Hown
      imod close_au cid true $$ Hci with ⟨%st, %d, He, Hd, Hk⟩
      imodintro
      iexists st, d
      iframe He Hd
      iintro %res %st' %d' %Hco He Hd
      imod Hk $$ %res %st' %d' %Hco He Hd with -
      imodintro; itrivial
    wp_for_post
    iframe
    iexists iv, cs, _, o
    iframe
    ipureintro; exact ⟨Hcs, by simp; omega⟩
  | nil =>
  have h4 : data.length = 4 := by rw [← Hbb]; exact hnil rfl
  wp_auto
  have hn4 : n = W64 4 := by rw [h4] at hn; word
  subst hn4
  rw [show decide ((W64 4 : w64) = W64 4) = true from by decide]
  wp_auto
  have hdrop0 : bb.drop data.length = [] := List.drop_eq_nil_of_le (by omega)
  rw [hdrop0]
  wp_apply encoding.binary.wp_LittleEndian_Uint32 _ data _ [] h4 $$ [$Hbin $Hb] as Hb
  have hdata : data = u32Le (leToU32 data) := (leToU32_le data h4).symm
  generalize leToU32 data = hs at hdata
  subst hdata
  have hPH : (W32 2147483648 : w32) = peerMark := rfl
  rw [hPH]
  simp only [List.nil_append]
  ihave #Hrok := Perennial.net.conn_readerOk nS.read tc cid true a la ra eof ed
    (gryffWireP γ (ip ++ go!":" ++ port)) $$ [$Hio $Hown $Heof $Hed]
  ihave #Hwok := Perennial.net.conn_streamWriterOk nS.write tc cid true a la ra ed
    (gryffWireQ γ (ip ++ go!":" ++ port)) (gryffWireQ_closed γ _) $$ [$Hown $Hed]
  by_cases hc : hs < peerMark
  · -- a client's handshake: `serveClient`
    rw [(and_peerMark_zero hs).2 hc]
    wp_auto
    wp_apply wp_NewReader_conn tc eof la ra ed _ (u32Le hs) $$ [$Hbufio $Hrok $Hrecv] as %crd Hcrd
    iapply fupd_wp
    imod clientConnIn_intro γ ρ k tc cid a (ip ++ go!":" ++ port) la ra ed eof
      crd hs hc ha $$ [Hcrd Hsend Hfresh] with Hcci
    · iframe Hown Heof Hcrd Hwok Hsend Hfresh Hsh
      unfold wire.readerOk; iframe Hio Hbufio
    imodintro
    wp_apply wp_fork $$ [Hcci]
    · wp_apply wp_serve _ crd hs $$ [Hcci]
      · iframe Hrep HgR Hcci
        ipureintro; exact hc
      itrivial
    wp_for_post
    iframe
    iexists iv, cs, _, o
    iframe
    ipureintro; exact ⟨Hcs, by simp [u32Le_length]⟩
  -- a peer's handshake
  rw [show decide (hs &&& peerMark = W32 0) = false from
    decide_eq_false (fun h => hc ((and_peerMark_zero hs).1 h))]
  wp_auto
  ihave ⟨Hrecv, Hpl⟩ := recvTokL_proto cid true _ _ $$ Hrecv
  iapply fupd_wp
  imod Hpl with #Hpp
  imodintro
  ihave %Hids := acc_peer_ids γ _ ha cid hs k hc $$ [$Hpp $Hport]
  rw [hPH]
  obtain ⟨hidlt, hidor⟩ := peer_split hs hc
  generalize hidv : hs &&& ~~~peerMark = idv at hidlt hidor Hids
  have hidZ : sint.Z idv = (idv.toNat : Int) := by
    have : idv.toNat < 2 ^ 31 := by unfold peerMark at hidlt; rw [BitVec.lt_def] at hidlt; simpa using hidlt
    unfold sint.Z; rw [BitVec.toInt_eq_toNat_cond]; simp; omega
  have hkZ : sint.Z (rid32 k) = (k.val : Int) := by unfold rid32; have := k.isLt; word
  rw [show decide (sint.Z idv ≤ sint.Z (rid32 k)) = false from decide_eq_false (by omega)]
  wp_auto
  rw [show decide (sint.Z (W32 (sint.Z (W64 3))) ≤ sint.Z idv) = false from
    decide_eq_false (by rw [show sint.Z (W32 (sint.Z (W64 3))) = 3 from by decide]; omega)]
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %sl6 ⟨Hsl6, -⟩
  ihave #Hla6 := logArgs_of_wf [interface.mkOk go.int32 #idv, interface.mkOk go.int #S.pS.len]
    (.cons_int _ _ _ (.int32 _) (.cons_int _ _ _ (.int _) .nil))
  wp_apply log.wp_Printf_logArg _ _ _ _ $$ [$Hsl6] as -
  · rw [set_two]; iexact Hla6
  -- peer `q`'s slot
  obtain ⟨q, hq⟩ : ∃ q : Fin 3, idv = W32 (q.val : Int) :=
    ⟨⟨idv.toNat, Hids.2⟩, by apply BitVec.eq_of_toNat_eq; simp⟩
  subst hq
  have hqZ : sint.Z (W64 (sint.Z (W32 (q.val : Int)))) = (q.val : Int) := by
    have := q.isLt; rw [hidZ]; simp only [BitVec.toNat_ofInt]; word
  have hkq : above k q = true := by
    unfold above; simp only [decide_eq_true_eq]; rw [Fin.lt_def]
    have := Hids.1; simp only [BitVec.toNat_ofInt] at this; omega
  ihave ⟨Hslot, Hslots⟩ := slots_acc γ k S (above k) cs q hkq $$ Hslots
  iunfold slotOwn at Hslot
  icases Hslot with ⟨%cv0, %rd0, %w0, %al0, Hcells, -⟩
  iunfold cellsAt at Hcells
  icases Hcells with ⟨Hp0, Hr0, Hw0, Ha0⟩
  have hl3 : ∀ s : GoSlice, sliceShape s 3 → sint.Z s.len = 3 := fun s h => h.1
  rw [hqZ, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by rw [hl3 _ hS.1]; omega⟩)]
  wp_auto
  subst hidor
  rw [show W32 (q.val : Int) ||| peerMark = peerHs q from rfl]
  have key := Net.recvTokL_sentLb (GF := GF) cid true (gryffWireP γ (ip ++ go!":" ++ port)) (u32Le (peerHs q))
  simp only [Bool.not_true] at key
  ihave ⟨Hrecv, #Hlb⟩ := key $$ Hrecv
  wp_apply wp_NewReader_conn tc eof la ra ed _ (u32Le (peerHs q)) $$ [$Hbufio $Hrok $Hrecv] as %prd Hprd
  rw [hqZ, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by rw [hl3 _ hS.2.1]; omega⟩)]
  wp_auto
  iapply fupd_wp
  imod peerStream_nil_upd γ.proto k q ws $$ Hpred with #Hps0
  imodintro
  ihave #Hwb := acc_peer_writer γ _ ha cid k q $$ [$Hport $Hlb]
  ihave #HQ0 := Hwb $$ %([] : List w8) Hps0
  rw [show ([] : List w8) ++ [] = [] from rfl]
  wp_apply wp_NewWriter_conn tc la ra ed _ _ [] $$ [$Hbufio $Hwok $Hsend $HQ0] as %pw Hpw
  rw [hqZ, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by rw [hl3 _ hS.2.2.1]; omega⟩)]
  wp_auto
  rw [hqZ, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by rw [hl3 _ hS.2.2.2]; omega⟩)]
  wp_auto
  ihave Hfilled : slotOwn γ k S q true $$ [Hp0 Hr0 Hw0 Ha0 Hprd Hpw]
  · iunfold slotOwn
    iexists _, prd, pw, true
    iunfold cellsAt
    iframe Hp0 Hr0 Hw0 Ha0
    simp only [↓reduceIte]
    isplitr
    · ipureintro; trivial
    isplitl [Hprd]
    · iunfold peerReaderB
      iexists connRSt tc eof la ra ed, _, u32Le (peerHs q), []
      isplitr
      · unfold wire.readerOk; iframe Hio Hbufio
      rw [List.append_nil]
      iframe Hprd
      isplitr
      · ipureintro; exact ⟨[], .nil, rfl⟩
      iapply acc_peer_reader γ _ ha cid k q prd (connRSt tc eof la ra ed) $$ Hport
    · iunfold peerWriterB
      iexists ⟨Perennial.net.connIface tc, Perennial.net.connWriteE la ra ed, 4096⟩,
        sendTok cid true (gryffWireQ γ (ip ++ go!":" ++ port)),
        gryffWireQ γ (ip ++ go!":" ++ port) cid, [], [], [], [], interface.nil
      iframe Hpw Hwok Hwb
      isplitr
      · ipureintro; exact ⟨⟨[], .nil, rfl⟩, List.prefix_refl _, fun _ => ⟨rfl, rfl⟩⟩
      iexists ws; iexact Hpred
  ihave Hslots := Hslots $$ %true Hfilled
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %sl7 ⟨Hsl7, -⟩
  ihave #Hla7 := logArgs_of_wf [interface.mkOk go.int32 #(W32 (q.val : Int))]
    (.cons_int _ _ _ (.int32 _) .nil)
  wp_apply log.wp_Printf_logArg _ _ _ _ $$ [$Hsl7 $Hla7] as -
  ihave %HcSl := ownSlice_len _ _ _ $$ HcS
  have hcS : sint.Z cS.len = 3 := by
    obtain ⟨h1, h2⟩ := HcSl
    simp only [List.length_cons, List.length_nil] at h1
    unfold sint.nat at h1; simp only [sint.Z] at h2; show cS.len.toInt = 3; omega
  have hq3 := q.isLt
  rw [hqZ]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
  have hget : [cs 0, cs 1, cs 2][(q.val : Int).toNat]? = some (cs q) := by
    obtain ⟨q, hq⟩ := q
    rcases q with _ | _ | _ | q <;> first | rfl | omega
  wp_apply wp_load_slice_index cS (q.val : Int) _ _ (cs q) (by omega) $$ [HcS] as HcS
  · iframe HcS; ipureintro; exact hget
  cases hcq : cs q
  · -- a new peer: counted
    wp_auto
    rw [hqZ]
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    wp_apply wp_store_slice_index $$ [HcS] as HcS
    · iframe HcS; ipureintro; simp; omega
    wp_for_post
    iframe
    iexists _, upd cs q true, _, o
    rw [set3 cs q]
    iframe
    ipureintro
    refine ⟨⟨fun j hj => ?_, ?_⟩, by simp [u32Le_length]⟩
    · unfold upd at hj; split at hj
      · subst_vars; unfold above at hkq; simpa using hkq
      · exact Hcs.1 j hj
    · rw [cnt_upd cs q hcq]; have := Hcs.2; push_cast; word
  · -- a peer's second connection: kept, not counted again
    wp_auto
    wp_for_post
    iframe
    iexists _, upd cs q true, _, o
    have hsame : upd cs q true = cs := by
      funext j; unfold upd; split
      · subst_vars; exact hcq.symm
      · rfl
    rw [hsame]
    iframe
    ipureintro; exact ⟨Hcs, by simp [u32Le_length]⟩

end

end Perennial.gryff.netN
