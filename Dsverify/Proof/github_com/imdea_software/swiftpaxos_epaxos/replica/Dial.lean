/-
The dialing phase of `ConnectToPeers` (package-internal): the listener goroutine's cells
(`wfOwnX`: the higher peers' cells and slots, with the slices' lengths) and
`serveConn(conn, false)`, which installs an accepted peer there (its reader kept for
`ConnectToPeers`).
-/
module

public import Proof.bufio.Writer__WriteByte
public import Proof.bufio.Writer__Flush
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.ServeConn

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS] [field_sem : net.FieldAssumptions] [io.Assumptions]

/-- The lengths of the framework's peer slices. -/
def fwLens (L : List GoString) (p : FwPtrs) : Prop :=
  sint.Z p.peers.len = L.length ∧ sint.Z p.readers.len = L.length ∧
    sint.Z p.writers.len = L.length ∧ sint.Z p.alive.len = L.length ∧
    sint.Z p.lat.len = L.length ∧ sint.Z p.ewma.len = L.length

/-- The listener goroutine's part while connecting, with the slices' lengths. -/
def wfOwnX (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) : IProp GF :=
  iprop(wfOwn γ id L p ∗ ⌜fwLens L p⌝)

/-- `r.serveConn(conn, false)` (from `waitForPeerConnections`, while dialing). -/
def replica.Replica.serveConnDial.specX : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (conn : GoInterface) (cid : Nat),
  {{ pkgInit_replica ∗ fwRun0 γ r id L p Rext ∗ wfOwnX γ id L p ∗ accEnd γ id L conn cid }}
    (App (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"serveConn"))
      (Val #conn)) (Val #false))
  {{ RET #(); wfOwnX γ id L p }}

/-- Peer `d`'s pending slot (`d > id`) is empty while `d`'s only connection is being accepted. -/
theorem pend_null_of_peer (γ : EpNames) (id : Nat) (L : List GoString) (ew : GoSlice) (d : Nat)
    (c : GoInterface) (rd w : Loc) (cid : Nat) (hd : id < d) :
    pendSlot (GF := GF) γ id L ew d c rd w -∗ peerConn γ d id cid -∗ connFresh cid true -∗
      ⌜c = interface.nil ∧ w = null ∧ rd = null⌝ ∗ sentHalf γ id d [] ∗ lisStart γ id ew d ∗
        connFresh cid true := by
  unfold pendSlot
  iintro ⟨%ms, Hs, (⟨%Hw, %Hc, %Hms, Hdf⟩ | ⟨%cid', %side, Hconn, -⟩)⟩ #Hpc Hfr
  · subst Hms
    iframe
    ipureintro; exact ⟨Hc hd, Hw.1, Hw.2⟩
  · unfold slotConn
    icases Hconn with ⟨%sent, %pend, %err, %ws, %t', %la', %ra', %ed', %eof', -, #Hpc', -, -, -, Hfr'⟩
    cases side
    · simp only [Bool.false_eq_true, ite_false]
      ihave %H := peerConn_ids $$ Hpc'
      exact absurd H.1 (by omega)
    · simp only [ite_true]
      ihave %Heq := peerConn_agree $$ Hpc Hpc'
      subst Heq
      iexfalso
      iapply connFresh_excl (Gg := hG.goose_globalGS) cid true
      iframe

theorem replica.Replica.serveConnDial.spec_holds
    (hCL : replica.Replica.clientListener.spec (GF := GF))
    (hPrintln : dlog.Logger.Println.spec (GF := GF)) (hPrintf : dlog.Logger.Printf.spec (GF := GF)) :
    replica.Replica.serveConnDial.specX (GF := GF) := by
  intro γ r id L p Rext conn cid
  wp_start as ⟨#Hrun, Hwf, Hacc⟩
  unfold fwRun0
  icases Hrun with ⟨#Hro, #Hmu⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, -, -, -, #HPeers, #HReaders, #HWriters, -, -, -, -, #HAlive,
    -, -, -, -, -, #HShut, -, -, -, -, -, -, -, -, -, %HL, #HLf, #HCI, -, -⟩
  unfold accEnd
  ihave #Hpkg0 : (pkgInit_replica (GF := GF)) $$ []
  · iPkgInit
  icases Hacc with ⟨⟨%tc, %la, %ra, %ed, %eof, #Hc⟩, Hsend, Hrecv, Hfresh⟩
  ihave #Hc' := Hc
  iunfold connIn at Hc'
  icases Hc' with ⟨%Hcv, ⟨%a, #Hca⟩, #Hed, #Heof⟩
  subst Hcv
  ihave #Hcis := sendTok_connIs cid true _ [] $$ Hsend
  have hN : L.length = 5 := HL.1
  rw [hN]
  wp_auto
  ihave Hb := slice_array (GF := GF) b_ptr 4 _ (by decide) $$ b
  -- the bytes read so far, in `b[:n]`, and the id they give
  ihave HI : (∃ (k : Nat) (first : List w8) (idv : w32),
      "n" ∷ n_ptr ↦ W64 k ∗ "id" ∷ id_ptr ↦ idv ∗
      "Hb" ∷ slice.mk b_ptr (W64 4) (W64 4) ↦* (first ++ List.replicate (4 - k) (W8 0)) ∗
      "Hrecv" ∷ recvTok cid true (repDialP γ (L.getD id [])) first ∗
      "%Hk" ∷ ⌜first.length = k ∧ k ≤ 4 ∧ idv = leAcc first⌝ : IProp GF) $$ [n id Hb Hrecv]
  · iexists 0, [], W32 0
    iframe
    ipureintro; exact ⟨rfl, by omega, rfl⟩
  wp_for HI
  wp_if_destruct
  · by_cases hc : uint.Z idv < uint.Z (W32 (sint.Z (W64 (5 : Nat))))
    · simp only [hc, decide_true, ite_true]
      have hk4 : k < 4 := by word
      icases bArr_split b_ptr k first hk4 Hk.1 $$ Hb with ⟨Hb1, Hb⟩
      wp_auto
      rw [if_pos (by refine ⟨by word, by word, by word⟩)]
      rw [show W64 (k : Int) + W64 1 - W64 (k : Int) = W64 1 by word,
        show sint.Z (W64 (k : Int)) = (k : Int) by word]
      ihave HrL := recvTok_L cid true _ first $$ Hrecv
      wp_apply (lc := 1) wp_ReadFull_conn tc cid a la ra eof ed _ first _ [W8 0] $$ [$Hca $Hed $Heof $HrL $Hb1]
        as %nn %err ⟨%data, %Hd, Hb1, HrL⟩
      ihave Hrecv := recvTokL_later $$ HrL
      iapply fupd_wp
      imod (lc_fupd_elim_later (GF := GF) (E := ⊤)) $$ Hlc1 Hrecv with Hrecv
      imodintro
      obtain ⟨rfl, hdl, herr⟩ := Hd
      rcases data with _ | ⟨x, _ | ⟨y, t⟩⟩
      · -- nothing read: an error; the connection is closed
        cases err with
        | nil => simp at herr
        | ok ei =>
        wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := GoInterface) (t := go.any)
        wp_auto
        isplitr
        · ipureintro; rfl
        iintro %sl_ptr ⟨-, -⟩
        wp_auto
        wp_apply wp_rPrintln hPrintln γ r id L p $$ [$Hro]
        wp_apply wp_connClose tc cid true a la ra $$ [$Hca $Hcis] as %e -
        wp_for_post
        iapply HΦ; itrivial
      · -- one byte read
        cases err with
        | ok ei => simp at herr
        | nil =>
        rw [show [x] ++ List.drop [x].length [W8 0] = [x] from rfl]
        ihave Hb := Hb $$ %x Hb1
        wp_auto
        rw [if_pos (by refine ⟨by word, by word⟩)]
        rw [show arrayIndexRef w8 (sint.Z (W64 (k : Int))) b_ptr =
          sliceIndexRef w8 (k : Int) (slice.mk b_ptr (W64 4) (W64 4)) by
            unfold sliceIndexRef; congr 1; word]
        wp_apply wp_load_slice_index (slice.mk b_ptr (W64 4) (W64 4)) (k : Int) _ _ x (by omega) $$ [Hb]
          as Hb
        · iframe; ipureintro
          simp only [Int.toNat_natCast]
          rw [List.append_assoc, List.getElem?_append_right (by omega)]
          simp [Hk.1]
        unfold go.shiftCount
        wp_auto
        rw [show decide (sint.Z (W64 8 * W64 (k : Int)) < sint.Z (W64 0)) = false by
          simp only [decide_eq_false_iff_not]; word]
        wp_auto
        wp_for_post
        iframe
        iexists k + 1, first ++ [x], _
        rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
        iframe
        ipureintro
        refine ⟨by simp [Hk.1], by omega, ?_⟩
        rw [leAcc_snoc, Hk.1, Hk.2.2]
        done
      · simp at hdl
    · -- `id ≥ N` before 4 bytes: impossible, the stream is a client's or a peer's
      have h5 : uint.Z (W32 (sint.Z (W64 ((5 : Nat) : Int)))) = 5 := by decide
      rw [h5, Hk.2.2] at hc
      by_cases h0 : first = []
      · exact (hc (leAcc_lt first (by omega) (Or.inl h0))).elim
      · icases conn_classify γ L id cid first HL.2 h0 (by omega) $$ HLf Hrecv
          with ⟨Hrecv, (⟨%c', %i, -, %Hp⟩ | ⟨%d, -, #Hpc, %Hp⟩)⟩
        · exact (hc (leAcc_lt first (by omega) (Or.inr (Or.inl ⟨c', i, Hp⟩)))).elim
        · ihave %Hd := peerConn_ids $$ Hpc
          exact (hc (leAcc_lt first (by omega) (Or.inr (Or.inr ⟨d, Hd.2, Hp⟩)))).elim
  · -- four bytes read: classify
    have hk : k = 4 := by have := Hk.2.1; word
    have hl4 : first.length = 4 := by rw [Hk.1, hk]
    have hne : first ≠ [] := by intro h; rw [h] at hl4; simp at hl4
    rw [hk] at *
    icases conn_classify γ L id cid first HL.2 hne (by omega) $$ HLf Hrecv
      with ⟨Hrecv, (⟨%c', %i, #Hcc', %Hp⟩ | ⟨%d, #Hrole, #Hpc, %Hp⟩)⟩
    · -- a client: `id` is 0, not a peer's
      have hid0 : idv = W32 0 := by
        rw [Hk.2.2, proposeBytes_zeros c' i first Hp (by omega), hl4]; decide
      subst hid0
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
      rw [show decide (uint.Z (W32 (id : Int)) < uint.Z (W32 0)) = false by
        simp only [decide_eq_false_iff_not]; word]
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked $HR]
      rw [show slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) b_ptr) (W64 ((4 : Nat) : Int) - W64 0)
          (W64 4 - W64 0) = slice.mk b_ptr (W64 4) (W64 4) by
          rw [show sint.Z (W64 0) = (0 : Int) by decide, go.arrayIndexRef_0]; rfl]
      simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
      wp_apply wp_fork $$ [Hsend Hrecv Hfresh Hb]
      · wp_apply hCL γ r id L p Rext _ cid c' i _ first tc la ra ed eof $$ [Hsend Hrecv Hfresh Hb]
        · rw [opTok_unseal]; unfold opTokDef fwRun0
          iframe; iframe #
          ipureintro; exact Hp
        itrivial
      iapply HΦ; itrivial
    · -- a peer `d > id`: its pending slot is empty; install it there
      ihave %Hd := peerConn_ids $$ Hpc
      have hfirst : first = encId d := by
        obtain ⟨t, ht⟩ := Hp
        have : t = [] := by
          have h := congrArg List.length ht
          simp only [List.length_append, encId_length, hl4] at h
          exact List.eq_nil_of_length_eq_zero (by omega)
        rw [this, List.append_nil] at ht; exact ht
      have hid : idv = W32 d := by
        rw [Hk.2.2, hfirst, show encId d = (encId d).take 4 from
          (List.take_of_length_le (by rw [encId_length]; omega)).symm]
        exact leAcc_encId d 4 Hd.2 (by omega) (by omega)
      subst hid
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
      unfold wfOwnX wfOwn
      icases Hwf with ⟨Hwf, %Hlens⟩
      have hd5 : d < 5 := by have := Hd.2; unfold nRep at this; exact this
      have hlk : (List.range L.length)[d]? = some d := by
        rw [List.getElem?_range (by rw [hN]; omega)]
      icases BigSepL.bigSepL_lookup_acc_impl hlk $$ Hwf with ⟨Hcell, Hwf⟩
      simp only [show id < d from Hd.1, ite_true]
      unfold pendCells
      icases Hcell with ⟨%c0, %rd0, %w0, %a0, Hpc0, Hrd0, Hw0, Ha0, Hslot⟩
      icases pend_null_of_peer γ id L _ d _ _ _ cid Hd.1 $$ Hslot Hpc Hfresh
        with ⟨%Hnull, Hsent, Hdf, Hfresh⟩
      obtain ⟨hc0, hw0, hrd0⟩ := Hnull
      subst hc0 hw0 hrd0
      rw [show decide (uint.Z (W32 (id : Int)) < uint.Z (W32 (d : Int))) = true by
        simp only [decide_eq_true_eq]; word]
      wp_auto
      rw [show decide (uint.Z (W32 (d : Int)) < uint.Z (W32 (sint.Z (W64 ((5 : Nat) : Int))))) = true by
        simp only [decide_eq_true_eq]; word]
      wp_auto
      have hdz : sint.Z (W64 (uint.Z (W32 (d : Int)))) = (d : Int) := by word
      obtain ⟨hlp, hlr, hlw, hla, hll, hle⟩ := Hlens
      rw [hN] at hlp hlr hlw hla
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.peers.len by omega)]
      wp_auto
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.peers.len by omega)]
      wp_auto
      ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
      · iPkgInit
      ihave #Hrdok := net.conn_readerOk net.Conn.Read.wp_proof tc cid true a la ra eof ed
        (repDialP γ (L.getD id [])) $$ [Hio Hca Heof Hed]
      · iframe #
      ihave HrL := recvTok_L cid true _ first $$ Hrecv
      wp_apply EtcdGrove.bufio.NewReader.wp_proofOk
        (EtcdGrove.bufio.NewReader.wp_proofE EtcdGrove.bufio.NewReaderSize.wp_proofE) (net.connIface tc)
        (fun _ m => 0 < m) (recvTokL (Gg := hG.goose_globalGS) cid true (repDialP γ (L.getD id [])))
        (net.connReadE eof la ra ed) first $$ [HrL] as %br Hbr
      · isplitr
        · ipureintro
          simp only [net.connIface, ne_eq, go.GoType.PointerType.injEq]
          unfold net.TCPConn.ty _root_.Perennial.bufio.Reader.ty; simp
        isplitr
        · iPkgInit
        iframe Hrdok HrL
        iapply EtcdGrove.bufio.preUpTo_trivial
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.readers.len by omega)]
      wp_auto
      ihave #Hwrok := net.conn_streamWriterOk net.Conn.Write.wp_proof tc cid true a la ra ed
        (repAccP γ (L.getD id [])) (repAccP_ppc γ _) $$ [Hca Hed]
      · iframe #
      wp_apply EtcdGrove.bufio.NewWriter.wp_proof EtcdGrove.bufio.NewWriterSize.wp_proof
        (net.connIface tc) _ _ _ [] $$ [Hsend] as %bw Hbw
      · isplitr
        · ipureintro
          simp only [net.connIface, ne_eq, go.GoType.PointerType.injEq]
          unfold net.TCPConn.ty _root_.Perennial.bufio.Writer.ty; simp
        isplitr
        · iPkgInit
        iframe Hwrok Hsend
        imodintro; unfold repAccP; ileft; ipureintro; rfl
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.writers.len by omega)]
      wp_auto
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.alive.len by omega)]
      wp_auto
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.readers.len by omega)]
      wp_auto
      ihave Hslot : pendSlot γ id L p.ewma d _ br bw $$ [Hsent Hbw Hfresh Hbr Hdf]
      · unfold pendSlot
        iexists []
        iframe Hsent
        iright
        iexists cid, true
        isplitl [Hbw Hfresh]
        · unfold slotConn peerPX dialerOf
          simp only [ite_true]
          iexists [], [], interface.nil, [], tc, la, ra, ed, eof
          simp only [wrOwn, connWr]
          iframe; iframe #
          ipureintro
          refine ⟨rfl, fun _ h => by simp at h, fun _ => ?_⟩
          simp [streamHdr]
        · unfold lisRes peerPin dialerOf streamHdr
          simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
          rw [hfirst]
          iframe; iframe #
          simp only [rdOwn, connRd]
          iframe Hbr
          ipureintro; exact Hd.1
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked $HR]
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.any)
      wp_auto
      isplitr
      · ipureintro; rfl
      iintro %sl_ptr ⟨-, -⟩
      wp_auto
      wp_apply wp_rPrintf hPrintf γ r id L p $$ [$Hro]
      iapply HΦ
      isplitl
      · iapply Hwf
        · imodintro
          iintro %k %y %hk %hkd H
          iexact H
        · simp only [show id < d from Hd.1, ite_true]
          iexists _, br, bw, true
          iframe
      · ipureintro; exact ⟨by rw [hN]; exact hlp, by rw [hN]; exact hlr, by rw [hN]; exact hlw,
          by rw [hN]; exact hla, hll, hle⟩
      done

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
