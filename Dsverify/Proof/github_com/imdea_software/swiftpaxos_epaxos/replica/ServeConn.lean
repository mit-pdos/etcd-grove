/-
`serveConn` (late: from `WaitForClientConnections`): the P1 classification of an accepted
connection by its first bytes, and the late peer's install in its slot.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.ClientListener
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Pkg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.LibDeps
public import Net.Proof.net.ConnIo
public import Proof.bufio.Own
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.RProg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Log

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The little-endian value of the bytes read so far (`serveConn`'s `id |= uint32(b[n]) << (8*n)`). -/
def leAcc (bs : List w8) : w32 :=
  bs.zipIdx.foldl (fun acc bk => acc ||| W32 (uint.Z bk.1) <<< (W64 8 * W64 (bk.2 : Int))) (W32 0)

theorem leAcc_snoc (bs : List w8) (x : w8) :
    leAcc (bs ++ [x]) = leAcc bs ||| W32 (uint.Z x) <<< (W64 8 * W64 (bs.length : Int)) := by
  unfold leAcc
  rw [List.zipIdx_append, List.foldl_append]
  simp

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS] [io.Assumptions] [field_sem : net.FieldAssumptions]

/-- The bytes of a client's stream are zeros up to its fifth byte (`PROPOSE`, `CommandId 0`). -/
theorem proposeBytes_zeros (c : w64) (i : KvI) (first : List w8) (h : first <+: proposeBytes c i)
    (hl : first.length ≤ 4) : first = List.replicate first.length (W8 0) := by
  have h4 : (proposeBytes c i).take 4 = List.replicate 4 (W8 0) := by
    unfold proposeBytes encPropose proposeTag; rfl
  have hp : first <+: List.replicate 4 (W8 0) := by
    rw [← h4]; exact List.prefix_take_iff.mpr ⟨h, hl⟩
  obtain ⟨t, ht⟩ := hp
  apply List.eq_replicate_iff.mpr
  refine ⟨rfl, fun b hb => ?_⟩
  have : b ∈ List.replicate 4 (W8 0) := by rw [← ht]; exact List.mem_append_left _ hb
  exact (List.mem_replicate.mp this).2

theorem leAcc_zeros (k : Nat) (hk : k ≤ 4) : leAcc (List.replicate k (W8 0)) = W32 0 := by
  rcases k with _ | _ | _ | _ | _ | k <;> first | decide | omega

/-- The id a peer's handshake gives, from its first byte on. -/
theorem leAcc_encId (d k : Nat) (hd : d < 5) (hk1 : 1 ≤ k) (hk : k ≤ 4) :
    leAcc ((encId d).take k) = W32 d := by
  rcases d with _ | _ | _ | _ | _ | d <;> rcases k with _ | _ | _ | _ | _ | k <;>
    first | decide | omega

theorem encId_length (d : Nat) : (encId d).length = 4 := by
  unfold encId; rfl

/-- The P1 classification's ghost part: the first bytes `first` (at most 4, not none) read
from a connection to replica `id`'s address are a client's (zeros: the op's role), or a peer
`d`'s handshake (`d > id`, `peerConn`). -/
theorem conn_classify (γ : EpNames) (L : List GoString) (id : Nat) (cid : Nat) (first : List w8)
    (hid : id < L.length) (hne : first ≠ []) (hl : first.length ≤ 4) :
    listFinal (GF := GF) γ L -∗ recvTok cid true (repDialP γ (L.getD id [])) first -∗
      recvTok cid true (repDialP γ (L.getD id [])) first ∗
      ((∃ (c : w64) (i : KvI), clientConn γ cid c i ∗ ⌜first <+: proposeBytes c i⌝) ∨
        (∃ d : Nat, roleElem γ cid (.peer (W64 d)) ∗ peerConn γ d id cid ∗
          ⌜first <+: encId d⌝)) := by
  iintro #Hlf Hr
  ihave ⟨Hr, #Hp⟩ := recvTok_proto $$ Hr
  iframe Hr
  unfold protoPrefix
  icases Hp with (%H | ⟨%ext, %Hpre, #HP⟩)
  · exact absurd H hne
  unfold repDialP
  icases HP with (%He | ⟨%rl, #Hrole, #Hm⟩)
  · subst He; exact absurd (List.eq_nil_of_prefix_nil Hpre) hne
  cases rl with
  | client c i =>
    unfold clientDialOk
    icases Hm with ⟨#Hcc, %Hp2⟩
    ileft
    iexists c, i
    iframe Hcc
    ipureintro; exact Hpre.trans Hp2
  | peer d =>
    unfold peerStreamOk
    icases Hm with ⟨%i', %ws, #Ha, #Hc, %Hp2, -⟩
    have hsome : L[id]? = some (L.getD id []) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hid]; rfl
    ihave #Ha' := listFinal_addrId γ L id _ hsome $$ Hlf
    ihave %Hi := addrId_agree $$ Ha Ha'
    subst Hi
    simp only [Bool.false_eq_true, ite_false]
    iright
    iexists uint.nat d
    rw [show W64 (uint.nat d : Int) = d by word]
    iframe Hrole Hc
    ipureintro
    have h1 : first <+: streamHdr (uint.nat d) false ++ ws.flatMap encMsg := Hpre.trans Hp2.2
    unfold streamHdr at h1
    simp only [Bool.false_eq_true, ite_false] at h1
    have h4 : first.length ≤ (encId (uint.nat d)).length := by rw [encId_length]; exact hl
    exact List.prefix_of_prefix_length_le h1 (List.prefix_append _ _) h4

/-- `b[k:k+1]` of `serveConn`'s `[4]byte` (as the slice `b[:4]`) holding `first` then zeros,
and back with the byte read. -/
theorem bArr_split (b : Loc) (k : Nat) (first : List w8) (hk : k < 4) (hl : first.length = k) :
    (slice.mk b (W64 4) (W64 4) ↦* (first ++ List.replicate (4 - k) (W8 0)) : IProp GF) ⊢
      slice.mk (arrayIndexRef w8 (k : Int) b) (W64 1) (W64 4 - W64 k) ↦* [W8 0] ∗
      (∀ x : w8, slice.mk (arrayIndexRef w8 (k : Int) b) (W64 1) (W64 4 - W64 k) ↦* [x] -∗
        slice.mk b (W64 4) (W64 4) ↦* ((first ++ [x]) ++ List.replicate (4 - (k + 1)) (W8 0))) := by
  iintro Hs
  have hb : 0 ≤ sint.Z (W64 k) ∧ sint.Z (W64 k) ≤ sint.Z (W64 (k + 1)) ∧
      sint.Z (W64 (k + 1)) ≤ sint.Z (slice.mk b (W64 4) (W64 4)).len := by
    simp only; refine ⟨by word, by word, by word⟩
  icases (ownSlice_slice (V := w8) (W64 k) (W64 (k + 1)) _ _ _ hb).1 $$ Hs with ⟨H1, H2, H3⟩
  have hsl : slice.slice (slice.mk b (W64 4) (W64 4)) w8 (W64 k) (W64 (k + 1)) =
      slice.mk (arrayIndexRef w8 (k : Int) b) (W64 1) (W64 4 - W64 k) := by
    unfold slice.slice sliceIndexRef
    simp only
    congr 2
    · word
    · word
  have hk1 : sint.nat (W64 k) = k := by word
  have hk2 : sint.nat (W64 (k + 1)) = k + 1 := by word
  have hmid : subslice k (k + 1) (first ++ List.replicate (4 - k) (W8 0)) = [W8 0] := by
    unfold subslice
    rw [List.take_append, List.drop_append]
    subst hl
    obtain ⟨j, hj⟩ : ∃ j, 4 - first.length = j + 1 := ⟨3 - first.length, by omega⟩
    rw [hj]
    simp
  rw [hsl, hk1, hk2, hmid]
  iframe H2
  iintro %x H2
  have hb' := hb
  iapply (ownSlice_slice (V := w8) (W64 k) (W64 (k + 1)) _ _ _ hb').2
  rw [hsl, hk1, hk2]
  have ht : ((first ++ [x]) ++ List.replicate (4 - (k + 1)) (W8 0)).take k =
      (first ++ List.replicate (4 - k) (W8 0)).take k := by
    subst hl; simp
  have hm : subslice k (k + 1) ((first ++ [x]) ++ List.replicate (4 - (k + 1)) (W8 0)) = [x] := by
    unfold subslice; subst hl
    rw [List.append_assoc, List.take_append, List.drop_append]
    simp
  have hd : ((first ++ [x]) ++ List.replicate (4 - (k + 1)) (W8 0)).drop (k + 1) =
      (first ++ List.replicate (4 - k) (W8 0)).drop (k + 1) := by
    subst hl
    rw [List.append_assoc, List.drop_append, List.drop_append]
    simp only [List.length_append, List.length_singleton, List.drop_replicate,
      List.length_replicate]
    obtain ⟨j, hj⟩ : ∃ j, 4 - first.length = j + 1 := ⟨3 - first.length, by omega⟩
    rw [hj]
    simp [List.replicate_succ]
    rw [List.drop_eq_nil_of_le (by omega), List.nil_append]
    congr 1; omega
  rw [ht, hm, hd]
  iframe

/-- The id of a prefix of at most 4 bytes of a protocol stream (a client's zeros, or a peer's
handshake) is a replica id. -/
theorem leAcc_lt (first : List w8) (hl : first.length ≤ 4)
    (h : first = [] ∨ (∃ c i, first <+: proposeBytes c i) ∨ (∃ d, d < 5 ∧ first <+: encId d)) :
    uint.Z (leAcc first) < 5 := by
  rcases h with rfl | ⟨c, i, hp⟩ | ⟨d, hd, hp⟩
  · decide
  · rw [proposeBytes_zeros c i first hp hl, leAcc_zeros _ hl]; decide
  · rcases Nat.eq_zero_or_pos first.length with h0 | h0
    · rw [List.eq_nil_of_length_eq_zero h0]; decide
    · have : first = (encId d).take first.length := by
        obtain ⟨t, ht⟩ := hp
        rw [← ht]; simp
      rw [this, leAcc_encId d _ hd h0 hl]
      rcases d with _ | _ | _ | _ | _ | d <;> first | decide | omega

/-- Peer `d`'s slot (`d > id`) is empty while `d`'s only connection (`peerConn`) is being
accepted: an installed connection of `d` would be the same one, accepted twice. -/
theorem slot_null_of_peer (γ : EpNames) (id : Nat) (L : List GoString) (ew : GoSlice) (d : Nat)
    (c : GoInterface) (w : Loc) (cid : Nat) (hd : id < d) :
    peerSlotX (GF := GF) γ id L ew d c w -∗ peerConn γ d id cid -∗ connFresh cid true -∗
      ⌜c = interface.nil ∧ w = null⌝ ∗ sentHalf γ id d [] ∗ lisStart γ id ew d ∗
        connFresh cid true := by
  unfold peerSlotX
  iintro ⟨%ms, Hs, (⟨%Hw, %Hc, %Hms, Hdf⟩ | ⟨%cid', %side, Hconn⟩)⟩ #Hpc Hfr
  · subst Hms
    iframe
    ipureintro; exact ⟨Hc hd, Hw⟩
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

/-- Install peer `d`'s accepted connection in its (empty) slot. -/
theorem slot_install (γ : EpNames) (id : Nat) (L : List GoString) (ew : GoSlice) (d : Nat)
    (conn : GoInterface)
    (cid : Nat) (w : Loc) (tc : Loc) (la ra ed eof : GoInterface) :
    sentHalf (GF := GF) γ id d [] -∗ connIn conn cid true tc la ra ed eof -∗ peerConn γ d id cid -∗
      roleElem γ cid (.peer (W64 d)) -∗
      EtcdGrove.bufio.ownBufWriter w (net.connIface tc) (sendTok (Gg := hG.goose_globalGS) cid true
        (repAccP γ (L.getD id []))) (repAccP γ (L.getD id []) cid) (net.connWriteE la ra ed) 4096 [] []
        interface.nil -∗
      connFresh cid true -∗ peerSlotX γ id L ew d conn w := by
  iintro Hs #Hc #Hpc #Hrole Hw Hfr
  unfold peerSlotX
  iexists []
  iframe Hs
  iright
  iexists cid, true
  unfold slotConn peerPX dialerOf
  simp only [ite_true]
  iexists [], [], interface.nil, [], tc, la, ra, ed, eof
  simp only [wrOwn, connWr]
  iframe
  iframe #
  ipureintro
  refine ⟨rfl, fun _ h => by simp at h, fun _ => ?_⟩
  simp [streamHdr]

variable [EpBufioDeps GF] [EpNetDeps GF] [EpReplicaDeps GF]

/-- `io.ReadFull(conn, buf)` on the acceptor's end of a connection (Perennial's `io.wp_ReadFull`
over `net.conn_readerOk`): the lab's `bufio.wp_ReadFull` shape. -/
theorem wp_ReadFull_conn (t : Loc) (cn : Nat) (a : GoString) (la ra eof ed : GoInterface)
    (P : Proto GF) (R : List w8) (buf : GoSlice) (bs : List w8) :
    {{ pkgInit_replica ∗ net.connAt (GF := GF) t cn true a la ra ∗ globalAddr io.EOF ↦□ eof ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
        recvTokL (Gg := hG.goose_globalGS) cn true P R ∗ buf ↦* bs }}
      (App (App (Val (@! io.ReadFull)) (Val #(interface.ok (net.connIface t)))) (Val #buf))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ data : List w8, ⌜n = W64 data.length ∧ data.length ≤ bs.length ∧
          (err = interface.nil ↔ data.length = bs.length)⌝ ∗
        buf ↦* (data ++ bs.drop data.length) ∗ recvTokL (Gg := hG.goose_globalGS) cn true P (R ++ data) }} := by
  iintro %Φ ⟨#Hpkg, #Hca, #Heof0, #Hed, Hr, Hb⟩ HΦ
  ihave #Hbuf : (isPkgInit (PROP := IProp GF) pkg_id.bufio) $$ []
  · iPkgInit
  ihave ⟨%eof', %ueof, %sb, %Hne, #Hio, #Heof, #Hueof, -⟩ := io_errs $$ Hbuf
  ihave #Hok := net.conn_readerOk EpNetDeps.connRead t cn true a la ra eof ed P $$ [Hio Hca Heof0 Hed]
  · iframe #
  wp_apply EpReplicaDeps.readFull (net.connIface t) _ (recvTokL (Gg := hG.goose_globalGS) cn true P) _ R buf bs
      eof' ueof $$ [$Hio $Hok $Heof $Hueof $Hr $Hb] as %n %err ⟨%ys, %Hys, Hb, Hr, #Hres⟩
  · ipureintro; intro ys hys; omega
  obtain ⟨hn, hle⟩ := Hys
  iunfold io.readFullRes at Hres
  iapply HΦ
  iexists ys
  iframe Hb Hr
  icases Hres with (%Hr | ⟨%e, %Hr, -⟩)
  · ipureintro
    exact ⟨EtcdGrove.bufio.w64_of_sintZ hn, hle, by simp [Hr.1, Hr.2]⟩
  · ipureintro
    obtain ⟨hlt, hne, h1, h2⟩ := Hr
    refine ⟨EtcdGrove.bufio.w64_of_sintZ hn, hle, ?_⟩
    constructor
    · intro herr
      by_cases hc : e = eof' ∧ ys ≠ []
      · exact absurd (h1 hc ▸ herr) Hne.1
      · exact absurd (h2 hc ▸ herr) hne
    · intro h; omega

theorem replica.Replica.serveConn.spec_holds
    (hCL : replica.Replica.clientListener.spec (GF := GF)) (hRL : replica.Replica.replicaListener.spec (GF := GF))
    (hPrintln : dlog.Logger.Println.spec (GF := GF)) (hPrintf : dlog.Logger.Printf.spec (GF := GF)) :
    replica.Replica.serveConn.spec (GF := GF) := by
  intro γ r id L p Rext conn cid
  wp_start as ⟨#Hfw, Hacc⟩
  ihave #Hfw' := isReplicaFw_def $$ Hfw
  iunfold isReplicaFwDef at Hfw'
  icases Hfw' with ⟨#Hro, #Hfz, #Hmu, #Hph1, #Hph2⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, -, -, -, #HPeers, #HReaders, #HWriters, -, -, -, -, #HAlive,
    -, -, -, -, -, #HShut, -, -, -, -, -, -, -, -, -, %HL, #HLf, #HCI, -, -⟩
  unfold accEnd
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
    · -- a peer `d > id`: its slot is empty; install it
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
      wp_apply (lc := 2) sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
      iunfold fwLockInv at HR
      icases HR with ⟨Hcore, HRext⟩
      ihave Hacc := fwCore_acc (GF := GF) γ id L p ⊤ CoPset.subseteq_top $$ Hph1 Hph2 Hcore Hlc1 Hlc2
      iapply fupd_wp
      imod Hacc with ⟨Hpeers, Hrd, Hcore⟩
      imodintro
      icases fwPeers_open γ id L _ _ _ _ _ d (by omega) (by omega) $$ Hpeers
        with ⟨%cs, %ws, %als, %ls, Hps, Hws, Has, Hls, %Hlen, Hslot, Hpeers⟩
      icases slot_null_of_peer γ id L _ d _ _ cid Hd.1 $$ Hslot Hpc Hfresh
        with ⟨%Hnull, Hsent, Hdf, Hfresh⟩
      unfold fwReaders
      icases Hrd with ⟨%rs, Hrs, %Hrsl⟩
      rw [show decide (uint.Z (W32 (id : Int)) < uint.Z (W32 (d : Int))) = true by
        simp only [decide_eq_true_eq]; word]
      wp_auto
      rw [show decide (uint.Z (W32 (d : Int)) < uint.Z (W32 (sint.Z (W64 ((5 : Nat) : Int))))) = true by
        simp only [decide_eq_true_eq]; have := Hd.2; unfold nRep at this; word]
      wp_auto
      ihave %Hpl := ownSlice_len _ _ _ $$ Hps
      have hdz : sint.Z (W64 (uint.Z (W32 (d : Int)))) = (d : Int) := by
        have := Hd.2; unfold nRep at this; word
      have hcs : cs.length = 5 := by rw [Hlen.1, HL.1]; rfl
      have hplen : sint.Z p.peers.len = 5 := by
        have h1 := Hpl.1; rw [hcs] at h1; have h2 := Hpl.2; word
      have hd5 : d < 5 := by have := Hd.2; unfold nRep at this; exact this
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.peers.len by omega)]
      have hcd : cs[d]? = some interface.nil := by
        have h1 := Hnull.1
        rw [List.getD_eq_getElem?_getD] at h1
        rw [List.getElem?_eq_getElem (by omega)] at h1 ⊢
        simp only [Option.getD_some] at h1; rw [h1]
      wp_apply wp_load_slice_index p.peers (d : Int) cs _ interface.nil (by omega) $$ [Hps] as Hps
      · iframe; ipureintro; simpa using hcd
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.peers.len by omega)]
      wp_apply wp_store_slice_index p.peers (d : Int) cs _ $$ [Hps] as Hps
      · iframe; ipureintro; omega
      ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
      · iPkgInit
      ihave #Hrdok := net.conn_readerOk EpNetDeps.connRead tc cid true a la ra eof ed
        (repDialP γ (L.getD id [])) $$ [Hio Hca Heof Hed]
      · iframe #
      ihave HrL := recvTok_L cid true _ first $$ Hrecv
      wp_apply EpBufioDeps.newReaderOk (net.connIface tc)
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
      ihave %Hrl := ownSlice_len _ _ _ $$ Hrs
      have hrs : rs.length = 5 := by rw [Hrsl, HL.1]; rfl
      have hrlen : sint.Z p.readers.len = 5 := by
        have h1 := Hrl.1; rw [hrs] at h1; have h2 := Hrl.2; word
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.readers.len by omega)]
      wp_apply wp_store_slice_index p.readers (d : Int) rs _ $$ [Hrs] as Hrs
      · iframe; ipureintro; omega
      ihave #Hwrok := net.conn_streamWriterOk EpNetDeps.connWrite tc cid true a la ra ed
        (repAccP γ (L.getD id [])) (repAccP_ppc γ _) $$ [Hca Hed]
      · iframe #
      wp_apply EpBufioDeps.newWriter
        (net.connIface tc) _ _ _ [] $$ [Hsend] as %bw Hbw
      · isplitr
        · ipureintro
          simp only [net.connIface, ne_eq, go.GoType.PointerType.injEq]
          unfold net.TCPConn.ty _root_.Perennial.bufio.Writer.ty; simp
        isplitr
        · iPkgInit
        iframe Hwrok Hsend
        imodintro; unfold repAccP; ileft; ipureintro; rfl
      ihave %Hwl := ownSlice_len _ _ _ $$ Hws
      have hwlen : sint.Z p.writers.len = 5 := by
        have h1 := Hwl.1; rw [Hlen.2.1, HL.1] at h1; have h2 := Hwl.2; unfold nRep at h1; word
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.writers.len by omega)]
      wp_apply wp_store_slice_index p.writers (d : Int) ws _ $$ [Hws] as Hws
      · iframe; ipureintro; omega
      ihave %Hal := ownSlice_len _ _ _ $$ Has
      have halen : sint.Z p.alive.len = 5 := by
        have h1 := Hal.1; rw [Hlen.2.2.1, HL.1] at h1; have h2 := Hal.2; unfold nRep at h1; word
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.alive.len by omega)]
      wp_apply wp_store_slice_index p.alive (d : Int) als _ $$ [Has] as Has
      · iframe; ipureintro; omega
      rw [hdz, if_pos (show 0 ≤ (d : Int) ∧ (d : Int) < sint.Z p.readers.len by omega)]
      simp only [Int.toNat_natCast]
      wp_apply wp_load_slice_index p.readers (d : Int) (rs.set d br) (DFrac.own 1) br (by omega)
        $$ [Hrs] as Hrs
      · iframe; ipureintro; simp [List.getElem?_set_self (show d < rs.length by omega)]
      ihave Hslot := slot_install (GF := GF) γ id L p.ewma d _ cid bw tc la ra ed eof $$ Hsent Hc Hpc Hrole Hbw Hfresh
      ihave Hpeers := Hpeers $$ %_ %bw %true Hps Hws Has Hls Hslot
      ihave Hcore := Hcore $$ Hpeers [Hrs]
      · iexists rs.set d br; iframe; ipureintro; simp [Hrsl]
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
      · unfold fwLockInv; iframe
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.any)
      wp_auto
      isplitr
      · ipureintro; rfl
      iintro %sl_ptr ⟨-, -⟩
      wp_auto
      wp_apply wp_rPrintf hPrintf γ r id L p $$ [$Hro]
      rw [show W64 (uint.Z (W32 (d : Int))) = W64 (d : Int) by
        have := hd5; apply BitVec.eq_of_toInt_eq; word]
      wp_apply wp_fork $$ [Hbr Hdf]
      · wp_apply hRL γ r id L p Rext d _ cid true br $$ [Hbr Hdf]
        · unfold fwRun0 lisRes peerPin dialerOf streamHdr
          simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
          rw [hfirst]
          iframe; iframe #
          simp only [rdOwn, connRd]
          iframe Hbr
          ipureintro; exact ⟨⟨by omega, by omega⟩, Hd.1⟩
        itrivial
      iapply HΦ; itrivial
      done

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
