/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Connect.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N1: `ConnectToPeers()`

Starts `waitForPeerConnections` (the higher peers' slots), dials each lower peer until its
handshake (`u32Le (k ||| PeerHandshake)`) is written whole (the N1 fix: a failed write closes the
connection and redials), takes the listener and the higher slots back through `done`, joins the
slots into the four slices, starts a `replicaListener` per peer, and assembles the run goroutine's
`loopTok` (`pendingOuts … [] []`: the peer writers with nothing sent, the self cursor, the client
writers) and `listenerOwn`.

The frozen `Replica.ConnectToPeers.wp` lacks `r.Replica ↦□ gR` (hub request N1-2): proved here
with it as an extra premise.
-/
module

public import Dsverify.Proof.gryff.N.ConnSlots
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

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
variable [binA : wire.BinaryVarintHyps GF]
variable [net.Assumptions] [nS : NetSpecs GF] [strA : StringsIndexHyp GF]


theorem sentToR_nil (q : Fin 3) : sentToR q [] = [] := by simp [sentToR, kahn.sentTo]; rfl
theorem streamOf_nil (k q : Fin 3) : streamOf k q [] = [] := by
  simp [streamOf, sentToR, outsP, kahn.runP, kahn.runFrom, kahn.sentTo]; rfl

/-- The peer writers as `netAt` lists them. -/
theorem writers_netAt (γ : GryffNames GF) (k : Fin 3) (wsl : List Loc) (hl : wsl.length = 3) :
    tri (fun j => if j = k then iprop(True) else peerWriterB γ k j (wsl.getD j.val null) []) ⊢
    [∗list] q ∈ peers k, ∃ (w : Loc) (ms : List model.Msg),
      ⌜wsl[q.val]? = some w ∧ ms ++ sentToR q [] = streamOf k q []⌝ ∗ peerWriterAt γ k q w ms := by
  iintro H
  iapply (peers_tri k _).2
  unfold tri
  icases H with ⟨H0, H1, H2⟩
  have key : ∀ j : Fin 3, (if j = k then iprop(True) else peerWriterB γ k j (wsl.getD j.val null) []) ⊢
      (if j = k then iprop(True) else iprop(∃ (w : Loc) (ms : List model.Msg),
        ⌜wsl[j.val]? = some w ∧ ms ++ sentToR j [] = streamOf k j []⌝ ∗ peerWriterAt γ k j w ms)) := by
    intro j
    by_cases h : j = k
    · simp only [h, ↓reduceIte]; iintro _; itrivial
    · simp only [h, ↓reduceIte]
      iintro H
      iexists wsl.getD j.val null, []
      isplitr
      · ipureintro
        refine ⟨?_, by rw [sentToR_nil, streamOf_nil]; rfl⟩
        have hlt : j.val < wsl.length := by rw [hl]; exact j.isLt
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      unfold peerWriterAt; iexact H
  ihave H0 := key 0 $$ H0
  ihave H1 := key 1 $$ H1
  ihave H2 := key 2 $$ H2
  iframe

theorem ports_pers (γ : GryffNames GF) (nodes : List GoString) :
    ([∗list] i ↦ a ∈ nodes, portId γ a (W32 (i : Int)) ∗
      addrProto a (gryffWireP γ a) (gryffWireQ γ a) ∗ ⌜a ∈ replicaAddrs⌝) ⊢
    [∗list] i ↦ a ∈ nodes, □ portId γ a (W32 (i : Int)) ∗
      addrProto a (gryffWireP γ a) (gryffWireQ γ a) ∗ ⌜a ∈ replicaAddrs⌝ := by
  apply BigSepL.bigSepL_mono
  intro i a _
  iintro ⟨Hp, #Ha, %Hm⟩
  ihave #Hp := portId_pers γ a _ Hm $$ Hp
  iframe Hp Ha
  ipureintro; exact Hm

theorem roles_pers (γ : GryffNames GF) (nodes : List GoString) (k : Fin 3) :
    ([∗list] i ↦ a ∈ nodes, ⌜i < k.val⌝ -∗ peerRole γ a (rid32 k)) ⊢
    [∗list] i ↦ a ∈ nodes, □ (if i < k.val then peerRole γ a (rid32 k) else True) := by
  apply BigSepL.bigSepL_mono
  intro i a _
  iintro H
  by_cases h : i < k.val
  · simp only [h, ↓reduceIte]
    iapply peerRole_pers
    iapply H
    ipureintro; trivial
  · simp only [h, ↓reduceIte]; iintro !>; itrivial

/-- `conn.Write(p)` on a connection's `*TCPConn` (`io.wp_streamWriter_Write` at its method). -/
theorem wp_conn_Write (tc : Loc) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF)
    (out : List w8) (p : GoSlice) (dq : DFrac) (xs : List w8) :
    {{ EtcdGrove.io.streamWriterOk (Perennial.net.connIface tc) J Q Ew ∗ J out ∗ □ Q (out ++ xs) ∗
        p ↦*{dq} xs }}
      (App (Val #(methods (go.GoType.PointerType Perennial.net.TCPConn.ty) go!"Write" #tc)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, ⌜n = W64 k ∧ k ≤ xs.length ∧ (err = interface.nil → k = xs.length)⌝ ∗
          p ↦*{dq} xs ∗ J (out ++ xs.take k) ∗ EtcdGrove.io.werrAt Ew err }} :=
  EtcdGrove.io.wp_streamWriter_Write (Perennial.net.connIface tc) J Q Ew out p dq xs

set_option goose.wp.extras true

/-- A replica port address split at its `:`. -/
theorem replicaAddrs_split {a : GoString} (ha : a ∈ replicaAddrs) :
    ∃ ip port : GoString, a = ip ++ go!":" ++ port := by
  simp only [replicaAddrs, portAddr, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨go!"127.0.0.1", go!"7502", rfl⟩
  · exact ⟨go!"127.0.0.1", go!"7503", rfl⟩
  · exact ⟨go!"127.0.0.1", go!"7504", rfl⟩

theorem ConnectToPeers_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR : Loc)
    (wp_serve : serveClientSpec γ ρ k r gR)
    (wp_rfl : lib.io.ReadFull.specLt (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ connectRes γ ρ k r gR }}
      (App (genM gR go!"ConnectToPeers") (Val #()))
    {{ RET #(); loopTok γ ρ k r ∗ listenerOwn γ ρ k gR }} := by
  wp_start as ⟨#Hrep, #HgR, Hcr⟩
  iunfold connectRes at Hcr
  icases Hcr with ⟨%pal, %pS, %rS, %wS, %aS, %nodes, %a0, %ws, #Hpal, #Hnodes, %Hn,
    Hports, Hroles, #Hlp, #Hsh, #HpS, Hp, #HrS, Hr, #HwS, Hw, #HaS, Ha, Hlis, Hcurs,
    Hcurk, #Hpred, Hboot, Hrest, Hclients⟩
  ihave Hx := (isReplica_open ..).1 $$ Hrep
  icases Hx with ⟨%gR2, %h, #Hex, #HgR2, -, -, -, -, -, -, #Hgen⟩
  icombine HgR HgR2 gives %Heq
  subst Heq
  ihave Hx := (isExec_open ..).1 $$ Hex
  icases Hx with ⟨%gR3, %mtx, %ex, %p, #HgR3, -, -, -, -, -, -, -, #HId, #HN, -, -, -, -, -, #Hpreds⟩
  icombine HgR HgR3 gives %Heq
  subst Heq
  let S : PeerSlices := ⟨pS, rS, wS, aS⟩
  icases slices_split γ k S $$ [$Hp $Hr $Hw $Ha] with ⟨%hS, Hlow, Hhigh, Hown⟩
  ihave #HportsP := ports_pers γ nodes $$ Hports
  ihave #HrolesP := roles_pers γ nodes k $$ Hroles
  have hk3 := k.isLt
  ihave #Hk := BigSepL.bigSepL_lookup (Φ := fun i a => iprop(□ portId γ a (W32 (i : Int)) ∗
      addrProto a (gryffWireP γ a) (gryffWireQ γ a) ∗ ⌜a ∈ replicaAddrs⌝)) Hn.2 $$ HportsP
  icases Hk with ⟨#HportK, #HprotoK, %HmemK⟩
  obtain ⟨ip, port, rfl⟩ := replicaAddrs_split HmemK
  ihave #Hgr : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
  · iexact Hpkg
  unfold genM
  wp_method_call
  wp_call
  wp_auto
  wp_apply (chan.wp_make1 (V := Bool)) as %ch %γd ⟨#Hch, -, Hoc⟩
  iapply fupd_wp
  imod start_bag (fun _ : Bool => doneRes γ k gR S (lisAddrOf (ip ++ go!":" ++ port))) _ ch γd (by simp)
    $$ Hch Hoc with #Hdone
  imodintro
  wp_apply wp_fork $$ [Hhigh Hlis]
  · wp_apply waitForPeerConnections_wp γ ρ k r gR S pal nodes ip port ch γd ws Hn HmemK hS wp_serve wp_rfl
      $$ [Hhigh Hlis]
    · iframe; iframe #
    itrivial
  ihave #Hlog : isPkgInit (PROP := IProp GF) pkg_id.log $$ []
  · iPkgInit
  ihave #Hnet : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · iPkgInit
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
  · iPkgInit
  ihave ⟨%ed, #Hed⟩ := ed_of_poll' $$ Hpoll
  ihave #Hioi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hioi with ⟨-, -, -, -, #HEOFv, -⟩
  ihave #HEOF := HEOFv
  iunfold _root_.Perennial.errors.newVar at HEOF
  icases HEOF with ⟨%xeof, #Heof, -⟩
  generalize interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xeof = eof
  ihave Hnil := ownSlice_nil (V := GoInterface) (hG := hG) (dq := DFrac.own 1)
  wp_apply log.wp_Printf _ _ [] _ .nil $$ [$Hnil] as -
  have e0 : arrayIndexRef w8 (sint.Z (W64 0)) b_ptr = b_ptr := go.arrayIndexRef_0 _ _
  have e4 : (W64 4 - W64 0 : w64) = W64 4 := rfl
  rw [e0, e4] at *
  ihave Hb := slice_array b_ptr _ _ (by decide) $$ b
  have hkZ : sint.Z (rid32 k) = (k.val : Int) := by unfold rid32; word
  ihave IHo : iprop(∃ (iv : w64) (bb : List w8),
      "i" ∷ i_ptr ↦ iv ∗ "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ k.val⌝ ∗
      "Hlow" ∷ slots γ k S (below k) (fun j => decide ((j.val : Int) < sint.Z iv)) ∗
      "Hb" ∷ slice.mk b_ptr (W64 4) (W64 4) ↦* bb ∗ "%Hbb" ∷ ⌜bb.length = 4⌝) $$ [i Hlow Hb]
  · iexists _, _
    iframe
    isplitr
    · ipureintro; constructor <;> simp
    isplitl [Hlow]
    · iapply slots_congr _ _ _ _ _ _ _ $$ Hlow
      intro j _; simp
    ipureintro; rfl
  wp_for IHo
  have hkW : sint.Z (W64 (sint.Z (rid32 k))) = (k.val : Int) := by rw [hkZ]; word
  rw [hkW]
  wp_if_destruct
  rotate_left
  · -- all lower peers dialed
    have hivk : sint.Z iv = k.val := by omega
    ihave Hlow := slots_congr _ _ _ _ _ (fun _ => true) (by
      intro j hj; unfold below at hj; simp at hj; simp [hivk]; exact hj) $$ Hlow
    wp_apply (wp_bag_receive γd ch (fun _ : Bool => doneRes γ k gR S (lisAddrOf (ip ++ go!":" ++ port))))
      $$ [$Hdone] as %vd Hd
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %sl9 ⟨Hsl9, -⟩
    ihave #Hla9 := logArgs_of_wf [interface.mkOk go.int32 #(rid32 k)]
      (.cons_int _ _ _ (.int32 _) .nil)
    wp_apply log.wp_Printf_logArg _ _ _ _ $$ [$Hsl9 $Hla9] as -
    iunfold doneRes at Hd
    icases Hd with ⟨%li, %l, %o, Hlis, #Hli, #Hon, Hnl, Hhigh⟩
    icases slices_join γ k S hS $$ [$Hlow $Hhigh $Hown] with
      ⟨%cvs, %rds, %wsl, %Hlens, Hp, Hr, Hw, Ha, Hrds, Hwss⟩
    ihave Hcurs := (peers_tri k _).1 $$ Hcurs
    ihave Hrc := tri_merge k _ _ $$ [$Hrds $Hcurs]
    have hrS3 : sint.Z rS.len = 3 := hS.2.1.1
    ihave IHr : iprop(∃ (n : w64) (rv : Loc) (rid : w64),
        "i" ∷ i_ptr ↦ n ∗ "reader" ∷ reader_ptr ↦ rv ∗ "rid" ∷ rid_ptr ↦ rid ∗
        "%Hn3" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 3⌝ ∗ "Hr" ∷ rS ↦* rds ∗
        "Hrc" ∷ tri (fun j => if j = k ∨ (j.val : Int) < sint.Z n then iprop(True) else
          iprop(peerReaderB γ j k (rds.getD j.val null) [] ∗ rxCurTok γ.proto j k 0)))
      $$ [i reader rid Hr Hrc]
    · iexists _, _, _
      iframe
      isplitr
      · ipureintro; constructor <;> simp
      have hf : (fun j : Fin 3 => if j = k ∨ (j.val : Int) < sint.Z (W64 0) then iprop(True) else
            iprop(peerReaderB γ j k (rds.getD j.val null) [] ∗ rxCurTok γ.proto j k 0)) =
          (fun j : Fin 3 => if j = k then iprop(True) else
            iprop(peerReaderB γ j k (rds.getD j.val null) [] ∗ rxCurTok γ.proto j k 0)) := by
        funext j; congr 1; simp; omega
      rw [hf]; iexact Hrc
    ipersist Hlis
    ipersist Hw
    ipersist Ha
    iapply fupd_wp
    imod monoListLbOwn_nil (A := model.Ev) (γ.proto.s2.trace k) with #Htlb
    imodintro
    wp_for IHr
    wp_if_destruct
    rotate_left
    · -- every listener started: the run goroutine's token and the listener
      iapply HΦ
      isplitl [Hboot Hrest Hwss Hcurk Hclients]
      · unfold loopTok
        iright
        iframe Hboot Hrest
        unfold pendingOuts
        isplitl
        · unfold netAt
          iexists gR, wS, wsl
          iframe HgR HwS Hw Hclients
          isplitl [Hwss]
          · iapply writers_netAt γ k wsl Hlens.2 $$ Hwss
          isplitl [Hcurk]
          · unfold selfOwn
            iexists 0
            iframe Hcurk
            ipureintro
            show 0 + (sentToR k []).length = _ ∧ (streamOf k k []).drop 0 = sentToR k []
            rw [sentToR_nil, streamOf_nil]; exact ⟨rfl, rfl⟩
          isplitr
          · unfold traceLb; iexact Htlb
          unfold aliveAt; iexists aS; iframe HaS Ha
        simp only [pure.extsIn, List.filterMap_nil]
        iapply BigSepL.bigSepL_nil.2; iempintro
      unfold listenerOwn rid32
      iexists li, l, (ip ++ go!":" ++ port), o
      iframe Hlis Hli Hon Hnl Hlp HportK Hsh
      ipureintro; exact HmemK
    obtain ⟨q, hqn⟩ : ∃ q : Fin 3, sint.Z n = (q.val : Int) :=
      ⟨⟨(sint.Z n).toNat, by omega⟩, by simp; omega⟩
    have hget : rds[(sint.Z n).toNat]? = some (rds.getD q.val null) := by
      have hlt : q.val < rds.length := by rw [Hlens.1]; exact q.isLt
      rw [hqn]; simp only [Int.toNat_natCast]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rw [if_pos (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z rS.len from ⟨by omega, by omega⟩)]
    wp_apply wp_load_slice_index rS (sint.Z n) rds _ _ (by omega) $$ [Hr] as Hr
    · iframe Hr; ipureintro; exact hget
    have hn1 : sint.Z (n + W64 1) = sint.Z n + 1 := by word
    have hW : (W32 (sint.Z n) = rid32 k) ↔ q = k := by
      unfold rid32; rw [hqn]
      constructor
      · intro h; apply Fin.ext
        have := congrArg BitVec.toNat h; simp at this
        first | done | (have := q.isLt; have := k.isLt; omega)
      · intro h; rw [h]
    by_cases hqk : q = k
    · -- own id: skipped
      rw [decide_eq_true (hW.2 hqk)]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      isplitr
      · ipureintro; omega
      ihave ⟨-, Hrc⟩ := tri_acc _ (fun j => if j = k ∨ (j.val : Int) < sint.Z (n + W64 1) then
          iprop(True) else
          iprop(peerReaderB γ j k (rds.getD j.val null) [] ∗ rxCurTok γ.proto j k 0)) q (by
            intro j hj; congr 1; rw [hn1]; apply propext; constructor
            · rintro (h | h); exact Or.inl h; exact Or.inr (by omega)
            · rintro (h | h); exact Or.inl h
              by_cases hjv : (j.val : Int) < sint.Z n
              · exact Or.inr hjv
              · exfalso; apply hj; apply Fin.ext; omega) $$ Hrc
      iapply Hrc
      rw [if_pos (Or.inl hqk)]; itrivial
    · -- a peer: its listener
      rw [decide_eq_false (fun h => hqk (hW.1 h))]
      wp_auto
      ihave ⟨Hq, Hrc⟩ := tri_acc _ (fun j => if j = k ∨ (j.val : Int) < sint.Z (n + W64 1) then
          iprop(True) else
          iprop(peerReaderB γ j k (rds.getD j.val null) [] ∗ rxCurTok γ.proto j k 0)) q (by
            intro j hj; congr 1; rw [hn1]; apply propext; constructor
            · rintro (h | h); exact Or.inl h; exact Or.inr (by omega)
            · rintro (h | h); exact Or.inl h
              by_cases hjv : (j.val : Int) < sint.Z n
              · exact Or.inr hjv
              · exfalso; apply hj; apply Fin.ext; omega) $$ Hrc
      rw [if_neg (by rintro (h | h); exact hqk h; omega)]
      icases Hq with ⟨Hrd, Hcur⟩
      have hnq : n = W64 (q.val : Int) := by
        apply BitVec.eq_of_toInt_eq; show sint.Z n = sint.Z (W64 (q.val : Int)); rw [hqn]
        have := q.isLt; word
      subst hnq
      wp_apply wp_fork $$ [Hrd Hcur]
      · wp_apply Replica.replicaListener.wp γ ρ k q r gR _ [] hqk $$ [Hrd Hcur]
        · iframe; iframe #
          unfold peerReaderAt; iexact Hrd
        itrivial
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      isplitr
      · ipureintro; omega
      iapply Hrc
      rw [if_pos (Or.inr (by omega))]; itrivial
  -- dial peer `q`
  obtain ⟨q, hqv⟩ : ∃ q : Fin 3, sint.Z iv = (q.val : Int) :=
    ⟨⟨(sint.Z iv).toNat, by omega⟩, by simp; omega⟩
  have hbq : below k q = true := by
    unfold below; simp only [decide_eq_true_eq]; rw [Fin.lt_def]; omega
  ihave ⟨Hslot, Hlow⟩ := slots_acc γ k S (below k) _ q hbq $$ Hlow
  have hq0 : (decide ((q.val : Int) < sint.Z iv)) = false := by simp; omega
  rw [hq0]
  iunfold slotOwn at Hslot
  icases Hslot with ⟨%cv0, %rd0, %w0, %al0, Hcells, -⟩
  iunfold cellsAt at Hcells
  icases Hcells with ⟨Hp0, Hr0, Hw0, Ha0⟩
  obtain ⟨aq, haq⟩ : ∃ aq, nodes[q.val]? = some aq := by
    have := q.isLt; exact ⟨_, List.getElem?_eq_getElem (by rw [Hn.1]; exact this)⟩
  ihave #Hq := BigSepL.bigSepL_lookup (Φ := fun i a => iprop(□ portId γ a (W32 (i : Int)) ∗
      addrProto a (gryffWireP γ a) (gryffWireQ γ a) ∗ ⌜a ∈ replicaAddrs⌝)) haq $$ HportsP
  icases Hq with ⟨#HportQ, #HprotoQ, %HmemQ⟩
  ihave #HroleQ := BigSepL.bigSepL_lookup (Φ := fun i a =>
      iprop(□ (if i < k.val then peerRole γ a (rid32 k) else True))) haq $$ HrolesP
  rw [if_pos (show q.val < k.val by omega)]
  ihave IHi : iprop(∃ (d : Bool) (cv : GoInterface) (bb : List w8),
      "done" ∷ done_ptr ↦ d ∗ "Hp0" ∷ sliceIndexRef GoInterface (q.val : Int) S.pS ↦ cv ∗
      "Hb" ∷ slice.mk b_ptr (W64 4) (W64 4) ↦* bb ∗ "%Hbb" ∷ ⌜bb.length = 4⌝ ∗
      "Hc" ∷ (if d then ∃ (tc : Loc) (cid : Nat) (la ra : GoInterface),
        ⌜cv = interface.mkOk (go.GoType.PointerType Perennial.net.TCPConn.ty) #tc⌝ ∗
        Perennial.net.connAt tc cid false aq la ra ∗
        sendTok cid false (gryffWireP γ aq) (u32Le (peerHs k)) ∗
        recvTok cid false (gryffWireQ γ aq) [] else True)) $$ [done Hp0 Hb]
  · iexists false, cv0, bb; iframe; isplitr
    · ipureintro; exact Hbb
    simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  wp_for IHi
  wp_if_destruct
  rotate_left
  · -- the handshake is written: the inner loop ends
    have hd : d = true := by
      cases d
      · exact absurd rfl Hif
      · rfl
    subst hd
    simp only [↓reduceIte]
    rw [if_pos (by simp)]
    icases Hc with ⟨%tc, %cid, %la, %ra, %Hcv, #Hown, Hsend, Hrecv⟩
    subst Hcv
    have hqZ : sint.Z iv = (q.val : Int) := hqv
    have hpS3 : sint.Z pS.len = 3 := hS.1.1
    have hrS3 : sint.Z rS.len = 3 := hS.2.1.1
    have hwS3 : sint.Z wS.len = 3 := hS.2.2.1.1
    have haS3 : sint.Z aS.len = 3 := hS.2.2.2.1
    wp_auto
    rw [if_pos (show 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z aS.len from ⟨by omega, by omega⟩), hqZ]
    wp_auto
    rw [if_pos (show 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z pS.len from ⟨by omega, by omega⟩), hqZ]
    wp_auto
    ihave #Hrok := Perennial.net.conn_readerOk nS.read tc cid false aq la ra eof ed
      (gryffWireQ γ aq) $$ [$Hio $Hown $Heof $Hed]
    ihave Hrecv := recvTok_L $$ Hrecv
    wp_apply wp_NewReader_conn tc eof la ra ed _ [] $$ [$Hbufio $Hrok $Hrecv] as %prd Hprd
    rw [if_pos (show 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z rS.len from ⟨by omega, by omega⟩), hqZ]
    wp_auto
    rw [if_pos (show 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z pS.len from ⟨by omega, by omega⟩), hqZ]
    wp_auto
    ihave #Hwok := Perennial.net.conn_streamWriterOk nS.write tc cid false aq la ra ed
      (gryffWireP γ aq) (gryffWireP_closed γ aq) $$ [$Hown $Hed]
    ihave #HroleQ' : □ peerRole γ aq (W32 (k.val : Int)) $$ []
    · iintro !>; unfold rid32; iexact HroleQ
    ihave #Hbr := dialer_bridge γ k q aq cid $$ [$HroleQ' $HportQ]
    iapply fupd_wp
    imod peerStream_nil_upd γ.proto k q ws $$ Hpred with #Hps0
    imodintro
    ihave #HP0 := Hbr $$ %([] : List w8) Hps0
    ihave #HP1 : □ gryffWireP γ aq cid (u32Le (peerHs k)) $$ []
    · iintro !>; simp only [List.append_nil]; iexact HP0
    ihave ⟨Hsend, #Hlb⟩ := sendTok_sentLb cid false _ _ $$ Hsend
    wp_apply wp_NewWriter_conn tc la ra ed _ _ (u32Le (peerHs k))
      $$ [$Hbufio $Hwok $Hsend $HP1] as %pw Hpw
    rw [if_pos (show 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z wS.len from ⟨by omega, by omega⟩), hqZ]
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
        iexists connRSt tc eof la ra ed, _, [], []
        isplitr
        · unfold wire.readerOk; iframe Hio Hbufio
        isplitl [Hprd]
        · rw [show ([] : List w8) ++ [] = [] from rfl]; iexact Hprd
        isplitr
        · ipureintro; exact ⟨[], .nil, rfl⟩
        iapply dial_reader γ aq HmemQ cid k q prd (connRSt tc eof la ra ed) $$ [$HportQ $Hlb]
      · iunfold peerWriterB
        iexists ⟨Perennial.net.connIface tc, Perennial.net.connWriteE la ra ed, 4096⟩,
          sendTok cid false (gryffWireP γ aq), gryffWireP γ aq cid,
          u32Le (peerHs k), [], u32Le (peerHs k), [], interface.nil
        iframe Hpw Hwok
        isplitr
        · ipureintro
          exact ⟨⟨[], .nil, rfl⟩, by simp, fun _ => ⟨rfl, by simp⟩⟩
        isplitr
        · iexact Hbr
        iexists ws; iexact Hpred
    ihave Hlow := Hlow $$ %true Hfilled
    have hqk : q.val < k.val := by unfold below at hbq; simp at hbq; exact hbq
    have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
    wp_for_post
    iframe
    iexists _, _
    iframe
    isplitr
    · ipureintro; omega
    isplitl
    · iapply slots_congr _ _ _ _ _ _ _ $$ Hlow
      intro j _
      unfold upd
      rw [hiv1]
      split
      · subst_vars; simp; omega
      · rename_i hjq
        have : (j.val : Int) ≠ sint.Z iv := by
          intro h; apply hjq; apply Fin.ext; omega
        simp only [decide_eq_decide]; omega
    ipureintro; exact Hbb
  have hd : d = false := by
    cases d
    · rfl
    · exact absurd Hif (show (#false : val) ≠ #true from fun h => absurd (go.intoVal_inj h) (by decide))
  subst hd
  have hqZ : sint.Z iv = (q.val : Int) := hqv
  ihave %Hpall := ownSlice_len _ _ _ $$ Hnodes
  have hpal : sint.Z pal.len = 3 := by
    obtain ⟨h1, h2⟩ := Hpall; rw [Hn.1] at h1; unfold sint.nat at h1
    simp only [sint.Z] at h2; show pal.len.toInt = 3; omega
  have hiv3 : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z pal.len := ⟨by omega, by omega⟩
  rw [if_pos hiv3]
  wp_apply wp_load_slice_index pal (sint.Z iv) nodes _ aq (by omega) $$ [Hnodes] as -
  · iframe Hnodes; ipureintro; rw [hqZ]; simpa using haq
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply log.wp_Printf_logArg _ _ _ _ $$ [$Hsl1] as -
  · iintro !>; rw [set_two]
    iapply (logArgs_of_wf _ (.cons_int _ _ _ (.int _) (.cons_string _ _ .nil)))
  rw [if_pos hiv3]
  wp_apply wp_load_slice_index pal (sint.Z iv) nodes _ aq (by omega) $$ [Hnodes] as -
  · iframe Hnodes; ipureintro; rw [hqZ]; simpa using haq
  ihave %Haok := addrTok_ok aq $$ [HprotoQ]
  · iapply addrProto_tok $$ HprotoQ
  wp_apply (nS.dial go!"tcp" Perennial.net.tcpNet_tcp aq iprop(True)
      (fun cn => iprop(connEnd cn false (gryffWireP γ aq) (gryffWireQ γ aq) [] [] ∗
        connFresh cn false))) $$ [] as %cv %derr Hres
  · isplitr
    · ipureintro; exact Haok
    isplit
    · itrivial
    · iapply dial_au $$ HprotoQ
  icases Hres with (⟨%Hderr, %cid, #Hcc, Hend, -⟩ | ⟨-, %x, -, #Hre⟩)
  rotate_left
  · -- the dial failed: retry
    ihave ⟨%Hne, #HeA⟩ := resErr_errAny _ _ _ _ _ _ _ $$ Hre
    obtain ⟨ie, rfl⟩ : ∃ ie, derr = interface.ok ie := by
      cases derr with
      | nil => exact absurd rfl Hne
      | ok ie => exact ⟨ie, rfl⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply log.wp_Printf_logArg _ _ _ _ $$ [$Hsl2] as -
    · iintro !>; rw [set_two]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply logArg_int
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_err $$ HeA
    wp_apply time.wp_Sleep
    wp_for_post
    iframe
    iexists false, _, _
    iframe
    ipureintro; exact Hbb
  subst Hderr
  iunfold Perennial.net.isConn at Hcc
  icases Hcc with ⟨%tc, %la, %ra, %Hcv, #Hown⟩
  subst Hcv
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %sl3 ⟨Hsl3, -⟩
  wp_apply log.wp_Printf_logArg _ _ _ _ $$ [$Hsl3] as -
  · iintro !>; rw [set_two]
    iapply (logArgs_of_wf _ (.cons_int _ _ _ (.int32 _) (.cons_int _ _ _ (.int _) .nil)))
  rw [show bb = bb ++ [] from (List.append_nil bb).symm]
  wp_apply encoding.binary.wp_LittleEndian_PutUint32 _ bb [] _ Hbb $$ [$Hbin $Hb] as Hb
  rw [show rid32 k ||| W32 2147483648 = peerHs k from rfl, List.append_nil]
  iunfold connEnd at Hend
  icases Hend with ⟨Hsend, Hrecv⟩
  ihave #HroleQ' : □ peerRole γ aq (W32 (k.val : Int)) $$ []
  · iintro !>; unfold rid32; iexact HroleQ
  ihave #Hbr := dialer_bridge γ k q aq cid $$ [$HroleQ' $HportQ]
  iapply fupd_wp
  imod peerStream_nil_upd γ.proto k q ws $$ Hpred with #Hps0
  imodintro
  ihave #HP0 := Hbr $$ %([] : List w8) Hps0
  simp only [List.append_nil]
  ihave #HP1 : □ gryffWireP γ aq cid ([] ++ u32Le (peerHs k)) $$ []
  · iintro !>; rw [List.nil_append]; iexact HP0
  ihave #Hwok := Perennial.net.conn_streamWriterOk nS.write tc cid false aq la ra ed
    (gryffWireP γ aq) (gryffWireP_closed γ aq) $$ [$Hown $Hed]
  wp_apply wp_conn_Write tc _ _ _ []
    _ (DFrac.own 1) (u32Le (peerHs k)) $$ [$Hwok $Hsend $HP1 $Hb] as %nw %werr ⟨%kw, %Hw, Hb, Hsend, #Hwe⟩
  obtain ⟨hnw, hkw, hwnil⟩ := Hw
  cases werr with
  | ok wi =>
    -- the handshake's write failed: close, redial
    wp_auto
    iunfold EtcdGrove.io.werrAt at Hwe
    icases Hwe with (%Hn | #Hwe)
    · cases Hn
    iunfold Perennial.net.connWriteE at Hwe
    icases Hwe with ⟨%kk, #Hre⟩
    ihave ⟨-, #HeA⟩ := resErr_errAny _ _ _ _ _ _ _ $$ Hre
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %sl4 ⟨Hsl4, -⟩
    wp_apply log.wp_Println_logArg _ _ _ $$ [$Hsl4] as -
    · iintro !>; rw [set_two]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply logArg_string
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_err $$ HeA
    ihave #Hci := sendTok_connIs $$ Hsend
    wp_apply (nS.close tc cid false aq la ra (fun _ => iprop(True))) $$ [] as %cerr -
    · iframe Hown
      imod close_au cid false $$ Hci with ⟨%st, %d, He, Hd, Hk⟩
      imodintro
      iexists st, d
      iframe He Hd
      iintro %res %st' %d' %Hco He Hd
      imod Hk $$ %res %st' %d' %Hco He Hd with -
      imodintro; itrivial
    wp_apply time.wp_Sleep
    wp_for_post
    iframe
    iexists false, _, _
    iframe
    ipureintro; simp [u32Le_length]
  | nil =>
  have hk4 : kw = 4 := by rw [hwnil rfl]; simp [u32Le_length]
  subst hk4
  wp_auto
  have hpS3 : sint.Z pS.len = 3 := hS.1.1
  rw [if_pos (show 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z pS.len from ⟨by omega, by omega⟩), hqZ]
  wp_auto
  wp_for_post
  iframe
  iexists true, _, _
  iframe
  isplitr
  · ipureintro; simp [u32Le_length]
  simp only [↓reduceIte]
  iexists tc, cid, la, ra
  iframe Hown
  isplitr
  · ipureintro; rfl
  simp only [List.nil_append, List.take_of_length_le (show (u32Le (peerHs k)).length ≤ 4 by simp [u32Le_length])]
  iframe

end

end Perennial.gryff.netN
