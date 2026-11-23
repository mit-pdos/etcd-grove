/-
`SendMsg`: the protocol message `m` to peer `t`, under `r.M`, with the caller's send update.
-/
module

public import Proof.bufio.Writer__WriteByte
public import Proof.bufio.Writer__Flush
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Log

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

/-- The stream of peer `t`'s connection may continue with the next protocol message `m` (its
`msgSent` at the next position). -/
theorem slot_send_ok (γ : EpNames) (id : Nat) (L : List GoString) (t : Nat) (cid : Nat)
    (side : Bool) (ws : List Msg) (m : Msg) (ht : t < L.length) (hid : id < L.length) (hL : L.length = 5)
    (hwf : ∀ x ∈ ws, x.wf) (hm : m.wf) (hp : m.isProto = true) :
    listFinal (GF := GF) γ L -∗ roleElem γ cid (.peer (W64 (dialerOf id t side))) -∗
      peerConn γ (if side then t else id) (if side then id else t) cid -∗
      sentHalf γ id t (protoMsgs ws ++ [m]) -∗
      sentHalf γ id t (protoMsgs ws ++ [m]) ∗
      □ peerPX γ id L t side cid
        (streamHdr (dialerOf id t side) side ++ (ws ++ [m]).flatMap encMsg) := by
  iintro #Hlf #Hrole #Hpc Hs
  ihave ⟨Hs, #Hall⟩ := sentHalf_all $$ Hs
  iframe Hs
  icases (BigSepL.bigSepL_snoc).1 $$ Hall with ⟨#Hws, #Hm⟩
  have hdl : ∀ (i : Nat) (h : i < L.length), L[i]? = some (L.getD i []) := fun i h => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl
  imodintro
  cases side
  · -- we dialed `t`: the dialers' protocol of `t`'s address
    unfold peerPX dialerOf
    simp only [Bool.false_eq_true, ite_false]
    ihave #Ha := listFinal_addrId γ L t _ (hdl t ht) $$ Hlf
    unfold repDialP
    iright
    iexists _
    iframe Hrole
    simp only
    have hd : uint.nat (W64 (id : Int)) = id := by
      have : id < 5 := by omega
      word
    ihave Hok := peerStreamOk_snoc (GF := GF) γ (L.getD t []) (W64 (id : Int)) false cid t ws m hm $$ Ha
    rw [hd] at *
    unfold streamDir
    simp only [Bool.false_eq_true, ite_false, hp, ite_true]
    iapply Hok $$ Hpc %hwf Hws Hm
  · -- `t` dialed us: the acceptors' protocol of our address
    unfold peerPX dialerOf
    simp only [ite_true]
    ihave #Ha := listFinal_addrId γ L id _ (hdl id hid) $$ Hlf
    unfold repAccP
    iright
    iexists _
    iframe Hrole
    simp only
    have hd : uint.nat (W64 (t : Int)) = t := by
      have : t < 5 := by omega
      word
    ihave Hok := peerStreamOk_snoc (GF := GF) γ (L.getD id []) (W64 (t : Int)) true cid id ws m hm $$ Ha
    rw [hd] at *
    unfold streamDir
    simp only [ite_true, hp]
    iapply Hok $$ [] %hwf Hws Hm
    itrivial

theorem msgObj_ok (obj : GoInterface) (m : Msg) (dq dq1 dq2 : DFrac) :
    msgObj (GF := GF) obj m dq dq1 dq2 ⊢ msgObj obj m dq dq1 dq2 ∗ ⌜∃ e, obj = interface.ok e⌝ := by
  unfold msgObj
  iintro ⟨%k, %l, %Hk, Hm⟩
  isplitl
  · iexists k, l; iframe; ipureintro; exact Hk
  · ipureintro; exact ⟨_, Hk.2⟩

theorem protoMsgs_snoc' (ws : List Msg) (m : Msg) :
    protoMsgs (ws ++ [m]) = protoMsgs ws ++ (if m.isProto then [m] else []) := by
  unfold protoMsgs; rw [List.filter_append]; cases h : m.isProto <;> simp [List.filter, h]

/-- What a write's prefix-closure step needs (`ProtoPrefixClosed.pre`). -/
theorem prefix_of_eq {A B c : List w8} (h : A = B ++ c) : B <+: A := h ▸ List.prefix_append B c

/-- The stream after `SendMsg`'s three writes: whole messages again when the writer is healthy. -/
theorem send_stream_eq (hdr old : List w8) (code : w8) (body : List w8)
    (sent pend sent1 pend1 sent2 pend2 : List w8) (err e1 e2 e3 : GoInterface) (k : Nat)
    (hst : err = interface.nil → sent ++ pend = hdr ++ old)
    (h1 : sent <+: sent1 ∧ (e1 = interface.nil → sent1 ++ pend1 = sent ++ pend ++ [code]) ∧
      (e1 ≠ interface.nil → sent1 ++ pend1 = sent ++ pend) ∧ (err ≠ interface.nil → e1 = err))
    (h2 : wroteSome sent1 pend1 body sent2 pend2 e1 e2)
    (h3 : k ≤ pend2.length ∧ (e3 = interface.nil → k = pend2.length) ∧
      (e2 ≠ interface.nil → e3 = e2 ∧ k = 0)) :
    e3 = interface.nil →
      (sent2 ++ pend2.take k) ++ pend2.drop k = hdr ++ (old ++ ([code] ++ body)) := by
  intro he3
  have he2 : e2 = interface.nil := by
    by_cases h : e2 = interface.nil
    · exact h
    · exact absurd ((h3.2.2 h).1 ▸ he3) h
  have he1 : e1 = interface.nil := by
    by_cases h : e1 = interface.nil
    · exact h
    · exact absurd ((h2.2.2.2.2 h).1 ▸ he2) h
  have herr : err = interface.nil := by
    by_cases h : err = interface.nil
    · exact h
    · exact absurd (h1.2.2.2 h ▸ he1) h
  rw [List.append_assoc, List.take_append_drop, h2.2.2.2.1 he2, h1.2.1 he1, hst herr]
  simp [List.append_assoc]

theorem replica.Replica.SendMsg.spec_holds (hPrintf : dlog.Logger.Printf.spec (GF := GF))
    (hM : Serializable.Marshal.spec (GF := GF)) (hNN : BufWriterNotNull (GF := GF)) :
    replica.Replica.SendMsg.spec (GF := GF) := by
  intro γ r id L p Rext t msg m dq dq1 dq2 Ψ Ψnil
  wp_start as ⟨%Ht, #Hfw, Hmsg, Hupd⟩
  ihave #Hfw' := isReplicaFw_def $$ Hfw
  iunfold isReplicaFwDef at Hfw'
  icases Hfw' with ⟨#Hro, #Hfz, #Hmu, #Hph1, #Hph2⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, -, -, -, #HPeers, #HReaders, #HWriters, -, -, -, -, #HAlive,
    -, -, -, -, -, #HShut, -, -, -, -, -, -, -, -, -, %HL, #HLf, #HCI, -, -⟩
  unfold fwMethod
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold fwLockInv at HR
  icases HR with ⟨Hcore, HRext⟩
  ihave Hacc := fwCore_peers_acc (GF := GF) γ id L p ⊤ CoPset.subseteq_top $$ Hph1 Hcore Hlc1
  iapply fupd_wp
  imod Hacc with ⟨Hpeers, Hcore⟩
  imodintro
  icases fwPeers_open γ id L _ _ _ _ _ t Ht.1 Ht.2.1 $$ Hpeers
    with ⟨%cs, %ws, %als, %ls, Hps, Hws, Has, Hls, %Hlen, Hslot, Hpeers⟩
  ihave %Hwl := ownSlice_len _ _ _ $$ Hws
  have hL5 : L.length = 5 := HL.1
  have ht5 : t < 5 := by have := Ht.1; omega
  have htz : sint.Z (W64 (sint.Z (W32 (t : Int)))) = (t : Int) := by word
  have hws5 : ws.length = 5 := by rw [Hlen.2.1, hL5]
  have hwlen : sint.Z p.writers.len = 5 := by
    have h1 := Hwl.1; rw [hws5] at h1; have h2 := Hwl.2; word
  rw [htz, if_pos (show 0 ≤ (t : Int) ∧ (t : Int) < sint.Z p.writers.len by omega)]
  have hwt : ws[t]? = some (ws.getD t null) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  wp_apply wp_load_slice_index p.writers (t : Int) ws (DFrac.own 1) (ws.getD t null) (by omega)
    $$ [Hws] as Hws
  · iframe; ipureintro; simpa using hwt
  ihave Hpeers := Hpeers $$ %(cs.getD t interface.nil) %(ws.getD t null) %(als.getD t false)
  rw [set_getD_self cs t _ (by omega), set_getD_self ws t _ (by omega),
    set_getD_self als t _ (by omega)]
  unfold peerSlotX
  icases Hslot with ⟨%ms, Hs, (⟨%Hw, %Hc, %Hms, Hdf⟩ | ⟨%cid, %side, Hconn⟩)⟩
  · -- not connected: nothing is sent
    rw [Hw]
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.any)
    wp_auto
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr ⟨-, -⟩
    wp_auto
    wp_apply wp_rPrintf hPrintf γ r id L p $$ [$Hro]
    ihave Hpeers := Hpeers $$ Hps Hws Has Hls [Hs Hdf]
    · iexists ms; iframe; ileft; iframe; ipureintro; exact ⟨by simp [Hw], Hc, Hms⟩
    ihave Hcore := Hcore $$ Hpeers
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
    · unfold fwLockInv; iframe
    icases Hupd with ⟨-, Hnil⟩
    iapply HΦ
    iframe
  · -- connected: the update runs, then code and body are written
    unfold slotConn
    icases Hconn with ⟨%sent, %pend, %err, %wsm, %tc, %la, %ra, %ed, %eof, #Hci, #Hpc, #Hrole, Hw,
      %Hpure, Hfr⟩
    ihave ⟨Hw, %Hnn⟩ := hNN _ _ _ _ _ _ _ _ _ $$ Hw
    rw [show decide (ws.getD t null = null) = false by
      simp only [decide_eq_false_iff_not]; exact Hnn]
    wp_auto
    icases Hupd with ⟨Hupd, -⟩
    unfold sendUpd
    ihave Hu := Hupd $$ %ms Hs
    iapply fupd_wp
    imod Hu with ⟨Hs, HΨ⟩
    imodintro
    obtain ⟨hpm, hwf, hst⟩ := Hpure
    subst hpm
    ihave ⟨Hs, #HQ⟩ := slot_send_ok γ id L t cid side wsm m Ht.1 HL.2 hL5 hwf Ht.2.2.2 Ht.2.2.1
      $$ HLf Hrole Hpc Hs
    ihave #Hep := fwFrozen_epaxos $$ Hfz
    have hppc := peerPX_ppc (GF := GF) γ id L t side
    have hfull : streamHdr (dialerOf id t side) side ++ (wsm ++ [m]).flatMap encMsg =
        (streamHdr (dialerOf id t side) side ++ wsm.flatMap encMsg ++ [m.code]) ++ m.body := by
      simp [encMsg, List.flatMap_append, List.append_assoc]
    wp_apply EtcdGrove.bufio.Writer.WriteByte.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof
      (ws.getD t null) _ _ _ _ _ sent pend err m.code
      $$ [$Hw] as %e1 ⟨%sent1, %pend1, %Hw1, Hw⟩
    · iintro %He
      have h1 := hst He
      rw [h1]
      simp only [connWr]
      have hpre : streamHdr (dialerOf id t side) side ++ wsm.flatMap encMsg ++ [m.code] <+:
          streamHdr (dialerOf id t side) side ++ (wsm ++ [m]).flatMap encMsg := by
        rw [hfull]; exact List.prefix_append _ _
      have hd : (if side = true then t else id) = dialerOf id t side := rfl
      rw [hd]
      iapply hppc.pre cid _ _ hpre $$ HQ
    ihave ⟨Hmsg, %Hok⟩ := msgObj_ok $$ Hmsg
    obtain ⟨e, he⟩ := Hok
    subst he
    wp_auto
    rw [show interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #(ws.getD t null) =
      bwIface (ws.getD t null) from rfl]
    wp_apply (hM _ e m dq dq1 dq2 rfl (ws.getD t null)
      (connWr tc cid side la ra ed (peerPX γ id L t side) hppc 4096) sent1 pend1 e1) $$ [Hw Hmsg]
      as ⟨Hmsg, %sent2, %pend2, %e2, %Hw2, Hw⟩
    · simp only [connWr]
      iframe Hw Hmsg
      iintro %He
      obtain ⟨_, h1a, _, h1c, _⟩ := Hw1
      have herr : err = interface.nil := by
        by_cases h : err = interface.nil
        · exact h
        · exact absurd ((h1c h).1 ▸ He) h
      rw [h1a He, hst herr]
      rw [show streamHdr (if side = true then t else id) side ++ List.flatMap encMsg wsm ++ [m.code] ++
          m.body = streamHdr (dialerOf id t side) side ++ List.flatMap encMsg (wsm ++ [m]) by
        unfold dialerOf; simp [encMsg, List.flatMap_append, List.append_assoc]]
      iexact HQ
    wp_apply EtcdGrove.bufio.Writer.Flush.wp_proof (ws.getD t null) _ _ _ _ _ sent2 pend2 e2
      $$ [$Hw] as %e3 ⟨%k, %Hk3, Hw⟩
    have Hw1' : sent <+: sent1 ∧ (e1 = interface.nil → sent1 ++ pend1 = sent ++ pend ++ [m.code]) ∧
        (e1 ≠ interface.nil → sent1 ++ pend1 = sent ++ pend) ∧ (err ≠ interface.nil → e1 = err) :=
      ⟨Hw1.1, Hw1.2.1, Hw1.2.2.1, fun h => (Hw1.2.2.2.1 h).1⟩
    ihave Hslot : peerSlotX γ id L p.ewma t (cs.getD t interface.nil) (ws.getD t null) $$ [Hs Hw Hfr]
    · unfold peerSlotX
      iexists protoMsgs (wsm ++ [m])
      rw [protoMsgs_snoc', if_pos Ht.2.2.1]
      iframe Hs
      iright
      iexists cid, side
      unfold slotConn
      iexists sent2 ++ pend2.take k, pend2.drop k, e3, wsm ++ [m], tc, la, ra, ed, eof
      simp only [wrOwn, connWr]
      iframe; iframe #
      ipureintro
      refine ⟨protoMsgs_snoc' wsm m ▸ by rw [if_pos Ht.2.2.1], ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hwf x hx
        · simp at hx; subst hx; exact Ht.2.2.2
      · intro he3
        rw [send_stream_eq _ _ m.code m.body sent pend sent1 pend1 sent2 pend2 err e1 e2 e3 k
          hst Hw1' Hw2 Hk3 he3]
        simp [encMsg, List.flatMap_append, List.append_assoc]
    iunfold peerSlotX at Hslot
    iunfold slotConn at Hslot
    ihave Hpeers := Hpeers $$ Hps Hws Has Hls Hslot
    ihave Hcore := Hcore $$ Hpeers
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
    · unfold fwLockInv; iframe
    iapply HΦ
    iframe
  done

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
