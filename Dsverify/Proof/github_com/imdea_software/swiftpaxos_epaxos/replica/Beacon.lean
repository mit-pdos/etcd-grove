/-
`ReplyBeacon` and `SendBeacon`: a beacon (reply) to a peer, under `r.M`, if connected. Not a
protocol message: the stream continues with it (`peerStreamOk_snoc`), no position is taken.
The internal specs need only phase 1 (the peer cells deposited): the reader goroutines answer
beacons before `ConnectToPeers` has deposited the readers slice.
-/
module

public import Proof.bufio.Writer__WriteByte
public import Proof.bufio.Writer__Flush
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.SendMsg
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos_epaxos.replica.defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

/-- The stream of peer `t`'s connection may continue with a beacon (reply) `m`. -/
theorem slot_beacon_ok (γ : EpNames) (id : Nat) (L : List GoString) (t : Nat) (cid : Nat)
    (side : Bool) (ws : List Msg) (m : Msg) (ht : t < L.length) (hid : id < L.length)
    (hL : L.length = 5) (hwf : ∀ x ∈ ws, x.wf) (hm : m.wf) (hp : m.isProto = false) :
    listFinal (GF := GF) γ L -∗ roleElem γ cid (.peer (W64 (dialerOf id t side))) -∗
      peerConn γ (if side then t else id) (if side then id else t) cid -∗
      sentHalf γ id t (protoMsgs ws) -∗
      sentHalf γ id t (protoMsgs ws) ∗
      □ peerPX γ id L t side cid
        (streamHdr (dialerOf id t side) side ++ (ws ++ [m]).flatMap encMsg) := by
  iintro #Hlf #Hrole #Hpc Hs
  ihave ⟨Hs, #Hall⟩ := sentHalf_all $$ Hs
  iframe Hs
  have hdl : ∀ (i : Nat) (h : i < L.length), L[i]? = some (L.getD i []) := fun i h => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl
  imodintro
  cases side
  · unfold peerPX dialerOf
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
    simp only [Bool.false_eq_true, ite_false, hp]
    iapply Hok $$ Hpc %hwf Hall
    itrivial
  · unfold peerPX dialerOf
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
    simp only [ite_true, hp, Bool.false_eq_true, ite_false]
    iapply Hok $$ [] %hwf Hall
    · itrivial
    itrivial

theorem protoMsgs_snoc_beacon (ws : List Msg) (m : Msg) (hp : m.isProto = false) :
    protoMsgs (ws ++ [m]) = protoMsgs ws := by
  rw [protoMsgs_snoc', hp]; simp

/-- `r.ReplyBeacon(b)` (internal: phase 1 is enough). -/
def replica.Replica.ReplyBeacon.specI : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (b : Loc) (dq : DFrac) (t : Nat) (ts : w64),
  {{ pkgInit_replica ∗ ⌜t < L.length ∧ t ≠ id⌝ ∗ fwRun0 γ r id L p Rext ∗ fwPhase1 γ id ∗
      b ↦{dq} replica.defs.GBeacon.mk (W32 t) ts }}
    (App (Val (fwMethod r go!"ReplyBeacon")) (Val #b))
  {{ RET #(); b ↦{dq} replica.defs.GBeacon.mk (W32 t) ts }}

theorem replica.Replica.ReplyBeacon.specI_holds (hPrintf : dlog.Logger.Printf.spec (GF := GF))
    (hM : replica.defs.BeaconReply.Marshal.spec (GF := GF)) :
    replica.Replica.ReplyBeacon.specI (GF := GF) := by
  intro γ r id L p Rext b dq t ts
  wp_start as ⟨%Ht, #Hrun, #Hph1, Hb⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hb with ⟨Hb, %Hbn⟩
  iStructNamed Hb
  unfold fwRun0
  icases Hrun with ⟨#Hro, #Hmu⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, -, -, -, #HPeers, #HReaders, #HWriters, -, -, -, -,
    #HAlive, -, -, -, -, -, #HShut, -, -, -, -, -, -, -, -, -, %HL, #HLf, #HCI, -, -⟩
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
  icases fwPeers_open γ id L _ _ _ _ _ t Ht.1 Ht.2 $$ Hpeers
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
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hbn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · -- connected: code and body are written
    unfold slotConn
    icases Hconn with ⟨%sent, %pend, %err, %wsm, %tc, %la, %ra, %ed, %eof, #Hci, #Hpc, #Hrole, Hw,
      %Hpure, Hfr⟩
    ihave ⟨Hw, %Hnn⟩ := bufWriterNotNull _ _ _ _ _ _ _ _ _ $$ Hw
    rw [show decide (ws.getD t null = null) = false by
      simp only [decide_eq_false_iff_not]; exact Hnn]
    wp_auto
    obtain ⟨hpm, hwf, hst⟩ := Hpure
    subst hpm
    have hm : (Msg.beaconReply ts).wf := by simp [Msg.wf]
    ihave ⟨Hs, #HQ⟩ := slot_beacon_ok γ id L t cid side wsm (Msg.beaconReply ts) Ht.1 HL.2 hL5 hwf hm
      rfl $$ HLf Hrole Hpc Hs
    have hppc := peerPX_ppc (GF := GF) γ id L t side
    have hfull : streamHdr (dialerOf id t side) side ++ (wsm ++ [Msg.beaconReply ts]).flatMap encMsg =
        (streamHdr (dialerOf id t side) side ++ wsm.flatMap encMsg ++ [W8 7]) ++ encBeacon ts := by
      simp [encMsg, Msg.code, Msg.body, List.flatMap_append, List.append_assoc]
    wp_apply EtcdGrove.bufio.Writer.WriteByte.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof
      (ws.getD t null) _ _ _ _ _ sent pend err (W8 7)
      $$ [$Hw] as %e1 ⟨%sent1, %pend1, %Hw1, Hw⟩
    · iintro %He
      have h1 := hst He
      rw [h1]
      simp only [connWr]
      have hd : (if side = true then t else id) = dialerOf id t side := rfl
      rw [hd]
      iapply hppc.pre cid _ _ (prefix_of_eq hfull) $$ HQ
    rw [show interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #(ws.getD t null) =
      bwIface (ws.getD t null) from rfl]
    wp_apply (hM _ (DFrac.own 1) ts (ws.getD t null)
      (connWr tc cid side la ra ed (peerPX γ id L t side) hppc 4096) sent1 pend1 e1)
      $$ [Hw «$r0»]
      as ⟨Hrb, %sent2, %pend2, %e2, %Hw2, Hw⟩
    · simp only [connWr]
      iframe
      iintro %He
      obtain ⟨_, h1a, _, h1c, _⟩ := Hw1
      have herr : err = interface.nil := by
        by_cases h : err = interface.nil
        · exact h
        · exact absurd ((h1c h).1 ▸ He) h
      rw [h1a He, hst herr]
      unfold dialerOf at hfull
      rw [← hfull]
      imodintro
      iexact HQ
    wp_apply EtcdGrove.bufio.Writer.Flush.wp_proof (ws.getD t null) _ _ _ _ _ sent2 pend2 e2
      $$ [$Hw] as %e3 ⟨%k, %Hk3, Hw⟩
    ihave Hslot : peerSlotX γ id L p.ewma t (cs.getD t interface.nil) (ws.getD t null) $$ [Hs Hw Hfr]
    · unfold peerSlotX
      iexists protoMsgs (wsm ++ [Msg.beaconReply ts])
      rw [protoMsgs_snoc_beacon wsm _ rfl]
      iframe Hs
      iright
      iexists cid, side
      unfold slotConn
      iexists sent2 ++ pend2.take k, pend2.drop k, e3, wsm ++ [Msg.beaconReply ts], tc, la, ra, ed, eof
      simp only [wrOwn, connWr]
      iframe; iframe #
      ipureintro
      refine ⟨protoMsgs_snoc_beacon wsm _ rfl, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hwf x hx
        · simp at hx; subst hx; exact hm
      · intro he3
        rw [send_stream_eq _ _ (W8 7) (encBeacon ts) sent pend sent1 pend1 sent2 pend2 err e1 e2 e3 k
          hst ⟨Hw1.1, Hw1.2.1, Hw1.2.2.1, fun h => (Hw1.2.2.2.1 h).1⟩ Hw2 Hk3 he3]
        simp [encMsg, Msg.code, Msg.body, List.flatMap_append, List.append_assoc]
    iunfold peerSlotX at Hslot
    iunfold slotConn at Hslot
    ihave Hpeers := Hpeers $$ Hps Hws Has Hls Hslot
    ihave Hcore := Hcore $$ Hpeers
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
    · unfold fwLockInv; iframe
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hbn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  done

theorem replica.Replica.ReplyBeacon.spec_holds (hPrintf : dlog.Logger.Printf.spec (GF := GF))
    (hM : replica.defs.BeaconReply.Marshal.spec (GF := GF)) :
    replica.Replica.ReplyBeacon.spec (GF := GF) := by
  intro γ r id L p Rext b dq t ts
  wp_start as ⟨%Ht, #Hfw, Hb⟩
  ihave #Hfw' := isReplicaFw_def $$ Hfw
  iunfold isReplicaFwDef at Hfw'
  icases Hfw' with ⟨#Hro, #Hfz, #Hmu, #Hph1, #Hph2⟩
  wp_apply (replica.Replica.ReplyBeacon.specI_holds hPrintf hM γ r id L p Rext b dq t ts) $$ [Hb] as Hb
  · unfold fwRun0; iframe; iframe #; ipureintro; exact Ht
  iapply HΦ; iexact Hb

theorem replica.Replica.SendBeacon.spec_holds (hPrintf : dlog.Logger.Printf.spec (GF := GF))
    (hM : replica.defs.Beacon.Marshal.spec (GF := GF)) (hNow : time.Now.spec (GF := GF))
    (hNano : time.Time.UnixNano.spec (GF := GF)) :
    replica.Replica.SendBeacon.spec (GF := GF) := by
  intro γ r id L p Rext t
  wp_start as ⟨%Ht, #Hfw⟩
  ihave #Hfw' := isReplicaFw_def $$ Hfw
  iunfold isReplicaFwDef at Hfw'
  icases Hfw' with ⟨#Hro, #Hfz, #Hmu, #Hph1, #Hph2⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, -, -, -, #HPeers, #HReaders, #HWriters, -, -, -, -,
    #HAlive, -, -, -, -, -, #HShut, -, -, -, -, -, -, -, -, -, %HL, #HLf, #HCI, -, -⟩
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
  icases fwPeers_open γ id L _ _ _ _ _ t Ht.1 Ht.2 $$ Hpeers
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
    iapply HΦ
    itrivial
  · -- connected: code and body are written
    unfold slotConn
    icases Hconn with ⟨%sent, %pend, %err, %wsm, %tc, %la, %ra, %ed, %eof, #Hci, #Hpc, #Hrole, Hw,
      %Hpure, Hfr⟩
    ihave ⟨Hw, %Hnn⟩ := bufWriterNotNull _ _ _ _ _ _ _ _ _ $$ Hw
    rw [show decide (ws.getD t null = null) = false by
      simp only [decide_eq_false_iff_not]; exact Hnn]
    wp_auto
    obtain ⟨hpm, hwf, hst⟩ := Hpure
    subst hpm
    have hm0 : (Msg.beacon (W64 0)).wf := by simp [Msg.wf]
    ihave ⟨Hs, #HQ0⟩ := slot_beacon_ok γ id L t cid side wsm (Msg.beacon (W64 0)) Ht.1 HL.2 hL5 hwf
      hm0 rfl $$ HLf Hrole Hpc Hs
    have hppc := peerPX_ppc (GF := GF) γ id L t side
    have hfull0 : streamHdr (dialerOf id t side) side ++ (wsm ++ [Msg.beacon (W64 0)]).flatMap encMsg =
        (streamHdr (dialerOf id t side) side ++ wsm.flatMap encMsg ++ [W8 6]) ++ encBeacon (W64 0) := by
      simp [encMsg, Msg.code, Msg.body, List.flatMap_append, List.append_assoc]
    wp_apply EtcdGrove.bufio.Writer.WriteByte.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof
      (ws.getD t null) _ _ _ _ _ sent pend err (W8 6)
      $$ [$Hw] as %e1 ⟨%sent1, %pend1, %Hw1, Hw⟩
    · iintro %He
      have h1 := hst He
      rw [h1]
      simp only [connWr]
      have hd : (if side = true then t else id) = dialerOf id t side := rfl
      rw [hd]
      iapply hppc.pre cid _ _ (prefix_of_eq hfull0) $$ HQ0
    wp_apply hNow as %tm _
    wp_apply hNano as %ts _
    have hm : (Msg.beacon ts).wf := by simp [Msg.wf]
    ihave ⟨Hs, #HQ⟩ := slot_beacon_ok γ id L t cid side wsm (Msg.beacon ts) Ht.1 HL.2 hL5 hwf hm
      rfl $$ HLf Hrole Hpc Hs
    have hfull : streamHdr (dialerOf id t side) side ++ (wsm ++ [Msg.beacon ts]).flatMap encMsg =
        (streamHdr (dialerOf id t side) side ++ wsm.flatMap encMsg ++ [W8 6]) ++ encBeacon ts := by
      simp [encMsg, Msg.code, Msg.body, List.flatMap_append, List.append_assoc]
    rw [show interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #(ws.getD t null) =
      bwIface (ws.getD t null) from rfl]
    wp_apply (hM _ (DFrac.own 1) ts (ws.getD t null)
      (connWr tc cid side la ra ed (peerPX γ id L t side) hppc 4096) sent1 pend1 e1)
      $$ [Hw «$r0»]
      as ⟨Hrb, %sent2, %pend2, %e2, %Hw2, Hw⟩
    · simp only [connWr]
      iframe
      iintro %He
      obtain ⟨_, h1a, _, h1c, _⟩ := Hw1
      have herr : err = interface.nil := by
        by_cases h : err = interface.nil
        · exact h
        · exact absurd ((h1c h).1 ▸ He) h
      rw [h1a He, hst herr]
      unfold dialerOf at hfull
      rw [← hfull]
      imodintro
      iexact HQ
    wp_apply EtcdGrove.bufio.Writer.Flush.wp_proof (ws.getD t null) _ _ _ _ _ sent2 pend2 e2
      $$ [$Hw] as %e3 ⟨%k, %Hk3, Hw⟩
    ihave Hslot : peerSlotX γ id L p.ewma t (cs.getD t interface.nil) (ws.getD t null) $$ [Hs Hw Hfr]
    · unfold peerSlotX
      iexists protoMsgs (wsm ++ [Msg.beacon ts])
      rw [protoMsgs_snoc_beacon wsm _ rfl]
      iframe Hs
      iright
      iexists cid, side
      unfold slotConn
      iexists sent2 ++ pend2.take k, pend2.drop k, e3, wsm ++ [Msg.beacon ts], tc, la, ra, ed, eof
      simp only [wrOwn, connWr]
      iframe; iframe #
      ipureintro
      refine ⟨protoMsgs_snoc_beacon wsm _ rfl, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hwf x hx
        · simp at hx; subst hx; exact hm
      · intro he3
        rw [send_stream_eq _ _ (W8 6) (encBeacon ts) sent pend sent1 pend1 sent2 pend2 err e1 e2 e3 k
          hst ⟨Hw1.1, Hw1.2.1, Hw1.2.2.1, fun h => (Hw1.2.2.2.1 h).1⟩ Hw2 Hk3 he3]
        simp [encMsg, Msg.code, Msg.body, List.flatMap_append, List.append_assoc]
    iunfold peerSlotX at Hslot
    iunfold slotConn at Hslot
    ihave Hpeers := Hpeers $$ Hps Hws Has Hls Hslot
    ihave Hcore := Hcore $$ Hpeers
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
    · unfold fwLockInv; iframe
    iapply HΦ
    itrivial
  done

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
