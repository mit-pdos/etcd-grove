/-
`replicaListener` (the reader goroutine of a peer's connection): reads whole messages; a beacon
is answered, a beacon reply updates the latencies, a protocol message gets its delivery token
and is sent, `deliverable`, on its kind's channel (by a goroutine of its own); on an error the
peer is marked dead.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Stream
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Beacon
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.RpcTable
public import Proof.bufio.Reader__ReadByte

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

theorem fwFrozen_table (γ : EpNames) (r : Loc) (id : Nat) (p : FwPtrs) :
    fwFrozen (GF := GF) γ r id p ⊢ tableOk γ id p.tbl := by
  rw [fwFrozen_unseal]; unfold fwFrozenDef
  iintro ⟨-, -, #H, -⟩
  iexact H

/-- A connection reader's stream fact (`bufio.ownBufReader_fact` at `connRd`). -/
theorem connRd_fact {br : Loc} {t : Loc} {cn : Nat} {s : Bool} {eof la ra ed : GoInterface}
    {P : Proto GF} {R : List w8} :
    EtcdGrove.bufio.ownBufReader br (net.connIface t) (fun _ m => 0 < m)
        (recvTokL (Gg := hG.goose_globalGS) cn s P) (net.connReadE eof la ra ed) R ⊢
      EtcdGrove.bufio.ownBufReader br (net.connIface t) (fun _ m => 0 < m)
        (recvTokL (Gg := hG.goose_globalGS) cn s P) (net.connReadE eof la ra ed) R ∗
      ▷ protoPrefix P cn R :=
  EtcdGrove.bufio.ownBufReader_fact _ _ _ _ _ _ _ (connRd t cn s eof la ra ed P).F_of
    (connRd t cn s eof la ra ed P).F_pre

/-- `connRd_fact` on `rdOwn`. -/
theorem connRd_fact' {br : Loc} {t : Loc} {cn : Nat} {s : Bool} {eof la ra ed : GoInterface}
    {P : Proto GF} {R : List w8} :
    rdOwn br (connRd t cn s eof la ra ed P) R ⊢
      rdOwn br (connRd t cn s eof la ra ed P) R ∗ ▷ protoPrefix P cn R :=
  connRd_fact

/-- `pin_stream` and `peerStreamOk_shape` on the reader's stream fact (a step later). -/
theorem listener_shape (γ : EpNames) (id : Nat) (L : List GoString) (j : Nat) (side : Bool)
    (cid : Nat) (R : List w8) (hR : R ≠ []) :
    roleElem (GF := GF) γ cid (.peer (W64 (dialerOf id j side))) -∗
      ▷ protoPrefix (peerPin γ id L j side) cid R -∗
      ▷ ⌜∃ ws' : List Msg, (∀ m ∈ ws', m.wf) ∧
        R <+: streamHdr (uint.nat (W64 (dialerOf id j side : Int))) (!side) ++ ws'.flatMap encMsg⌝ := by
  iintro #Hr Hp
  inext
  ihave #Hs := pin_stream γ id L j side cid (dialerOf id j side) R rfl hR $$ Hr Hp
  iapply peerStreamOk_shape $$ Hs

/-- `listener_msgSent` on the reader's stream fact (a step later). -/
theorem listener_msgSent_later (γ : EpNames) (id : Nat) (L : List GoString) (j : Nat) (side : Bool)
    (cid : Nat) (dl : Nat) (hdl : dl = dialerOf id j side) (hd : dl < 5) (hid : id < L.length)
    (hj : j < L.length) (ws : List Msg) (m : Msg) (hwf : ∀ m ∈ ws, m.wf) (hm : m.wf)
    (hp : m.isProto = true) :
    listFinal (GF := GF) γ L -∗ roleElem γ cid (.peer (W64 dl)) -∗
      ▷ protoPrefix (peerPin γ id L j side) cid (streamHdr dl (!side) ++ (ws ++ [m]).flatMap encMsg) -∗
      ▷ msgSent γ j id (protoMsgs ws).length m := by
  iintro #Hf #Hr Hp
  inext
  iapply listener_msgSent γ id L j side cid dl hdl hd hid hj ws m hwf hm hp $$ Hf Hr Hp

theorem replica.Replica.replicaListener.spec_holds
    (hRB : replica.Replica.ReplyBeacon.specI (GF := GF))
    (hBU : replica.defs.Beacon.Unmarshal.spec (GF := GF)) (hBRU : replica.defs.BeaconReply.Unmarshal.spec (GF := GF))
    (hNew : Serializable.New.spec (GF := GF)) (hUnm : Serializable.Unmarshal.spec (GF := GF))
    (hNow : time.Now.spec (GF := GF)) (hNano : time.Time.UnixNano.spec (GF := GF)) :
    replica.Replica.replicaListener.spec (GF := GF) := by
  intro γ r id L p Rext j c cid side rd
  wp_start as ⟨#Hrun, #Hfz, #Hph1, %Hj, Hlis⟩
  unfold fwRun0
  icases Hrun with ⟨#Hro, #Hmu⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, -, -, -, #HPeers, #HReaders, #HWriters, -, -, -, -,
    #HAlive, -, #HRPC, -, -, -, #HShut, -, -, -, -, -, -, #HEwma, #HLat, #HDt, %HL, #HLf,
    #HCI, -, -⟩
  ihave #Hep := fwFrozen_epaxos $$ Hfz
  ihave #Htb := fwFrozen_table $$ Hfz
  unfold tableOk
  icases Htb with ⟨%E, #Htbl, #HE⟩
  unfold lisRes lisStart
  icases Hlis with ⟨%tc, %la, %ra, %ed, %eof, #Hci, %Hside, #Hrole, Hrd, Hdf, %Hewl, %v0, Hew⟩
  wp_auto
  ipersist r
  ipersist reader
  ipersist rid
  ihave HI : (∃ (e : GoInterface) (mt : w8) (gb : replica.defs.Beacon)
      (gbr : replica.defs.BeaconReply),
      "err" ∷ err_ptr ↦ e ∗ "msgType" ∷ msgType_ptr ↦ mt ∗ "gbeacon" ∷ gbeacon_ptr ↦ gb ∗
      "gbeaconReply" ∷ gbeaconReply_ptr ↦ gbr ∗
      "Hew" ∷ (∃ v : w64, sliceIndexRef w64 (j : Int) p.ewma ↦ v) ∗
      "Hst" ∷ (⌜e ≠ interface.nil⌝ ∨ (⌜e = interface.nil⌝ ∗ ∃ ws : List Msg, ⌜∀ m ∈ ws, m.wf⌝ ∗
        rdOwn rd (connRd tc cid side eof la ra ed (peerPin γ id L j side))
          (streamHdr (dialerOf id j side) (!side) ++ ws.flatMap encMsg) ∗
        delivFrom γ id j (protoMsgs ws).length)) : IProp GF) $$ [err msgType gbeacon gbeaconReply Hew Hrd Hdf]
  · iexists interface.nil, _, _, _
    iframe
    isplitl [Hew]
    · iexists v0; iframe
    iright
    isplitr
    · ipureintro; rfl
    iexists []
    simp only [List.flatMap_nil, List.append_nil, protoMsgs, List.filter_nil, List.length_nil]
    iframe
    ipureintro; simp
  wp_for HI
  icases Hst with (%He | ⟨%He, %ws, %Hwf, Hrd, Hdf⟩)
  · -- an error: the loop ends; the peer is marked dead
    cases e with
    | nil => exact absurd rfl He
    | ok ei =>
    wp_auto
    wp_if_destruct
    · exfalso
      simp only [goose_wp_simp_extra, goose_wp_simp] at Hif
    wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
    iunfold fwLockInv at HR
    icases HR with ⟨Hcore, HRext⟩
    ihave Hacc := fwCore_peers_acc (GF := GF) γ id L p ⊤ CoPset.subseteq_top $$ Hph1 Hcore Hlc1
    iapply fupd_wp
    imod Hacc with ⟨Hpeers, Hcore⟩
    imodintro
    iunfold fwPeers at Hpeers
    icases Hpeers with ⟨%cs, %ws, %als, %ls, Hps, Hws, Has, Hls, %Hlen, Hsl⟩
    ihave %Hal := ownSlice_len _ _ _ $$ Has
    have hj5 : j < 5 := by have := Hj.1; have := HL.1; unfold nRep at *; omega
    have hjz : sint.Z (W64 (j : Int)) = (j : Int) := by word
    have hal : sint.Z p.alive.len = 5 := by
      have h1 := Hal.1; rw [Hlen.2.2.1, HL.1] at h1; have h2 := Hal.2; unfold nRep at h1; word
    rw [hjz, if_pos (show 0 ≤ (j : Int) ∧ (j : Int) < sint.Z p.alive.len by omega)]
    wp_apply wp_store_slice_index p.alive (j : Int) als false $$ [Has] as Has
    · iframe; ipureintro; omega
    ihave Hcore := Hcore $$ [Hps Hws Has Hls Hsl]
    · unfold fwPeers
      iexists cs, ws, als.set j false, ls
      simp only [Int.toNat_natCast]
      iframe
      ipureintro; simp [Hlen]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
    · unfold fwLockInv; iframe
    iapply HΦ; itrivial
  subst He
  wp_auto
  wp_if_destruct
  rotate_left
  · exfalso; simp only [goose_wp_simp_extra, goose_wp_simp] at Hif
  wp_apply EtcdGrove.bufio.Reader.ReadByte.wp_proof rd _ _ _ _ _ $$ [$Hrd] as %b %e1 Hrb
  icases Hrb with (⟨%He1, Hrd⟩ | ⟨%He1, #Herr, -, Hrd⟩)
  rotate_left
  · -- the read failed: the loop ends
    cases e1 with
    | nil => exact absurd rfl He1
    | ok ei =>
    wp_auto
    wp_for_post
    wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
    iunfold fwLockInv at HR
    icases HR with ⟨Hcore, HRext⟩
    ihave Hacc := fwCore_peers_acc (GF := GF) γ id L p ⊤ CoPset.subseteq_top $$ Hph1 Hcore Hlc1
    iapply fupd_wp
    imod Hacc with ⟨Hpeers, Hcore⟩
    imodintro
    iunfold fwPeers at Hpeers
    icases Hpeers with ⟨%cs, %ws, %als, %ls, Hps, Hws, Has, Hls, %Hlen, Hsl⟩
    ihave %Hal := ownSlice_len _ _ _ $$ Has
    have hj5 : j < 5 := by have := Hj.1; have := HL.1; unfold nRep at *; omega
    have hjz : sint.Z (W64 (j : Int)) = (j : Int) := by word
    have hal : sint.Z p.alive.len = 5 := by
      have h1 := Hal.1; rw [Hlen.2.2.1, HL.1] at h1; have h2 := Hal.2; unfold nRep at h1; word
    rw [hjz, if_pos (show 0 ≤ (j : Int) ∧ (j : Int) < sint.Z p.alive.len by omega)]
    wp_apply wp_store_slice_index p.alive (j : Int) als false $$ [Has] as Has
    · iframe; ipureintro; omega
    ihave Hcore := Hcore $$ [Hps Hws Has Hls Hsl]
    · unfold fwPeers
      iexists cs, ws, als.set j false, ls
      simp only [Int.toNat_natCast]
      iframe
      ipureintro; simp [Hlen]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
    · unfold fwLockInv; iframe
    iapply HΦ; itrivial
  subst He1
  -- the next message's code
  have hdl5 : dialerOf id j side < 5 := by
    unfold dialerOf; have := Hj.1; have := HL; unfold nRep at *; split <;> omega
  ihave ⟨Hrd, #Hpp⟩ := connRd_fact $$ Hrd
  ihave Hsh := listener_shape γ id L j side cid _ (by simp) $$ Hrole Hpp
  imod Hsh with %Hsh
  obtain ⟨ws', hwf', hpre⟩ := Hsh
  have hdn : uint.nat (W64 ((dialerOf id j side : Nat) : Int)) = dialerOf id j side := by word
  rw [hdn] at hpre
  have hpre' : ws.flatMap encMsg ++ b :: [] <+: ws'.flatMap encMsg :=
    (List.prefix_append_right_inj (streamHdr (dialerOf id j side) (!side))).mp
      (by simpa [List.append_assoc] using hpre)
  obtain ⟨m, rest, hws', hcode, -⟩ := stream_next ws ws' b [] Hwf hwf' hpre'
  have hmwf : m.wf := hwf' m (by rw [hws']; simp)
  clear hpre hpre' hws'
  rcases Msg.code_cases m with h6 | h7 | ⟨k, hk, hkc, hkk⟩
  · -- a beacon: answered
    subst hcode
    rw [h6]
    wp_auto
    ihave #Hnx := listener_nextIs γ id L j side cid tc eof la ra ed (dialerOf id j side) rfl hdl5 ws (W8 6) encBeacon
      (fun _ => True) Hwf (fun m' _ hc => by
        obtain ⟨ts', rfl⟩ := Msg.code_beacon m' hc
        exact ⟨ts', trivial, rfl⟩) $$ Hrole
    rw [show interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #rd = brIface rd from rfl]
    wp_apply (hBU gbeacon_ptr gb rd (connRd tc cid side eof la ra ed (peerPin γ id L j side)) _) $$ [Hrd $Hnx $gbeacon] as %err2 Hres
    · simp only [rdOwn, connRd]; iframe
    icases Hres with (⟨%He2, %ts, -, Hrd, Hgb⟩ | ⟨%He2, %data, Hrd, %gb', Hgb⟩)
    rotate_left
    · -- the body could not be read: the loop ends
      cases err2 with
      | nil => exact absurd rfl He2
      | ok ei =>
      wp_auto
      wp_for_post
      iframe
      iexists GoInterface.ok ei, _, _, _
      iframe
      ileft; ipureintro; exact He2
    subst He2
    wp_auto
    have hj5 : j < 5 := by have := Hj.1; have := HL.1; unfold nRep at *; omega
    rw [show sint.Z (W64 (j : Int)) = (j : Int) by word]
    wp_apply (hRB γ r id L p Rext _ (DFrac.own 1) j ts) $$ [«$a0»] as -
    · unfold fwRun0; iframe; iframe #; ipureintro; exact Hj
    wp_for_post
    iframe
    iexists GoInterface.nil, _, _, _
    iframe
    iright
    isplitr
    · ipureintro; rfl
    iexists ws ++ [Msg.beacon ts]
    rw [protoMsgs_snoc_beacon ws _ rfl]
    iframe
    isplitr
    · ipureintro
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Hwf x hx
      · simp at hx; subst hx; simp [Msg.wf]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, encMsg, Msg.code, Msg.body,
      List.append_nil, List.append_assoc]
    iexact Hrd
  · -- a beacon reply: the latency is updated
    subst hcode
    rw [h7]
    wp_auto
    ihave #Hnx := listener_nextIs γ id L j side cid tc eof la ra ed (dialerOf id j side) rfl hdl5 ws (W8 7) encBeacon
      (fun _ => True) Hwf (fun m' _ hc => by
        obtain ⟨ts', rfl⟩ := Msg.code_beaconReply m' hc
        exact ⟨ts', trivial, rfl⟩) $$ Hrole
    rw [show interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #rd = brIface rd from rfl]
    wp_apply (hBRU gbeaconReply_ptr gbr rd (connRd tc cid side eof la ra ed (peerPin γ id L j side)) _) $$ [Hrd $Hnx $gbeaconReply] as %err2 Hres
    · simp only [rdOwn, connRd]; iframe
    icases Hres with (⟨%He2, %ts, -, Hrd, Hgb⟩ | ⟨%He2, %data, Hrd, %gb', Hgb⟩)
    rotate_left
    · -- the body could not be read: the loop ends
      cases err2 with
      | nil => exact absurd rfl He2
      | ok ei =>
      wp_auto
      wp_for_post
      iframe
      iexists GoInterface.ok ei, _, _, _
      iframe
      ileft; ipureintro; exact He2
    subst He2
    wp_auto
    have hj5 : j < 5 := by have := Hj.1; have := HL.1; unfold nRep at *; omega
    have hjz : sint.Z (W64 (j : Int)) = (j : Int) := by word
    wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
    iunfold fwLockInv at HR
    icases HR with ⟨Hcore, HRext⟩
    ihave Hacc := fwCore_peers_acc (GF := GF) γ id L p ⊤ CoPset.subseteq_top $$ Hph1 Hcore Hlc1
    iapply fupd_wp
    imod Hacc with ⟨Hpeers, Hcore⟩
    imodintro
    iunfold fwPeers at Hpeers
    icases Hpeers with ⟨%cs, %ws2, %als, %ls, Hps, Hws, Has, Hls, %Hlen, Hsl⟩
    ihave %Hll := ownSlice_len _ _ _ $$ Hls
    have hll : sint.Z p.lat.len = 5 := by
      have h1 := Hll.1; rw [Hlen.2.2.2, HL.1] at h1; have h2 := Hll.2; unfold nRep at h1; word
    rw [hjz, if_pos (show 0 ≤ (j : Int) ∧ (j : Int) < sint.Z p.lat.len by omega)]
    wp_auto
    rw [hjz, if_pos (show 0 ≤ (j : Int) ∧ (j : Int) < sint.Z p.lat.len by omega)]
    have hlj : ls[j]? = some (ls.getD j (W64 0)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    wp_apply wp_load_slice_index p.lat (j : Int) ls (DFrac.own 1) (ls.getD j (W64 0)) (by omega)
      $$ [Hls] as Hls
    · iframe; ipureintro; simpa using hlj
    wp_apply hNow as %tm _
    wp_apply hNano as %x _
    wp_apply wp_store_slice_index p.lat (j : Int) ls _ $$ [Hls] as Hls
    · iframe; ipureintro; omega
    ihave Hcore := Hcore $$ [Hps Hws Has Hls Hsl]
    · unfold fwPeers
      iexists cs, ws2, als, _
      iframe
      ipureintro; simp [Hlen]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
    · unfold fwLockInv; iframe
    wp_apply hNow as %tm2 _
    wp_apply hNano as %x2 _
    icases Hew with ⟨%ev, Hew⟩
    rw [hjz, if_pos (show 0 ≤ (j : Int) ∧ (j : Int) < sint.Z p.ewma.len by omega)]
    wp_auto
    -- `Ewma[j] = 0.99*Ewma[j] + 0.01*float64(now - Timestamp)`: Perennial's float steps
    wp_apply wp_float64_mul as %f1 -
    try wp_auto
    wp_apply wp_float64_mul as %f2 -
    wp_apply wp_float64_add as %f3 -
    try wp_auto
    try rw [hjz, if_pos (show 0 ≤ (j : Int) ∧ (j : Int) < sint.Z p.ewma.len by omega)]
    try rw [if_pos (show 0 ≤ (j : Int) ∧ (j : Int) < sint.Z p.ewma.len by omega)]
    wp_auto
    wp_for_post
    iframe
    iexists GoInterface.nil, _, _, _
    iframe
    isplitl [Hew]
    · iexists _; iexact Hew
    iright
    isplitr
    · ipureintro; rfl
    iexists ws ++ [Msg.beaconReply ts]
    rw [protoMsgs_snoc_beacon ws _ rfl]
    iframe
    isplitr
    · ipureintro
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Hwf x hx
      · simp at hx; subst hx; simp [Msg.wf]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, encMsg, Msg.code, Msg.body,
      List.append_nil, List.append_assoc]
    iexact Hrd
  · -- a protocol message: delivered on its kind's channel
    subst hcode
    rw [hkc]
    have hk6 : k.code ≠ W8 6 := by cases k <;> decide
    have hk7 : k.code ≠ W8 7 := by cases k <;> decide
    wp_auto
    rw [show decide (k.code = W8 6) = false from decide_eq_false hk6]
    wp_auto
    rw [show decide (k.code = W8 7) = false from decide_eq_false hk7]
    wp_auto
    unfold tableEntriesOk
    icases HE with ⟨%HEc, #HEs⟩
    ihave #Hk := (BigSepL.bigSepL_mem hk) $$ HEs
    icases Hk with ⟨%obj, %ch, %γc, %Hlk, #Hbag⟩
    obtain ⟨Hlk, Hpo⟩ := Hlk
    wp_apply rpc.Table.Get.wp_proof p.tbl E k.code $$ [Htbl]
    · iframe #
    rw [Hlk]
    simp only [Option.getD_some, Option.isSome_some]
    wp_auto
    obtain ⟨l0, hl0⟩ := Hpo
    subst hl0
    wp_auto
    wp_apply (hNew k _ _ rfl ⟨l0, rfl⟩) as %obj' ⟨%l', %Hobj', Hany⟩
    subst Hobj'
    wp_auto
    ihave #Hnx := listener_nextIs γ id L j side cid tc eof la ra ed (dialerOf id j side) rfl hdl5 ws k.code Msg.body
      (fun m' => m'.kind = some k ∧ m'.wf) Hwf (fun m' hw hc =>
        ⟨m', ⟨Msg.code_kind m' k hc, hw⟩, rfl⟩) $$ Hrole
    rw [show interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #rd = brIface rd from rfl]
    wp_apply (hUnm k l' rd (connRd tc cid side eof la ra ed (peerPin γ id L j side)) _) $$ [Hrd $Hnx $Hany] as %err2 Hres
    · simp only [rdOwn, connRd]; iframe
    icases Hres with (⟨%He2, %m2, %Hm2, Hrd, Hmo⟩ | ⟨%He2, %data, Hrd, Hany⟩)
    rotate_left
    · -- the body could not be read: the loop ends
      cases err2 with
      | nil => exact absurd rfl He2
      | ok ei =>
      wp_auto
      wp_for_post
      iframe
      iexists GoInterface.ok ei, _, _, _
      iframe
      ileft; ipureintro; exact He2
    subst He2
    wp_auto
    obtain ⟨hk2, hw2⟩ := Hm2
    have hc2 : m2.code = k.code := Msg.kind_code m2 k hk2
    have hp2 : m2.isProto = true := by
      cases m2 <;> simp_all [Msg.kind, Msg.isProto]
    have hR : streamHdr (dialerOf id j side) (!side) ++ ws.flatMap encMsg ++ [k.code] ++ m2.body =
        streamHdr (dialerOf id j side) (!side) ++ (ws ++ [m2]).flatMap encMsg := by
      simp [encMsg, hc2, List.flatMap_append, List.append_assoc]
    rw [hR]
    ihave ⟨Hrd, #Hpp2⟩ := connRd_fact' $$ Hrd
    ihave Hsent := listener_msgSent_later γ id L j side cid _ rfl hdl5 HL.2 Hj.1 ws m2 Hwf hw2 hp2
      $$ HLf Hrole Hpp2
    imod Hsent with #Hsent
    iapply fupd_wp
    imod delivFrom_mint $$ Hdf with ⟨Hdf, Htok⟩
    imodintro
    wp_apply wp_fork $$ [Htok Hmo p]
    · wp_auto
      wp_apply (wp_WaitDurationID_nil (W64 (j : Int)))
      wp_apply time.Sleep.wp_proof
      wp_apply (wp_bag_send γc ch (interface.mkOk (go.GoType.PointerType k.ty) #l')
        (deliverChanP γ id k)) $$ [Htok Hmo]
      · iframe #
        unfold deliverChanP deliverable
        iexists j, (protoMsgs ws).length, m2
        iframe
        iframe #
        ipureintro
        refine ⟨hk2, ⟨?_, Hj.2⟩, hw2⟩
        have := Hj.1; have := HL.1; unfold nRep at *; omega
      itrivial
    wp_for_post
    iframe
    iexists GoInterface.nil, _, _, _
    iframe
    iright
    isplitr
    · ipureintro; rfl
    iexists ws ++ [m2]
    rw [protoMsgs_snoc', hp2]
    simp only [ite_true, List.length_append, List.length_singleton]
    iframe
    ipureintro
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Hwf x hx
    · simp at hx; subst hx; exact hw2

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
