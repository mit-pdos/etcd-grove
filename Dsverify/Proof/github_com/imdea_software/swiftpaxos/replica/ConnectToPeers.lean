/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ConnectToPeers.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.ConnectToPeers()`: proved over its callees' specs (`waitForPeerConnections`,
`replicaListener`, dlog's `Println`/`Printf`).

The slots of `Peers`, `PeerReaders`, `PeerWriters`, `Alive` are split into their elements
(`replica.slots_open`): those of the peers below `me` go to the dial loop, those above to
`waitForPeerConnections` (a goroutine, which hands them back on `done` with the listener and
the pending clients), `me`'s stays empty. The dial loop dials peer `i` until `Dial` succeeds,
registers the connection as a peer's (`sp.conn_register`), writes the hello (`sp.hello_inP`)
and makes the reader (nothing read: `outQ`'s stream) and the writer (`peerOut me`: the hello
sent). After `done`, the slots are put back (`replica.slots_close`), `r.M` gets
`replica.lockInv` (no client writer yet: a fresh ghost map `γw`), and a `replicaListener` is
started for every peer with a reader, with its `Ewma` element.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnSlots
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Conn

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
open BigSepL

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [bufio.Assumptions] [net.Assumptions] [net.FieldAssumptions] [io.Assumptions]
  [io.ExtraAssumptions] [errors.Assumptions] [dlog.Assumptions] [time.Assumptions]
  [strings.Assumptions] [encoding.binary.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- The readers' loop: on to the next index. -/
local macro "nextIt" : tactic => `(tactic| (
  wp_for_post
  iframe
  iexists (j + W64 1)
  rw [hj1]
  iframe i
  isplitr
  · ipureintro; omega
  isplitl [reader]
  · iexists _; iexact reader
  isplitl [rid]
  · iexists _; iexact rid
  iapply bigSepL_mono _ $$ Hz
  iintro %k %x %_ Hx
  rw [show (sint.Z j).toNat + 1 + k = (sint.Z j).toNat + (k + 1) by omega]
  iexact Hx))

set_option maxHeartbeats 1600000 in
theorem replica.Replica.ConnectToPeers.wp_proof
    (wp_wait : replica.Replica.waitForPeerConnections.spec (hG := hG))
    (wp_listen : replica.Replica.replicaListener.spec (hG := hG))
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG))
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.ConnectToPeers.spec (hG := hG) := by
  intro r γ γc γm γl N me a ip
  wp_start as Hpre
  unfold replica.connPre
  icases Hpre with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %asl, %pssl, %prsl, %pwsl,
    %alsl, %latsl, %ewsl, %l, %cwm, %lats, %ews, %al, #Hinv, #Hlg, #Hq, #HN, #HId, #HCfg,
    #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag, #HSd, #HLR, #HDt, #HAlias, #HAL, #Hl, #HPs, Hps,
    #HPR, Hpr, #HPW, Hpw, #HAl, Hal, #HLat, Hlat, #HEw, Hew, #HCW, Hcw, HM, HLis, Hpc, %Hpure,
    Htok, #Hip, #Haps⟩
  obtain ⟨hla, hmem, hpre, hme0, hmeN, hN7, hlN, hall, hlats, hews⟩ := Hpure
  have hamem : a ∈ replicaAddrs := List.elem_iff.1 (by simpa using hmem)
  ihave #Hap := bigSepL_mem (Φ := fun a' => addrProto a' (sp.inP γ γc γm) (sp.outQ γ γc γm))
    hamem $$ Haps
  ihave %Hpsl := ownSlice_len _ _ _ $$ Hps
  ihave %Hprl := ownSlice_len _ _ _ $$ Hpr
  ihave %Hpwl := ownSlice_len _ _ _ $$ Hpw
  ihave %Hall := ownSlice_len _ _ _ $$ Hal
  ihave %Hewl := ownSlice_len _ _ _ $$ Hew
  ihave %Hll := ownSlice_len _ _ _ $$ Hl
  simp only [List.length_replicate] at Hpsl Hprl Hpwl Hall
  have hpsl : sint.Z pssl.len = N := by
    have e1 : sint.nat pssl.len = (sint.Z pssl.len).toNat := rfl; omega
  have hprl : sint.Z prsl.len = N := by
    have e1 : sint.nat prsl.len = (sint.Z prsl.len).toNat := rfl; omega
  have hpwl : sint.Z pwsl.len = N := by
    have e1 : sint.nat pwsl.len = (sint.Z pwsl.len).toNat := rfl; omega
  have hall' : sint.Z alsl.len = N := by
    have e1 : sint.nat alsl.len = (sint.Z alsl.len).toNat := rfl; omega
  have hewl : sint.Z ewsl.len = N := by
    have e1 : sint.nat ewsl.len = (sint.Z ewsl.len).toNat := rfl; omega
  icases replica.slots_open N pssl prsl pwsl alsl $$ [$Hps $Hpr $Hpw $Hal] with ⟨Hslots, Hback⟩
  icases (replica.range_split3 _ N me.toInt.toNat (by omega)).1 $$ Hslots with ⟨Hlo, Hme, Hhi⟩
  wp_auto
  ihave Hsl := slice_array b_ptr 5 (Perennial.zero_val (GoArray w8 5)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 5 - W64 0 = W64 5 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 5)).arr = List.replicate 5 (W8 0) from rfl]
  wp_apply (chan.wp_make1 (V := Bool)) as %dch %γd ⟨#Hdch, -, Hdown⟩
  imod start_bag (fun _ : Bool => replica.acceptSt r γ γc γm N me a pssl prsl pwsl alsl) _ dch γd
    trivial $$ Hdch Hdown with #Hdone
  try wp_auto
  wp_apply wp_fork $$ [HLis Hpc Htok Hhi]
  · wp_apply wp_wait r γ γc γm N me asl l a ip lg pssl prsl pwsl alsl _ _ dch γd
      $$ [$HLis $Hpc $Htok $Hlg $Hq $HN $HId $HAL $Hl $HPs $HPR $HPW $HAl $Hap $Hip $Hdone Hhi]
    · isplitr
      · ipureintro
        refine ⟨rfl, hla, hmem, hpre, hme0, hmeN, hN7, hlN, ?_, ?_, ?_, ?_⟩ <;> omega
      iapply bigSepL_mono _ $$ Hhi
      iintro %k %j %_ Hj
      unfold replica.emptySlot
      iexact Hj
    itrivial
  have hmez : sint.Z (W64 (sint.Z me)) = me.toInt := by
    have : sint.Z me = me.toInt := rfl
    rw [this]; simp only [W64, sint.Z]; rw [BitVec.toInt_ofInt]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  ihave HL : (∃ (iv : w64) (bb : List w8), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ slice.mk b_ptr (W64 5) (W64 5) ↦* bb ∗
      "%Hiv" ∷ ⌜bb.length = 5 ∧ 0 ≤ sint.Z iv ∧ sint.Z iv ≤ me.toInt⌝ ∗
      "Hdn" ∷ ([∗list] j ∈ List.range (sint.Z iv).toNat,
        replica.peerSlot γ γc γm me pssl prsl pwsl alsl j) ∗
      "Hlo" ∷ ([∗list] j ∈ List.range' (sint.Z iv).toNat (me.toInt.toNat - (sint.Z iv).toNat),
        replica.emptySlot pssl prsl pwsl alsl j) : IProp netDistGF) $$ [i Hsl Hlo]
  · iexists (W64 0), _
    iframe i Hsl
    isplitr
    · ipureintro; exact ⟨rfl, by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩
    simp only [show sint.Z (W64 0) = 0 from rfl, Int.toNat_zero, List.range_zero, Nat.sub_zero]
    isplitr
    · iapply (BigSepL.bigSepL_nil_intro (P := iprop(True))); itrivial
    · rw [← List.range_eq_range']; iexact Hlo
  wp_for HL
  wp_if_destruct
  · -- dial peer `iv`
    rw [hmez] at Hif
    obtain ⟨hbb, hiv0, hivme⟩ := Hiv
    obtain ⟨k, hk⟩ : ∃ k, me.toInt.toNat - (sint.Z iv).toNat = k + 1 :=
      ⟨me.toInt.toNat - (sint.Z iv).toNat - 1, by omega⟩
    rw [hk, List.range'_succ]
    icases (bigSepL_cons (Φ := fun _ j => replica.emptySlot pssl prsl pwsl alsl j)).1 $$ Hlo
      with ⟨Hcur, Hlo⟩
    iunfold replica.emptySlot at Hcur
    icases Hcur with ⟨%cv0, %rd0, %w0, %al0, Hps1, Hpr1, Hpw1, Hal1, %Hrw0⟩
    have hivz : (((sint.Z iv).toNat : Nat) : Int) = sint.Z iv := Int.toNat_of_nonneg hiv0
    iunfold replica.elem at Hps1 Hpr1 Hpw1 Hal1
    rw [hivz]
    obtain ⟨a', ha'⟩ : ∃ a', l[(sint.Z iv).toNat]? = some a' :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have ha'mem : a' ∈ replicaAddrs := hall a' (List.mem_of_getElem? ha')
    ihave #Hap' := bigSepL_mem (Φ := fun a' => addrProto a' (sp.inP γ γc γm) (sp.outQ γ γc γm))
      ha'mem $$ Haps
    wp_for
    have hasl : sint.Z asl.len = N := by
      have e1 : sint.nat asl.len = (sint.Z asl.len).toNat := rfl; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hiv0, by omega⟩)]
    wp_apply wp_load_slice_index _ _ _ _ a' hiv0 $$ [Hl] as -
    · iframe Hl; ipureintro; exact ha'
    wp_apply net.Dial.wp_proof a' (sp.inP γ γc γm) (sp.outQ γ γc γm) $$ [$Hap'] as %cv %er Hres
    unfold net.newConnResult
    icases Hres with (⟨%c, %cid, ⟨%Hcv, %Her⟩, #Hown, ⟨Hsend, Hrecv⟩, Hfresh⟩ |
      ⟨%ie, ⟨%Hcv, %Her⟩, Herr⟩)
    · subst Hcv Her
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hiv0, by omega⟩)]
      try wp_auto
      wp_for_post
      iapply fupd_wp
      imod (sp.conn_register (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⊤ (by solve_ndisj) cid
        .peer) $$ [Hfresh] with #Hkind
      · iframe; iframe #
      imodintro
      ihave #Hhello := sp.hello_inP (γ := γ) (γc := γc) (γm := γm) cid me $$ Hkind
      wp_apply wp_store_slice_index _ (sint.Z (W64 0)) bb (W8 255) $$ [Hsl] as Hsl
      · iframe Hsl; ipureintro; rw [hbb]; decide
      try wp_auto
      obtain ⟨x0, x1, x2, x3, x4, rfl⟩ : ∃ x0 x1 x2 x3 x4 : w8, bb = [x0, x1, x2, x3, x4] := by
        match bb, hbb with
        | [x0, x1, x2, x3, x4], _ => exact ⟨x0, x1, x2, x3, x4, rfl⟩
      have hsl5 : sint.Z (slice.mk b_ptr (W64 5) (W64 5)).len = 5 := rfl
      icases (ownSlice_slice (W64 1) (W64 5) _ _ _ ⟨by decide, by decide, by rw [hsl5]; decide⟩).1
        $$ Hsl with ⟨Hs0, Hs1, Hs2⟩
      have hsub : subslice (sint.nat (W64 1)) (sint.nat (W64 5))
          ([x0, x1, x2, x3, x4].set 0 (W8 255)) = [x1, x2, x3, x4] ++ [] := rfl
      rw [hsub]
      wp_apply encoding.binary.wp_LittleEndian_PutUint32 _ [x1, x2, x3, x4] [] me rfl
        $$ [$Hpkg5 $Hs1] as Hs1
      have hl4 : (u32Le me).length = 4 := by simp [u32Le_length]
      ihave Hsl := (ownSlice_slice (W64 1) (W64 5) _ _ (sp.helloBytes me)
          ⟨by decide, by decide, by rw [hsl5]; decide⟩).2 $$ [Hs0 Hs1 Hs2]
      · have e0 : (sp.helloBytes me).take (sint.nat (W64 1)) =
            ([x0, x1, x2, x3, x4].set 0 (W8 255)).take (sint.nat (W64 1)) := rfl
        have e1 : subslice (sint.nat (W64 1)) (sint.nat (W64 5)) (sp.helloBytes me) =
            u32Le me ++ [] := by
          simp only [subslice, sp.helloBytes, sp.le32, List.append_nil]
          rw [show sint.nat (W64 1) = 1 from rfl, show sint.nat (W64 5) = 5 from rfl]
          simp [List.take_of_length_le, hl4]
        have e2 : (sp.helloBytes me).drop (sint.nat (W64 5)) =
            ([x0, x1, x2, x3, x4].set 0 (W8 255)).drop (sint.nat (W64 5)) := by
          simp only [sp.helloBytes, sp.le32]
          rw [show sint.nat (W64 5) = 5 from rfl]
          simp [List.drop_eq_nil_of_le, hl4]
        rw [e0, e1, e2]; iframe
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hiv0, by omega⟩)]
      try wp_auto
      ihave Hhello' : (□ sp.inP γ γc γm cid ([] ++ sp.helloBytes me) : IProp netDistGF) $$ []
      · imodintro; rw [List.nil_append]; iexact Hhello
      wp_apply net.TCPConn.Write.wp_proof c cid false _ (sp.helloBytes me) _ (sp.inP γ γc γm) []
        $$ [$Hpkg3 $Hown $Hsend $Hhello' $Hsl] as %nw %ew ⟨%k5, %code, %Hw, Hsl, Hsend, Herrw⟩
      obtain ⟨hnw, hk5, herrw, hnil⟩ := Hw
      try wp_auto
      have hiv1 : (sint.Z (iv + W64 1)).toNat = (sint.Z iv).toNat + 1 := by
        have : sint.Z me = me.toInt := rfl
        word
      have hk' : me.toInt.toNat - ((sint.Z iv).toNat + 1) = k := by omega
      have hivp : sint.Z (iv + W64 1) = sint.Z iv + 1 := by
        have : sint.Z me = me.toInt := rfl
        word
      rcases ew with ew | _
      · -- the hello's write failed: no connection to this peer
        try wp_auto
        wp_apply wp_slice_literal (V := GoInterface)
        isplitr
        · ipureintro; rfl
        iintro %s1 ⟨-, -⟩
        try wp_auto
        wp_apply replica.wp_Println wp_Println $$ [$Hlg $Hq]
        wp_for_post
        iframe
        iexists _, _
        iframe
        rw [hiv1, hk']
        isplitr
        · ipureintro
          refine ⟨by simp [sp.helloBytes, sp.le32, u32Le_length], by rw [hivp]; omega,
            by rw [hivp]; omega⟩
        isplitl [Hdn Hps1 Hpr1 Hpw1 Hal1]
        · rw [List.range_succ]
          iapply (bigSepL_snoc (Φ := fun _ j => replica.peerSlot γ γc γm me pssl prsl pwsl alsl j)).2
          iframe Hdn
          unfold replica.peerSlot replica.elem
          iexists _, rd0, w0, al0
          rw [hivz]
          iframe Hps1 Hpr1 Hpw1 Hal1
          ileft; ipureintro; exact Hrw0
        · iexact Hlo
      · -- the hello is written: the dialer's reader and writer
        have hhl : (sp.helloBytes me).length = 5 := by simp [sp.helloBytes, sp.le32, u32Le_length]
        have hk5' : k5 = 5 := by have := hnil rfl; omega
        subst hk5'
        rw [List.nil_append, List.take_of_length_le (by omega)]
        wp_pures
        try wp_auto
        repeat rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hiv0, by omega⟩)]
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hiv0, by omega⟩)]
        try wp_auto
        ihave #Hci : net.rpc.connIface (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)
          cid false $$ []
        · unfold net.rpc.connIface; iexists c; iframe Hown; ipureintro; rfl
        ihave #Hrdok := bufio.readerOk_conn _ cid false (sp.outQ γ γc γm) $$ [$Hpkg3 $Hci]
        wp_apply bufio.wp_NewReader _ _ [] $$ [$Hpkg2 $Hrdok $Hrecv] as %br Hrd
        try wp_auto
        repeat rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hiv0, by omega⟩)]
        try wp_auto
        repeat rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hiv0, by omega⟩)]
        try wp_auto
        ihave #Hpc : bufio.prefixClosed (sp.inP γ γc γm cid) $$ []
        · iunfold bufio.prefixClosed; iapply sp.inP_prefixClosed
        ihave #Hwok := bufio.writerOk_conn _ cid false (sp.inP γ γc γm) $$ [$Hpkg3 $Hci $Hpc]
        wp_apply bufio.wp_NewWriter _ _ _ (sp.helloBytes me) $$ [$Hpkg2 $Hwok $Hsend $Hhello] as %w Hw
        try wp_auto
        repeat rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hiv0, by omega⟩)]
        try wp_auto
        wp_apply wp_slice_literal (V := GoInterface)
        isplitr
        · ipureintro; rfl
        iintro %s1 ⟨-, -⟩
        try wp_auto
        wp_apply replica.wp_Printf wp_Printf $$ [$Hlg $Hq]
        wp_for_post
        iframe
        iexists _, _
        iframe
        rw [hiv1, hk']
        isplitr
        · ipureintro
          refine ⟨by simp [sp.helloBytes, sp.le32, u32Le_length], by rw [hivp]; omega,
            by rw [hivp]; omega⟩
        isplitl [Hdn Hps1 Hpr1 Hpw1 Hal1 Hrd Hw]
        · rw [List.range_succ]
          iapply (bigSepL_snoc (Φ := fun _ j => replica.peerSlot γ γc γm me pssl prsl pwsl alsl j)).2
          iframe Hdn
          have hk : sp.peerRdKind me (sint.Z iv).toNat = .peerOut := by
            unfold sp.peerRdKind; rw [if_pos (by omega)]
          have hw : sp.peerWrKind me (sint.Z iv).toNat = .peerOut me := by
            unfold sp.peerWrKind; rw [if_pos (by omega)]
          unfold replica.peerSlot replica.elem
          iexists _, br, w, true
          rw [hivz, hk, hw]
          iframe Hps1 Hpr1 Hpw1 Hal1
          iright
          iexists cid, []
          simp only [sp.RdKind.side, sp.RdKind.proto]
          iframe Hci Hkind Hrd
          isplitr
          · ipureintro; exact ⟨by simp [sp.RdKind.head, sp.framesOf], by simp⟩
          unfold sp.wrSt
          iexists _, cid, (sp.helloBytes me), [], _
          simp only [sp.WrKind.side, sp.WrKind.proto, sp.WrKind.conn]
          iframe Hci Hkind Hwok Hw
          iright
          unfold sp.wrAt
          iexists []
          isplitr
          · ipureintro; exact ⟨by simp [sp.WrKind.head, sp.framesOf], by simp⟩
          · iapply (BigSepL.bigSepL_nil_intro (P := iprop(True))); itrivial
        · iexact Hlo
    · subst Hcv Her
      try wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
  -- the dial loop is done: `iv = me`
  rw [hmez] at Hif
  obtain ⟨-, hiv0, hivme⟩ := Hiv
  have hivme' : (sint.Z iv).toNat = me.toInt.toNat := by omega
  rw [hivme']
  wp_apply (wp_bag_receive (V := Bool) γd dch _) $$ [$Hdone] as %bd Hacc
  iunfold replica.acceptSt at Hacc
  icases Hacc with ⟨%lv, %pcsl, %pcs, HLis, #Hlis, Hpc, Hpcs, Hpok, Hhi⟩
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %s1 ⟨-, -⟩
  try wp_auto
  wp_apply replica.wp_Printf wp_Printf $$ [$Hlg $Hq]
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %s2 ⟨-, -⟩
  try wp_auto
  wp_apply replica.wp_Printf wp_Printf $$ [$Hlg $Hq]
  try wp_auto
  -- the slots back
  ihave Hall := (replica.range_split3
      (fun j => replica.peerSlot γ γc γm me pssl prsl pwsl alsl j) N me.toInt.toNat (by omega)).2
    $$ [Hdn Hme Hhi]
  · iframe Hdn Hhi
    iunfold replica.emptySlot at Hme
    icases Hme with ⟨%cv, %rd, %w, %al, A, B, C, D, %Hn⟩
    unfold replica.peerSlot
    iexists cv, rd, w, al
    iframe A B C D
    ileft; ipureintro; exact Hn
  icases replica.slots_close γ γc γm me N pssl prsl pwsl alsl $$ [$Hall $Hback] with
    ⟨%cvs, %rds, %pws, %als, Hps, Hpr, Hpw, Hal, %Hlens, Hrds, Hwrs⟩
  obtain ⟨hcvl, hrdl, hpwl', hall2⟩ := Hlens
  ipersist Hpw
  ipersist Hpr
  -- `r.M`'s invariant, with a fresh name for the clients' writers
  iapply fupd_wp
  imod (ghost_map_alloc_empty (GF := netDistGF) (K := Loc) (V := w32)) with ⟨%γw, Hγw⟩
  imod (sync.init_Mutex (replica.lockInv γ γc γm γw me N pws alsl latsl cwm) ⊤ _) $$ HM
    [Hal Hlat Hwrs Hcw Hγw] with #Hmu
  · inext
    unfold replica.lockInv
    iexists als, lats
    iframe Hal Hlat
    isplitr
    · ipureintro; exact ⟨hall2, hlats⟩
    isplitl [Hwrs]
    · iapply bigSepL_mono _ $$ Hwrs
      iintro %k %x %_ Hx
      unfold replica.writerPart
      iexact Hx
    unfold replica.clientWrs
    iexists ∅, ∅
    iframe Hcw Hγw
    isplitr
    · ipureintro; intro id w h; simp at h
    · iapply (BigSepM.bigSepM_empty (Φ := fun (w : Loc) (cl : w32) => sp.wrSt γ γc γm w (.client cl))).2
      iempintro
  imodintro
  ihave #Hrep : replica.isReplica r γ γc γm γw N me $$ []
  · unfold replica.isReplica
    iexists lg, cfgp, tbl, pc, fr, nid, ents, γpc, pwsl, alsl, latsl, pws, cwm
    iframe Hlg Hq HN HId HCfg Hplain HRPC Htbl HtOk HPC Hpcbag HSd HLR HDt HPW Hpw HAl HLat HCW Hmu
    ipureintro; exact ⟨hpwl', hme0, hmeN, hN7⟩
  -- a listener per peer with a reader, with its `Ewma` element
  icases ownSlice_elems_acc ewsl (DFrac.own 1) ews $$ Hew with ⟨Hews, -⟩
  ihave Hz := (bigSepL_sep_zip (Φ := fun i rd => replica.readerPart γ γc γm me i rd)
      (Ψ := fun i e => typedPointsto (sliceIndexRef w64 (i : Int) ewsl) e (DFrac.own 1))
      (show rds.length = ews.length by omega)).2 $$ [Hrds Hews]
  · iframe
  ihave HL2 : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ N⌝ ∗
      "reader" ∷ (∃ v : Loc, reader_ptr ↦ v) ∗ "rid" ∷ (∃ v : w64, rid_ptr ↦ v) ∗
      "Hz" ∷ ([∗list] k ↦ x ∈ (rds.zip ews).drop (sint.Z j).toNat,
        replica.readerPart γ γc γm me ((sint.Z j).toNat + k) x.1 ∗
        typedPointsto (sliceIndexRef w64 (((sint.Z j).toNat + k : Nat) : Int) ewsl) x.2
          (DFrac.own 1)) : IProp netDistGF) $$ [i reader rid Hz]
  · iexists (W64 0)
    iframe i
    isplitr
    · ipureintro; exact ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩
    isplitl [reader]
    · iexists _; iexact reader
    isplitl [rid]
    · iexists _; iexact rid
    rw [show (sint.Z (W64 0)).toNat = 0 from rfl, List.drop_zero]
    iapply bigSepL_mono _ $$ Hz
    iintro %k %x %_ Hx
    rw [Nat.zero_add]
    iexact Hx
  wp_for HL2
  wp_if_destruct
  · rw [hprl] at Hif
    obtain ⟨hj0, hjN⟩ := Hj
    have hjz : (((sint.Z j).toNat : Nat) : Int) = sint.Z j := Int.toNat_of_nonneg hj0
    have hjl : (sint.Z j).toNat < (rds.zip ews).length := by simp; omega
    rw [List.drop_eq_getElem_cons hjl]
    icases (bigSepL_cons (Φ := fun k (x : Loc × w64) => iprop(
        replica.readerPart γ γc γm me ((sint.Z j).toNat + k) x.1 ∗
        typedPointsto (sliceIndexRef w64 (((sint.Z j).toNat + k : Nat) : Int) ewsl) x.2
          (DFrac.own 1)))).1 $$ Hz with ⟨⟨Hrd, Hew1⟩, Hz⟩
    simp only [List.getElem_zip, Nat.add_zero]
    have hrd : rds[(sint.Z j).toNat]? = some rds[(sint.Z j).toNat] :=
      List.getElem?_eq_getElem (by omega)
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hj0, by omega⟩)]
    wp_apply wp_load_slice_index _ _ _ _ rds[(sint.Z j).toNat] hj0 $$ [$Hpr] as -
    · ipureintro; exact hrd
    icases reader with ⟨%v1, reader⟩
    icases rid with ⟨%v2, rid⟩
    try wp_auto
    have hj1 : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
    have hj1' : sint.Z (j + W64 1) = sint.Z j + 1 := by word
    wp_if_destruct
    · nextIt
    wp_if_destruct
    · nextIt
    iunfold replica.readerPart at Hrd
    icases Hrd with (%Hn | ⟨%cv, %cid, %R, #Hci, #Hk, Hrd, %Hat⟩)
    · exact absurd Hn Hif
    try wp_auto
    have hkc : (sp.peerRdKind me (sint.Z j).toNat).conn = .peer := by
      unfold sp.peerRdKind; split <;> rfl
    ihave #Hk' : sp.connKind γ cid (sp.peerRdKind me (sint.Z j).toNat).conn $$ []
    · rw [hkc]; iexact Hk
    wp_apply wp_fork $$ [Hrd Hew1]
    · wp_apply wp_listen r γ γc γm γw N me j _ (sp.peerRdKind me (sint.Z j).toNat) cv cid R []
        ewsl _ $$ [$Hrep $Hci $Hk' $Hrd $HEw Hew1]
      · isplitr
        · ipureintro; unfold sp.peerRdKind; split <;> simp
        isplitr
        · ipureintro; omega
        isplitr
        · ipureintro; exact Hat
        isplitr
        · ipureintro; exact hewl
        rw [hjz]; iexact Hew1
      itrivial
    nextIt
  iapply HΦ
  iexists γw
  iframe Hrep
  unfold replica.serveSt
  iexists lv, pcsl, pcs, al
  iframe HLis Hlis Hap Hpc Hpcs Hpok HAlias

end proof

end Perennial.github_com.imdea_software.swiftpaxos
