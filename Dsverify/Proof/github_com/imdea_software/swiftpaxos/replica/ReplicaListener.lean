/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ReplicaListener.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.replicaListener(rid, br)` (riskiest step): the peer reader's loop over a stream the protocol
admits (`sp.stream_next`), every table message handed on with its witness.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.pkg.TimeInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.StreamLaw
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Fatal
public import Perennial.Proof.time.Results

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [bufio.Assumptions] [net.Assumptions] [net.FieldAssumptions] [io.Assumptions] [net.rpc.Assumptions]
  [errors.Assumptions] [dlog.Assumptions] [time.Assumptions]
  [state.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- After the loop: `Alive[rid] = false` under `r.M`. -/
local macro "postloop" : tactic => `(tactic| (
  try wp_pures
  try wp_load
  try wp_pures
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  unfold replica.lockInv
  icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
  ihave %Hall := ownSlice_len _ _ _ $$ Hal
  have hlen : sint.Z alsl.len = N := by
    obtain ⟨h1, h2⟩ := Hall; rw [Hl.1] at h1
    have e1 : sint.nat alsl.len = (sint.Z alsl.len).toNat := rfl
    omega
  try wp_pures
  wp_load
  try wp_pures
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hrid.1, by omega⟩)]
  wp_apply wp_store_slice_index _ _ _ _ $$ [Hal] as Hal
  · iframe Hal; ipureintro; exact ⟨Hrid.1, by omega⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
  · iframe Hmu Hlocked
    try inext
    try unfold replica.lockInv
    iexists _, lats
    iframe
    ipureintro; simp; omega
  try wp_pures
  iapply HΦ; itrivial))

theorem replica.Replica.replicaListener.wp_proof
    (wp_ReplyBeacon : replica.Replica.ReplyBeacon.spec (hG := hG))
    (wp_WaitDurationID : replica.defs.LatencyTable.WaitDurationID.spec (hG := hG))
    (wp_Get : rpc.Table.Get.spec (hG := hG))
    (wp_BUnm : replica.defs.Beacon.Unmarshal.spec (GF := netDistGF) (hG := hG))
    (wp_BRUnm : replica.defs.BeaconReply.Unmarshal.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.replicaListener.spec (hG := hG) := by
  intro r γ γc γm γw N me rid br k cv cid R done ewsl e
  wp_start as ⟨#Hrep, %Hk, %Hrid, #Hc, #Hkind, Hrd, %Hat, #Hew, %Hewl, He⟩
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  wp_auto
  ipersist r
  ipersist rid
  ihave HL : (∃ (R : List w8) (done : List sp.Msg) (er : GoInterface) (mt : w8)
      (gb : replica.defs.Beacon) (gbr : replica.defs.BeaconReply) (e' : w64),
      "err" ∷ err_ptr ↦ er ∗ "msgType" ∷ msgType_ptr ↦ mt ∗ "gbeacon" ∷ gbeacon_ptr ↦ gb ∗
      "gbeaconReply" ∷ gbeaconReply_ptr ↦ gbr ∗
      "Hrd" ∷ bufio.ownReader br cv (recvTokL cid k.side (k.proto γ γc γm)) R ∗
      "%Hat" ∷ ⌜er = interface.nil → sp.rdAt k done R⌝ ∗
      "He" ∷ typedPointsto (sliceIndexRef w64 (sint.Z rid) ewsl) e' (DFrac.own 1) :
      IProp netDistGF) $$ [err msgType gbeacon gbeaconReply Hrd He]
  · iexists R, done, _, _, _, _, e
    iframe
    ipureintro; intro _; exact Hat
  wp_for HL
  rcases er with eo | _
  · -- an error: the loop ends; `Alive[rid] = false` under `r.M`
    wp_auto
    cleanup_bool_decide
    postloop
  · wp_auto
    rw [if_pos (by simp)]
    wp_auto
    ihave #Hrdok := bufio.readerOk_conn cv cid k.side (k.proto γ γc γm) $$ [$Hpkg3 $Hc]
    wp_apply (lc := 1) bufio.wp_ReadByte br cv _ R $$ [$Hpkg2 $Hrdok $Hrd] as %c %er Hr
    icases Hr with (⟨%Hen, Hrd⟩ | ⟨%Hen, #Hea, Hrd⟩)
    · subst Hen
      wp_auto
      -- the byte read is the type of the stream's next message, a peer message
      icases sp.ownReader_proto br cv cid k.side _ (R ++ [c]) $$ Hrd with ⟨Hrd, HpL⟩
      iapply fupd_wp
      imod (lc_fupd_elim_later (GF := netDistGF) (E := ⊤)) $$ Hlc1 HpL with Hp
      imodintro
      icases Hp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
      · simp at Hnil
      have hok : ∀ m, k.ok m = m.isPeer := by
        intro m; rcases Hk with ⟨id, rfl⟩ | rfl <;> rfl
      obtain ⟨hR, hdone⟩ := Hat rfl
      ihave %Hcode := sp.stream_code k cid ext done c (by rw [← hR]; exact Hext)
        (fun d hd => (hdone d hd).1) $$ [$Hkind $HP]
      obtain ⟨m0, hm0, hc0⟩ := Hcode
      rw [hok] at hm0
      wp_if_destruct
      · -- a beacon
        ihave #Hrs := bufio.bufioReadsOk br cv _ $$ [$Hpkg2 $Hrdok]
        wp_apply (lc := 1) wp_BUnm gbeacon_ptr gb _ _ (R ++ [W8 6]) $$ [$Hpkg4 $Hrs $Hrd $gbeacon]
          as %er ⟨%data, Hrd, Hres⟩
        icases Hres with (⟨%Hen, %ts, %Hd, Hgb⟩ | ⟨%Hen, %gb', Hgb⟩)
        · subst Hen Hd
          icases sp.ownReader_proto br cv cid k.side _ (R ++ [W8 6] ++ sp.le64 ts) $$ Hrd with ⟨Hrd, HpL⟩
          iapply fupd_wp
          imod (lc_fupd_elim_later (GF := netDistGF) (E := ⊤)) $$ Hlc1 HpL with Hp
          imodintro
          icases Hp with (%Hnil | ⟨%ext2, %Hext2, #HP2⟩)
          · simp at Hnil
          have hpre : k.head ++ sp.framesOf done ++ W8 6 :: sp.le64 ts <+: ext2 := by
            rw [← hR]; simpa [List.append_assoc] using Hext2
          ihave ⟨-, %Hst⟩ := sp.stream_next k cid ext2 done (W8 6) (sp.le64 ts) (.beacon ts) hpre
            (sp.decodes_of_body rfl trivial) (fun d hd => (hdone d hd).1) $$ [$Hkind $HP2]
          wp_auto
          have hrid32 : 0 ≤ (W32 (sint.Z rid)).toInt ∧ (W32 (sint.Z rid)).toInt < N := by
            have : (W32 (sint.Z rid)).toInt = sint.Z rid := by
              have h7 := Hlens.2.2.2; simp only [W32]; rw [BitVec.toInt_ofInt]
              exact Int.bmod_eq_of_le (by omega) (by omega)
            omega
          wp_apply wp_ReplyBeacon r γ γc γm γw N me _ (W32 (sint.Z rid)) ts $$ [$Hrep $«$a0»]
          · ipureintro; exact hrid32
          wp_for_post
          iframe
          iexists (R ++ W8 6 :: sp.le64 ts), done ++ [.beacon ts], _, _, _, _, _
          rw [show R ++ [W8 6] ++ sp.le64 ts = R ++ W8 6 :: sp.le64 ts by simp]
          iframe
          ipureintro
          intro _
          exact sp.rdAt_snoc ⟨hR, hdone⟩ Hst.2 trivial Hst.1
        · -- an error: the loop ends at its condition
          rcases er with eo | _
          · wp_auto
            wp_for_post
            iframe
            iexists _, done, _, _, _, _, _
            iframe
            ipureintro; intro h; cases h
          · exact absurd rfl Hen
      · have hc6 : ¬ c = W8 6 := Hif
        wp_if_destruct
        · -- a beacon's reply
          ihave #Hrs := bufio.bufioReadsOk br cv _ $$ [$Hpkg2 $Hrdok]
          wp_apply (lc := 1) wp_BRUnm gbeaconReply_ptr gbr _ _ (R ++ [W8 7]) $$
            [$Hpkg4 $Hrs $Hrd $gbeaconReply] as %er ⟨%data, Hrd, Hres⟩
          icases Hres with (⟨%Hen, %ts, %Hd, Hgb⟩ | ⟨%Hen, %gb', Hgb⟩)
          · subst Hen Hd
            icases sp.ownReader_proto br cv cid k.side _ (R ++ [W8 7] ++ sp.le64 ts) $$ Hrd with ⟨Hrd, HpL⟩
            iapply fupd_wp
            imod (lc_fupd_elim_later (GF := netDistGF) (E := ⊤)) $$ Hlc1 HpL with Hp
            imodintro
            icases Hp with (%Hnil | ⟨%ext2, %Hext2, #HP2⟩)
            · simp at Hnil
            have hpre : k.head ++ sp.framesOf done ++ W8 7 :: sp.le64 ts <+: ext2 := by
              rw [← hR]; simpa [List.append_assoc] using Hext2
            ihave ⟨-, %Hst⟩ := sp.stream_next k cid ext2 done (W8 7) (sp.le64 ts) (.beaconReply ts)
              hpre (sp.decodes_of_body rfl trivial) (fun d hd => (hdone d hd).1) $$ [$Hkind $HP2]
            wp_auto
            wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
            · iexact Hmu
            iunfold replica.lockInv at HR
            icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
            ihave %Hlatl := ownSlice_len _ _ _ $$ Hlat
            have hlen : sint.Z latsl.len = N := by
              obtain ⟨h1, h2⟩ := Hlatl; rw [Hl.2] at h1
              have e1 : sint.nat latsl.len = (sint.Z latsl.len).toNat := rfl
              omega
            wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hrid.1, by omega⟩)]
            wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hrid.1, by omega⟩)]
            obtain ⟨lv, hlv⟩ : ∃ lv, lats[(sint.Z rid).toNat]? = some lv :=
              ⟨_, List.getElem?_eq_getElem (by omega)⟩
            wp_apply wp_load_slice_index _ _ _ _ lv Hrid.1 $$ [Hlat] as Hlat
            · iframe Hlat; ipureintro; exact hlv
            ihave #Htm1 := replica.time_init $$ Hpkg
            wp_apply time.wp_Now $$ [$Htm1] as %tm -
            wp_apply time.Time.wp_UnixNano' as %ns -
            try wp_auto
            wp_apply wp_store_slice_index _ _ _ _ $$ [Hlat] as Hlat
            · iframe Hlat; ipureintro; exact ⟨Hrid.1, by omega⟩
            try wp_auto
            wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
            · iframe Hmu Hlocked
              try inext
              try unfold replica.lockInv
              iexists alive, _
              iframe
              ipureintro; simp; omega
            ihave #Htm2 := replica.time_init $$ Hpkg
            wp_apply time.wp_Now $$ [$Htm2] as %tm2 -
            wp_apply time.Time.wp_UnixNano' as %ns2 -
            try wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hrid.1, by omega⟩)]
            wp_auto
            wp_apply wp_float64_mul as %f1 _
            try wp_auto
            wp_apply wp_float64_mul as %f2 _
            try wp_auto
            wp_apply wp_float64_add as %f3 _
            try wp_auto
            try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hrid.1, by omega⟩)]
            try wp_auto
            wp_for_post
            iframe
            iexists (R ++ W8 7 :: sp.le64 ts), done ++ [.beaconReply ts], _, _, _, _, _
            rw [show R ++ [W8 7] ++ sp.le64 ts = R ++ W8 7 :: sp.le64 ts by simp]
            iframe
            ipureintro
            intro _
            exact sp.rdAt_snoc ⟨hR, hdone⟩ Hst.2 trivial Hst.1
          · rcases er with eo | _
            · wp_auto
              wp_for_post
              iframe
              iexists _, done, _, _, _, _, _
              iframe
              ipureintro; intro h; cases h
            · exact absurd rfl Hen
        · -- a table message: its type is registered
          ihave #HtOk' := HtOk
          iunfold sp.tableOk at HtOk'
          icases HtOk' with ⟨%Hcomplete, #Hents⟩
          obtain ⟨pr, hpr⟩ : ∃ pr, ents !! c = some pr := by
            have := Hcomplete m0 hm0 (by rw [hc0]; exact hc6) (by rw [hc0]; exact Hif)
            rw [hc0] at this
            exact Option.isSome_iff_exists.1 this
          ihave #Hent := Hents $$ %c %pr %hpr
          iunfold sp.entryOk at Hent
          icases Hent with ⟨%Rep, %γch, #Hnew, #Hch⟩
          iunfold sp.newOk at Hnew
          icases Hnew with ⟨%eo, %Heo, #Hnew⟩
          wp_apply wp_Get tbl nid ents c $$ [$Htbl]
          rw [hpr]
          simp only [Option.getD_some, Option.isSome_some]
          wp_auto
          ipersist p
          rw [Heo]
          wp_apply Hnew as %o Hun
          try wp_auto
          iunfold sp.unmarshalOk at Hun
          icases Hun with ⟨%eu, %Heu, Hun⟩
          subst Heu
          ihave #Hlaw := sp.reader_streamLaw (γc := γc) (γm := γm) br cv k
            (fun m hm => (hok m) ▸ hm) cid done R c hR
            (fun d hd => (hdone d hd).1) $$ Hkind
          wp_apply (lc := 1) Hun $$ Hrdok Hlaw Hrd as %er %data Hrd Hres
          icases Hres with (⟨%Hen, %m, %Hdec, HRep⟩ | %Hen)
          · subst Hen
            icases sp.ownReader_proto br cv cid k.side _ (R ++ [c] ++ data) $$ Hrd with ⟨Hrd, HpL⟩
            iapply fupd_wp
            imod (lc_fupd_elim_later (GF := netDistGF) (E := ⊤)) $$ Hlc1 HpL with Hp
            imodintro
            icases Hp with (%Hnil | ⟨%ext2, %Hext2, #HP2⟩)
            · simp at Hnil
            have hpre : k.head ++ sp.framesOf done ++ c :: data <+: ext2 := by
              rw [← hR]; simpa [List.append_assoc] using Hext2
            ihave ⟨#Hmsg, %Hst⟩ := sp.stream_next k cid ext2 done c data m hpre Hdec
              (fun d hd => (hdone d hd).1) $$ [$Hkind $HP2]
            ihave #pcopy := p
            iStructNamed pcopy
            wp_auto
            wp_apply wp_fork $$ [HRep]
            · -- the goroutine: hand the message on
              wp_auto
              wp_apply wp_WaitDurationID
              wp_apply time.wp_Sleep
              try wp_auto
              wp_apply (wp_bag_send (V := GoInterface) γch pr.Chan' (GoInterface.ok eu)
                (sp.chanMsgP γ γc γm c Rep)) $$ [HRep]
              · iframe Hch
                iunfold sp.chanMsgP
                iexists m
                iframe HRep Hmsg
                ipureintro; exact Hdec.1
              itrivial
            wp_for_post
            iframe
            iexists (R ++ c :: data), done ++ [m], _, _, _, _, _
            rw [show R ++ [c] ++ data = R ++ c :: data by simp]
            iframe
            ipureintro
            intro _
            exact sp.rdAt_snoc ⟨hR, hdone⟩ Hst.2 Hdec.2.1 Hst.1
          · rcases er with eo | _
            · wp_auto
              wp_for_post
              iframe
              iexists _, done, _, _, _, _, _
              iframe
              ipureintro; intro h; cases h
            · exact absurd rfl Hen
    · rcases er with eo | _
      · wp_auto
        wp_for_post
        postloop
      · exact absurd rfl Hen

end proof

end Perennial.github_com.imdea_software.swiftpaxos
