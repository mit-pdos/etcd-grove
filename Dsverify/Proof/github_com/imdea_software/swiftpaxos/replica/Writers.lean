/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/Writers.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica's writing side, proved: `BeaconReply.Marshal`, `ReplyBeacon`, `SendMsg`,
`SendClientMsg`, `SendBeacon` (specs: Proof/replica/WriterSpecs.lean, Specs.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.pkg.TimeInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WriterSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv wire

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section marshal

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF] [github_com.imdea_software.swiftpaxos.SwiftHyps GF]
variable [replica.defs.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- One store `bs[i] = x` into the 8-byte buffer `Hsl`. -/
local macro "store8" : tactic => `(tactic| (
  (try rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by decide⟩)])
  wp_pures
  wp_apply wp_store_slice_index _ _ _ _ $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro
    simp only [List.length_set, List.length_replicate]
    decide
  (try wp_auto)))

/-- `(*BeaconReply).Marshal(wire)`: the timestamp's 8 bytes. -/
theorem replica.defs.BeaconReply.Marshal.wp_proof (t : Loc) (dq : DFrac) (ts : w64)
    (wr : GoInterface) (S Q : List w8 → IProp GF) (W : List w8) :
    {{ sinkOk wr S Q ∗ S W ∗ □ Q (W ++ sp.le64 ts) ∗
        t ↦{dq} replica.defs.BeaconReply.mk ts }}
      (App (Val (t @!! go.GoType.PointerType replica.defs.BeaconReply.ty @!! go!"Marshal"))
        (Val #wr))
    {{ RET #(); S (W ++ sp.le64 ts) ∗ t ↦{dq} replica.defs.BeaconReply.mk ts }} := by
  wp_start as ⟨#Hsink, HS, #HQ, Ht⟩
  ihave %Htn := typedPointsto_not_null $$ Ht
  iStructNamed Ht
  wp_auto
  ihave Hsl := slice_array b_ptr 8 (Perennial.zero_val (GoArray w8 8)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) from rfl]
  store8
  store8
  store8
  store8
  store8
  store8
  store8
  store8
  rw [set8 _ (by simp), le64_sbytes]
  iunfold sinkOk at Hsink
  icases Hsink with ⟨%e, %He, #HW⟩
  subst He
  wp_pures
  wp_apply HW $$ HS HQ Hsl as %nn %err HS Hsl
  iapply HΦ
  iframe HS
  iapply typedPointsto_combine _ _ _ Htn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-- `(*Beacon).Marshal(wire)`: the timestamp's 8 bytes. -/
theorem replica.defs.Beacon.Marshal.wp_proof (t : Loc) (dq : DFrac) (ts : w64)
    (wr : GoInterface) (S Q : List w8 → IProp GF) (W : List w8) :
    {{ sinkOk wr S Q ∗ S W ∗ □ Q (W ++ sp.le64 ts) ∗
        t ↦{dq} replica.defs.Beacon.mk ts }}
      (App (Val (t @!! go.GoType.PointerType replica.defs.Beacon.ty @!! go!"Marshal"))
        (Val #wr))
    {{ RET #(); S (W ++ sp.le64 ts) ∗ t ↦{dq} replica.defs.Beacon.mk ts }} := by
  wp_start as ⟨#Hsink, HS, #HQ, Ht⟩
  ihave %Htn := typedPointsto_not_null $$ Ht
  iStructNamed Ht
  wp_auto
  ihave Hsl := slice_array b_ptr 8 (Perennial.zero_val (GoArray w8 8)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) from rfl]
  store8
  store8
  store8
  store8
  store8
  store8
  store8
  store8
  rw [set8 _ (by simp), le64_sbytes]
  iunfold sinkOk at Hsink
  icases Hsink with ⟨%e, %He, #HW⟩
  subst He
  wp_pures
  wp_apply HW $$ HS HQ Hsl as %nn %err HS Hsl
  iapply HΦ
  iframe HS
  iapply typedPointsto_combine _ _ _ Htn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end marshal

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv wire

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [bufio.Assumptions] [net.Assumptions] [net.FieldAssumptions] [dlog.Assumptions]
  [time.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- `r.M.Unlock()` (deferred) with the lock invariant back, then return. -/
local macro "unlockret" : tactic => `(tactic| (
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
  · iframe Hmu Hlocked
    try inext
    try unfold replica.lockInv
    iexists alive, lats
    iframe
    ipureintro; exact Hl
  try wp_auto
  try wp_pures
  iapply HΦ; itrivial))

set_option hygiene false in
/-- `r.M.Unlock()` (deferred) with the lock invariant back, then return `P`. -/
local macro "unlockretP" : tactic => `(tactic| (
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
  · iframe Hmu Hlocked
    try inext
    try unfold replica.lockInv
    iexists alive, lats
    iframe
    ipureintro; exact Hl
  try wp_auto
  try wp_pures
  iapply HΦ; iexact HP))

set_option hygiene false in
/-- Write one frame of `m` (`code`, then `msg.Marshal`, then `Flush`) on the writer `Hw`
(`wrSt`), with `hk`, `hcode`, `Hm`, `Hmar`, `HP`; `Hw` back. -/
local macro "writeframe" : tactic => `(tactic| (
  ihave Hop := sp.wrSt_open γ γc γm w _ _ hk $$ [Hw]
  · iframe Hw Hm
  icases Hop with ⟨%cv, %cid, %W, #Hwr, Hs, #HQ, Hclose⟩
  ihave #Hwr' := Hwr
  iunfold bufio.writerOk at Hwr'
  icases Hwr' with ⟨%e, %Ew, -, #Hpc0, -⟩
  ihave #Hpc := Hpc0
  iunfold bufio.prefixClosed at Hpc
  have hfr : W ++ [m.code] ++ m.body = W ++ m.frame := by simp [sp.Msg.frame]
  ihave #HQ1 : □ sp.WrKind.proto γ γc γm _ cid (W ++ [m.code]) $$ []
  · imodintro; iapply Hpc $$ %(W ++ [m.code]) %m.body; rw [hfr]; iexact HQ
  subst hcode
  wp_apply wire.wp_WriteByte_sink w cv _ _ W m.code $$ [Hs] as %e1 Hs
  · iframe Hwr Hs HQ1
  ihave #Hsk := wire.bufio_sinkOk w cv _ _ $$ []
  · iframe Hwr; iPkgInit
  ihave #HQ2 : □ sp.WrKind.proto γ γc γm _ cid (W ++ [m.code] ++ m.body) $$ []
  · imodintro; rw [hfr]; iexact HQ
  iunfold sp.marshalOk at Hmar
  icases Hmar with ⟨%em, %Hem, #HM⟩
  subst Hem
  try wp_auto
  wp_bind (App (Val #(methods em.ty go!"Marshal" em.v)) _)
  iapply HM $$ HP Hsk Hs Hpc0 HQ2
  inext
  iintro HP Hs
  try wp_auto
  wp_apply wire.wp_Flush_sink w cv _ _ _ $$ [Hs] as %e2 ⟨%sent, %pend, %err, Hown, %Hdone⟩
  · iframe Hwr Hs
  ihave Hw := Hclose $$ %sent %pend %err Hown %(by rw [← hfr]; exact Hdone)
  try wp_auto))

theorem replica.Replica.ReplyBeacon.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.ReplyBeacon.spec (hG := hG) := by
  intro r γ γc γm γw N me g rid ts
  wp_start as ⟨#Hrep, Hg, %Hrid⟩
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  iunfold replica.lockInv at HR
  icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
  ihave %Hpwl := ownSlice_len _ _ _ $$ Hpws
  iStructNamed Hg
  wp_auto
  have hi : sint.Z (W64 (sint.Z rid)) = rid.toInt := by
    have : sint.Z rid = rid.toInt := rfl
    rw [this]; word
  have hlen : sint.Z pwsl.len = N := by
    obtain ⟨h1, h2⟩ := Hpwl; rw [Hlens.1] at h1
    have e1 : sint.nat pwsl.len = (sint.Z pwsl.len).toNat := rfl
    omega
  rw [hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨Hrid.1, by omega⟩)]
  obtain ⟨w, hw⟩ : ∃ w, pws[rid.toInt.toNat]? = some w :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  wp_apply wp_load_slice_index _ _ _ _ w Hrid.1 $$ [Hpws] as -
  · iframe Hpws; ipureintro; exact hw
  icases BigSepL.bigSepL_insert_acc hw $$ Hpw with ⟨Hw, Hpw⟩
  try wp_auto
  wp_if_destruct
  · -- no writer: log and return
    wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int32 #rid]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨-, -⟩
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType replica.Replica.ty) (m := go!"Printf") #r]
    try wp_auto
    try wp_load
    try wp_pures
    wp_apply wp_Printf $$ [$Hquiet]
    ihave Hpw := Hpw $$ %null []
    · ileft; ipureintro; rfl
    have e := list_set_lookup_self pws _ null hw
    isimp only [e] at Hpw
    unlockret
  · icases Hw with (%Hn | Hw)
    · exact absurd Hn Hif
    have hk : (sp.peerWrKind me rid.toInt.toNat).ok (.beaconReply ts) ∧ (sp.Msg.beaconReply ts).wf := by
      unfold sp.peerWrKind; split <;> exact ⟨trivial, trivial⟩
    ihave #Hm : sp.msgOk γ γc γm (.beaconReply ts) $$ []
    · simp only [sp.msgOk]; itrivial
    icases sp.wrSt_open γ γc γm w _ _ hk $$ [$Hw $Hm] with ⟨%cv, %cid, %W, #Hwr, Hs, #HQ, Hclose⟩
    ihave #Hwr' := Hwr
    iunfold bufio.writerOk at Hwr'
    icases Hwr' with ⟨%e, %Ew, -, #Hpc, -⟩
    iunfold bufio.prefixClosed at Hpc
    have hfr : (sp.Msg.beaconReply ts).frame = [W8 7] ++ sp.le64 ts := rfl
    rw [hfr] at *
    ihave #HQ1 : □ sp.WrKind.proto γ γc γm (sp.peerWrKind me rid.toInt.toNat) cid (W ++ [W8 7]) $$ []
    · imodintro; iapply Hpc $$ %_ %(sp.le64 ts); rw [← List.append_assoc]; iexact HQ
    wp_apply wire.wp_WriteByte_sink w cv _ _ W (W8 7) $$ [$Hwr $Hs $HQ1] as %e1 Hs
    ihave #Hsk := wire.bufio_sinkOk w cv _ _ $$ []
    · iframe Hwr; iPkgInit
    ihave #HQ2 : □ sp.WrKind.proto γ γc γm (sp.peerWrKind me rid.toInt.toNat) cid
      (W ++ [W8 7] ++ sp.le64 ts) $$ []
    · imodintro; rw [List.append_assoc]; iexact HQ
    wp_apply replica.defs.BeaconReply.Marshal.wp_proof _ (DFrac.own 1) ts _ _ _ (W ++ [W8 7])
      $$ [$Hsk $Hs $HQ2 $«$r0»] as ⟨Hs, -⟩
    wp_apply wire.wp_Flush_sink w cv _ _ _ $$ [$Hwr $Hs] as %e2 ⟨%sent, %pend, %err, Hown, %Hdone⟩
    ihave Hw := Hclose $$ %sent %pend %err Hown %(by simpa [List.append_assoc] using Hdone)
    ihave Hpw := Hpw $$ [Hw]
    · iright; iexact Hw
    have e := list_set_lookup_self pws _ w hw
    isimp only [e] at Hpw
    unlockret

theorem replica.Replica.SendBeacon.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.SendBeacon.spec (hG := hG) := by
  intro r γ γc γm γw N me rid
  wp_start as ⟨#Hrep, %Hrid⟩
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  iunfold replica.lockInv at HR
  icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
  ihave %Hpwl := ownSlice_len _ _ _ $$ Hpws
  wp_auto
  have hi : sint.Z (W64 (sint.Z rid)) = rid.toInt := by
    have : sint.Z rid = rid.toInt := rfl
    rw [this]; word
  have hlen : sint.Z pwsl.len = N := by
    obtain ⟨h1, h2⟩ := Hpwl; rw [Hlens.1] at h1
    have e1 : sint.nat pwsl.len = (sint.Z pwsl.len).toNat := rfl
    omega
  rw [hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨Hrid.1, by omega⟩)]
  obtain ⟨w, hw⟩ : ∃ w, pws[rid.toInt.toNat]? = some w :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  wp_apply wp_load_slice_index _ _ _ _ w Hrid.1 $$ [Hpws] as -
  · iframe Hpws; ipureintro; exact hw
  icases BigSepL.bigSepL_insert_acc hw $$ Hpw with ⟨Hw, Hpw⟩
  try wp_auto
  wp_if_destruct
  · -- no writer: log and return
    wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int32 #rid]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨-, -⟩
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType replica.Replica.ty) (m := go!"Printf") #r]
    try wp_auto
    try wp_load
    try wp_pures
    wp_apply wp_Printf $$ [$Hquiet]
    ihave Hpw := Hpw $$ %null []
    · ileft; ipureintro; rfl
    have e := list_set_lookup_self pws _ null hw
    isimp only [e] at Hpw
    unlockret
  · icases Hw with (%Hn | Hw)
    · exact absurd Hn Hif
    have hk : ∀ ts : w64, (sp.peerWrKind me rid.toInt.toNat).ok (.beacon ts) ∧
        (sp.Msg.beacon ts).wf := by
      intro ts; unfold sp.peerWrKind; split <;> exact ⟨trivial, trivial⟩
    have hmk : ∀ ts : w64, (⊢ sp.msgOk γ γc γm (.beacon ts)) := by
      intro ts; simp only [sp.msgOk]; iintro; itrivial
    icases sp.wrSt_open_gen γ γc γm w _ $$ Hw with ⟨%cv, %cid, %W, #Hwr, Hs, #HQall, Hclose⟩
    ihave #Hwr' := Hwr
    iunfold bufio.writerOk at Hwr'
    icases Hwr' with ⟨%e, %Ew, -, #Hpc0, -⟩
    ihave #Hpc := Hpc0
    iunfold bufio.prefixClosed at Hpc
    ihave #HQ0 := HQall $$ %(sp.Msg.beacon 0) %(hk 0) []
    · iapply hmk
    ihave #HQ1 : □ sp.WrKind.proto γ γc γm (sp.peerWrKind me rid.toInt.toNat) cid (W ++ [W8 6]) $$ []
    · imodintro; iapply Hpc $$ %(W ++ [W8 6]) %(sp.le64 0)
      rw [show W ++ [W8 6] ++ sp.le64 0 = W ++ (sp.Msg.beacon 0).frame by simp [sp.Msg.frame, sp.Msg.code, sp.Msg.body]]
      iexact HQ0
    wp_apply wire.wp_WriteByte_sink w cv _ _ W (W8 6) $$ [$Hwr $Hs $HQ1] as %e1 Hs
    ihave #Htm1 := replica.time_init $$ Hpkg
    wp_apply time.wp_Now $$ [$Htm1] as %tm -
    wp_apply time.Time.wp_UnixNano' as %ts -
    try wp_auto
    ihave #Hsk := wire.bufio_sinkOk w cv _ _ $$ []
    · iframe Hwr; iPkgInit
    ihave #HQt := HQall $$ %(sp.Msg.beacon ts) %(hk ts) []
    · iapply hmk
    have hfr : W ++ [W8 6] ++ sp.le64 ts = W ++ (sp.Msg.beacon ts).frame := by
      simp [sp.Msg.frame, sp.Msg.code, sp.Msg.body]
    ihave #HQ2 : □ sp.WrKind.proto γ γc γm (sp.peerWrKind me rid.toInt.toNat) cid
      (W ++ [W8 6] ++ sp.le64 ts) $$ []
    · imodintro; rw [hfr]; iexact HQt
    wp_apply replica.defs.Beacon.Marshal.wp_proof _ (DFrac.own 1) ts _ _ _ (W ++ [W8 6])
      $$ [$Hsk $Hs $HQ2 $«$r0»] as ⟨Hs, -⟩
    wp_apply wire.wp_Flush_sink w cv _ _ _ $$ [$Hwr $Hs] as %e2 ⟨%sent, %pend, %err, Hown, %Hdone⟩
    ihave Hw := Hclose $$ %(sp.Msg.beacon ts) %sent %pend %err %(hk ts) [] Hown
      %(by rw [← hfr]; exact Hdone)
    · iapply hmk
    ihave Hpw := Hpw $$ [Hw]
    · iright; iexact Hw
    have e := list_set_lookup_self pws _ w hw
    isimp only [e] at Hpw
    unlockret

theorem replica.Replica.SendMsg.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.SendMsg.spec (hG := hG) := by
  intro r γ γc γm γw N me peerId code msg m P
  wp_start as ⟨#Hrep, #Hmar, HP, #Hm, %Hpre⟩
  obtain ⟨hpeer, hwf, hcode, hp0, hpN⟩ := Hpre
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  iunfold replica.lockInv at HR
  icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
  ihave %Hpwl := ownSlice_len _ _ _ $$ Hpws
  wp_auto
  have hi : sint.Z (W64 (sint.Z peerId)) = peerId.toInt := by
    have : sint.Z peerId = peerId.toInt := rfl
    rw [this]; word
  have hlen : sint.Z pwsl.len = N := by
    obtain ⟨h1, h2⟩ := Hpwl; rw [Hlens.1] at h1
    have e1 : sint.nat pwsl.len = (sint.Z pwsl.len).toNat := rfl
    omega
  rw [hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨hp0, by omega⟩)]
  obtain ⟨w, hw⟩ : ∃ w, pws[peerId.toInt.toNat]? = some w :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  wp_apply wp_load_slice_index _ _ _ _ w hp0 $$ [Hpws] as -
  · iframe Hpws; ipureintro; exact hw
  icases BigSepL.bigSepL_insert_acc hw $$ Hpw with ⟨Hw, Hpw⟩
  try wp_auto
  wp_if_destruct
  · -- no writer: log and return
    wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int32 #peerId]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨-, -⟩
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType replica.Replica.ty) (m := go!"Printf") #r]
    try wp_auto
    try wp_load
    try wp_pures
    wp_apply wp_Printf $$ [$Hquiet]
    ihave Hpw := Hpw $$ %null []
    · ileft; ipureintro; rfl
    have e := list_set_lookup_self pws _ null hw
    isimp only [e] at Hpw
    unlockretP
  · icases Hw with (%Hn | Hw)
    · exact absurd Hn Hif
    have hk : (sp.peerWrKind me peerId.toInt.toNat).ok m ∧ m.wf := by
      unfold sp.peerWrKind; split <;> exact ⟨hpeer, hwf⟩
    ihave Hop := sp.wrSt_open γ γc γm w _ _ hk $$ [Hw]
    · iframe Hw Hm
    icases Hop with ⟨%cv, %cid, %W, #Hwr, Hs, #HQ, Hclose⟩
    ihave #Hwr' := Hwr
    iunfold bufio.writerOk at Hwr'
    icases Hwr' with ⟨%e, %Ew, -, #Hpc0, -⟩
    ihave #Hpc := Hpc0
    iunfold bufio.prefixClosed at Hpc
    have hfr : W ++ [m.code] ++ m.body = W ++ m.frame := by simp [sp.Msg.frame]
    ihave #HQ1 : □ sp.WrKind.proto γ γc γm _ cid (W ++ [m.code]) $$ []
    · imodintro; iapply Hpc $$ %(W ++ [m.code]) %m.body; rw [hfr]; iexact HQ
    subst hcode
    wp_apply wire.wp_WriteByte_sink w cv _ _ W m.code $$ [Hs] as %e1 Hs
    · iframe Hwr Hs HQ1
    ihave #Hsk := wire.bufio_sinkOk w cv _ _ $$ []
    · iframe Hwr; iPkgInit
    ihave #HQ2 : □ sp.WrKind.proto γ γc γm _ cid (W ++ [m.code] ++ m.body) $$ []
    · imodintro; rw [hfr]; iexact HQ
    iunfold sp.marshalOk at Hmar
    icases Hmar with ⟨%em, %Hem, #HM⟩
    subst Hem
    try wp_auto
    wp_bind (App (Val #(methods em.ty go!"Marshal" em.v)) _)
    iapply HM $$ HP Hsk Hs Hpc0 HQ2
    inext
    iintro HP Hs
    try wp_auto
    wp_apply wire.wp_Flush_sink w cv _ _ _ $$ [Hs] as %e2 ⟨%sent, %pend, %err, Hown, %Hdone⟩
    · iframe Hwr Hs
    ihave Hw := Hclose $$ %sent %pend %err Hown %(by rw [← hfr]; exact Hdone)
    try wp_auto
    ihave Hpw := Hpw $$ [Hw]
    · iright; iexact Hw
    have e := list_set_lookup_self pws _ w hw
    isimp only [e] at Hpw
    unlockretP

theorem replica.Replica.SendClientMsg.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.SendClientMsg.spec (hG := hG) := by
  intro r γ γc γm γw N me id code msg m P
  wp_start as ⟨#Hrep, #Hmar, HP, #Hm, %Hpre⟩
  obtain ⟨hcl, hwf, hcode⟩ := Hpre
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  iunfold replica.lockInv at HR
  icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
  iunfold replica.clientWrs at Hcw
  icases Hcw with ⟨%cw, %ws, Hcwm, Hauth, %Hcws, Hws⟩
  try wp_auto
  wp_apply (wp_map_lookup1 (K := w32) (V := Loc) _ _ cwm cw id) $$ [$Hcwm] as Hcwm
  try wp_auto
  wp_if_destruct
  · -- no writer: log and return
    wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int32 #id]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨-, -⟩
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType replica.Replica.ty) (m := go!"Printf") #r]
    try wp_auto
    try wp_load
    try wp_pures
    wp_apply wp_Printf $$ [$Hquiet]
    ihave Hcw : replica.clientWrs γ γc γm γw cwm $$ [Hcwm Hauth Hws]
    · iunfold replica.clientWrs; iexists cw, ws; iframe; ipureintro; exact Hcws
    unlockretP
  · obtain ⟨w, hw⟩ : ∃ w, cw !! id = some w := by
      cases h : cw !! id with
      | none => rw [h] at Hif; exact absurd rfl Hif
      | some w => exact ⟨w, rfl⟩
    rw [hw] at Hif ⊢
    simp only [Option.getD_some]
    have hws := Hcws id w hw
    icases BigSepM.bigSepM_lookup_acc hws $$ Hws with ⟨Hw, Hws⟩
    have hk : (sp.WrKind.client id).ok m ∧ m.wf := ⟨hcl, hwf⟩
    writeframe
    ihave Hws := Hws $$ Hw
    ihave Hcw : replica.clientWrs γ γc γm γw cwm $$ [Hcwm Hauth Hws]
    · iunfold replica.clientWrs; iexists cw, ws; iframe; ipureintro; exact Hcws
    unlockretP

set_option hygiene false in
/-- (C18) Write one frame of a message chosen among `Pm` (`code`, then `msg.Marshal`, then
`Flush`) on the writer `Hw` (`wrSt`), with `hk`, `hcode` (for every candidate), `hex` (one
candidate), `Hms`, `Hmar` (`marshalOkP`), `HP`; `Hw` back. -/
local macro "writeframeP" : tactic => `(tactic| (
  obtain ⟨m0, hm0⟩ := hex
  icases sp.wrSt_open_gen γ γc γm w _ $$ Hw with ⟨%cv, %cid, %W, #Hwr, Hs, #HQall, Hclose⟩
  ihave #Hwr' := Hwr
  iunfold bufio.writerOk at Hwr'
  icases Hwr' with ⟨%e, %Ew, -, #Hpc0, -⟩
  ihave #Hpc := Hpc0
  iunfold bufio.prefixClosed at Hpc
  ihave #Hms' := Hms
  iunfold sp.msgsOk at Hms'
  have hfr : ∀ m : sp.Msg, W ++ [m.code] ++ m.body = W ++ m.frame := by
    intro m; simp [sp.Msg.frame]
  ihave #HQ1 : □ sp.WrKind.proto γ γc γm _ cid (W ++ [code]) $$ []
  · imodintro
    rw [hcode m0 hm0]
    iapply Hpc $$ %(W ++ [m0.code]) %m0.body
    rw [hfr]
    ihave #Hm0 := Hms' $$ %m0 %hm0
    ihave #HQ0 := HQall $$ %m0 %(hk m0 hm0) Hm0
    iexact HQ0
  wp_apply wire.wp_WriteByte_sink w cv _ _ W code $$ [Hs] as %e1 Hs
  · iframe Hwr Hs HQ1
  ihave #Hsk := wire.bufio_sinkOk w cv _ _ $$ []
  · iframe Hwr; iPkgInit
  ihave #HQ2 : □ ∀ m : sp.Msg, ⌜Pm m⌝ -∗
      □ sp.WrKind.proto γ γc γm _ cid (W ++ [code] ++ m.body) $$ []
  · imodintro
    iintro %m %hm
    imodintro
    rw [hcode m hm, hfr]
    ihave #Hmm := Hms' $$ %m %hm
    ihave #HQm := HQall $$ %m %(hk m hm) Hmm
    iexact HQm
  iunfold sp.marshalOkP at Hmar
  icases Hmar with ⟨%em, %Hem, #HM⟩
  subst Hem
  try wp_auto
  wp_bind (App (Val #(methods em.ty go!"Marshal" em.v)) _)
  iapply HM $$ HP Hsk Hs Hpc0 HQ2
  inext
  iintro %m %hm HP Hs
  try wp_auto
  wp_apply wire.wp_Flush_sink w cv _ _ _ $$ [Hs] as %e2 ⟨%sent, %pend, %err, Hown, %Hdone⟩
  · iframe Hwr Hs
  ihave #Hmm := Hms' $$ %m %hm
  ihave Hw := Hclose $$ %m %sent %pend %err %(hk m hm) Hmm Hown
    %(by rw [hcode m hm, hfr m] at Hdone; exact Hdone)
  try wp_auto))

theorem replica.Replica.SendMsgP.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.SendMsgP.spec (hG := hG) := by
  intro r γ γc γm γw N me peerId code msg Pm P
  wp_start as ⟨#Hrep, #Hmar, HP, #Hms, %Hpre⟩
  obtain ⟨hex, hall, hp0, hpN⟩ := Hpre
  have hcode : ∀ m, Pm m → code = m.code := fun m h => (hall m h).2.2
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  iunfold replica.lockInv at HR
  icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
  ihave %Hpwl := ownSlice_len _ _ _ $$ Hpws
  wp_auto
  have hi : sint.Z (W64 (sint.Z peerId)) = peerId.toInt := by
    have : sint.Z peerId = peerId.toInt := rfl
    rw [this]; word
  have hlen : sint.Z pwsl.len = N := by
    obtain ⟨h1, h2⟩ := Hpwl; rw [Hlens.1] at h1
    have e1 : sint.nat pwsl.len = (sint.Z pwsl.len).toNat := rfl
    omega
  rw [hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨hp0, by omega⟩)]
  obtain ⟨w, hw⟩ : ∃ w, pws[peerId.toInt.toNat]? = some w :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  wp_apply wp_load_slice_index _ _ _ _ w hp0 $$ [Hpws] as -
  · iframe Hpws; ipureintro; exact hw
  icases BigSepL.bigSepL_insert_acc hw $$ Hpw with ⟨Hw, Hpw⟩
  try wp_auto
  wp_if_destruct
  · -- no writer: log and return
    wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int32 #peerId]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨-, -⟩
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType replica.Replica.ty) (m := go!"Printf") #r]
    try wp_auto
    try wp_load
    try wp_pures
    wp_apply wp_Printf $$ [$Hquiet]
    ihave Hpw := Hpw $$ %null []
    · ileft; ipureintro; rfl
    have e := list_set_lookup_self pws _ null hw
    isimp only [e] at Hpw
    unlockretP
  · icases Hw with (%Hn | Hw)
    · exact absurd Hn Hif
    have hk : ∀ m, Pm m → (sp.peerWrKind me peerId.toInt.toNat).ok m ∧ m.wf := by
      intro m hm
      unfold sp.peerWrKind; split <;> exact ⟨(hall m hm).1, (hall m hm).2.1⟩
    writeframeP
    ihave Hpw := Hpw $$ [Hw]
    · iright; iexact Hw
    have e := list_set_lookup_self pws _ w hw
    isimp only [e] at Hpw
    unlockretP

theorem replica.Replica.SendClientMsgP.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.SendClientMsgP.spec (hG := hG) := by
  intro r γ γc γm γw N me id code msg Pm P
  wp_start as ⟨#Hrep, #Hmar, HP, #Hms, %Hpre⟩
  obtain ⟨hex, hall⟩ := Hpre
  have hcode : ∀ m, Pm m → code = m.code := fun m h => (hall m h).2.2
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  iunfold replica.lockInv at HR
  icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
  iunfold replica.clientWrs at Hcw
  icases Hcw with ⟨%cw, %ws, Hcwm, Hauth, %Hcws, Hws⟩
  try wp_auto
  wp_apply (wp_map_lookup1 (K := w32) (V := Loc) _ _ cwm cw id) $$ [$Hcwm] as Hcwm
  try wp_auto
  wp_if_destruct
  · -- no writer: log and return
    wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int32 #id]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨-, -⟩
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType replica.Replica.ty) (m := go!"Printf") #r]
    try wp_auto
    try wp_load
    try wp_pures
    wp_apply wp_Printf $$ [$Hquiet]
    ihave Hcw : replica.clientWrs γ γc γm γw cwm $$ [Hcwm Hauth Hws]
    · iunfold replica.clientWrs; iexists cw, ws; iframe; ipureintro; exact Hcws
    unlockretP
  · obtain ⟨w, hw⟩ : ∃ w, cw !! id = some w := by
      cases h : cw !! id with
      | none => rw [h] at Hif; exact absurd rfl Hif
      | some w => exact ⟨w, rfl⟩
    rw [hw] at Hif ⊢
    simp only [Option.getD_some]
    have hws := Hcws id w hw
    icases BigSepM.bigSepM_lookup_acc hws $$ Hws with ⟨Hw, Hws⟩
    have hk : ∀ m, Pm m → (sp.WrKind.client id).ok m ∧ m.wf :=
      fun m hm => ⟨(hall m hm).1, (hall m hm).2.1⟩
    writeframeP
    ihave Hws := Hws $$ Hw
    ihave Hcw : replica.clientWrs γ γc γm γw cwm $$ [Hcwm Hauth Hws]
    · iunfold replica.clientWrs; iexists cw, ws; iframe; ipureintro; exact Hcws
    unlockretP

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
