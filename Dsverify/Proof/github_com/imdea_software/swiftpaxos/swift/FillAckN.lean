/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/FillAckN.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**Phase 4 (round N4, sv-swc): `fillNewLeaderAckN`'s proof** (recovery.go:417-536) over the
descriptor side's N1-R1/N1-R2 (NewLeaderReqs.lean, used only through the structures' fields) and
its callees' specs (hypotheses, linked in ServersLink.lean's newLeader line). Top-down: every Go
statement is stepped; the steps not proved yet are named sorries `N4: <item>`.

The report is built in four collections, each appended to the four local slices `cmdIds`,
`phases`, `cmds`, `deps` (the accumulator `swift.fillAcc`, with the `seen` map):
1. the execution log under `execL` (`R1.exec`): the entries `XS`;
2. the last `MSync`'s `Phases` map range (`syncObj`'s maps): the base, in `COMMIT`;
3. `cmdDescs.IterCb` (`IterCbVN`, `R1.desc`): the stopped descriptors' entries `S`;
4. the `proposes` range, skipping `delivered.Has` (`R1.deliv`), in `START`, with the
   descriptor's `proposeDep` (`cmdDescs.Get`) or `proposeDeps`'s.
Then the rank map (first position in `handled` plus one), `idx` sorted by `(rank, index)`
(`slices.SortFunc.specOn`), the four fields filled along `idx`, and `sp.upd_report` (h4-h9
from `localOk`, `coverOk` (N1-R2) and `swift.fill_order`; the witnesses by
`swift.repEntW_entryWit`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewLeaderReqs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FillOrder
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync
public import Dsverify.Proof.github_com.orcaman.concurrent_map.IterCbNDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FillFacts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps2
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FillAckNDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

end defs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

end lemmas

section reqs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

end reqs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

set_option maxHeartbeats 8000000 in
/-- **`fillNewLeaderAckN`** (recovery.go:417; see the file header). -/
theorem swift.Replica.fillNewLeaderAckN.wp_proofN (rp : Loc) (γ : sp.Names) (γc γm : GName)
    (x : swift.RunX) (R1 : swift.N1R1 (hG := hG) rp γ γc γm x)
    (R2 : swift.N1R2 (hG := hG) rp γ γc γm x R1)
    (wp_IterCbVN : github_com.orcaman.concurrent_map.ConcurrentMap.IterCbVN.spec (GF := netDistGF))
    (wp_GetV : github_com.orcaman.concurrent_map.ConcurrentMap.GetV.spec (GF := netDistGF))
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec (hG := hG) dm γdl)
    (wp_Str : swift.CommandId.String.specS (hG := hG) swift.cmdStr)
    (wp_SortFunc : slices.SortFunc.specOn (hG := hG)) :
    swift.Replica.fillNewLeaderAckN.specN (hG := hG) rp γ γc γm x := by
  intro p rep bl cb
  haveI hWP : ∀ c e, Persistent (R1.W c e) := R1.W_pers
  haveI hWdP : ∀ c z D, Persistent (R1.Wd c z D) := R1.Wd_pers
  haveI hWXP : ∀ c e, Persistent (R1.WX c e) := R1.WX_pers
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨HI, Hp, Htk, %Hrep⟩
  iapply wp_fupd
  iunfold swift.recInvB at HI
  icases HI with ⟨#Hd, #Hsc, Hrl, ⟨%ld, %v, %M0, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hep⟩
  -- the stopped epoch at its `cballot` (round 51, `epStoppedXc`), opened; its pin half frozen
  -- (N1-R1 `freeze`, D70/D71 (1))
  iunfold swift.epStoppedXc at Hep
  icases Hep with ⟨%bw, %st0, %stp, %stpX', %bc, Hb2, Hst2, HState, Hrc2, Htok, Hxp, Hxe, Hrm, Hds,
    Hout, Hhs, Hfz, Hfq, %Hbc⟩
  ihave #HdX : swift.descCtxX γ γc γm x rp $$ []
  · iexact Hd
  ihave Hxp : ghostVar x.γxp (1 : Iris.Qp).half (sint.Z cb).toNat $$ [Hxp]
  · rw [← Hbc]
    iapply (show (ghostVar x.syncN.γxp (1 : Iris.Qp).half bc.2 : IProp netDistGF) ⊢
      ghostVar x.γxp (1 : Iris.Qp).half bc.2 from .rfl)
    iexact Hxp
  iapply fupd_wp
  imod R1.freeze (sint.Z cb).toNat $$ [Hxp] with ⟨%X, HFz⟩
  · iframe HdX Hxp
  imodintro
  ihave ⟨%Hstr, Hrl⟩ := BI.persistent_entails_right (swift.runLoopCtx_str rp γ γc γm x) $$ Hrl
  iunfold swift.runSt at Hrun
  icases Hrun with ⟨Hbal, Hcb, Hstat, Hhd, Hhdl, Hhdc, Hpr, Hprs, Hk, Hks, Hhl, Hhls, Hpe,
    Hpes, Hls0, Hlso, Hw, #Hlb, %Hok2⟩
  have hcw0 : w.2.1 = (sint.Z cb).toNat := by rw [Hok2.1.2.2.2.1, Hn.2.2.2.1]; rfl
  ihave #Hd2 := Hd
  iunfold swift.descCtxE at Hd2
  icases Hd2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc0, %γrc, #HR, #HisR,
    %Hids, -, -, -, #Hspi, #Hcfg, #HnI, #Hdmf, #HdmV, #HdI, -, -, #HexL, -, -, -, -, -, #Hng⟩
  try wp_auto
  -- `cmdIds`, `phases`, `cmds`, `deps`: empty; `seen`: empty
  wp_apply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) []
  isplitr
  · ipureintro; rfl
  iintro %s10 ⟨Hs1, Hc1⟩
  try wp_auto
  wp_apply wp_slice_literal (V := w64) (t := go.int) []
  isplitr
  · ipureintro; rfl
  iintro %s20 ⟨Hs2, Hc2⟩
  try wp_auto
  wp_apply wp_slice_literal (V := state.Command) (t := state.Command.ty) []
  isplitr
  · ipureintro; rfl
  iintro %s30 ⟨Hs3, Hc3⟩
  try wp_auto
  wp_apply wp_slice_literal (V := swift.SDep) (t := swift.SDep.ty) []
  isplitr
  · ipureintro; rfl
  iintro %s40 ⟨Hs4, Hc4⟩
  try wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %sm0 Hsm0
  try wp_auto
  -- 1. the execution log, under `execL`
  wp_apply sync.Mutex.wp_Lock $$ [$HexL] as ⟨Hlocked, HL⟩
  iunfold swift.execLInvE at HL
  icases HL with ⟨%sl, %es, %bX, %X0, %stpX, Hlog, Hsl, Hslcap, HXl, HXe, Hown, #HXlb,
    #HXok, HXt, %HXp⟩
  -- the execution log's entries `XS` (N1-R1 `exec`, round 51: on `execL`'s contents)
  iapply fupd_wp
  imod R1.exec (sint.Z cb).toNat X es bX X0 HXp.1 $$ [HFz HXl] with
    ⟨HFz, HXl, %HbX, %XS, %HXS, #HXE, #HWX, #HWXX⟩
  · iframe HdX HFz HXl HXok
  imodintro
  ihave %Hsll := ownSlice_len $$ Hsl
  try wp_auto
  ihave HA0 : swift.fillAcc γ x.N x.r (sint.Z cb).toNat cmdIds_ptr phases_ptr cmds_ptr deps_ptr
      seen_ptr [] 0 $$ [cmdIds phases cmds deps seen Hs1 Hc1 Hs2 Hc2 Hs3 Hc3 Hs4 Hc4 Hsm0]
  · iunfold swift.fillAcc
    iexists _, _, _, _, [], [], _, ∅
    simp only [List.map_nil]
    iframe
    isplitr
    · ipureintro
      refine ⟨rfl, rfl, List.nodup_nil, Nat.le_refl _, fun y => ?_⟩
      simp
    iapply BigSepL.bigSepL_nil.2
    itrivial
  ihave HI1 : (∃ (i : w64) (ev : swift.commandStaticDesc) (E : List sp.RepEntry),
      "i" ∷ i_ptr ↦ i ∗ "e" ∷ e_ptr ↦ ev ∗
      "HA" ∷ swift.fillAcc γ x.N x.r (sint.Z cb).toNat cmdIds_ptr phases_ptr cmds_ptr deps_ptr
        seen_ptr E E.length ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ es.length ∧ (∀ e ∈ E, e ∈ XS) ∧
        ∀ j e, j < sint.nat i → XS[j]? = some e → e.id ∈ E.map (·.id)⌝ : IProp netDistGF)
    $$ [i e HA0]
  · iexists W64 0, _, []
    iframe
    ipureintro
    refine ⟨by decide, by simp, by simp, fun j e hj _ => absurd hj (by simp)⟩
  wp_for HI1
  wp_if_destruct
  · -- the `i`-th entry of the log
    have hlt : sint.Z i < sint.Z sl.len := by simpa using Hif
    have hil : sint.nat i < es.length := by rw [Hsll.1]; word
    obtain ⟨esi, hesi⟩ : ∃ esi, es[sint.nat i]? = some esi := ⟨_, List.getElem?_eq_getElem hil⟩
    ihave #Hei := (BigSepL.bigSepL_lookup hesi) $$ HXE
    icases Hei with ⟨%e, %vs, %He, #Hvs, %D, #HD, %HD⟩
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨Hi.1, hlt⟩)]
    wp_apply (wp_load_slice_index (V := swift.commandStaticDesc) sl (sint.Z i) es _ esi Hi.1)
      $$ [Hsl] as Hsl
    · iframe; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact hesi
    iunfold swift.fillAcc at HA
    icases HA with ⟨%s1, %s2, %s3, %s4, %cmL, %dpL, %sm, %sM, Hci, Hs1, Hc1, Hph, Hs2, Hc2, Hcm,
      Hs3, Hc3, Hdp, Hs4, Hc4, Hsn, Hsm, %HA, HB⟩
    try wp_auto
    wp_apply (wp_map_lookup2 swift.CommandId.ty (go.StructType []) sm sM esi.cmdId' (DFrac.own 1))
      $$ [$Hsm] as Hsm
    try wp_auto
    have htk : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    have hXi : XS[sint.nat i]? = some e := He.1
    have hseenE := HA.2.2.2.2
    rw [List.take_length] at hseenE
    wp_if_destruct
    · -- seen: the entry's id is already reported
      have hin : e.id ∈ E.map (·.id) := by
        rw [← He.2.1]; exact (hseenE _).1 (by simpa using Hif)
      wp_for_post
      iframe
      iexists i + W64 1, esi, E
      iframe
      isplitl [Hci Hs1 Hc1 Hph Hs2 Hc2 Hcm Hs3 Hc3 Hdp Hs4 Hc4 Hsn Hsm HB]
      · iunfold swift.fillAcc
        iexists s1, s2, s3, s4, cmL, dpL, sm, sM
        iframe
        ipureintro; exact HA
      ipureintro
      refine ⟨by word, by rw [htk]; omega, Hi.2.2.1, fun j e' hj hj' => ?_⟩
      rw [htk] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact Hi.2.2.2 j e' hj hj'
      · rw [hXi] at hj'; cases hj'; exact hin
    · -- new: reported with its phase (at least `PRE_ACCEPT`)
      have hnin : e.id ∉ E.map (·.id) := by
        rw [← He.2.1]; intro h; apply Hif; simpa using (hseenE _).2 h
      have hcmd : ofCmdId e.id = esi.cmdId' := by rw [← He.2.1]; rfl
      try wp_auto
      wp_apply (wp_mapInsert swift.CommandId.ty sm sM esi.cmdId' ()) $$ [$Hsm] as Hsm
      try wp_auto
      have hph : e.phase = (if sint.Z esi.phase' < sint.Z (W64 1) then W64 1 else esi.phase') := by
        have h := He.2.2.1
        by_cases h1 : sint.Z esi.phase' < 1
        · rw [if_pos h1] at h
          rw [if_pos (by simpa using h1)]
          apply BitVec.eq_of_toNat_eq; simp; omega
        · rw [if_neg h1] at h
          rw [if_neg (by simpa using h1)]
          apply BitVec.eq_of_toNat_eq; rw [← h]
          have := BitVec.toInt_eq_toNat_cond esi.phase'
          word
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun vv => iprop(phase_ptr ↦ e.phase ∗ ⌜vv = executeVal⌝))) $$ [phase]
      · wp_if_destruct
        · try wp_auto
          rw [hph, if_pos Hif]
          iframe
        · try wp_auto
          rw [hph, ite_eq_right Hif]
          iframe
      iintro %vv ⟨phase, %Hvv⟩
      subst Hvv
      try wp_auto
      wp_apply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [esi.cmdId']
      isplitr
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [Hs1 Hc1 Hl1] as %n1 ⟨Hs1, Hc1, -⟩
      · iframe
      try wp_auto
      wp_apply wp_slice_literal (V := w64) (t := go.int) [e.phase]
      isplitr
      · ipureintro; rfl
      iintro %l2 ⟨Hl2, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [Hs2 Hc2 Hl2] as %n2 ⟨Hs2, Hc2, -⟩
      · iframe
      try wp_auto
      wp_apply wp_slice_literal (V := state.Command) (t := state.Command.ty) [esi.cmd']
      isplitr
      · ipureintro; rfl
      iintro %l3 ⟨Hl3, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [Hs3 Hc3 Hl3] as %n3 ⟨Hs3, Hc3, -⟩
      · iframe
      try wp_auto
      wp_apply wp_slice_literal (V := swift.SDep) (t := swift.SDep.ty) [swift.SDep.mk esi.dep']
      isplitr
      · ipureintro; rfl
      iintro %l4 ⟨Hl4, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [Hs4 Hc4 Hl4] as %n4 ⟨Hs4, Hc4, -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      ihave #Hwe0 := (BigSepL.bigSepL_lookup hXi) $$ HWX
      ihave #Hwe := R1.W_wit _ e $$ Hwe0
      iexists i + W64 1, esi, E ++ [e]
      iframe
      isplitl [Hci Hs1 Hc1 Hph Hs2 Hc2 Hcm Hs3 Hc3 Hdp Hs4 Hc4 Hsn Hsm HB]
      · rw [List.length_append, List.length_singleton]
        iapply (swift.fillAcc_snoc γ x.N x.r (sint.Z cb).toNat cmdIds_ptr phases_ptr cmds_ptr deps_ptr
          seen_ptr E e (E.length + 1) n1 n2 n3 n4 cmL dpL esi.cmd' (swift.SDep.mk esi.dep') sm
          (<[esi.cmdId' := ()]> sM) ⟨HA.1, HA.2.1⟩ ?_ (Nat.le_refl _) ?_)
        · rw [List.map_append, List.nodup_append]
          refine ⟨HA.2.2.1, by simp, ?_⟩
          intro a ha b hb; simp at hb; subst hb; intro h; subst h; exact hnin ha
        · intro y
          rw [show E.length + 1 = (E ++ [e]).length by simp, List.take_length]
          rw [GMap.lookup_insert_eq_iff]
          by_cases hy : esi.cmdId' = y
          · subst hy; simp [He.2.1]
          · rw [if_neg hy, hseenE y]
            simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
              List.mem_singleton]
            constructor
            · exact Or.inl
            · rintro (h | h)
              · exact h
              · exfalso; apply hy; rw [← hcmd, ← h]; rfl
        · rw [hcmd]
          iframe
          isplitl []
          · iunfold swift.repEntryObj
            iexists vs
            isplitr
            · ipureintro; exact He.2.2.2
            iframe Hvs
            have hD : e.dep.map ofCmdId = D := by
              rw [← HD, List.map_map]; exact List.map_id' D |>.trans rfl
            rw [hD]; iexact HD
          · iexact Hwe
      ipureintro
      refine ⟨by word, by rw [htk]; omega, fun e' he' => ?_, fun j e' hj hj' => ?_⟩
      · rcases List.mem_append.mp he' with h | h
        · exact Hi.2.2.1 e' h
        · simp at h; subst h; exact List.mem_of_getElem? hXi
      · rw [htk] at hj
        rw [List.map_append, List.mem_append]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact Or.inl (Hi.2.2.2 j e' hj hj')
        · rw [hXi] at hj'; cases hj'; exact Or.inr (by simp)
  · -- the log done: `XS`'s ids are reported
    have hge : ¬ (sint.Z i < sint.Z sl.len) := by simpa using Hif
    have hiE : sint.nat i = XS.length := by rw [HXS.1, Hsll.1]; word
    have HE1 : (∀ e ∈ E, swift.fillSrc XS [] M0 v.propsM e) ∧ ∀ e ∈ XS, e.id ∈ E.map (·.id) :=
      ⟨fun e he => Or.inl (Hi.2.2.1 e he), fun e he => by
        obtain ⟨j, hj, hje⟩ := List.getElem_of_mem he
        exact Hi.2.2.2 j e (by omega) (by rw [← hje]; exact List.getElem?_eq_getElem hj)⟩
    clear Hi
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$HexL $Hlocked Hlog Hsl Hslcap HXl HXe Hown HXt]
    · iunfold swift.execLInvE
      iexists sl, es, bX, X0, stpX
      iframe; iframe HXlb HXok; ipureintro; exact HXp
    try wp_auto
    -- 2. the last `MSync`'s commands, in `COMMIT`
    haveI : Persistent (swift.syncObj γ x.N v.lastSync w.2.1 M0) := by
      cases M0 <;> (unfold swift.syncObj; infer_instance)
    ihave #Hlso := Hlso
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun vv => iprop(⌜vv = executeVal⌝ ∗ m_ptr ↦ v.lastSync ∗
      ∃ E2 : List sp.RepEntry,
        swift.fillAcc γ x.N x.r (sint.Z cb).toNat cmdIds_ptr phases_ptr cmds_ptr deps_ptr seen_ptr
          E2 E2.length ∗
        ⌜(∀ e ∈ E2, swift.fillSrc XS [] M0 v.propsM e) ∧ (∀ e ∈ XS, e.id ∈ E2.map (·.id)) ∧
          ∀ M, M0 = some M → ∀ q ∈ M, q.1 ∈ E2.map (·.id)⌝))) $$ [HA m]
    · rcases M0 with _ | M
      · iunfold swift.syncObj at Hlso
        icases Hlso with %Hnull
        rw [Hnull]
        try wp_auto
        iframe
        isplitr
        · ipureintro; rfl
        ipureintro
        exact ⟨HE1.1, HE1.2, fun M h => by cases h⟩
      · iunfold swift.syncObj at Hlso
        icases Hlso with ⟨%ph0, %cm0, %dp0, %rep0, %bl0, #Hls0', %Hbl0, #HsI, #HMs, #HlbS⟩
        -- round N7 (`I1: base locLb`): the `MSync`'s sequence and commands, for the base
        -- entries' witness (with the leader's `locLb` `HlbS`, `syncObj`'s)
        iapply fupd_wp
        imod sp.syncIs_seq ⊤ (fun _ _ => CoPset.mem_full) _ M $$ [Hspi HsI] with %HMseq
        · iframe Hspi HsI
        imod sp.syncIs_cmdIs ⊤ (fun _ _ => CoPset.mem_full) _ M $$ [Hspi HsI] with #HMcmds
        · iframe Hspi HsI
        imodintro
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hls0'
        -- the `MSync`'s maps (`syncObj` carries them, round N5)
        iunfold swift.syncMaps at HMs
        icases HMs with ⟨%rep1, %bl1, %ph, %cm, %dp, %phM, %cmM, %dpM, #Hls1, #HphM, #HcmM, #HdpM,
          %HMf, #HMe⟩
        ihave #Hls2 := Hls1
        iStructNamed Hls2
        rw [decide_eq_false Hnn]
        try wp_auto
        wp_func_lits
        wp_bind (App (App (Val (map.forRange _ _)) _) _)
        iapply (wp_map_for_range (K := swift.CommandId) (V := w64) (fun keys i => iprop(∃ (E2 : List sp.RepEntry) (cv : swift.CommandId),
            cmdId_ptr ↦ cv ∗ m_ptr ↦ v.lastSync ∗
            swift.fillAcc γ x.N x.r (sint.Z cb).toNat cmdIds_ptr phases_ptr cmds_ptr deps_ptr seen_ptr
              E2 E2.length ∗
            ⌜(∀ e ∈ E2, swift.fillSrc XS [] (some M) v.propsM e) ∧ (∀ e ∈ XS, e.id ∈ E2.map (·.id)) ∧
              (∀ k ∈ keys.take i.toNat, toCmdId k ∈ E2.map (·.id)) ∧ 0 ≤ i⌝))) $$ HphM
        iintro %keys %Hkeys
        isplitl [cmdId m HA]
        · iexists E, _
          iframe
          ipureintro
          exact ⟨HE1.1, HE1.2, by simp, Int.le_refl _⟩
        isplitl []
        · imodintro
          iintro %i %key %pv %Hiv ⟨%E2, %cv, cmdId, m, HA, %Hi⟩
          have hkM : toCmdId key ∈ M.map Prod.fst := (HMf.2.2 key).1 (by rw [Hiv.2]; rfl)
          obtain ⟨q, hqM, hq1⟩ := List.mem_map.mp hkM
          have htk : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
            rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hiv.1]; rfl
          obtain ⟨jq, hjq⟩ := List.mem_iff_getElem?.mp hqM
          ihave #Hq := (BigSepL.bigSepL_lookup hjq) $$ HMe
          iunfold swift.fillAcc at HA
          icases HA with ⟨%s1, %s2, %s3, %s4, %cmL, %dpL, %sm, %sM, Hci, Hs1, Hc1, Hph, Hs2, Hc2,
            Hcm, Hs3, Hc3, Hdp, Hs4, Hc4, Hsn, Hsm, %HA, HB⟩
          have hseenE := HA.2.2.2.2
          rw [List.take_length] at hseenE
          try wp_auto
          wp_apply (wp_map_lookup2 swift.CommandId.ty (go.StructType []) sm sM key (DFrac.own 1))
            $$ [$Hsm] as Hsm
          try wp_auto
          wp_if_destruct
          · -- seen
            have hin : toCmdId key ∈ E2.map (·.id) := (hseenE _).1 (by simpa using Hif)
            try wp_auto
            unfold forMapPostcondition
            ileft
            isplitr
            · ipureintro; rfl
            iexists E2, key
            iframe
            isplitl [Hci Hs1 Hc1 Hph Hs2 Hc2 Hcm Hs3 Hc3 Hdp Hs4 Hc4 Hsn Hsm HB]
            · iunfold swift.fillAcc
              iexists s1, s2, s3, s4, cmL, dpL, sm, sM
              iframe
              ipureintro; exact HA
            ipureintro
            refine ⟨Hi.1, Hi.2.1, fun k hk => ?_, by omega⟩
            rw [htk] at hk
            rcases List.mem_append.mp hk with hk | hk
            · exact Hi.2.2.1 k hk
            · simp at hk; subst hk; exact hin
          · -- new: in `COMMIT`, with the `MSync`'s command and dependencies
            have hnin : q.1 ∉ E2.map (·.id) := by
              rw [hq1]; intro h; apply Hif; simpa using (hseenE _).2 h
            try wp_auto
            wp_apply (wp_mapInsert swift.CommandId.ty sm sM key ()) $$ [$Hsm] as Hsm
            try wp_auto
            icases Hq with ⟨%vs, %dsl, %Hqv, #Hvs, #Hdsl⟩
            have hkq : ofCmdId q.1 = key := by rw [hq1]; rfl
            rw [hkq] at Hqv
            wp_apply (wp_map_lookup1 swift.CommandId.ty swift.Dep.ty dp dpM key DFrac.discard)
              $$ [$HdpM] as -
            rw [Hqv.2]
            simp only [Option.getD_some]
            try wp_auto
            wp_bind (If _ _ _)
            iapply (wp_wand (Φ := fun vv => iprop(⌜vv = executeVal⌝ ∗ ∃ d' : GoSlice,
                dep_ptr ↦ d' ∗ d' ↦*□ (q.2.2.map ofCmdId)))) $$ [dep]
            · wp_if_destruct
              · -- `nil`: no dependencies
                ihave %Hdl := ownSlice_len $$ Hdsl
                have hnil : q.2.2.map ofCmdId = [] := by
                  apply List.eq_nil_of_length_eq_zero; rw [Hdl.1]; rfl
                wp_apply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty)
                  (st := swift.Dep.ty) []
                isplitr
                · ipureintro; rfl
                iintro %l0 ⟨Hl0, -⟩
                ipersist Hl0
                try wp_auto
                isplitr
                · ipureintro; first | rfl | trivial
                iexists _
                iframe
                rw [hnil]
                iexact Hl0
              · try wp_auto
                isplitr
                · ipureintro; first | rfl | trivial
                iexists dsl
                iframe
                iexact Hdsl
            iintro %vv ⟨%Hvv, %d', dep, #Hd'⟩
            subst Hvv
            try wp_auto
            wp_apply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [key]
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hs1 Hc1 Hl1] as %n1 ⟨Hs1, Hc1, -⟩
            · iframe
            try wp_auto
            wp_apply wp_slice_literal (V := w64) (t := go.int) [swift.phCOMMIT]
            isplitr
            · ipureintro; rfl
            iintro %l2 ⟨Hl2, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hs2 Hc2 Hl2] as %n2 ⟨Hs2, Hc2, -⟩
            · iframe
            try wp_auto
            wp_apply (wp_map_lookup1 swift.CommandId.ty state.Command.ty cm cmM key DFrac.discard)
              $$ [$HcmM] as -
            rw [Hqv.1]
            simp only [Option.getD_some]
            try wp_auto
            wp_apply wp_slice_literal (V := state.Command) (t := state.Command.ty)
              [state.Command.mk q.2.1.op q.2.1.key vs]
            isplitr
            · ipureintro; rfl
            iintro %l3 ⟨Hl3, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hs3 Hc3 Hl3] as %n3 ⟨Hs3, Hc3, -⟩
            · iframe
            try wp_auto
            wp_apply wp_slice_literal (V := swift.SDep) (t := swift.SDep.ty) [swift.SDep.mk d']
            isplitr
            · ipureintro; rfl
            iintro %l4 ⟨Hl4, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hs4 Hc4 Hl4] as %n4 ⟨Hs4, Hc4, -⟩
            · iframe
            try wp_auto
            -- the entry, of the base: its witness
            ihave #Hwe : swift.repEntW γ x.N x.r (sint.Z cb).toNat
                ⟨q.1, swift.phCOMMIT, q.2.1, q.2.2⟩ $$ []
            · -- round N7 (`I1: base locLb`): in `COMMIT`, the leader's `locLb` of the `MSync`'s
              -- sequence (`syncObj`'s), which has `q` with its dependencies (`syncIs_seq`)
              iunfold swift.repEntW
              ihave #Hcq := (BigSepL.bigSepL_lookup hjq) $$ HMcmds
              isplitr
              · iexact Hcq
              iright; iright
              isplitr
              · ipureintro; left; show (3 : Nat) ≥ 2; omega
              iexists sp.syncSeq M
              rw [← hcw0]
              isplitr
              · iexact HlbS
              ipureintro
              obtain ⟨hmem, hperm⟩ := HMseq.2 q.1 q.2.1 q.2.2 hqM
              exact ⟨List.mem_map_of_mem (f := Prod.fst) hmem, hperm⟩
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists E2 ++ [⟨q.1, swift.phCOMMIT, q.2.1, q.2.2⟩], key
            iframe
            isplitl [Hci Hs1 Hc1 Hph Hs2 Hc2 Hcm Hs3 Hc3 Hdp Hs4 Hc4 Hsn Hsm HB]
            · rw [List.length_append, List.length_singleton]
              iapply (swift.fillAcc_snoc γ x.N x.r (sint.Z cb).toNat cmdIds_ptr phases_ptr cmds_ptr
                deps_ptr seen_ptr E2 ⟨q.1, swift.phCOMMIT, q.2.1, q.2.2⟩ (E2.length + 1) n1 n2 n3 n4 cmL
                dpL (state.Command.mk q.2.1.op q.2.1.key vs) (swift.SDep.mk d') sm
                (<[key := ()]> sM) ⟨HA.1, HA.2.1⟩ ?_ (Nat.le_refl _) ?_)
              · rw [List.map_append, List.nodup_append]
                refine ⟨HA.2.2.1, by simp, ?_⟩
                intro a ha b hb; simp at hb; subst hb; intro h; subst h; exact hnin ha
              · intro y
                rw [show E2.length + 1 = (E2 ++ [_]).length by simp, List.take_length]
                rw [GMap.lookup_insert_eq_iff]
                by_cases hy : key = y
                · subst hy; simp [hq1]
                · rw [ite_eq_right hy, hseenE y]
                  simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
                    List.mem_singleton]
                  constructor
                  · exact Or.inl
                  · rintro (h | h)
                    · exact h
                    · exfalso; apply hy; rw [← hkq, ← h]; rfl
              · simp only [hkq]
                iframe
                isplitl []
                · iunfold swift.repEntryObj
                  iexists vs
                  isplitr
                  · ipureintro; rfl
                  iframe Hvs Hd'
                · iexact Hwe
            ipureintro
            refine ⟨fun e' he' => ?_, fun e' he' => ?_, fun k hk => ?_, by omega⟩
            · rcases List.mem_append.mp he' with h | h
              · exact Hi.1 e' h
              · simp at h; subst h
                exact Or.inr (Or.inr ⟨M, rfl, rfl, hqM⟩)
            · rw [List.map_append]; exact List.mem_append_left _ (Hi.2.1 e' he')
            · rw [htk] at hk
              rw [List.map_append, List.mem_append]
              rcases List.mem_append.mp hk with hk | hk
              · exact Or.inl (Hi.2.2.1 k hk)
              · simp at hk; subst hk; exact Or.inr (by simp [hq1])
        · iintro ⟨%E2, %cv, cmdId, m, HA, %Hi⟩ -
          try wp_auto
          iframe
          isplitr
          · ipureintro; rfl
          ipureintro
          refine ⟨Hi.1, Hi.2.1, fun M' hM' q hq => ?_⟩
          cases hM'
          have hk : ofCmdId q.1 ∈ keys := by
            apply (Hkeys.1 _).2
            apply (HMf.2.2 _).2
            simpa using List.mem_map_of_mem (f := Prod.fst) hq
          have := Hi.2.2.1 _ (by rw [List.take_of_length_le (by rw [Hkeys.2.1]; omega)]; exact hk)
          simpa using this
    iintro %vv ⟨%Hvv, m, %E2, HA, %HE2⟩
    subst Hvv
    clear HE1
    try wp_auto
    -- 3. the stopped descriptors' entries (`IterCb`; round 51: `R1.desc` per entry, the reads'
    -- fields held until after the report, the reported reads' entries `S`, D76 (1))
    -- round 58 (D82 (1)): the homes at the stopped ballot
    ihave Hds : swift.descsStopped x.γd (swift.descDF (x.DR γ (sint.Z cb).toNat)) (swift.stopPS x bc.2)
        rp $$ [Hds]
    · rw [← Hbc]; iexact Hds
    iunfold swift.descsStopped at Hds
    icases Hds with ⟨%dm1, %γdc, %Mc, Hcd, #Hdm1, Hrd1, Hview, #Hpool, HPS, Hents⟩
    -- round 58 (D82 (1)): the stopped view is injective (each entry's `descFree` owns `msgs`)
    ihave ⟨Hents, %HMinj⟩ := swift.keep_pureF (swift.descsMap_injAll _ Mc) $$ Hents
    -- round 56 (D79 (1), 52-3): the stopped epoch's commit record and registration; round 57
    -- (D80 (4)): `R1.desc` takes the first part, so it travels in `IterCb`'s invariant
    iunfold swift.stopPS at HPS
    icases HPS with ⟨HPSi, HPSf, HPSk⟩
    ihave HPSi : ▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = (sint.Z cb).toNat⌝ ∗
        swift.cgG x g $$ [HPSi]
    · rw [← Hbc]; iexact HPSi
    -- round B1 (D82 (4)): the stopped epoch's free permit, for N1-R2
    ihave HPSf : swift.freeP x.γcg (sint.Z cb).toNat $$ [HPSf]
    · rw [← Hbc]; iexact HPSf
    have hXiXS : X.map (fun e => toCmdId e.1) = XS.map (·.id) := HXS.2.symm
    wp_method_call
    try wp_auto
    wp_func_lits
    wp_apply (github_com.orcaman.concurrent_map.ConcurrentMap.wp_IterCbOwnN wp_IterCbVN dm1 γdc
        (swift.descR x.γd) _ Mc (fun vis => iprop(R1.Fz (sint.Z cb).toNat X ∗
          (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = (sint.Z cb).toNat⌝ ∗ swift.cgG x g) ∗
          ([∗map] k ↦ vv ∈ Mc, ⌜k ∈ vis.map Prod.fst⌝ ∨ ∃ d : Loc,
            ⌜vv = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗
            swift.descFree (swift.descDF (x.DR γ (sint.Z cb).toNat)) d) ∗
          ∃ (E3 : List sp.RepEntry) (SR : List swift.DescRead) (S : List sp.RepEntry),
          swift.fillAcc γ x.N x.r (sint.Z cb).toNat cmdIds_ptr phases_ptr cmds_ptr deps_ptr
            seen_ptr E3 E3.length ∗
          ([∗list] r ∈ SR, swift.rdHeld γ x (sint.Z cb).toNat (R1.Wd (sint.Z cb).toNat) r) ∗
          ([∗list] e ∈ S, R1.W (sint.Z cb).toNat e) ∗
          ⌜SR.map (fun r => (r.k,
              interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.d)) = vis ∧
            (∀ e ∈ S, ∃ r ∈ SR, r.entry = some e) ∧
            (∀ r ∈ SR, ∀ e, r.entry = some e → e.id ∈ E3.map (·.id)) ∧
            (∀ e ∈ S, e ∈ E3) ∧ (∀ e ∈ S, e.phase.toNat = 0 → e.dep.length < 2 ^ 62) ∧
            (∀ e ∈ E3, swift.fillSrc XS S M0 v.propsM e) ∧ (∀ e ∈ XS, e.id ∈ E3.map (·.id)) ∧
            (∀ M, M0 = some M → ∀ q ∈ M, q.1 ∈ E3.map (·.id)) ∧
            -- round N7 (`N5: R2-a`): an `MSync` command's entry is the log's or the `MSync`'s
            ∀ M, M0 = some M → ∀ q ∈ M, ∃ e ∈ E3, e.id = q.1 ∧
              (e ∈ XS ∨ (e.phase = swift.phCOMMIT ∧ (e.id, e.cmd, e.dep) ∈ M))⌝)))
      $$ [Hrd1 Hview Hents HA HFz HPSi] as
        ⟨Hrd1, Hview, %vis, ⟨HFz, HPSi, -, %E3, %SR, %S, HA, Hheld, #HWS, %HE3⟩, %Hvis⟩
    · iframe Hrd1 Hview HFz HPSi
      isplitl [Hents HA]
      · isplitl [Hents]
        · ihave H := swift.visMap_init Mc (fun _ vv => iprop(∃ d : Loc,
            ⌜vv = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗
            swift.descFree (swift.descDF (x.DR γ (sint.Z cb).toNat)) d)) $$ Hents
          iexact H
        iexists E2, [], []
        iframe
        isplitl []
        · iapply BigSepL.bigSepL_nil.2; itrivial
        isplitl []
        · iapply BigSepL.bigSepL_nil.2; itrivial
        ipureintro
        refine ⟨rfl, by simp, by simp, by simp, by simp, fun e he => ?_, HE2.2.1, HE2.2.2, ?_⟩
        · exact swift.fillSrc_mono XS [] [] M0 v.propsM e (by simp) (HE2.1 e he)
        · intro M hM q hq
          obtain ⟨e, he, hid⟩ := List.mem_map.mp (HE2.2.2 M hM q hq)
          refine ⟨e, he, hid, ?_⟩
          rcases HE2.1 e he with h | h | ⟨M', hM', hph, hmem⟩
          · exact Or.inl h
          · cases h
          · obtain rfl : M' = M := Option.some.inj (hM'.symm.trans hM)
            exact Or.inr ⟨hph, hmem⟩
      imodintro
      iintro %vis %k %vv %Φ' %Hkf - ⟨HFz, HPSi, Hents, %E3, %SR, %S, HA, Hheld, #HWS, %HE3⟩ HΦ'
      obtain ⟨hk, hkv⟩ := Hkf
      icases (BigSepM.bigSepM_delete hk).1 $$ Hents with ⟨Hk1, Hents⟩
      icases Hk1 with (%Hkin | ⟨%d, %Hvd, Hd⟩)
      · exact absurd Hkin hkv
      subst Hvd
      -- the read (N1-R1 `desc`, one entry of the stopped view)
      iapply fupd_wp
      imod R1.desc (sint.Z cb).toNat X k d Mc hk (fun k' hk' => HMinj k k' d hk hk')
          (by rw [Hstr]; exact swift.cmdStr_inj) $$ [HFz HPSi Hd] with
        ⟨HFz, HPSi, %r, %Hrkd, Hf, Hcl, Hback, Hok⟩
      · iframe HdX HFz HPSi Hd
      -- round 59 (D84 (2)): the read's claim, held with the wand (`swift.rdHeld`)
      icombine Hcl Hback as Hback
      imodintro
      rcases r with ⟨rk, rd, q, pg, ph, op, key, vs, dsl, pdsl, D, PD, y, c'⟩
      obtain ⟨hrk, hrd⟩ := Hrkd
      dsimp only at hrk hrd
      subst hrk hrd
      iunfold swift.descReadOk at Hok
      icases Hok with ⟨Hpr, Hpdk⟩
      ihave #Hrpd : swift.rdPd x.str (R1.Wd (sint.Z cb).toNat)
          ⟨rk, rd, q, pg, ph, op, key, vs, dsl, pdsl, D, PD, y, c'⟩ $$ [Hpdk]
      · iunfold swift.rdPd
        icases Hpdk with (%Hnil | Hwd)
        · ileft; ipureintro; exact Hnil
        · by_cases hz : ∃ z : sp.CmdId, x.str (ofCmdId z) = rk
          · obtain ⟨z, hz⟩ := hz
            iright; iright
            iexists z
            isplitr
            · ipureintro; exact hz
            ispecialize Hwd $$ %z
            iapply Hwd
            ipureintro; exact hz
          · iright; ileft; ipureintro; intro z hz'; exact hz ⟨z, hz'⟩
      iunfold swift.DescRead.fields at Hf
      iunfold swift.descRepFields at Hf
      icases Hf with ⟨Fp, Fph, Fcmd, Fdep, Fdl, Fpd, Fpdl⟩
      try wp_auto
      icases Hpr with (%Hpn | ⟨%pp, %w0, %mu, %addr, %vs', %ts, #Hgp, #Hpp, %Hy, #Hvs, #Hwy⟩)
      · -- no proposal: nothing reported
        have Hpn' : pg = null := Hpn
        subst Hpn'
        try wp_auto
        iapply HΦ'
        iframe HFz HPSi
        isplitl [Hents]
        · iapply (BigSepM.bigSepM_delete hk).2
          isplitr
          · ileft; ipureintro; simp
          iapply (swift.visMap_mono _ vis (vis ++ [(rk, _)]) _ (fun k' h' => by simp [h'])) $$ Hents
        iexists E3, SR ++ [⟨rk, rd, q, null, ph, op, key, vs, dsl, pdsl, D, PD, y, c'⟩], S
        iframe HA HWS
        isplitl [Hheld Hback Fp Fph Fcmd Fdep Fdl Fpd Fpdl]
        · iapply BigSepL.bigSepL_snoc.2
          iframe Hheld
          iunfold swift.rdHeld
          isplitr
          · ipureintro; intro h; exact absurd rfl h
          iframe Hback Hrpd
          iunfold swift.DescRead.fields
          iunfold swift.descRepFields
          iframe
        ipureintro
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := HE3
        refine ⟨by rw [List.map_append, h1]; rfl, fun e he => ?_, fun r hr e he => ?_, h4, h5, h6,
          h7, h8, h9⟩
        · obtain ⟨r, hr, hre⟩ := h2 e he
          exact ⟨r, List.mem_append_left _ hr, hre⟩
        · rcases List.mem_append.mp hr with hr | hr
          · exact h3 r hr e he
          · simp at hr; subst hr
            simp [swift.DescRead.entry] at he
      · -- a proposal: reported if not seen
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgp
        rw [decide_eq_false Hnn]
        ihave #Hgp2 := Hgp
        iStructNamed Hgp2
        ihave #Hpp2 := Hpp
        iStructNamed Hpp2
        try wp_auto
        iunfold swift.fillAcc at HA
        icases HA with ⟨%s1, %s2, %s3, %s4, %cmL, %dpL, %sm, %sM, Hci, Hs1, Hc1, Hph, Hs2, Hc2,
          Hcm, Hs3, Hc3, Hdp, Hs4, Hc4, Hsn, Hsm, %HA, HB⟩
        have hseenE := HA.2.2.2.2
        rw [List.take_length] at hseenE
        try wp_auto
        wp_apply (wp_map_lookup2 swift.CommandId.ty (go.StructType []) sm sM (swift.CommandId.mk y.cl y.seq)
          (DFrac.own 1)) $$ [$Hsm] as Hsm
        try wp_auto
        have hent : swift.DescRead.entry ⟨rk, rd, q, pg, ph, op, key, vs, dsl, pdsl, D, PD, y, c'⟩ =
            some ⟨y, ph, c', D.map toCmdId⟩ := by
          unfold swift.DescRead.entry; rw [if_neg Hnn]
        wp_if_destruct
        · -- seen: nothing reported
          have hin : y ∈ E3.map (·.id) := by
            have := (hseenE ⟨y.cl, y.seq⟩).1 (by simpa using Hif); exact this
          try wp_auto
          iapply HΦ'
          iframe HFz HPSi
          isplitl [Hents]
          · iapply (BigSepM.bigSepM_delete hk).2
            isplitr
            · ileft; ipureintro; simp
            iapply (swift.visMap_mono _ vis (vis ++ [(rk, _)]) _ (fun k' h' => by simp [h'])) $$ Hents
          iexists E3, SR ++ [⟨rk, rd, q, pg, ph, op, key, vs, dsl, pdsl, D, PD, y, c'⟩], S
          iframe HWS
          isplitl [Hci Hs1 Hc1 Hph Hs2 Hc2 Hcm Hs3 Hc3 Hdp Hs4 Hc4 Hsn Hsm HB]
          · iunfold swift.fillAcc
            iexists s1, s2, s3, s4, cmL, dpL, sm, sM
            iframe
            ipureintro; exact HA
          isplitl [Hheld Hback Fp Fph Fcmd Fdep Fdl Fpd Fpdl]
          · iapply BigSepL.bigSepL_snoc.2
            iframe Hheld
            iunfold swift.rdHeld
            isplitr
            · ipureintro; exact fun _ => Hy.2.2.1
            iframe Hback Hrpd
            iunfold swift.DescRead.fields
            iunfold swift.descRepFields
            iframe
          ipureintro
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := HE3
          refine ⟨by rw [List.map_append, h1]; rfl, fun e he => ?_, fun r hr e he => ?_, h4, h5, h6,
            h7, h8, h9⟩
          · obtain ⟨r, hr, hre⟩ := h2 e he
            exact ⟨r, List.mem_append_left _ hr, hre⟩
          · rcases List.mem_append.mp hr with hr | hr
            · exact h3 r hr e he
            · simp at hr; subst hr
              rw [hent] at he; cases he; exact hin
        · -- new: reported with the descriptor's phase, command and dependencies
          have hnin : y ∉ E3.map (·.id) := fun h => by
            have := (hseenE ⟨y.cl, y.seq⟩).2 h; simp_all
          -- its facts `W` (round 54, 53-3: not a command of the frozen record, whose ids are
          -- the log's, all `seen`)
          ihave #HWe : R1.W (sint.Z cb).toNat ⟨y, ph, c', D.map toCmdId⟩ $$ []
          · icases Hwy with (%HyX | #HW)
            · exfalso
              rw [hXiXS] at HyX
              obtain ⟨e', he', hid⟩ := List.mem_map.mp HyX
              exact hnin (by rw [← hid]; exact HE3.2.2.2.2.2.2.1 e' he')
            · iexact HW
          ihave #Hwe := R1.W_wit _ _ $$ HWe
          wp_apply (wp_mapInsert swift.CommandId.ty sm sM (swift.CommandId.mk y.cl y.seq) ())
            $$ [$Hsm] as Hsm
          try wp_auto
          wp_apply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty)
            [swift.CommandId.mk y.cl y.seq]
          isplitr
          · ipureintro; rfl
          iintro %l1 ⟨Hl1, -⟩
          try wp_auto
          wp_apply wp_slice_append $$ [Hs1 Hc1 Hl1] as %n1 ⟨Hs1, Hc1, -⟩
          · iframe
          try wp_auto
          wp_apply wp_slice_literal (V := w64) (t := go.int) [ph]
          isplitr
          · ipureintro; rfl
          iintro %l2 ⟨Hl2, -⟩
          try wp_auto
          wp_apply wp_slice_append $$ [Hs2 Hc2 Hl2] as %n2 ⟨Hs2, Hc2, -⟩
          · iframe
          try wp_auto
          wp_apply wp_slice_literal (V := state.Command) (t := state.Command.ty)
            [state.Command.mk op key vs]
          isplitr
          · ipureintro; rfl
          iintro %l3 ⟨Hl3, -⟩
          try wp_auto
          wp_apply wp_slice_append $$ [Hs3 Hc3 Hl3] as %n3 ⟨Hs3, Hc3, -⟩
          · iframe
          try wp_auto
          wp_apply wp_slice_literal (V := swift.SDep) (t := swift.SDep.ty) [swift.SDep.mk dsl]
          isplitr
          · ipureintro; rfl
          iintro %l4 ⟨Hl4, -⟩
          try wp_auto
          wp_apply wp_slice_append $$ [Hs4 Hc4 Hl4] as %n4 ⟨Hs4, Hc4, -⟩
          · iframe
          try wp_auto
          ihave #Fdl2 := Fdl
          iapply HΦ'
          iframe HFz HPSi
          isplitl [Hents]
          · iapply (BigSepM.bigSepM_delete hk).2
            isplitr
            · ileft; ipureintro; simp
            iapply (swift.visMap_mono _ vis (vis ++ [(rk, _)]) _ (fun k' h' => by simp [h'])) $$ Hents
          iexists E3 ++ [⟨y, ph, c', D.map toCmdId⟩],
            SR ++ [⟨rk, rd, q, pg, ph, op, key, vs, dsl, pdsl, D, PD, y, c'⟩],
            S ++ [⟨y, ph, c', D.map toCmdId⟩]
          isplitl [Hci Hs1 Hc1 Hph Hs2 Hc2 Hcm Hs3 Hc3 Hdp Hs4 Hc4 Hsn Hsm HB]
          · rw [List.length_append, List.length_singleton]
            iapply (swift.fillAcc_snoc γ x.N x.r (sint.Z cb).toNat cmdIds_ptr phases_ptr cmds_ptr
              deps_ptr seen_ptr E3 ⟨y, ph, c', D.map toCmdId⟩ (E3.length + 1) n1 n2 n3 n4 cmL dpL
              (state.Command.mk op key vs) (swift.SDep.mk dsl) sm
              (<[swift.CommandId.mk y.cl y.seq := ()]> sM) ⟨HA.1, HA.2.1⟩ ?_ (Nat.le_refl _) ?_)
            · rw [List.map_append, List.nodup_append]
              refine ⟨HA.2.2.1, by simp, ?_⟩
              intro a ha b hb; simp at hb; subst hb; intro h; subst h; exact hnin ha
            · intro z
              rw [show E3.length + 1 = (E3 ++ [_]).length by simp, List.take_length]
              rw [GMap.lookup_insert_eq_iff]
              by_cases hz : swift.CommandId.mk y.cl y.seq = z
              · subst hz; simp; exact Or.inr rfl
              · rw [ite_eq_right hz, hseenE z]
                simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
                  List.mem_singleton]
                constructor
                · exact Or.inl
                · rintro (h | h)
                  · exact h
                  · exfalso; apply hz; rw [← h]; rfl
            · iframe
              isplitl []
              · iunfold swift.repEntryObj
                iexists vs
                isplitr
                · ipureintro
                  have h1 : op = c'.op := Hy.1
                  have h2 : key = c'.key := Hy.2.1
                  rw [h1, h2]
                iframe Hvs
                have hD : (D.map toCmdId).map ofCmdId = D := by
                  rw [List.map_map]; exact List.map_id' D |>.trans rfl
                rw [hD]; iexact Fdl2
              · iexact Hwe
          isplitl [Hheld Hback Fp Fph Fcmd Fdep Fpd Fpdl]
          · iapply BigSepL.bigSepL_snoc.2
            iframe Hheld
            iunfold swift.rdHeld
            isplitr
            · ipureintro; exact fun _ => Hy.2.2.1
            iframe Hback Hrpd
            iunfold swift.DescRead.fields
            iunfold swift.descRepFields
            iframe
            iexact Fdl2
          isplitl []
          · iapply BigSepL.bigSepL_snoc.2
            iframe HWS HWe
          ipureintro
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := HE3
          refine ⟨by rw [List.map_append, h1]; rfl, fun e he => ?_, fun r hr e he => ?_,
            fun e he => ?_, fun e he => ?_, fun e he => ?_, fun e he => ?_, fun M hM q hq => ?_,
            fun M hM q hq => ?_⟩
          · rcases List.mem_append.mp he with he | he
            · obtain ⟨r, hr, hre⟩ := h2 e he
              exact ⟨r, List.mem_append_left _ hr, hre⟩
            · simp at he; subst he
              exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hent⟩
          · rw [List.map_append]
            rcases List.mem_append.mp hr with hr | hr
            · exact List.mem_append_left _ (h3 r hr e he)
            · simp at hr; subst hr
              rw [hent] at he; cases he; exact List.mem_append_right _ (by simp)
          · rcases List.mem_append.mp he with he | he
            · exact List.mem_append_left _ (h4 e he)
            · exact List.mem_append_right _ he
          · rcases List.mem_append.mp he with he | he
            · exact h5 e he
            · simp at he; subst he
              intro h0
              have hph : ph = W64 0 := by
                apply BitVec.eq_of_toNat_eq; simpa using h0
              simpa using Hy.2.2.2 hph
          · rcases List.mem_append.mp he with he | he
            · exact swift.fillSrc_mono XS S _ M0 v.propsM e
                (fun e' he' => List.mem_append_left _ he') (h6 e he)
            · simp at he; subst he
              exact Or.inr (Or.inl (List.mem_append_right _ (List.mem_singleton_self _)))
          · rw [List.map_append]; exact List.mem_append_left _ (h7 e he)
          · rw [List.map_append]; exact List.mem_append_left _ (h8 M hM q hq)
          · obtain ⟨e, he, h⟩ := h9 M hM q hq
            exact ⟨e, List.mem_append_left _ he, h⟩
    obtain ⟨hSRvis, hSS, hSRrep, hSE3, hSdep, hE3src, hE3XS, hE3M, hE3B⟩ := HE3
    have HE3 : (∀ e ∈ E3, swift.fillSrc XS S M0 v.propsM e) ∧ (∀ e ∈ XS, e.id ∈ E3.map (·.id)) ∧
        ∀ M, M0 = some M → ∀ q ∈ M, q.1 ∈ E3.map (·.id) := ⟨hE3src, hE3XS, hE3M⟩
    -- every key of the stopped view read (`IterCb`'s `vis`)
    have hSRp : (SR.map (fun r => (r.k,
        interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.d))).Perm Mc.toList := by
      rw [hSRvis]; exact Hvis
    have hMcSR : ∀ k vv, Mc !! k = some vv → ∃ r ∈ SR, r.k = k ∧
        vv = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.d := by
      intro k vv hk
      have hm : (k, vv) ∈ SR.map (fun r => (r.k,
          interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.d)) :=
        hSRp.symm.subset ((GMap.mem_toList _ _ _).mpr hk)
      obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at he
      exact ⟨r, hr, he.1, he.2.symm⟩
    -- `delivered`'s commands: the frozen record's (N1-R1 `deliv`)
    obtain ⟨dl, hdl⟩ : ∃ dl : List sp.CmdId, dl = X.map (fun e => toCmdId e.1) := ⟨_, rfl⟩
    have hinj : Function.Injective x.str := by rw [Hstr]; exact swift.cmdStr_inj
    try wp_auto
    -- 4. the pending proposals not handled by a descriptor, in `START`
    iunfold swift.propsOwn at Hprs
    icases Hprs with ⟨Hpm, #Hpms⟩
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply (wp_map_for_range (K := swift.CommandId) (V := Loc) (fun keys i => iprop(
        ∃ (E4 : List sp.RepEntry) (cv : swift.CommandId) (pv : Loc)
          (Pd : List (sp.CmdId × List sp.CmdId)),
        cmdId_ptr ↦ cv ∗ propose_ptr ↦ pv ∗ r_ptr ↦ rp ∗ swift.runReader rp x.γdl ∗
        swift.fld rp go!"cmdDescs" ↦ dm1 ∗
        github_com.orcaman.concurrent_map.readerV dm1 γdc (swift.descR x.γd) ∗
        github_com.orcaman.concurrent_map.cmapView γdc Mc ∗
        ([∗list] r ∈ SR, swift.rdHeld γ x (sint.Z cb).toNat (R1.Wd (sint.Z cb).toNat) r) ∗
        R1.Fz (sint.Z cb).toNat X ∗ ([∗list] p ∈ Pd, R1.Wd (sint.Z cb).toNat p.1 p.2) ∗
        swift.propDepsOwn rp (bs ++ hd) ∗
        swift.fillAcc γ x.N x.r (sint.Z cb).toNat cmdIds_ptr phases_ptr cmds_ptr deps_ptr seen_ptr
          E4 E3.length ∗
        ⌜∀ p ∈ Pd, ∃ r ∈ SR, x.str (ofCmdId p.1) = r.k ∧ r.pdsl ≠ slice.nil ∧
          p.2 = r.PD.map toCmdId⌝ ∗
        ⌜E3 <+: E4 ∧ (∀ e ∈ E4.drop E3.length, swift.startOk v.propsM (bs ++ hd) e) ∧
          (∀ e ∈ XS, e.id ∈ E4.map (·.id)) ∧
          (∀ M, M0 = some M → ∀ q ∈ M, q.1 ∈ E4.map (·.id)) ∧
          (∀ k ∈ keys.take i.toNat, toCmdId k ∈ E4.map (·.id) ∨ toCmdId k ∈ dl) ∧
          (∀ e ∈ E4.drop E3.length, ofCmdId e.id ∈ keys.take i.toNat) ∧ 0 ≤ i⌝))) $$ Hpm
    iintro %keys %Hkeys
    isplitl [cmdId propose r Hdr Hcd Hrd1 Hview Hheld HFz Hpd HA]
    · iexists E3, _, _, []
      iframe
      isplitl []
      · iapply BigSepL.bigSepL_nil.2; itrivial
      isplitr
      · ipureintro; simp
      ipureintro
      refine ⟨List.prefix_refl _, by simp, HE3.2.1, HE3.2.2, by simp, by simp, Int.le_refl _⟩
    isplitl []
    · imodintro
      iintro %i %key %gp %Hiv ⟨%E4, %cv, %pv, %Pd, cmdId, propose, r, Hdr, Hcd, Hrd1, Hview, Hheld,
        HFz, HPdW, Hpd, HA, %HPd, %Hi⟩
      have htk : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hiv.1]; rfl
      have hknd : key ∉ keys.take i.toNat := by
        intro h
        have hnd := Hkeys.2.2
        rw [← List.take_append_drop (i.toNat) keys] at hnd
        have hd : key ∈ keys.drop i.toNat := by
          rw [List.mem_iff_getElem?]; exact ⟨0, by rw [List.getElem?_drop]; simpa using Hiv.1⟩
        exact (List.nodup_append.mp hnd).2.2 key h key hd rfl
      iunfold swift.fillAcc at HA
      icases HA with ⟨%s1, %s2, %s3, %s4, %cmL, %dpL, %sm, %sM, Hci, Hs1, Hc1, Hph, Hs2, Hc2,
        Hcm, Hs3, Hc3, Hdp, Hs4, Hc4, Hsn, Hsm, %HA, HB⟩
      have hseenE := HA.2.2.2.2
      try wp_auto
      wp_apply (wp_map_lookup2 swift.CommandId.ty (go.StructType []) sm sM key (DFrac.own 1))
        $$ [$Hsm] as Hsm
      try wp_auto
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun bv => iprop(cmdId_ptr ↦ key ∗ swift.runReader rp x.γdl ∗
          r_ptr ↦ rp ∗ R1.Fz (sint.Z cb).toNat X ∗ ⌜(bv = continueVal ∧
              (toCmdId key ∈ (E4.take E3.length).map (·.id) ∨ toCmdId key ∈ dl)) ∨
            (bv = executeVal ∧ (sM !! key).isSome = false)⌝)))
        $$ [cmdId Hdr r HFz]
      · wp_if_destruct
        · try wp_auto
          iframe
          ipureintro
          exact Or.inl ⟨by first | rfl | trivial, Or.inl ((hseenE key).1 (by simpa using Hif))⟩
        · wp_apply (wp_Str cmdId_ptr _ key) $$ [$cmdId] as cmdId
          iunfold swift.runReader at Hdr
          icases Hdr with ⟨%dm', #Hdm', Hrd⟩
          ihave %Hdmeq := typedPointsto_agree_wand _ _ _ _ _ $$ Hdmf Hdm'
          subst Hdmeq
          try wp_auto
          wp_method_call
          try wp_auto
          wp_apply (wp_HasV dm x.γdl (swift.cmdStr key)
              ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
              (fun ok => iprop(R1.Fz (sint.Z cb).toNat X ∗ ⌜ok = true → toCmdId key ∈ dl⌝)))
              $$ [$Hrd HFz] as %ok ⟨Hrd, HFz, %Hok⟩
          · imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
              swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
            iunfold swift.delivInv at Hi
            icases Hi with ⟨%Md, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
            ihave Hi : swift.delivInv γ x.N x.r x.γdl x.γx x.γxp x.γxm γa x.γxe γrm x.str
                $$ [HV HXi HXeD HMx HXx]
            · iunfold swift.delivInv; iexists Md, bX', X', Mx, rm; iframe; ipureintro; exact HM
            -- round 51: `R1.deliv` on the opened body
            ihave ⟨HFz, %Md', HV, Hback, %Hdl⟩ := R1.deliv (sint.Z cb).toNat X γa γrm hinj
              $$ [HFz Hi]
            · iframe
            imodintro
            iexists Md'
            iframe HV
            iintro HV
            ihave Hi := Hback $$ HV
            imod Hclose $$ [Hi] with -
            · inext; iexact Hi
            imodintro
            iframe HFz
            ipureintro
            intro h
            rw [hdl]
            apply Hdl
            rw [Hstr]; simpa using h
          ihave Hdr : swift.runReader rp x.γdl $$ [Hrd]
          · iunfold swift.runReader; iexists dm; iframe Hrd; iexact Hdmf
          cases ok
          · try wp_auto
            iframe
            ipureintro
            exact Or.inr ⟨by first | rfl | trivial, by simpa using Hif⟩
          · try wp_auto
            iframe
            ipureintro
            exact Or.inl ⟨by first | rfl | trivial, Or.inr (Hok rfl)⟩
      iintro %bv ⟨cmdId, Hdr, r, HFz, %Hb⟩
      rcases Hb with ⟨rfl, Hb⟩ | ⟨rfl, Hb⟩
      · -- seen, or delivered (then executed: in the log, `R1.deliv`): skipped
        try wp_auto
        unfold forMapPostcondition
        ileft
        isplitr
        · ipureintro; rfl
        iexists E4, key, gp, Pd
        iframe
        isplitl [Hci Hs1 Hc1 Hph Hs2 Hc2 Hcm Hs3 Hc3 Hdp Hs4 Hc4 Hsn Hsm HB]
        · iunfold swift.fillAcc
          iexists s1, s2, s3, s4, cmL, dpL, sm, sM
          iframe
          ipureintro; exact HA
        isplitr
        · ipureintro; exact HPd
        ipureintro
        refine ⟨Hi.1, Hi.2.1, Hi.2.2.1, Hi.2.2.2.1, fun k hk => ?_, fun e he => ?_, by omega⟩
        · rw [htk] at hk
          rcases List.mem_append.mp hk with hk | hk
          · exact Hi.2.2.2.2.1 k hk
          · simp at hk; subst hk
            rcases Hb with h | h
            · exact Or.inl (List.map_subset _ (List.take_subset _ _) h)
            · exact Or.inr h
        · rw [htk]; exact List.mem_append_left _ (Hi.2.2.2.2.2.1 e he)
      · -- reported in `START`
        try wp_auto
        wp_apply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) []
        isplitr
        · ipureintro; rfl
        iintro %d0 ⟨Hd0, -⟩
        ipersist Hd0
        try wp_auto
        wp_apply (wp_Str cmdId_ptr _ key) $$ [$cmdId] as cmdId
        try wp_auto
        wp_method_call
        try wp_auto
        wp_apply (swift.wp_GetOwn wp_GetV dm1 γdc (swift.descR x.γd) (swift.cmdStr key) Mc)
          $$ [$Hrd1 $Hview] as %gv %gok ⟨Hrd1, Hview, %Hg⟩
        try wp_auto
        -- the dependencies: the descriptor's `proposeDep`, or `proposeDeps`'s, or none
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun bv => iprop(⌜bv = executeVal⌝ ∗ v_ptr ↦ gv ∗ exists_ptr ↦ gok ∗
            cmdId_ptr ↦ key ∗ r_ptr ↦ rp ∗ swift.propDepsOwn rp (bs ++ hd) ∗
            ([∗list] r ∈ SR, swift.rdHeld γ x (sint.Z cb).toNat (R1.Wd (sint.Z cb).toNat) r) ∗
            ∃ (d' : GoSlice) (Dd : List swift.CommandId) (Pe : List (sp.CmdId × List sp.CmdId)),
              dep_ptr ↦ d' ∗ d' ↦*□ Dd ∗ ([∗list] p ∈ Pe, R1.Wd (sint.Z cb).toNat p.1 p.2) ∗
              ⌜((∀ d ∈ Dd, toCmdId d ∈ sp.depsIn (bs ++ hd) (toCmdId key)) ∧ Dd.length < 2 ^ 62) ∧
                ∀ p ∈ Pe, ∃ r ∈ SR, x.str (ofCmdId p.1) = r.k ∧ r.pdsl ≠ slice.nil ∧
                  p.2 = r.PD.map toCmdId⌝)))
          $$ [v «exists» cmdId r Hpd Hheld dep]
        · rcases gok with _ | _
          · -- not in `cmdDescs`: `proposeDeps` is not read (`exists && ok`)
            have hnone : Mc !! swift.cmdStr key = none := by
              cases h : Mc !! swift.cmdStr key with
              | none => rfl
              | some _ => rw [h] at Hg; exact absurd Hg.2 (by simp)
            try wp_auto
            iunfold swift.propDepsOwn at Hpd
            icases Hpd with ⟨%pdm, %PDm, Hpdf, Hpdm, #Hpdms⟩
            try wp_auto
            wp_apply (wp_map_lookup2 swift.CommandId.ty swift.Dep.ty pdm PDm key (DFrac.own 1))
              $$ [$Hpdm] as Hpdm
            try wp_auto
            ihave Hpd : swift.propDepsOwn rp (bs ++ hd) $$ [Hpdf Hpdm]
            · iunfold swift.propDepsOwn; iexists pdm, PDm; iframe; iexact Hpdms
            rcases hpk : PDm !! key with _ | psl
            · simp only [hpk, Option.getD_none, Option.isSome_none]
              try wp_auto
              iframe
              try (isplitr; · ipureintro; rfl)
              iexists _, []
              isplitr
              · iexact Hd0
              isplitl []
              · iapply BigSepL.bigSepL_nil.2; itrivial
              ipureintro
              exact ⟨⟨fun _ hd => (List.not_mem_nil hd).elim, (by simp)⟩, by simp⟩
            · ihave #Hpsl := (BigSepM.bigSepM_lookup hpk) $$ Hpdms
              icases Hpsl with ⟨%PS, #Hpsl, %Hpok⟩
              simp only [hpk, Option.getD_some, Option.isSome_some]
              try wp_auto
              iframe
              try (isplitr; · ipureintro; rfl)
              iexists _, []
              isplitr
              · iexact Hd0
              isplitl []
              · iapply BigSepL.bigSepL_nil.2; itrivial
              ipureintro
              exact ⟨⟨fun _ hd => (List.not_mem_nil hd).elim, (by simp)⟩, by simp⟩
          · -- the descriptor at `cmdId`'s key: its held read's `proposeDep` (round 51: the
            -- read `IterCb` made, `hMcSR`)
            obtain ⟨vv, hvv⟩ : ∃ vv, Mc !! swift.cmdStr key = some vv := by
              cases h : Mc !! swift.cmdStr key with
              | none => rw [h] at Hg; exact absurd Hg.2 (by simp)
              | some vv => exact ⟨vv, rfl⟩
            have hgv : gv = vv := by rw [Hg.1, hvv]; rfl
            subst hgv
            obtain ⟨rr, hrr, hrk, hrv⟩ := hMcSR _ _ hvv
            subst hrv
            icases (BigSepL.bigSepL_mem_acc hrr) $$ Hheld with ⟨Hr, Hheld⟩
            iunfold swift.rdHeld at Hr
            icases Hr with ⟨%Hkey, Hf, Hback, #Hrpd⟩
            iunfold swift.DescRead.fields at Hf
            iunfold swift.descRepFields at Hf
            icases Hf with ⟨Fp, Fph, Fcmd, Fdep, Fdl, Fpd, #Fpdl⟩
            -- round 54 (N6's request (3)): the key's `proposeDep` against the run loop's
            -- sequence (`R1.Wd_seq`)
            have hkz : x.str (ofCmdId (toCmdId key)) = rr.k := by rw [hrk, Hstr]; rfl
            ihave #Hlbc : sp.locLb γ x.r (sint.Z cb).toNat (bs ++ hd) $$ []
            · rw [← hcw0]; iexact Hlb
            iapply fupd_wp
            imod swift.rdPd_seq rp γ γc γm x R1 (sint.Z cb).toNat key rr (bs ++ hd) hinj hkz
              $$ [Hrpd Hlbc] with %HWs
            · iframe HdX Hrpd Hlbc
            imodintro
            try wp_auto
            wp_if_destruct
            · -- not set: `proposeDeps`'s
              ihave Hheld := Hheld $$ [Fp Fph Fcmd Fdep Fdl Fpd Hback]
              · iunfold swift.rdHeld
                isplitr
                · ipureintro; exact Hkey
                iframe Hback Hrpd
                iunfold swift.DescRead.fields
                iunfold swift.descRepFields
                iframe
                iexact Fpdl
              try wp_auto
              iunfold swift.propDepsOwn at Hpd
              icases Hpd with ⟨%pdm, %PDm, Hpdf, Hpdm, #Hpdms⟩
              try wp_auto
              wp_apply (wp_map_lookup2 swift.CommandId.ty swift.Dep.ty pdm PDm key (DFrac.own 1))
                $$ [$Hpdm] as Hpdm
              try wp_auto
              ihave Hpd : swift.propDepsOwn rp (bs ++ hd) $$ [Hpdf Hpdm]
              · iunfold swift.propDepsOwn; iexists pdm, PDm; iframe; iexact Hpdms
              rcases hpk : PDm !! key with _ | psl
              · simp only [hpk, Option.getD_none, Option.isSome_none]
                try wp_auto
                iframe
                try (isplitr; · ipureintro; rfl)
                iexists _, []
                isplitr
                · iexact Hd0
                isplitl []
                · iapply BigSepL.bigSepL_nil.2; itrivial
                ipureintro
                exact ⟨⟨fun _ hd => (List.not_mem_nil hd).elim, (by simp)⟩, by simp⟩
              · ihave #Hpsl := (BigSepM.bigSepM_lookup hpk) $$ Hpdms
                icases Hpsl with ⟨%PS, #Hpsl, %Hpok⟩
                simp only [hpk, Option.getD_some, Option.isSome_some]
                try wp_auto
                iframe
                try (isplitr; · ipureintro; rfl)
                iexists _, []
                isplitr
                · iexact Hpsl
                isplitl []
                · iapply BigSepL.bigSepL_nil.2; itrivial
                ipureintro
                exact ⟨⟨Hpok.2.1, Hpok.2.2⟩, by simp⟩
            · -- `proposeDep` set: taken, with its facts at the key's command (round 54, N6's
              -- request (3): `R1.Wd_seq` against the run loop's sequence)
              try wp_auto
              have hpdn : rr.pdsl ≠ slice.nil := by
                intro h; apply Hif; rw [h]; try rfl
              ihave HWd0 := swift.rdPd_wd x.str (R1.Wd (sint.Z cb).toNat) rr key hinj hkz $$ Hrpd
              icases HWd0 with (%Hnil | #HWd)
              · exact absurd Hnil hpdn
              ihave Hheld := Hheld $$ [Fp Fph Fcmd Fdep Fdl Fpd Hback]
              · iunfold swift.rdHeld
                isplitr
                · ipureintro; exact Hkey
                iframe Hback Hrpd
                iunfold swift.DescRead.fields
                iunfold swift.descRepFields
                iframe
                iexact Fpdl
              iframe
              try (isplitr; · ipureintro; rfl)
              iexists _, [(toCmdId key, rr.PD.map toCmdId)]
              isplitr
              · iexact Fpdl
              isplitl []
              · iapply BigSepL.bigSepL_singleton.2; iexact HWd
              ipureintro
              refine ⟨?_, fun p hp => ?_⟩
              · obtain ⟨h1, h2⟩ := HWs hpdn (by
                  -- a pending proposal is in the run loop's sequence (`localOk`)
                  obtain ⟨-, -, -, -, -, -, -, hloc0, -, -, -, -, hpropsIn0⟩ := Hok2.1
                  have hsq : (bs ++ hd).map Prod.fst = w.locAt w.2.1 := by
                    rw [List.map_append, Hok2.2.2, Hok2.2.1, hloc0]
                  rw [hsq]; exact hpropsIn0 _ (by simp [Hiv.2]))
                refine ⟨fun d hd => h1 _ (List.mem_map_of_mem hd), by simpa using h2⟩
              · simp at hp; subst hp
                exact ⟨rr, hrr, hkz, hpdn, rfl⟩
        iintro %bv ⟨%Hbv, v, «exists», cmdId, r, Hpd, Hheld, %d', %Dd, %Pe, dep, #Hd', HPe, %HDd⟩
        obtain ⟨HDd, HPe'⟩ := HDd
        subst Hbv
        try wp_auto
        ihave #Hgp := (BigSepM.bigSepM_lookup Hiv.2) $$ Hpms
        icases Hgp with ⟨%c', #Hgp⟩
        iunfold swift.propIs at Hgp
        icases Hgp with ⟨%pp, %w0, %mu, %addr, %ts, %vs', #Hgp, #Hpp, #Hvs', #Hc', %Hcw⟩
        ihave #Hgp2 := Hgp
        iStructNamed Hgp2
        ihave #Hpp2 := Hpp
        iStructNamed Hpp2
        wp_apply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [key]
        isplitr
        · ipureintro; rfl
        iintro %l1 ⟨Hl1, -⟩
        try wp_auto
        wp_apply wp_slice_append $$ [Hs1 Hc1 Hl1] as %n1 ⟨Hs1, Hc1, -⟩
        · iframe
        try wp_auto
        wp_apply wp_slice_literal (V := w64) (t := go.int) [W64 0]
        isplitr
        · ipureintro; rfl
        iintro %l2 ⟨Hl2, -⟩
        try wp_auto
        wp_apply wp_slice_append $$ [Hs2 Hc2 Hl2] as %n2 ⟨Hs2, Hc2, -⟩
        · iframe
        try wp_auto
        wp_apply wp_slice_literal (V := state.Command) (t := state.Command.ty)
          [state.Command.mk c'.op c'.key vs']
        isplitr
        · ipureintro; rfl
        iintro %l3 ⟨Hl3, -⟩
        try wp_auto
        wp_apply wp_slice_append $$ [Hs3 Hc3 Hl3] as %n3 ⟨Hs3, Hc3, -⟩
        · iframe
        try wp_auto
        wp_apply wp_slice_literal (V := swift.SDep) (t := swift.SDep.ty) [swift.SDep.mk d']
        isplitr
        · ipureintro; rfl
        iintro %l4 ⟨Hl4, -⟩
        try wp_auto
        wp_apply wp_slice_append $$ [Hs4 Hc4 Hl4] as %n4 ⟨Hs4, Hc4, -⟩
        · iframe
        try wp_auto
        have hpre := Hi.1
        have hE3 : E3.length ≤ E4.length := hpre.length_le
        have hnin : toCmdId key ∉ E4.map (·.id) := by
          intro h
          rw [← List.take_append_drop E3.length E4, List.map_append, List.mem_append] at h
          rcases h with h | h
          · have := (hseenE key).2 h; rw [Hb] at this; cases this
          · obtain ⟨e', he', hid⟩ := List.mem_map.mp h
            have := Hi.2.2.2.2.2.1 e' he'
            rw [hid] at this; exact hknd this
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        ihave HPdW : ([∗list] p ∈ Pd ++ Pe, R1.Wd (sint.Z cb).toNat p.1 p.2) $$ [HPdW HPe]
        · iapply BigSepL.bigSepL_append.2
          iframe
        iexists E4 ++ [⟨toCmdId key, W64 0, c', Dd.map toCmdId⟩], key, gp, Pd ++ Pe
        iframe
        isplitl [Hci Hs1 Hc1 Hph Hs2 Hc2 Hcm Hs3 Hc3 Hdp Hs4 Hc4 Hsn Hsm HB]
        · iapply (swift.fillAcc_snoc γ x.N x.r (sint.Z cb).toNat cmdIds_ptr phases_ptr cmds_ptr
            deps_ptr seen_ptr E4 ⟨toCmdId key, W64 0, c', Dd.map toCmdId⟩ E3.length n1 n2 n3 n4 cmL dpL
            (state.Command.mk c'.op c'.key vs') (swift.SDep.mk d') sm sM ⟨HA.1, HA.2.1⟩ ?_
            (by omega) ?_)
          · rw [List.map_append, List.nodup_append]
            refine ⟨HA.2.2.1, by simp, ?_⟩
            intro a ha b hb; simp at hb; subst hb; intro h; subst h; exact hnin ha
          · intro z
            rw [List.take_append_of_le_length hE3]
            exact hseenE z
          · iframe
            isplitl []
            · iunfold swift.repEntryObj
              iexists vs'
              isplitr
              · ipureintro; rfl
              iframe Hvs'
              have hD : (Dd.map toCmdId).map ofCmdId = Dd := by
                rw [List.map_map]; exact List.map_id' Dd |>.trans rfl
              rw [hD]; iexact Hd'
            · iunfold swift.repEntW
              iframe Hc'
              ileft; ipureintro; rfl
        isplitr
        · ipureintro
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact HPd p hp
          · exact HPe' p hp
        ipureintro
        refine ⟨hpre.trans (List.prefix_append _ _), fun e' he' => ?_, fun e' he' => ?_,
          fun M' hM' q' hq' => ?_, fun k hk => ?_, fun e' he' => ?_, by omega⟩
        · rw [List.drop_append_of_le_length hE3] at he'
          rcases List.mem_append.mp he' with h | h
          · exact Hi.2.1 e' h
          · simp at h; subst h
            refine ⟨rfl, by simp [Hiv.2], fun d hd => ?_, by rw [List.length_map]; exact HDd.2⟩
            obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
            exact HDd.1 d0 hd0
        · rw [List.map_append]; exact List.mem_append_left _ (Hi.2.2.1 e' he')
        · rw [List.map_append]; exact List.mem_append_left _ (Hi.2.2.2.1 M' hM' q' hq')
        · rw [htk] at hk
          rcases List.mem_append.mp hk with hk | hk
          · rcases Hi.2.2.2.2.1 k hk with h | h
            · exact Or.inl (by rw [List.map_append]; exact List.mem_append_left _ h)
            · exact Or.inr h
          · simp at hk; subst hk; exact Or.inl (by simp)
        · rw [List.drop_append_of_le_length hE3] at he'
          rw [htk]
          rcases List.mem_append.mp he' with h | h
          · exact List.mem_append_left _ (Hi.2.2.2.2.2.1 e' h)
          · simp at h; subst h; exact List.mem_append_right _ (by simp)
      try wp_auto
      done
    · iintro ⟨%E4, %cv, %pv, %Pd, cmdId, propose, r, Hdr, Hcd, Hrd1, Hview, Hheld, HFz, HPdW, Hpd,
        HA, %HPd, %Hi⟩ Hpm
      have htk : keys.take (↑(GMap.size v.propsM) : Int).toNat = keys := by
        rw [List.take_of_length_le]; rw [Hkeys.2.1]; omega
      rw [htk] at Hi
      have HE4 : (∀ e ∈ E4.drop E3.length, swift.startOk v.propsM (bs ++ hd) e) ∧
          (∀ e ∈ XS, e.id ∈ E4.map (·.id)) ∧
          (∀ M, M0 = some M → ∀ q ∈ M, q.1 ∈ E4.map (·.id)) ∧
          (∀ k, (v.propsM !! k).isSome → toCmdId k ∈ E4.map (·.id) ∨ toCmdId k ∈ dl) ∧
          E3 <+: E4 :=
        ⟨Hi.2.1, Hi.2.2.1, Hi.2.2.2.1, fun k hk => Hi.2.2.2.2.1 k ((Hkeys.1 k).2 hk), Hi.1⟩
      clear Hi
      ihave #HWall : ([∗list] e ∈ XS ++ S, R1.W (sint.Z cb).toNat e) $$ []
      · iapply BigSepL.bigSepL_append.2
        iframe HWX HWS
      clear hWP hWdP
      try wp_auto
      -- the rank: the first position in `handled`, plus one
      wp_apply (wp_map_make1 (K := swift.CommandId) (V := w64)) as %rm0 Hrm0
      try wp_auto
      rename_i iv_ptr
      irename: (typedPointsto iv_ptr (Perennial.zero_val w64) (DFrac.own 1)) => Hiv
      ihave %Hhdll := ownSlice_len $$ Hhdl
      ihave HR1 : (∃ (j jv : w64) (cv : swift.CommandId) (rM : GMap swift.CommandId w64),
          "i" ∷ i_ptr ↦ j ∗ "Hiv" ∷ iv_ptr ↦ jv ∗ "cmdId" ∷ cmdId_ptr ↦ cv ∗ "Hrm" ∷ rm0 ↦$ rM ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ v.handled.length ∧ ∀ z, rM !! z =
            if z ∈ v.handled.take (sint.nat j) then some (W64 (swift.hrank v.handled z : Int))
            else none⌝ : IProp netDistGF) $$ [i Hiv cmdId Hrm0]
      · iexists W64 0, _, _, ∅
        iframe
        ipureintro
        refine ⟨by decide, by simp, fun z => by rw [show sint.nat (W64 0) = 0 by word]; simp⟩
      wp_for HR1
      wp_if_destruct
      · have hlt : sint.Z j < sint.Z v.hdSl.len := by
          clear HE4 HE3 HE2 hSRp hMcSR hSS hSRrep hSE3 hSdep hE3src hE3XS hE3M hE3B hSRvis Hvis
          cases h : decide (sint.Z j < sint.Z v.hdSl.len) <;> simp_all
        have hjl : sint.nat j < v.handled.length := by rw [Hhdll.1]; word
        obtain ⟨z, hz⟩ : ∃ z, v.handled[sint.nat j]? = some z :=
          ⟨_, List.getElem?_eq_getElem hjl⟩
        rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z v.hdSl.len from ⟨Hj.1, hlt⟩)]
        wp_apply (wp_load_slice_index (V := swift.CommandId) v.hdSl (sint.Z j) v.handled _ z Hj.1)
          $$ [Hhdl] as Hhdl
        · iframe; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact hz
        try wp_auto
        wp_apply (wp_map_lookup2 swift.CommandId.ty go.int rm0 rM z (DFrac.own 1)) $$ [$Hrm] as Hrm
        try wp_auto
        have htk : v.handled.take (sint.nat (j + W64 1)) = v.handled.take (sint.nat j) ++ [z] := by
          rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hz]; rfl
        wp_if_destruct
        · try wp_auto
          wp_for_post
          iframe
          iexists j + W64 1, j, z, rM
          iframe
          ipureintro
          have hzin : z ∈ v.handled.take (sint.nat j) := by
            refine Classical.byContradiction fun h => ?_
            have := Hj.2.2 z; rw [ite_eq_right h] at this; rw [this] at Hif
            revert Hif; simp
          refine ⟨by word, by rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]; omega,
            fun y => ?_⟩
          rw [htk, Hj.2.2 y]
          simp only [List.mem_append, List.mem_singleton]
          by_cases hy : y = z
          · subst hy; simp [hzin]
          · simp [hy]
        · -- first occurrence: its rank `j + 1`
          have hzn : z ∉ v.handled.take (sint.nat j) := by
            intro h; have := Hj.2.2 z; rw [if_pos h] at this; rw [this] at Hif
            revert Hif; simp
          have hrk : swift.hrank v.handled z = sint.nat j + 1 := by
            unfold swift.hrank
            rw [if_pos (List.mem_of_getElem? hz), swift.idxOf_first _ _ _ hz hzn]
          wp_apply (wp_mapInsert swift.CommandId.ty rm0 rM z (j + W64 1)) $$ [$Hrm] as Hrm
          try wp_auto
          wp_for_post
          iframe
          iexists j + W64 1, j, z, _
          iframe
          ipureintro
          refine ⟨by word, by rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]; omega,
            fun y => ?_⟩
          rw [htk, GMap.lookup_insert_eq_iff]
          by_cases hy : z = y
          · subst hy; simp [hrk]; word
          · rw [ite_eq_right hy, Hj.2.2 y]
            simp only [List.mem_append, List.mem_singleton]
            by_cases hy' : y ∈ v.handled.take (sint.nat j)
            · simp [hy']
            · simp [hy', Ne.symm hy]
      · -- the ranks of all of `handled`
        have hje : sint.nat j = v.handled.length := by
          have : ¬ (sint.Z j < sint.Z v.hdSl.len) := by
            first
            | simpa using Hif
            | (intro hc; apply Hif; simp [hc])
            | (intro hc; simp [hc] at Hif)
          rw [Hhdll.1]; word
        rw [hje, List.take_length] at Hj
        have HrM := Hj.2.2
        -- the report's slices, read-only from here (the comparator and the last loop read them)
        iunfold swift.fillAcc at HA
        icases HA with ⟨%s1, %s2, %s3, %s4, %cmL, %dpL, %sm, %sM, Hci, Hs1, Hc1, Hph, Hs2, Hc2,
          Hcm, Hs3, Hc3, Hdp, Hs4, Hc4, Hsn, Hsm, %HA, HB⟩
        ihave %Hs1l := ownSlice_len $$ Hs1
        ipersist Hci
        ipersist Hs1
        ipersist Hph
        ipersist Hs2
        ipersist Hcm
        ipersist Hs3
        ipersist Hdp
        ipersist Hs4
        ipersist rank
        ipersist Hrm
        try wp_auto
        -- `idx`: `0, …, n-1`
        wp_apply (wp_slice_make2 (V := w64) (t := go.int) s1.len) as %isl ⟨Hisl, Hicap⟩
        · ipureintro; exact Hs1l.2
        try wp_auto
        rename_i iv2_ptr
        irename: (typedPointsto iv2_ptr (Perennial.zero_val w64) (DFrac.own 1)) => Hiv2
        simp only [List.length_map] at Hs1l
        ihave %Hisll := ownSlice_len $$ Hisl
        simp only [List.length_replicate] at Hisll
        ihave HI2 : (∃ (j jv : w64), "i" ∷ i_ptr ↦ j ∗ "Hiv2" ∷ iv2_ptr ↦ jv ∗
            "Hisl" ∷ isl ↦* ((List.range (sint.nat j)).map (fun (k : Nat) => W64 (k : Int)) ++
              List.replicate (E4.length - sint.nat j) (W64 0)) ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ E4.length⌝ : IProp netDistGF) $$ [i Hiv2 Hisl]
        · iexists W64 0, _
          iframe
          rw [show sint.nat (W64 0) = 0 by word, Hs1l.1]
          simp only [List.range_zero, List.map_nil, List.nil_append, Nat.sub_zero]
          iframe
          ipureintro; exact ⟨by decide, by omega⟩
        wp_for HI2
        wp_if_destruct
        · have hlt : sint.Z j < sint.Z isl.len := by
            clear HE4 HE3 HE2; cases h : decide (sint.Z j < sint.Z isl.len) <;> simp_all
          have hjl : sint.nat j < E4.length := by
            have := Hs1l.1; have := Hisll.1; word
          obtain ⟨L, hL⟩ : ∃ L, L = (List.range (sint.nat j)).map (fun (k : Nat) => W64 (k : Int)) ++
            List.replicate (E4.length - sint.nat j) (W64 0) := ⟨_, rfl⟩
          rw [← hL]
          have hLl : L.length = E4.length := by rw [hL]; simp; omega
          obtain ⟨u, hu⟩ : ∃ u, L[sint.nat j]? = some u := ⟨_, List.getElem?_eq_getElem (by omega)⟩
          rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z isl.len from ⟨Hj.1, hlt⟩)]
          wp_apply (wp_load_slice_index (V := w64) isl (sint.Z j) L _ u Hj.1) $$ [Hisl] as Hisl
          · iframe; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact hu
          try wp_auto
          rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z isl.len from ⟨Hj.1, hlt⟩)]
          wp_apply (wp_store_slice_index (V := w64) isl (sint.Z j) L j) $$ [Hisl] as Hisl
          · iframe; ipureintro; refine ⟨Hj.1, ?_⟩; rw [hLl]; have := hjl; word
          try wp_auto
          wp_for_post
          iframe
          iexists j + W64 1, j
          iframe
          have hset : L.set (sint.Z j).toNat j = (List.range (sint.nat (j + W64 1))).map
              (fun (k : Nat) => W64 (k : Int)) ++
              List.replicate (E4.length - sint.nat (j + W64 1)) (W64 0) := by
            rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, hL,
              show (sint.Z j).toNat = sint.nat j by word]
            have := swift.idx_set E4.length (sint.nat j) hjl
            rw [show (W64 ((sint.nat j : Nat) : Int)) = j by word] at this
            exact this
          rw [hset]
          iframe
          ipureintro
          exact ⟨by word, by rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]; omega⟩
        · have hje : sint.nat j = E4.length := by
            have : ¬ (sint.Z j < sint.Z isl.len) := by
              first
              | simpa using Hif
              | (intro hc; apply Hif; simp [hc])
              | (intro hc; simp [hc] at Hif)
            have := Hs1l.1; have := Hisll.1; word
          rw [hje, Nat.sub_self, List.replicate_zero, List.append_nil]
          try wp_auto
          -- sorted by `(rank, index)`
          have hrkv : ∀ z, (rM !! z).getD (W64 0) = W64 (swift.hrank v.handled z : Int) := by
            intro z
            rw [HrM z]
            by_cases hz : z ∈ v.handled
            · rw [if_pos hz]; rfl
            · rw [ite_eq_right hz]; simp [swift.hrank, hz]
          have hrkb : ∀ z, swift.hrank v.handled z ≤ v.handled.length := by
            intro z; unfold swift.hrank
            split
            · have := List.idxOf_lt_length_of_mem (by assumption : z ∈ v.handled); omega
            · omega
          -- the report's length: distinct registered commands (`sp.cmdIs_list_len`)
          ihave ⟨HB, #HBc⟩ := swift.fillB_cmdIs γ x.N x.r (sint.Z cb).toNat E4 cmL dpL $$ HB
          iapply fupd_wp
          imod sp.cmdIs_list_len ⊤ (by simp) (E4.map (·.id)) HA.2.2.1 $$ [Hspi HBc] with %HE4len
          · iframe Hspi; iexact HBc
          imodintro
          wp_func_lits
          wp_apply (wp_SortFunc (E := w64) (S := go.GoType.SliceType go.int)
              (swift.FillLt v.handled (E4.map (fun e => ofCmdId e.id)))
              (fun a => iprop(⌜0 ≤ sint.Z a ∧ sint.Z a < E4.length⌝)) isl _
              ((List.range E4.length).map (fun (k : Nat) => W64 (k : Int)))
              (swift.fillLt_swo _ _)) $$ [Hisl] as %xs' ⟨Hisl, %Hperm, %Hsorted⟩
          · iframe
            isplitr
            · ipureintro; simp
              simp only [List.length_map] at HE4len
              omega
            isplitl []
            · iapply BigSepL.bigSepL_pure.2
              ipureintro
              intro k a ha
              have hm := List.mem_of_getElem? ha
              simp only [List.mem_map, List.mem_range] at hm
              obtain ⟨k', hk', rfl⟩ := hm
              have := Hs1l.1; have := Hs1l.2
              constructor <;> word
            iunfold slices.cmpImplementsOn
            iintro %a %b
            imodintro
            iintro %Φc ⟨%Ha, %Hb⟩ HΦc
            try wp_auto
            have hlen := Hs1l.1
            have hlen2 := Hs1l.2
            have hhl := Hhdll.1
            have hhl2 := Hhdll.2
            have hal : sint.Z a < sint.Z s1.len := by word
            have hbl : sint.Z b < sint.Z s1.len := by word
            obtain ⟨za, hza⟩ : ∃ z, (E4.map (fun e => ofCmdId e.id))[(sint.Z a).toNat]? = some z :=
              ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
            obtain ⟨zb, hzb⟩ : ∃ z, (E4.map (fun e => ofCmdId e.id))[(sint.Z b).toNat]? = some z :=
              ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
            have hra : sint.Z (W64 (swift.hrank v.handled za : Int)) = swift.hrank v.handled za := by
              have := hrkb za; word
            have hrb : sint.Z (W64 (swift.hrank v.handled zb : Int)) = swift.hrank v.handled zb := by
              have := hrkb zb; word
            have hfa : swift.fillRk v.handled (E4.map (fun e => ofCmdId e.id)) a =
                swift.hrank v.handled za := by unfold swift.fillRk; rw [hza]
            have hfb : swift.fillRk v.handled (E4.map (fun e => ofCmdId e.id)) b =
                swift.hrank v.handled zb := by unfold swift.fillRk; rw [hzb]
            rw [ite_eq_left (show 0 ≤ sint.Z a ∧ sint.Z a < sint.Z s1.len from ⟨Ha.1, hal⟩)]
            wp_apply (wp_load_slice_index (V := swift.CommandId) s1 (sint.Z a) _ DFrac.discard za Ha.1)
              $$ [Hs1] as -
            · iframe Hs1; ipureintro; exact hza
            wp_apply (wp_map_lookup1 swift.CommandId.ty go.int rm0 rM za DFrac.discard) $$ [Hrm] as -
            · iexact Hrm
            try wp_auto
            rw [ite_eq_left (show 0 ≤ sint.Z b ∧ sint.Z b < sint.Z s1.len from ⟨Hb.1, hbl⟩)]
            wp_apply (wp_load_slice_index (V := swift.CommandId) s1 (sint.Z b) _ DFrac.discard zb Hb.1)
              $$ [Hs1] as -
            · iframe Hs1; ipureintro; exact hzb
            wp_apply (wp_map_lookup1 swift.CommandId.ty go.int rm0 rM zb DFrac.discard) $$ [Hrm] as -
            · iexact Hrm
            have e1 := hrkv za
            have e2 := hrkv zb
            simp only [show (Perennial.zero_val w64) = W64 0 from rfl, e1, e2]
            try wp_auto
            rw [hra, hrb]
            repeat' (first | wp_if_destruct | wp_auto)
            all_goals (iapply HΦc; ipureintro; unfold swift.FillLt; rw [hfa, hfb])
            all_goals (simp only [show sint.Z (W64 (-1)) = -1 by word, show sint.Z (W64 1) = 1 by word,
              show sint.Z (W64 0) = 0 by word])
            all_goals (simp_all; try omega)
            all_goals (intro h; have h' := Int.ofNat.inj h; simp_all)
          try wp_auto
          -- the ack's four slices, along `idx`
          wp_apply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) []
          isplitr
          · ipureintro; rfl
          iintro %f10 ⟨Hf1, Hf1c⟩
          try wp_auto
          wp_apply wp_slice_literal (V := w64) (t := go.int) []
          isplitr
          · ipureintro; rfl
          iintro %f20 ⟨Hf2, Hf2c⟩
          try wp_auto
          wp_apply wp_slice_literal (V := state.Command) (t := state.Command.ty) []
          isplitr
          · ipureintro; rfl
          iintro %f30 ⟨Hf3, Hf3c⟩
          try wp_auto
          wp_apply wp_slice_literal (V := swift.SDep) (t := swift.SDep.ty) []
          isplitr
          · ipureintro; rfl
          iintro %f40 ⟨Hf4, Hf4c⟩
          try wp_auto
          rename_i iv3_ptr
          irename: (typedPointsto iv3_ptr (Perennial.zero_val w64) (DFrac.own 1)) => Hiv3
          ihave %Hxsl := ownSlice_len $$ Hisl
          have hpl := Hperm.length_eq
          simp only [List.length_map, List.length_range] at hpl
          have hxs : ∀ (k : Nat) (a : w64), xs'[k]? = some a → 0 ≤ sint.Z a ∧ (sint.Z a).toNat < E4.length := by
            intro k a ha
            have hm : a ∈ (List.range E4.length).map (fun (k : Nat) => W64 (k : Int)) :=
              Hperm.symm.subset (List.mem_of_getElem? ha)
            simp only [List.mem_map, List.mem_range] at hm
            obtain ⟨k', hk', rfl⟩ := hm
            have := Hs1l.1; have := Hs1l.2
            constructor <;> word
          ihave HI3 : (∃ (j jv : w64) (g1 g2 g3 g4 : GoSlice),
              "i" ∷ i_ptr ↦ j ∗ "Hiv3" ∷ iv3_ptr ↦ jv ∗
              "Hp" ∷ p ↦ swift.MNewLeaderAckN.mk rep bl cb g1 g2 g3 g4 ∗
              "Hg1" ∷ g1 ↦* (((xs'.take (sint.nat j)).filterMap (fun a => E4[(sint.Z a).toNat]?)).map
                (fun e => ofCmdId e.id)) ∗ "Hg1c" ∷ ownSliceCap swift.CommandId g1 (DFrac.own 1) ∗
              "Hg2" ∷ g2 ↦* (((xs'.take (sint.nat j)).filterMap (fun a => E4[(sint.Z a).toNat]?)).map
                (·.phase)) ∗ "Hg2c" ∷ ownSliceCap w64 g2 (DFrac.own 1) ∗
              "Hg3" ∷ g3 ↦* ((xs'.take (sint.nat j)).filterMap (fun a => cmL[(sint.Z a).toNat]?)) ∗
                "Hg3c" ∷ ownSliceCap state.Command g3 (DFrac.own 1) ∗
              "Hg4" ∷ g4 ↦* ((xs'.take (sint.nat j)).filterMap (fun a => dpL[(sint.Z a).toNat]?)) ∗
                "Hg4c" ∷ ownSliceCap swift.SDep g4 (DFrac.own 1) ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ xs'.length⌝ : IProp netDistGF)
            $$ [i Hiv3 Hp Hf1 Hf1c Hf2 Hf2c Hf3 Hf3c Hf4 Hf4c]
          · iexists W64 0, _, _, _, _, _
            rw [show sint.nat (W64 0) = 0 by word]
            simp only [List.take_zero, List.filterMap_nil, List.map_nil]
            iframe
            ipureintro; exact ⟨by decide, by omega⟩
          ihave %Hs2l := ownSlice_len $$ Hs2
          ihave %Hs3l := ownSlice_len $$ Hs3
          ihave %Hs4l := ownSlice_len $$ Hs4
          simp only [List.length_map] at Hs2l
          wp_for HI3
          wp_if_destruct
          · have hlt : sint.Z j < sint.Z isl.len := by
              clear HE4 HE3 HE2; cases h : decide (sint.Z j < sint.Z isl.len) <;> simp_all
            have hjl : sint.nat j < xs'.length := by have := Hxsl.1; word
            obtain ⟨a, ha⟩ : ∃ a, xs'[sint.nat j]? = some a := ⟨_, List.getElem?_eq_getElem hjl⟩
            obtain ⟨ha0, hal⟩ := hxs _ _ ha
            obtain ⟨e, he⟩ : ∃ e, E4[(sint.Z a).toNat]? = some e := ⟨_, List.getElem?_eq_getElem hal⟩
            obtain ⟨cv, hcv⟩ : ∃ cv, cmL[(sint.Z a).toNat]? = some cv :=
              ⟨_, List.getElem?_eq_getElem (by rw [HA.1]; exact hal)⟩
            obtain ⟨sd, hsd⟩ : ∃ sd, dpL[(sint.Z a).toNat]? = some sd :=
              ⟨_, List.getElem?_eq_getElem (by rw [HA.2.1]; exact hal)⟩
            have hb1 : sint.Z a < sint.Z s1.len := by have := Hs1l.1; word
            have hb2 : sint.Z a < sint.Z s2.len := by have := Hs2l.1; word
            have hb3 : sint.Z a < sint.Z s3.len := by have := Hs3l.1; have := HA.1; word
            have hb4 : sint.Z a < sint.Z s4.len := by have := Hs4l.1; have := HA.2.1; word
            rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z isl.len from ⟨Hj.1, hlt⟩)]
            wp_apply (wp_load_slice_index (V := w64) isl (sint.Z j) xs' _ a Hj.1) $$ [Hisl] as Hisl
            · iframe; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact ha
            try wp_auto
            rw [ite_eq_left (show 0 ≤ sint.Z a ∧ sint.Z a < sint.Z s1.len from ⟨ha0, hb1⟩)]
            wp_apply (wp_load_slice_index (V := swift.CommandId) s1 (sint.Z a) _ DFrac.discard
              (ofCmdId e.id) ha0) $$ [Hs1] as -
            · iframe Hs1; ipureintro; rw [List.getElem?_map, he]; rfl
            try wp_auto
            rw [ite_eq_left (show 0 ≤ sint.Z a ∧ sint.Z a < sint.Z s3.len from ⟨ha0, hb3⟩)]
            wp_apply (wp_load_slice_index (V := state.Command) s3 (sint.Z a) _ DFrac.discard cv ha0)
              $$ [Hs3] as -
            · iframe Hs3; ipureintro; exact hcv
            try wp_auto
            rw [ite_eq_left (show 0 ≤ sint.Z a ∧ sint.Z a < sint.Z s4.len from ⟨ha0, hb4⟩)]
            wp_apply (wp_load_slice_index (V := swift.SDep) s4 (sint.Z a) _ DFrac.discard sd ha0)
              $$ [Hs4] as -
            · iframe Hs4; ipureintro; exact hsd
            try wp_auto
            wp_apply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [ofCmdId e.id]
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hg1 Hg1c Hl1] as %n1 ⟨Hg1, Hg1c, -⟩
            · iframe
            try wp_auto
            rw [ite_eq_left (show 0 ≤ sint.Z a ∧ sint.Z a < sint.Z s2.len from ⟨ha0, hb2⟩)]
            wp_apply (wp_load_slice_index (V := w64) s2 (sint.Z a) _ DFrac.discard e.phase ha0)
              $$ [Hs2] as -
            · iframe Hs2; ipureintro; rw [List.getElem?_map, he]; rfl
            try wp_auto
            wp_apply wp_slice_literal (V := w64) (t := go.int) [e.phase]
            isplitr
            · ipureintro; rfl
            iintro %l2 ⟨Hl2, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hg2 Hg2c Hl2] as %n2 ⟨Hg2, Hg2c, -⟩
            · iframe
            try wp_auto
            wp_apply wp_slice_literal (V := state.Command) (t := state.Command.ty) [cv]
            isplitr
            · ipureintro; rfl
            iintro %l3 ⟨Hl3, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hg3 Hg3c Hl3] as %n3 ⟨Hg3, Hg3c, -⟩
            · iframe
            try wp_auto
            wp_apply wp_slice_literal (V := swift.SDep) (t := swift.SDep.ty) [sd]
            isplitr
            · ipureintro; rfl
            iintro %l4 ⟨Hl4, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hg4 Hg4c Hl4] as %n4 ⟨Hg4, Hg4c, -⟩
            · iframe
            try wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, a, n1, n2, n3, n4
            have htk : xs'.take (sint.nat (j + W64 1)) = xs'.take (sint.nat j) ++ [a] := by
              rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, ha]; rfl
            rw [htk]
            simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, he, hcv, hsd,
              List.map_append, List.map_cons, List.map_nil]
            iframe
            ipureintro
            exact ⟨by word, by rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]; omega⟩
          · -- all of `idx`: the report
            have hje : sint.nat j = xs'.length := by
              have : ¬ (sint.Z j < sint.Z isl.len) := by
                first
                | simpa using Hif
                | (intro hc; apply Hif; simp [hc])
                | (intro hc; simp [hc] at Hif)
              have := Hxsl.1; word
            rw [hje, List.take_length]
            ipersist Hp
            ipersist Hg1
            ipersist Hg2
            ipersist Hg3
            ipersist Hg4
            try wp_auto
            -- L2: the end, `ghostReport(newLeaderAckN)`, below (the report step in its update)
            iapply fupd_wp
            -- the report `R`: the entries along the sorted indices
            obtain ⟨hb0, hcb0, hw1, hw2, -, -, hMn, hloc, hprops, habove, -, hlnd, hpropsIn⟩ :=
              Hok2.1
            have hbw : w.1 = (sint.Z bl).toNat := by rw [hw1, Hn.2.2.1]; rfl
            have hcw : w.2.1 = (sint.Z cb).toNat := by rw [hw2, Hn.2.2.2.1]; rfl
            have hxs' : ∀ a ∈ xs', (sint.Z a).toNat < E4.length := fun a ha => by
              obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ha; exact (hxs k a hk).2
            ihave ⟨HRo, HRw⟩ := swift.fill_ackEnts γ x.N x.r (sint.Z cb).toNat E4 cmL dpL xs' hxs'
              $$ HB
            have hlenR : (xs'.filterMap (fun a => E4[(sint.Z a).toNat]?)).length = xs'.length :=
              swift.filterMap_len _ xs' (fun a ha => by simp [hxs' a ha])
            have hlenC : (xs'.filterMap (fun a => cmL[(sint.Z a).toNat]?)).length = xs'.length :=
              swift.filterMap_len _ xs' (fun a ha => by have := hxs' a ha; simp [HA.1, this])
            have hlenD : (xs'.filterMap (fun a => dpL[(sint.Z a).toNat]?)).length = xs'.length :=
              swift.filterMap_len _ xs' (fun a ha => by have := hxs' a ha; simp [HA.2.1, this])
            -- round N6: the entries' bounds (`Msg.wf`, D75 (2)) from their witnesses
            ihave #HRw2 := HRw
            imod swift.repEntWs_wf γ γc γm x.γl x.N x.r (sint.Z cb).toNat _ $$ [Hspi HRw2]
              with %hwfW
            · iframe Hspi HRw2
            -- round N6: the base's ids and dependencies (`syncIs`, D75 (2): `syncSeq`'s ids are
            -- the run loop's, small)
            ihave HMf : |={⊤}=> ⌜∀ M, M0 = some M → (∀ y ∈ M.map Prod.fst, y ∈ sp.syncOrder M) ∧
                (∀ q ∈ M, q.2.2.length < 2 ^ 62) ∧ (M.map Prod.fst).Nodup⌝ $$ []
            · rcases hM0 : M0 with _ | M
              · imodintro; ipureintro; intro M h; cases h
              · iunfold swift.syncObj at Hlso
                dsimp only
                icases Hlso with ⟨%ph1, %cm1, %dp1, %rep1, %bl1, -, -, #HsI, -, -⟩
                imod sp.syncIs_facts ⊤ (fun _ _ => CoPset.mem_full) _ M $$ [Hspi HsI] with %HMf
                · iframe Hspi HsI
                imod sp.syncIs_seq ⊤ (fun _ _ => CoPset.mem_full) _ M $$ [Hspi HsI] with %Hseq
                · iframe Hspi HsI
                ihave Hsm := swift.locLb_small (γ := γ) (γc := γc) (γm := γm) (γl := x.γl) x.r w.2.1
                  (bs ++ hd) $$ [Hspi Hlb]
                · iframe Hspi Hlb
                imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hsm with %Hsm
                imodintro
                ipureintro
                intro M' hM'
                cases hM'
                have hbsM : bs.map Prod.fst = sp.syncOrder M := by rw [Hok2.2.2, hM0]; rfl
                refine ⟨fun y hy => sp.syncOrder_complete M HMf.2 y hy, fun q hq => ?_, HMf.2⟩
                obtain ⟨y, c, D⟩ := q
                obtain ⟨-, hpm⟩ := Hseq.2 y c D hq
                have hlenS : (sp.syncSeq M).length ≤ 6 * 2 ^ 32 := by
                  have := swift.small_ids_len ((sp.syncSeq M).map Prod.fst)
                    (by rw [Hseq.1]; exact sp.syncOrder_nodup M)
                    (by
                      intro z hz
                      rw [Hseq.1, ← hbsM] at hz
                      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
                      exact Hsm p (List.mem_append_left _ hp))
                  simpa using this
                show D.length < 2 ^ 62
                rw [hpm.length_eq]
                have := sp.depsIn_length (sp.syncSeq M) y
                omega
            imod HMf with %hMf
            -- round N6: the report's sources (the four collections) and order
            have hRs : (xs'.filterMap (fun a => E4[(sint.Z a).toNat]?)).Perm E4 :=
              swift.fill_perm E4 xs' (by have := HE4len; simp only [List.length_map] at this; omega)
                Hperm
            have hsortR := swift.fill_sorted E4 v.handled xs' Hsorted
            have hE3t : E4.take E3.length = E3 := (List.prefix_iff_eq_take.mp HE4.2.2.2.2).symm
            -- round 54 (D76 (1)): `S` is the reported reads' entries, so reported
            have hSv : ∀ e ∈ S, e.id ∈ E3.map (·.id) := fun e he => List.mem_map_of_mem (hSE3 e he)
            -- round 54 (D76 (2)): the log's entries are at least `PRE_ACCEPT`, a `START` read's
            -- dependencies are few (`descReadOk`)
            ihave %hXSph := swift.XS_phase XS es HXS.1 $$ HXE
            have hR1dep : ∀ e ∈ XS ++ S, e.phase.toNat = 0 → e.dep.length < 2 ^ 62 := by
              intro e he h0
              rcases List.mem_append.mp he with he | he
              · exact absurd h0 (hXSph e he)
              · exact hSdep e he h0
            have htake : ∀ e ∈ E4.take E3.length, e ∈ XS ∨ e ∈ S ∨
                (e.phase.toNat = 3 ∧ e.id ∈ (M0.map sp.syncOrder).getD []) := by
              intro e he
              rw [hE3t] at he
              rcases HE3.1 e he with h | h | ⟨M, hM, hph, hq⟩
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · refine Or.inr (Or.inr ⟨by rw [hph]; rfl, ?_⟩)
                rw [hM]
                exact (hMf M hM).1 _ (List.mem_map.mpr ⟨_, hq, rfl⟩)
            have hcovT : ∀ y, y ∈ (XS ++ S).map (·.id) ∨ y ∈ (M0.map sp.syncOrder).getD [] →
                y ∈ (E4.take E3.length).map (·.id) := by
              intro y hy
              rw [hE3t]
              rcases hy with hy | hy
              · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
                rcases List.mem_append.mp he with h | h
                · exact HE3.2.1 e h
                · exact hSv e h
              · rcases hM0 : M0 with _ | M
                · simp [hM0] at hy
                · simp only [hM0, Option.map_some, Option.getD_some] at hy
                  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (sp.syncOrder_mem M y hy)
                  exact HE3.2.2 M hM0 q hq
            -- the base fact (the last `MSync`, `syncObj`); round N7 (`N5: R2-a`): a base command
            -- is reported as the `MSync` has it, or it is a log entry (reported as it is), for
            -- which `fill_report` takes N1-R2's R2-a
            ihave #HBf : (⌜(sint.Z cb).toNat = 0 ∧ (M0.map sp.syncOrder).getD [] = []⌝ ∨
                ⌜0 < (sint.Z cb).toNat⌝ ∗ ∃ M, ⌜M0 = some M⌝ ∗ sp.syncIs γ (sint.Z cb).toNat M ∗
                  ⌜(M0.map sp.syncOrder).getD [] = sp.syncOrder M ∧ (M.map Prod.fst).Nodup ∧
                    ∀ q ∈ M,
                    (∃ e ∈ xs'.filterMap (fun a => E4[(sint.Z a).toNat]?), e.id = q.1 ∧
                      e.phase.toNat = 3 ∧ e.dep.Perm q.2.2) ∨
                    (∃ e ∈ XS, e ∈ xs'.filterMap (fun a => E4[(sint.Z a).toNat]?) ∧ e.id = q.1 ∧
                      e.id ∈ (M0.map sp.syncOrder).getD [])⌝) $$ []
            · rcases hM0 : M0 with _ | M
              · ileft; ipureintro; exact ⟨by rw [← hcw]; exact hMn.1 hM0, rfl⟩
              · iunfold swift.syncObj at Hlso
                dsimp only
                icases Hlso with ⟨%ph1, %cm1, %dp1, %rep1, %bl1, -, -, #HsI, -, -⟩
                iright
                isplitr
                · ipureintro
                  have : w.2.1 ≠ 0 := fun h => by have := hMn.2 h; rw [hM0] at this; cases this
                  omega
                iexists M
                rw [← hcw]
                isplitr
                · ipureintro; rfl
                iframe HsI
                ipureintro
                refine ⟨rfl, (hMf M hM0).2.2, fun q hq => ?_⟩
                obtain ⟨e, he, hid, hsrc⟩ := hE3B M hM0 q hq
                have heR : e ∈ xs'.filterMap (fun a => E4[(sint.Z a).toNat]?) :=
                  hRs.symm.subset (HE4.2.2.2.2.subset he)
                rcases hsrc with heX | ⟨hph, hmem⟩
                · right
                  refine ⟨e, heX, heR, hid, ?_⟩
                  show e.id ∈ sp.syncOrder M
                  rw [hid]; exact (hMf M hM0).1 _ (List.mem_map_of_mem hq)
                · left
                  have hqe := sp.mem_eq_of_fst (hMf M hM0).2.2 hmem hq hid
                  subst hqe
                  exact ⟨_, heR, rfl, by rw [hph]; rfl, List.Perm.refl _⟩
            -- the base, as N1-R2 takes it (`syncObj`)
            ihave #HB0 : (⌜(sint.Z cb).toNat = 0 ∧ (M0.map sp.syncOrder).getD [] = [] ∧ M0 = none⌝ ∨
                ∃ M : sp.SyncMsg, ⌜M0 = some M⌝ ∗ sp.syncIs γ (sint.Z cb).toNat M ∗
                  sp.locLb γ (sp.leaderOf x.N (sint.Z cb).toNat) (sint.Z cb).toNat (sp.syncSeq M) ∗
                  ⌜(M0.map sp.syncOrder).getD [] = sp.syncOrder M⌝) $$ []
            · rcases hM0 : M0 with _ | M
              · ileft; ipureintro; exact ⟨by rw [← hcw]; exact hMn.1 hM0, rfl, rfl⟩
              · iunfold swift.syncObj at Hlso
                dsimp only
                icases Hlso with ⟨%ph1, %cm1, %dp1, %rep1, %bl1, -, -, #HsI, -, #HlbL⟩
                iright
                iexists M
                rw [← hcw]
                iframe HsI HlbL
                ipureintro; exact ⟨rfl, rfl⟩
            -- every read's entry reported or `seen` (round 53, `IterCb`'s accumulator)
            have hrepSR : ∀ r ∈ SR, ∀ e, r.entry = some e → e.id ∈ (XS ++ S).map (·.id) ∨
                e.id ∈ (M0.map sp.syncOrder).getD [] := by
              intro r hr e he
              obtain ⟨e', he', hid⟩ := List.mem_map.mp (hSRrep r hr e he)
              rw [← hid]
              rcases hE3src e' he' with h | h | ⟨M, hM, -, hq⟩
              · exact Or.inl (List.mem_map_of_mem (List.mem_append_left _ h))
              · exact Or.inl (List.mem_map_of_mem (List.mem_append_right _ h))
              · right; rw [hM]; exact (hMf M hM).1 _ (List.mem_map.mpr ⟨_, hq, rfl⟩)
            -- the held reads' fields, the entries' facts; round 56: their key facts
            ihave ⟨Hheld, %hkey⟩ := swift.keep_pureF
              (swift.rdHeld_keys γ x (sint.Z cb).toNat (R1.Wd (sint.Z cb).toNat) SR) $$ Hheld
            ihave ⟨Hf, Hcls, Hfb⟩ := swift.rdHeld_fields γ x (sint.Z cb).toNat (R1.Wd (sint.Z cb).toNat) SR $$ Hheld
            -- round 56 (D79 (1), 52-3): the stopped epoch's commit record and registration
            ihave Hout : ghostMapAuth x.γout (1 : Iris.Qp).half
                (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp)) $$ [Hout]
            · iapply (show (ghostMapAuth x.syncN.γout (1 : Iris.Qp).half
                (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp)) : IProp netDistGF) ⊢
                ghostMapAuth x.γout (1 : Iris.Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp))
                from .rfl)
              iexact Hout
            -- the report step (`swift.fill_report`)
            ihave #Hlb' : sp.locLb γ x.r (sint.Z cb).toNat (bs ++ hd) $$ []
            · rw [← hcw]; iexact Hlb
            -- L2: the report at its resolution (`ghostReport(newLeaderAckN)`, `fill_report` in its
            -- update)
            ihave #Hcpk : isPkgInit (PROP := IProp netDistGF)
                pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
            · iPkgInit
            ihave #HRo2 := HRo
            have hcbG : 0 ≤ sint.Z cb := by rw [← Hn.2.2.2.1]; exact hcb0
            have hblG : 0 ≤ sint.Z bl := by rw [← Hn.2.2.1]; exact hb0
            ihave #HobjB : swift.ackObjB p bl (x.r, (⟨(sint.Z cb).toNat, xs'.filterMap (fun a => E4[(sint.Z a).toNat]?)⟩ : sp.Report)) $$ []
            · iunfold swift.ackObjB
              iexists rep, cb, g1, g2, g3, g4, xs'.filterMap (fun a => cmL[(sint.Z a).toNat]?),
                xs'.filterMap (fun a => dpL[(sint.Z a).toNat]?)
              iframe Hp Hg1 Hg2 Hg3 Hg4 HRo2
              ipureintro
              refine ⟨Hrep, by show sint.Z cb = (((sint.Z cb).toNat : Nat) : Int); omega, ?_, ?_⟩
              · rw [hlenC, hlenR]
              · rw [hlenD, hlenR]
            imodintro
            wp_bind (App (Val (@! swift.ghostReport)) (Val _))
            iapply (swift.wp_ghostReport γ x.k p bl (x.r, (⟨(sint.Z cb).toNat, xs'.filterMap (fun a => E4[(sint.Z a).toNat]?)⟩ : sp.Report))
              iprop(ghostVar x.γv (1 : Iris.Qp).half w ∗ R1.Fz (sint.Z cb).toNat X ∗
                (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = (sint.Z cb).toNat⌝ ∗ swift.cgG x g) ∗
                swift.freeP x.γcg (sint.Z cb).toNat ∗
                ghostMapAuth x.γout (1 : Iris.Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp)) ∗
                github_com.orcaman.concurrent_map.cmapView γdc Mc ∗ ([∗list] r ∈ SR, r.fields) ∗
                ([∗list] r ∈ SR, swift.rdCl x.sn.γcl (sint.Z cb).toNat r) ∗
                sp.reported γ x.r (sint.Z bl).toNat (⟨(sint.Z cb).toNat, xs'.filterMap (fun a => E4[(sint.Z a).toNat]?)⟩ : sp.Report)))
              $$ [Hw Htk HFz HPSi HPSf Hout Hview Hf Hcls HPdW]
            · iframe Hpkg Hcpk Hng HobjB
              isplitr
              · ipureintro; exact hblG
              iunfold swift.ghostUpd
              iintro %W' Hpre
              rw [show sp.bal bl = (sint.Z bl).toNat from rfl]
              imod (swift.fill_report rp γ γc γm x R1 R2 fr lg w (sint.Z bl).toNat
                    ⟨(sint.Z cb).toNat, xs'.filterMap (fun a => E4[(sint.Z a).toNat]?)⟩ (bs ++ hd)
                    ((M0.map sp.syncOrder).getD []) X XS S SR γdc Mc dl Pd M0 Hids.2.2.1
                    Hids.2.2.2.2.2 hbw hcw
                    (by have := Hn.2.1; rw [hbw, hcw] at this; exact this) habove
                    (by show _ = w.locAt (sint.Z cb).toNat
                        rw [List.map_append, Hok2.2.2, Hok2.2.1, ← hcw, hloc])
                    (by show _ <+: w.locAt (sint.Z cb).toNat
                        rw [← hcw, hloc]; exact List.prefix_append _ _)
                    HXS.2 hSS hMcSR HPd (fun y hy => by rw [hdl] at hy; exact hy) hrepSR hkey hinj
                    (fun st hw hcov hbase => by
                      -- round N6: `swift.fillFacts_of` (FillFacts.lean)
                      subst hw
                      have hlocS : st.locAt (sint.Z cb).toNat =
                          (swift.viewOf st).locAt (swift.viewOf st).2.1 := by rw [hcw]; rfl
                      refine swift.fillFacts_of x.N x.r (sint.Z bl).toNat (sint.Z cb).toNat st (bs ++ hd)
                        ((M0.map sp.syncOrder).getD []) XS S dl Pd E4 E3.length v.handled _ hcov hbase
                        (by rw [hlocS, hloc]) (by rw [hlocS]; exact hlnd) HA.2.2.1 htake ?_ hcovT ?_
                        hRs hsortR
                      · intro e he
                        obtain ⟨h0, hs, hd', -⟩ := HE4.1 e he
                        refine ⟨by rw [h0]; rfl, ?_, hd'⟩
                        rw [hlocS]; exact hpropsIn _ hs
                      · intro y hy
                        rw [hlocS] at hy
                        rcases HE4.2.2.2.1 (ofCmdId y) (hprops y hy) with h | h
                        · exact h
                        · have h' : y ∈ dl := h
                          obtain ⟨e, he, hid⟩ := List.mem_map.mp (hcov.2.2.1 _ h')
                          rw [← hid]; exact HE4.2.1 e he) W')
                $$ [Hw Htk HFz HPSi HPSf Hout Hview Hf Hcls HPdW Hpre]
                with ⟨Hw, HFz, HPSi, HPSf, Hout, Hview, Hf, Hcls, #Hrep, Hpost⟩
              · iframe Hspi Hcfg HnI HdX Hw Htk Hlb' HBf HB0 HFz HPSi HPSf Hout Hview Hf Hcls HWall
                  HWXX HPdW HRw2 Hpre
              imodintro
              iframe Hpost Hw HFz HPSi HPSf Hout Hview Hf Hcls Hrep
            inext
            iintro ⟨Hw, HFz, HPSi, HPSf, Hout, Hview, Hf, Hcls, #Hrep⟩
            try wp_auto
            ihave HPS : swift.stopPS x bc.2 Mc $$ [HPSi HPSf HPSk]
            · iunfold swift.stopPS
              iframe HPSk
              isplitl [HPSi]
              · rw [Hbc]; iexact HPSi
              rw [Hbc]; iexact HPSf
            -- the reads' descriptors back (round 51), the record thawed, the stopped epoch whole
            ihave Hds := Hfb $$ Hf Hcls
            ihave Hents := swift.held_map Mc SR
              (fun d => swift.descFree (swift.descDF (x.DR γ (sint.Z cb).toNat)) d) hSRp $$ Hds
            ihave Hout : ghostMapAuth x.syncN.γout (1 : Iris.Qp).half
                (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp)) $$ [Hout]
            · iapply (show (ghostMapAuth x.γout (1 : Iris.Qp).half
                (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp)) : IProp netDistGF) ⊢
                ghostMapAuth x.syncN.γout (1 : Iris.Qp).half
                  (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp)) from .rfl)
              iexact Hout
            imod R1.thaw (sint.Z cb).toNat X $$ [HFz] with Hxp
            · iframe HdX HFz
            ihave Hxp : ghostVar x.syncN.γxp (1 : Iris.Qp).half bc.2 $$ [Hxp]
            · rw [Hbc]
              iapply (show (ghostVar x.γxp (1 : Iris.Qp).half (sint.Z cb).toNat : IProp netDistGF) ⊢
                ghostVar x.syncN.γxp (1 : Iris.Qp).half (sint.Z cb).toNat from .rfl)
              iexact Hxp
            ihave Hds : swift.descsStopped x.γd (swift.descDF (x.DR γ (sint.Z cb).toNat))
                (swift.stopPS x bc.2) rp $$ [Hcd Hrd1 Hview HPS Hents]
            · iunfold swift.descsStopped
              iexists dm1, γdc, Mc
              iframe
              iframe Hdm1 Hpool
            ihave Hds : swift.descsStopped x.γd (swift.descDF (x.DR γ bc.2)) (swift.stopPS x bc.2) rp
                $$ [Hds]
            · rw [Hbc]; iexact Hds
            ihave Hep : swift.epStoppedXc γ x rp (sint.Z cb).toNat $$ [Hb2 Hst2 HState Hrc2 Htok
                Hxp Hxe Hrm Hds Hout Hhs Hfz Hfq]
            · iunfold swift.epStoppedXc
              iexists bw, st0, stp, stpX', bc
              iframe
              ipureintro; exact Hbc
            imodintro
            iapply HΦ
            isplitl [Hseq Hdr Hrf Hpd Hrl Hbal Hcb Hstat Hhd Hhdl Hhdc Hpr Hpm Hk Hks Hhl Hhls Hpe Hpes
              Hls0 Hw Hep]
            · iunfold swift.recInvB
              iframe Hd Hsc Hrl Hseq Hdr Hrf Hep
              iexists ld, v, M0, bs, hd, w
              isplitr [Hpd]
              · iunfold swift.runSt
                iframe
                isplitl [Hpm]
                · iunfold swift.propsOwn; iframe Hpm Hpms
                iframe Hlso Hlb
                ipureintro; exact Hok2
              · iframe Hpd; ipureintro; exact Hn
            iexists ⟨(sint.Z cb).toNat, xs'.filterMap (fun a => E4[(sint.Z a).toNat]?)⟩
            iframe Hrep
            isplitl []
            · iunfold swift.ackObj
              iexists rep, bl, cb, g1, g2, g3, g4, xs'.filterMap (fun a => cmL[(sint.Z a).toNat]?),
                xs'.filterMap (fun a => dpL[(sint.Z a).toNat]?)
              iframe Hp Hg1 Hg2 Hg3 Hg4 HRo2
              ipureintro
              have hcb' : 0 ≤ sint.Z cb := by rw [← Hn.2.2.2.1]; exact hcb0
              refine ⟨Hrep, by rw [show ((sint.Z cb).toNat : Int) = sint.Z cb by omega], ?_, ?_⟩
              · rw [hlenC, hlenR]
              · rw [hlenD, hlenR]
            isplitl []
            · iunfold swift.ackBal; iexists rep, cb, g1, g2, g3, g4; iexact Hp
            ipureintro
            refine ⟨rfl, ⟨?_, ?_⟩⟩
            · simp only [List.length_map] at HE4len
              show (xs'.filterMap (fun a => E4[(sint.Z a).toNat]?)).length < 2 ^ 62
              rw [hlenR, ← hpl]; omega
            · -- round N6: `cmd.wf` from the witnesses (`cmdIs`), `depWf` from the sources (D75 (2))
              intro e he
              refine ⟨(hwfW e he).1, ?_⟩
              show e.dep.length < 2 ^ 62
              have he4 : e ∈ E4 := hRs.subset he
              rw [← List.take_append_drop E3.length E4] at he4
              rcases List.mem_append.mp he4 with h | h
              · rw [hE3t] at h
                have hw : (e ∈ XS ∨ e ∈ S) → e.dep.length < 2 ^ 62 := fun hx => by
                  by_cases h0 : e.phase.toNat = 0
                  · exact hR1dep e (by rcases hx with hx | hx <;> simp [hx]) h0
                  · exact (hwfW e he).2 h0
                rcases HE3.1 e h with hx | hx | ⟨M, hM, -, hq⟩
                · exact hw (Or.inl hx)
                · exact hw (Or.inr hx)
                · exact (hMf M hM).2.1 _ hq
              · exact (HE4.1 e h).2.2.2

end proof

end Perennial.github_com.imdea_software.swiftpaxos

end
