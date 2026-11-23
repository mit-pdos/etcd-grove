/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/GhostSteps2.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2 (notes/prove-s2-g.md): the specs of the recovery's ghost step resolvers (fork db37a86,
swift/ghost.go): `ghostReport` (a replica's report, `fillNewLeaderAckN`'s end) and
`ghostComputeSync` (the new leader's `MSync`, `handleNewLeaderAckNs`), in the style of
GhostSteps.lean (E's): each builds its event's words (`sp.encP e`) and resolves them on the
node's ghost; the caller's update (`swift.ghostUpd`) runs at the last word. (`ghostCmd`'s
spec is E's `swift.wp_ghostCmd`.)
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- `swift.ackObj` with its ballot `bl` exposed (`ghostReport` resolves `m.Ballot`). -/
def swift.ackObjB (p : Loc) (bl : w32) (a : Nat × sp.Report) : IProp netDistGF :=
  iprop(∃ (rep cb : w32) (ids ph cm dp : GoSlice) (cmL : List state.Command)
      (dpL : List swift.SDep),
    p ↦□ swift.MNewLeaderAckN.mk rep bl cb ids ph cm dp ∗
    ids ↦*□ (a.2.entries.map (fun e => ofCmdId e.id)) ∗
    ph ↦*□ (a.2.entries.map (·.phase)) ∗ cm ↦*□ cmL ∗ dp ↦*□ dpL ∗
    ⌜sint.Z rep = a.1 ∧ sint.Z cb = a.2.cbal ∧ cmL.length = a.2.entries.length ∧
      dpL.length = a.2.entries.length⌝ ∗
    [∗list] i ↦ e ∈ a.2.entries, ∃ (c : state.Command) (sd : swift.SDep),
      ⌜cmL[i]? = some c ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj c sd e)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
instance swift.ackObjB_persistent (p : Loc) (bl : w32) (a : Nat × sp.Report) :
    Persistent (swift.ackObjB p bl a) := by
  unfold swift.ackObjB; infer_instance

theorem swift.ackObjB_ackObj (p : Loc) (bl : w32) (a : Nat × sp.Report) :
    swift.ackObjB p bl a ⊢ swift.ackObj p a := by
  iintro H
  iunfold swift.ackObjB at H
  icases H with ⟨%rep, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, H⟩
  iunfold swift.ackObj
  iexists rep, bl, cb, ids, ph, cm, dp, cmL, dpL
  iexact H

end defs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [client.Assumptions]

set_option goose.wp.extras true

theorem swift.sint_w32_lt (x : w32) : sint.Z x < 2 ^ 31 := by
  have := BitVec.toInt_lt (x := x)
  show x.toInt < _
  simp at this
  omega

/-- `computeSync`'s words. -/
theorem swift.encP_computeSync (b : Nat) (ids : List Nat) :
    sp.encP (.computeSync b ids) =
      [W64 10, sp.natW b, W64 (ids.length : Int)] ++ ids.flatMap (fun r => [sp.natW r]) := by
  simp [sp.encP, sp.listW]

/-- `ghostComputeSync(b, msgs)`: the reports' replicas in `msgs`' order. -/
theorem swift.wp_ghostComputeSync (γ : sp.Names) (k : Nat) (b : w32) (msl : GoSlice) (dq : DFrac)
    (ms : List GoInterface) (reps : List (Nat × sp.Report)) (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗
      msl ↦*{dq} ms ∗ swift.acksIs ms reps ∗
      swift.ghostUpd γ k (.computeSync (sp.bal b) (reps.map Prod.fst)) Q }}
    (App (App (Val (@! swift.ghostComputeSync)) (Val #b)) (Val #msl))
  {{ RET #(); msl ↦*{dq} ms ∗ Q }} := by
  wp_start as ⟨#Hok, %Hb, Hmsl, #Hacks, Hupd⟩
  iunfold swift.acksIs at Hacks
  icases Hacks with ⟨%prs, %Hprs, #Hprs⟩
  obtain ⟨rfl, rfl⟩ := Hprs
  ihave %Hlen := ownSlice_len $$ Hmsl
  simp only [List.length_map] at Hlen
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64)
    [W64 10, sp.natW (sp.bal b), W64 (prs.length : Int)]
  wp_auto
  isplitl []
  · ipureintro
    have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
    have : msl.len = W64 (prs.length : Int) := by have := Hlen.1; word
    simp [sp.natW, sp.bal, h, this]
    try rfl
  iintro %lp ⟨Hl, Hc⟩
  wp_auto
  ihave IH : iprop(∃ (n : w64) (s2 : GoSlice) (mv : GoInterface),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗ "ws" ∷ ws_ptr ↦ s2 ∗
      "Hs" ∷ s2 ↦* ([W64 10, sp.natW (sp.bal b), W64 (prs.length : Int)] ++
        (prs.take (sint.Z n).toNat).flatMap (fun q => [sp.natW q.2.1])) ∗
      "Hc" ∷ ownSliceCap w64 s2 (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (prs.length : Int) ∧
        ∀ q ∈ prs.take (sint.Z n).toNat, q.2.1 < 2 ^ 31⌝) $$ [i m ws Hl Hc]
  · iexists _, _, _
    iframe
    isplitl [Hl]
    · simp; iexact Hl
    ipureintro; exact ⟨by word, by word, by simp⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.Z n < sint.Z msl.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif) | simpa using Hif
    have Hlt : (sint.Z n).toNat < prs.length := by have := Hlen.1; word
    obtain ⟨q, Hq⟩ : ∃ q, prs[(sint.Z n).toNat]? = some q := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left ⟨Hn.1, hlt⟩]
    wp_apply wp_load_slice_index msl (sint.Z n) _ dq
      (interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #q.1) Hn.1 $$ [Hmsl] as Hmsl
    · iframe; ipureintro; rw [List.getElem?_map, Hq]; rfl
    ihave #Hqo := (BigSepL.bigSepL_lookup (Φ := fun _ q => swift.ackObj q.1 q.2) Hq) $$ Hprs
    iunfold swift.ackObj at Hqo
    icases Hqo with ⟨%rep, %bl, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, #Hp, -, -, -, -, %Hqf, -⟩
    iStructNamed Hp
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w64) (t := go.uint64) [sp.natW q.2.1]
    wp_auto
    isplitl []
    · ipureintro
      have h0 : 0 ≤ sint.Z rep := by rw [Hqf.1]; omega
      have h : (((sint.Z rep).toNat : Nat) : Int) = sint.Z rep := Int.toNat_of_nonneg h0
      rw [show q.2.1 = (sint.Z rep).toNat by omega]
      simp [sp.natW, h]
      try rfl
    iintro %lq ⟨Hlq, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hs Hc Hlq] as %s3 ⟨Hs, Hc, -⟩
    · iframe
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    isplitl [Hs]
    · have Hsucc : (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 := by word
      rw [Hsucc, List.take_succ, Hq]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton,
        List.append_assoc]
      iexact Hs
    ipureintro
    refine ⟨by word, by word, ?_⟩
    have Hsucc : (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 := by word
    rw [Hsucc, List.take_succ, Hq]
    intro q' hq'
    rcases List.mem_append.mp hq' with h | h
    · exact Hn.2.2 q' h
    · simp only [Option.toList_some, List.mem_singleton] at h
      subst h
      have := Hqf.1
      have := swift.sint_w32_lt rep
      omega
  · have hge : ¬ sint.Z n < sint.Z msl.len := by
      first | exact Hif | simpa using Hif
    have hk : (sint.Z n).toNat = prs.length := by have := Hlen.1; word
    try rw [if_pos (by simp [hge])]
    try wp_auto
    have hfull : prs.take (sint.Z n).toNat = prs := by
      rw [hk, List.take_of_length_le (Nat.le_refl _)]
    have Hall := Hn.2.2
    rw [hfull] at Hall
    ihave Hs : s2 ↦* ([W64 10, sp.natW (sp.bal b), W64 (prs.length : Int)] ++
        prs.flatMap (fun q => [sp.natW q.2.1])) $$ [Hs]
    · iExactEq Hs; rw [hfull]
    have hwf : sp.PEvWf (.computeSync (sp.bal b) ((prs.map Prod.snd).map Prod.fst)) := by
      refine ⟨by have := swift.bal_lt b; omega, by simp; have := Hlen.1; word, ?_⟩
      intro r hr
      simp only [List.map_map, List.mem_map] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      have := Hall q hq
      simp only [Function.comp]
      omega
    wp_bind (App (Val (@! client.GhostStep)) (Val _))
    iapply (swift.ghostStep_slice γ k _ Q hwf _ _)
    iframe Hpkg2 Hok Hupd
    isplitl [Hs]
    · iExactEq Hs
      rw [swift.encP_computeSync]
      simp [List.flatMap_map]
    iintro HQ
    try wp_auto
    iapply HΦ
    iframe

/-- `report`'s words. -/
theorem swift.encP_report (b : Nat) (R : sp.Report) :
    sp.encP (.report b R) =
      [W64 9, sp.natW b, sp.natW R.cbal, W64 (R.entries.length : Int)] ++
        R.entries.flatMap sp.repEntryW := by
  simp [sp.encP, sp.listW]

/-- `ghostReport(m)`: the report's ballot, `cballot`, then each entry's id, phase, command and
dependencies (`sp.repEntryW`). -/
theorem swift.wp_ghostReport (γ : sp.Names) (k : Nat) (p : Loc) (bl : w32) (a : Nat × sp.Report)
    (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z bl⌝ ∗ swift.ackObjB p bl a ∗
      swift.ghostUpd γ k (.report (sp.bal bl) a.2) Q }}
    (App (Val (@! swift.ghostReport)) (Val #p))
  {{ RET #(); Q }} := by
  wp_start as ⟨#Hok, %Hb, #Hobj, Hupd⟩
  iunfold swift.ackObjB at Hobj
  icases Hobj with ⟨%rep, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, #Hp, #Hids, #Hph, #Hcm, #Hdp,
    %Hqf, #Hents⟩
  ihave %Hidl := ownSlice_len $$ Hids
  ihave %Hphl := ownSlice_len $$ Hph
  ihave %Hcml := ownSlice_len $$ Hcm
  ihave %Hdpl := ownSlice_len $$ Hdp
  simp only [List.length_map] at Hidl Hphl
  ihave #Hp2 := Hp
  iStructNamed Hp2
  have hcb0 : 0 ≤ sint.Z cb := by rw [Hqf.2.1]; omega
  have hcb31 : a.2.cbal < 2 ^ 31 := by
    have := Hqf.2.1; have := swift.sint_w32_lt cb; omega
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64)
    [W64 9, sp.natW (sp.bal bl), sp.natW a.2.cbal, W64 (a.2.entries.length : Int)]
  wp_auto
  isplitl []
  · ipureintro
    have h : (((sint.Z bl).toNat : Nat) : Int) = sint.Z bl := Int.toNat_of_nonneg Hb
    have hc : ((a.2.cbal : Nat) : Int) = sint.Z cb := Hqf.2.1.symm
    have : ids.len = W64 (a.2.entries.length : Int) := by have := Hidl.1; word
    simp [sp.natW, sp.bal, h, hc, this]
    try rfl
  iintro %lp ⟨Hl, Hc⟩
  wp_auto
  rename_i gi_ptr
  irename: (typedPointsto gi_ptr (Perennial.zero_val w64) (DFrac.own 1)) => Hgi
  ihave IH : iprop(∃ (n gv : w64) (s2 : GoSlice),
      "i" ∷ i_ptr ↦ n ∗ "Hgi" ∷ gi_ptr ↦ gv ∗ "ws" ∷ ws_ptr ↦ s2 ∗
      "Hs" ∷ s2 ↦* ([W64 9, sp.natW (sp.bal bl), sp.natW a.2.cbal,
          W64 (a.2.entries.length : Int)] ++
        (a.2.entries.take (sint.Z n).toNat).flatMap sp.repEntryW) ∗
      "Hc" ∷ ownSliceCap w64 s2 (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (a.2.entries.length : Int) ∧
        ∀ e ∈ a.2.entries.take (sint.Z n).toNat, sp.EntryWf e⌝) $$ [i Hgi ws Hl Hc]
  · iexists _, _, _
    iframe
    isplitl [Hl]
    · simp; iexact Hl
    ipureintro; exact ⟨by word, by word, by simp⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.Z n < sint.Z ids.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif) | simpa using Hif
    have Hlt : (sint.Z n).toNat < a.2.entries.length := by have := Hidl.1; word
    obtain ⟨e, He⟩ : ∃ e, a.2.entries[(sint.Z n).toNat]? = some e :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    ihave #Hent := (BigSepL.bigSepL_lookup (Φ := fun i e => iprop(∃ (c : state.Command)
      (sd : swift.SDep), ⌜cmL[i]? = some c ∧ dpL[i]? = some sd⌝ ∗
      swift.repEntryObj c sd e)) He) $$ Hents
    icases Hent with ⟨%c, %sd, %hcsd, #He⟩
    iunfold swift.repEntryObj at He
    icases He with ⟨%vs, %hc, #Hvs, #Hsd⟩
    ihave %Hvsl := ownSlice_len $$ Hvs
    ihave %Hsdl := ownSlice_len $$ Hsd
    simp only [List.length_map] at Hsdl
    have hb1 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ids.len := ⟨Hn.1, hlt⟩
    have hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ph.len := by
      constructor <;> (have := Hphl.1; have := Hidl.1; word)
    have hb3 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z cm.len := by
      constructor <;> (have := Hcml.1; have := Hidl.1; have := Hqf.2.2.1; word)
    have hb4 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z dp.len := by
      constructor <;> (have := Hdpl.1; have := Hidl.1; have := Hqf.2.2.2; word)
    try rw [ite_eq_left hb1]
    wp_apply wp_load_slice_index ids (sint.Z n) _ DFrac.discard (ofCmdId e.id) Hn.1 $$ [] as -
    · iframe Hids; ipureintro; rw [List.getElem?_map, He]; rfl
    try wp_auto
    try rw [ite_eq_left hb1]
    wp_apply wp_load_slice_index ids (sint.Z n) _ DFrac.discard (ofCmdId e.id) Hn.1 $$ [] as -
    · iframe Hids; ipureintro; rw [List.getElem?_map, He]; rfl
    wp_apply swift.wp_ghostId $$ [Hs Hc] as %s3 ⟨Hs, Hc⟩
    · iframe
    try wp_auto
    try rw [ite_eq_left hb2]
    wp_apply wp_load_slice_index ph (sint.Z n) _ DFrac.discard e.phase Hn.1 $$ [] as -
    · iframe Hph; ipureintro; rw [List.getElem?_map, He]; rfl
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w64) (t := go.uint64) [e.phase]
    try wp_auto
    isplitl []
    · ipureintro; simp; try rfl
    iintro %lq ⟨Hlq, -⟩
    try wp_auto
    wp_apply wp_slice_append $$ [Hs Hc Hlq] as %s4 ⟨Hs, Hc, -⟩
    · iframe
    try wp_auto
    try rw [ite_eq_left hb3]
    wp_apply wp_load_slice_index cm (sint.Z n) _ DFrac.discard c Hn.1 $$ [] as -
    · iframe Hcm; ipureintro; exact hcsd.1
    rw [hc]
    wp_apply swift.wp_ghostCmd $$ [Hs Hc] as %s5 ⟨Hs, Hc, -⟩
    · iframe; iexact Hvs
    try wp_auto
    try rw [ite_eq_left hb4]
    icases ownSlice_elem_acc (V := swift.SDep) (sint.Z n) sd dp _ dpL Hn.1 hcsd.2 $$ Hdp
      with ⟨Hsde, -⟩
    iStructNamed Hsde
    try wp_auto
    wp_apply swift.wp_ghostIds $$ [Hs Hc] as %s6 ⟨Hs, Hc, -⟩
    · iframe; iexact Hsd
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    have Hsucc : (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 := by word
    isplitl [Hs]
    · rw [Hsucc, List.take_succ, He]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton,
        List.append_assoc, List.map_map, sp.repEntryW, List.singleton_append, List.cons_append]
      iExactEq Hs
      simp [Function.comp_def]
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [Hsucc, List.take_succ, He]
    intro e' he'
    rcases List.mem_append.mp he' with h | h
    · exact Hn.2.2 e' h
    · simp only [Option.toList_some, List.mem_singleton] at h
      subst h
      refine ⟨?_, ?_⟩
      · show e'.cmd.val.length < 2 ^ 64; have := Hvsl.1; word
      · have := Hsdl.1; word
  · have hge : ¬ sint.Z n < sint.Z ids.len := by
      first | exact Hif | simpa using Hif
    have hk : (sint.Z n).toNat = a.2.entries.length := by have := Hidl.1; word
    try rw [if_pos (by simp [hge])]
    try wp_auto
    have hfull : a.2.entries.take (sint.Z n).toNat = a.2.entries := by
      rw [hk, List.take_of_length_le (Nat.le_refl _)]
    have Hall := Hn.2.2
    rw [hfull] at Hall
    ihave Hs : s2 ↦* ([W64 9, sp.natW (sp.bal bl), sp.natW a.2.cbal,
          W64 (a.2.entries.length : Int)] ++ a.2.entries.flatMap sp.repEntryW) $$ [Hs]
    · iExactEq Hs; rw [hfull]
    have hwf : sp.PEvWf (.report (sp.bal bl) a.2) :=
      ⟨by have := swift.bal_lt bl; omega, by omega, by have := Hidl.1; word, Hall⟩
    wp_bind (App (Val (@! client.GhostStep)) (Val _))
    iapply (swift.ghostStep_slice γ k _ Q hwf _ _)
    iframe Hpkg2 Hok Hupd
    isplitl [Hs]
    · iExactEq Hs
      rw [swift.encP_report]
    iintro HQ
    try wp_auto
    iapply HΦ
    iexact HQ

end proof

end Perennial.github_com.imdea_software.swiftpaxos
