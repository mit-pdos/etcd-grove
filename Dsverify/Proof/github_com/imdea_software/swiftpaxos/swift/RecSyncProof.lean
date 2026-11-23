/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecSyncProof.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`recoveredSync`'s proof (spec: Proof/swift/RecSync.lean), phase by phase as the Go function:
the reports, sorted; `U`; rule 1; `R`; rule 2; the closure (with `best`); rule 3b; rule 4; the
order; the `MSync`'s maps along the order.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSyncPure2
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecKept
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSyncPure3
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHashPure

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section helpers
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- The reports' pointers determine their replicas. -/
theorem swift.acks_ptrOk (prs : List swift.rec.Pr) :
    ([∗list] q ∈ prs, swift.ackObj q.1 q.2 : IProp netDistGF) ⊢ ⌜swift.rec.PtrOk prs⌝ := by
  iintro #H
  unfold swift.rec.PtrOk
  iapply (pure_forall (PROP := IProp netDistGF)).2
  iintro %q1
  iapply (pure_forall (PROP := IProp netDistGF)).2
  iintro %hq1
  iapply (pure_forall (PROP := IProp netDistGF)).2
  iintro %q2
  iapply (pure_forall (PROP := IProp netDistGF)).2
  iintro %hq2
  iapply (pure_forall (PROP := IProp netDistGF)).2
  iintro %he
  ihave #H1 := (BigSepL.bigSepL_mem (Φ := fun q => swift.ackObj q.1 q.2) hq1) $$ H
  ihave #H2 := (BigSepL.bigSepL_mem (Φ := fun q => swift.ackObj q.1 q.2) hq2) $$ H
  iunfold swift.ackObj at H1 H2
  icases H1 with ⟨%r1, %b1, %c1, %i1, %p1, %m1, %d1, %cl1, %dl1, #Hp1, -, -, -, -, %Hf1, -⟩
  icases H2 with ⟨%r2, %b2, %c2, %i2, %p2, %m2, %d2, %cl2, %dl2, #Hp2, -, -, -, -, %Hf2, -⟩
  rw [he]
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Hp1 Hp2
  ipureintro
  cases Heq
  have := Hf1.1.symm.trans Hf2.1
  omega

end helpers

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [slices.Assumptions]

set_option maxHeartbeats 4000000 in
theorem swift.Replica.recoveredSync.wp_proof
    (wp_SortFunc : slices.SortFunc.specOn (hG := hG))
    (wp_sortedIds : swift.sortedIds.specC (hG := hG))
    (wp_recReaches : swift.recReaches.specM (hG := hG))
    (wp_recOrder : swift.recOrder.specI (hG := hG))
    (wp_inConflict : swift.inConflict.specI (hG := hG))
    (wp_keysOf : swift.keysOf.specI (hG := hG))
    (wp_Contains : swift.Dep.Contains.specI (hG := hG))
    (wp_Equals : swift.Dep.Equals.specG (hG := hG))
    (wp_Leader : replica.Leader.spec (hG := hG))
    (wp_AQ : replica.QuorumSystem.AQ.spec (hG := hG))
    (wp_qContains : replica.Quorum.Contains.spec (hG := hG))
    (wp_newLKI : swift.lki.newLightKeyInfo.spec (hG := hG))
    (wp_lkiAdd : swift.lki.lightKeyInfo.add.spec (hG := hG))
    (wp_lkiGet : swift.lki.lightKeyInfo.getConflictCmds.spec (hG := hG)) :
    swift.Replica.recoveredSync.specI (hG := hG) := by
  intro rp rr qs N me bal dq msl ms reps
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hrr, #HN, #Hme, #Hqs, #HQS, Hbal, #Hmsl, #Hacks, %Hok⟩
  iunfold swift.acksIs at Hacks
  icases Hacks with ⟨%prs, %Hprs, #Hprs⟩
  obtain ⟨rfl, rfl⟩ := Hprs
  ihave %Hmsll := ownSlice_len $$ Hmsl
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.GoType.SliceType (go.GoType.PointerType swift.MNewLeaderAckN.ty))))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType swift.MNewLeaderAckN.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %asl0 ⟨Has0, Hacap0⟩
  wp_auto
  -- the reports, collected (`acks`), with the highest `cballot`
  ihave HI0 : (∃ (i : w64) (asl : GoSlice) (mc : w32) (mv : GoInterface),
      "i" ∷ i_ptr ↦ i ∗ "msg" ∷ msg_ptr ↦ mv ∗ "acks" ∷ acks_ptr ↦ asl ∗
      "Has" ∷ asl ↦* ((prs.take (sint.nat i)).map Prod.fst) ∗
      "Hacap" ∷ ownSliceCap Loc asl (DFrac.own 1) ∗ "maxCbal" ∷ maxCbal_ptr ↦ mc ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z msl.len ∧
        sint.Z mc = ((prs.take (sint.nat i)).map (fun q => (q.2.2.cbal : Int))).foldl max (-1)⌝ :
      IProp netDistGF) $$ [i msg acks Has0 Hacap0 maxCbal]
  · iexists W64 0, _, _, _
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil]
    iframe
    ipureintro
    refine ⟨by word, by word, rfl⟩
  wp_for HI0
  wp_if_destruct
  · simp only [List.length_map] at Hmsll
    have hil : sint.nat i < prs.length := by word
    obtain ⟨q, hq⟩ : ∃ q, prs[sint.nat i]? = some q := ⟨_, List.getElem?_eq_getElem hil⟩
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z msl.len from ⟨Hi.1, Hif⟩)]
    wp_apply (wp_load_slice_index (V := GoInterface) msl (sint.Z i) _ _
      (interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #q.1) Hi.1) $$ [Hmsl] as -
    · iframe #; ipureintro
      rw [show (sint.Z i).toNat = sint.nat i by word, List.getElem?_map, hq]; rfl
    wp_bind (App (Val (GoInstruction (CompositeLiteral
      (go.GoType.SliceType (go.GoType.PointerType swift.MNewLeaderAckN.ty))))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType swift.MNewLeaderAckN.ty) [q.1]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Has Hacap Hlsl] as %nsl ⟨Has, Hacap, -⟩
    · iframe
    ihave #Hq := (BigSepL.bigSepL_lookup (Φ := fun _ q => swift.ackObj q.1 q.2) hq) $$ Hprs
    iunfold swift.ackObj at Hq
    icases Hq with ⟨%rep, %bl, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, #Hp, #Hids, #Hph, #Hcm, #Hdp,
      %Hqf, #Hents⟩
    ihave #Hp2 := Hp
    iStructNamed Hp2
    wp_auto
    have htake : prs.take (sint.nat (i + W64 1)) = prs.take (sint.nat i) ++ [q] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, hq]; rfl
    have hfold : ((prs.take (sint.nat i) ++ [q]).map (fun q => (q.2.2.cbal : Int))).foldl max (-1) =
        max (sint.Z mc) (sint.Z cb) := by
      rw [List.map_append, List.foldl_append, ← Hi.2.2, Hqf.2.1]; rfl
    wp_if_destruct
    · wp_for_post
      iframe
      iexists i + W64 1, _, cb, _
      rw [htake, show List.map Prod.fst (List.take (sint.nat i) prs ++ [q]) =
        List.map Prod.fst (List.take (sint.nat i) prs) ++ [q.1] by simp]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [hfold]; omega
    · wp_for_post
      iframe
      iexists i + W64 1, _, mc, _
      rw [htake, show List.map Prod.fst (List.take (sint.nat i) prs ++ [q]) =
        List.map Prod.fst (List.take (sint.nat i) prs) ++ [q.1] by simp]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [hfold]; omega
  · -- all reports collected
    simp only [List.length_map] at Hmsll
    have hilen : sint.nat i = prs.length := by word
    rw [hilen, List.take_length] at Hi ⊢
    -- sorted by replica
    ihave %Hptr := swift.acks_ptrOk prs $$ Hprs
    have hlen62 : (prs.map Prod.fst).length ≤ 2 ^ 62 := by
      have := Hok.len; simp only [List.length_map] at this ⊢; have := Hok.hN; omega
    wp_apply (wp_SortFunc (E := Loc) (swift.rec.RepLt prs)
      (fun p => iprop(∃ a, ⌜(p, a) ∈ prs⌝ ∗ swift.ackObj p a)) asl _ (prs.map Prod.fst)
      (swift.rec.repLt_swo prs)) $$ [Has]
      as %ps' ⟨Has, %Hperm, %Hsorted⟩
    · iframe
      isplitr
      · ipureintro; exact hlen62
      isplitl []
      · rw [BigSepL.bigSepL_map]
        iapply (BigSepL.bigSepL_mono (PROP := IProp netDistGF) (l := prs)
          (Φ := fun (_ : Nat) (q : swift.rec.Pr) => swift.ackObj q.1 q.2) ?_) $$ Hprs
        intro k q hq
        iintro #Hq
        iexists q.2
        isplitr
        · ipureintro; exact List.mem_of_getElem? hq
        · iexact Hq
      · iunfold slices.cmpImplementsOn
        iintro %x %y
        imodintro
        iintro %Φc ⟨⟨%a, %ha, #Ha⟩, ⟨%b, %hb, #Hb⟩⟩ HΦc
        iunfold swift.ackObj at Ha Hb
        icases Ha with ⟨%ra, %-, %-, %-, %-, %-, %-, %-, %-, #Hpa, -, -, -, -, %Hfa, -⟩
        icases Hb with ⟨%rb, %-, %-, %-, %-, %-, %-, %-, %-, #Hpb, -, -, -, -, %Hfb, -⟩
        iStructNamedSuffix Hpa "a"
        iStructNamedSuffix Hpb "b"
        have hra : swift.rec.repOf prs x = sint.Z ra := by
          rw [swift.rec.repOf_of_mem Hptr ha]; exact Hfa.1.symm
        have hrb : swift.rec.repOf prs y = sint.Z rb := by
          rw [swift.rec.repOf_of_mem Hptr hb]; exact Hfb.1.symm
        wp_auto
        wp_if_destruct
        · iapply HΦc; ipureintro; unfold swift.rec.RepLt; rw [hra, hrb]; simp [Hif]
        · wp_if_destruct
          · iapply HΦc; ipureintro; unfold swift.rec.RepLt; rw [hra, hrb]; simp; omega
          · iapply HΦc; ipureintro; unfold swift.rec.RepLt; rw [hra, hrb]; simp; omega
    -- the model's sorted reports `acks`
    obtain ⟨prsA, hAperm, hAfst, hAsnd⟩ := swift.rec.sorted_acks prs Hptr Hok.nodup ps' Hperm Hsorted
    subst hAfst
    ihave #HprsA : ([∗list] q ∈ prsA, swift.ackObj q.1 q.2) $$ [Hprs]
    · iapply (BigSepL.bigSepL_perm (Φ := fun q : swift.rec.Pr => swift.ackObj q.1 q.2) hAperm).2
      iexact Hprs
    have hne : prs ≠ [] := by
      intro h; apply Hok.ne; rw [h]; rfl
    have hmc : sint.Z mc = (sp.recMaxC (sp.recAcks (prs.map Prod.snd)) : Int) := by
      rw [Hi.2.2, swift.rec.maxC_eq prs prsA hne hAperm, hAsnd]
    -- `U`
    wp_bind (App (Val (GoInstruction (CompositeLiteral
      (go.GoType.SliceType (go.GoType.PointerType swift.MNewLeaderAckN.ty))))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType swift.MNewLeaderAckN.ty) []
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %usl0 ⟨Hus0, Hucap0⟩
    wp_auto
    ihave %HAlen := ownSlice_len $$ Has
    obtain ⟨maxC, hmaxC⟩ : ∃ m, m = sp.recMaxC (sp.recAcks (prs.map Prod.snd)) := ⟨_, rfl⟩
    rw [← hmaxC] at hmc
    obtain ⟨pU, hpU⟩ : ∃ f : swift.rec.Pr → Bool, f = fun q => q.2.2.cbal == maxC := ⟨_, rfl⟩
    ihave HIU : (∃ (j : w64) (usl : GoSlice) (av : Loc),
        "j" ∷ i_ptr ↦ j ∗ "a" ∷ a_ptr ↦ av ∗ "U" ∷ U_ptr ↦ usl ∗
        "Hus" ∷ usl ↦* (((prsA.take (sint.nat j)).filter pU).map Prod.fst) ∗
        "Hucap" ∷ ownSliceCap Loc usl (DFrac.own 1) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z asl.len⌝ : IProp netDistGF)
      $$ [i a U Hus0 Hucap0]
    · iexists W64 0, _, _
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil, List.map_nil]
      iframe
      ipureintro; word
    simp only [List.length_map] at HAlen
    wp_for HIU
    wp_if_destruct
    · have hjl : sint.nat j < prsA.length := by word
      obtain ⟨q, hq⟩ : ∃ q, prsA[sint.nat j]? = some q := ⟨_, List.getElem?_eq_getElem hjl⟩
      rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z asl.len from ⟨Hj.1, Hif⟩)]
      wp_apply (wp_load_slice_index (V := Loc) asl (sint.Z j) _ _ q.1 Hj.1) $$ [Has] as Has
      · iframe; ipureintro
        rw [show (sint.Z j).toNat = sint.nat j by word, List.getElem?_map, hq]; rfl
      ihave #Hq := (BigSepL.bigSepL_lookup (Φ := fun _ q => swift.ackObj q.1 q.2) hq) $$ HprsA
      iunfold swift.ackObj at Hq
      icases Hq with ⟨%rep, %bl, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, #Hp, -, -, -, -, %Hqf, -⟩
      iStructNamed Hp
      wp_auto
      have htake : prsA.take (sint.nat (j + W64 1)) = prsA.take (sint.nat j) ++ [q] := by
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hq]; rfl
      wp_if_destruct
      · -- `q` of the highest `cballot`: in `U`
        have hpq : pU q = true := by
          simp only [hpU, beq_iff_eq]
          have := Hqf.2.1; rw [Hif] at this; rw [hmc] at this; omega
        wp_bind (App (Val (GoInstruction (CompositeLiteral
          (go.GoType.SliceType (go.GoType.PointerType swift.MNewLeaderAckN.ty))))) (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType swift.MNewLeaderAckN.ty) [q.1]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %lsl ⟨Hlsl, -⟩
        wp_auto
        wp_apply wp_slice_append $$ [Hus Hucap Hlsl] as %nsl ⟨Hus, Hucap, -⟩
        · iframe
        wp_for_post
        iframe
        iexists j + W64 1, _, _
        rw [htake, List.filter_append, List.filter_cons, hpq]
        simp only [↓reduceIte, List.filter_nil, List.map_append, List.map_cons, List.map_nil]
        iframe
        ipureintro; word
      · have hpq : pU q = false := by
          simp only [hpU, beq_eq_false_iff_ne, ne_eq]
          intro h; apply Hif
          have := Hqf.2.1; rw [h, ← hmc] at this
          exact (BitVec.toInt_inj).mp this
        wp_for_post
        iframe
        iexists j + W64 1, _, _
        rw [htake, List.filter_append, List.filter_cons, hpq]
        simp only [Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
        iframe
        ipureintro; word
    · -- `U`: the reports of the highest `cballot`
      have hjlen : sint.nat j = prsA.length := by word
      rw [hjlen, List.take_length]
      -- the old leader and its fast quorum
      have hmc0 : 0 ≤ sint.Z mc := by rw [hmc]; omega
      wp_apply (wp_Leader mc (W64 N))
      · ipureintro; have := Hok.hN; constructor <;> word
      wp_apply (wp_AQ qs N mc) as %aqp #Haq
      · iframe #; ipureintro; exact hmc0
      wp_apply (wp_map_make1 (K := swift.CommandId) (V := Loc)) as %km0 Hkm
      obtain ⟨oldL, hoLd⟩ : ∃ l, l = sp.leaderOf N maxC := ⟨_, rfl⟩
      have hN := Hok.hN
      have hoL : sint.Z (BitVec.srem mc (W32 (sint.Z (W64 (N : Int))))) = (oldL : Int) := by
        rw [show sint.Z (W64 (N : Int)) = (N : Int) by word,
          replica.quorum.leader_val mc N ⟨by omega, by omega⟩ hmc0, hmc, hoLd]
        simp only [sp.leaderOf, Int.natCast_emod]
      obtain ⟨prsU, hprsU⟩ : ∃ l, l = prsA.filter pU := ⟨_, rfl⟩
      rw [← hprsU]
      ihave %HUlen := ownSlice_len $$ Hus
      simp only [List.length_map] at HUlen
      ihave HIL : (∃ (j : w64) (av : Loc) (li : Bool),
          "j" ∷ i_ptr ↦ j ∗ "a" ∷ a_ptr ↦ av ∗ "leaderInU" ∷ leaderInU_ptr ↦ li ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z usl.len ∧
            li = (prsU.take (sint.nat j)).any (fun q => q.2.1 == oldL)⌝ : IProp netDistGF)
        $$ [i a leaderInU]
      · iexists W64 0, _, false
        iframe
        ipureintro; refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
      wp_for HIL
      wp_if_destruct
      · have hjl : sint.nat j < prsU.length := by word
        obtain ⟨q, hq⟩ : ∃ q, prsU[sint.nat j]? = some q := ⟨_, List.getElem?_eq_getElem hjl⟩
        have hqA : q ∈ prsA := by
          have := List.mem_of_getElem? hq; rw [hprsU] at this; exact (List.mem_filter.mp this).1
        rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z usl.len from ⟨Hj.1, Hif⟩)]
        wp_apply (wp_load_slice_index (V := Loc) usl (sint.Z j) _ _ q.1 Hj.1) $$ [Hus] as Hus
        · iframe; ipureintro
          rw [show (sint.Z j).toNat = sint.nat j by word, List.getElem?_map, hq]; rfl
        ihave #Hq := (BigSepL.bigSepL_mem (Φ := fun q : swift.rec.Pr => swift.ackObj q.1 q.2) hqA) $$ HprsA
        iunfold swift.ackObj at Hq
        icases Hq with ⟨%rep, %bl, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, #Hp, -, -, -, -, %Hqf, -⟩
        iStructNamed Hp
        wp_auto
        have htake : prsU.take (sint.nat (j + W64 1)) = prsU.take (sint.nat j) ++ [q] := by
          rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hq]; rfl
        wp_if_destruct
        · wp_for_post
          iframe
          iexists j + W64 1, _, true
          iframe
          ipureintro; refine ⟨by word, by word, ?_⟩
          rw [htake, List.any_append]
          have : q.2.1 = oldL := by
            have h1 := Hqf.1; rw [hoL] at h1; omega
          simp [this]
        · wp_for_post
          iframe
          iexists j + W64 1, _, li
          iframe
          ipureintro; refine ⟨by word, by word, ?_⟩
          rw [htake, List.any_append, Hj.2.2]
          have : q.2.1 ≠ oldL := by
            intro h; apply Hif
            apply BitVec.eq_of_toInt_eq
            have h1 := Hqf.1
            change sint.Z rep = sint.Z _
            rw [hoL, h1, h]
          simp [this]
      · have hjlen : sint.nat j = prsU.length := by word
        rw [hjlen, List.take_length] at Hj
        have hli : li = prsU.any (fun q => q.2.1 == oldL) := Hj.2.2
        -- rule 1
        ihave Hkept := swift.kept_empty km0 (fun _ => false) $$ Hkm
        ihave HI1 : (∃ (j : w64) (av : Loc) (k : sp.Kept),
            "j" ∷ i_ptr ↦ j ∗ "a" ∷ a_ptr ↦ av ∗ "Hkept" ∷ swift.keptOwn km0 k (fun _ => false) ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z usl.len ∧
              k = (prsU.take (sint.nat j)).foldl
                (fun k q => q.2.2.entries.foldl (swift.rec.r1e oldL q.2) k) []⌝ : IProp netDistGF)
          $$ [i a Hkept]
        · iexists W64 0, _, []
          iframe
          ipureintro; refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
        wp_for HI1
        wp_if_destruct
        · have hjl : sint.nat j < prsU.length := by word
          obtain ⟨q, hq⟩ : ∃ q, prsU[sint.nat j]? = some q := ⟨_, List.getElem?_eq_getElem hjl⟩
          have hqA : q ∈ prsA := by
            have := List.mem_of_getElem? hq; rw [hprsU] at this; exact (List.mem_filter.mp this).1
          rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z usl.len from ⟨Hj.1, Hif⟩)]
          wp_apply (wp_load_slice_index (V := Loc) usl (sint.Z j) _ _ q.1 Hj.1) $$ [Hus] as Hus
          · iframe; ipureintro
            rw [show (sint.Z j).toNat = sint.nat j by word, List.getElem?_map, hq]; rfl
          ihave #Hq := (BigSepL.bigSepL_mem (Φ := fun q : swift.rec.Pr => swift.ackObj q.1 q.2) hqA) $$ HprsA
          iunfold swift.ackObj at Hq
          icases Hq with ⟨%rep, %bl, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, #Hp, #Hids, #Hph, #Hcm,
            #Hdp, %Hqf, #Hents⟩
          iStructNamed Hp
          generalize hjp : i_ptr = jp
          wp_auto
          rename_i gip
          irename i => Hrng
          irename i => Hgi
          ihave %Hidsl := ownSlice_len $$ Hids
          ihave %Hphl := ownSlice_len $$ Hph
          simp only [List.length_map] at Hidsl Hphl
          ihave HI1' : (∃ (ii : w64) (cid : swift.CommandId) (gi : w64) (k' : sp.Kept),
              "ii" ∷ i_ptr ↦ ii ∗ "cmdId" ∷ cmdId_ptr ↦ cid ∗ "gi" ∷ gip ↦ gi ∗
              "Hkept" ∷ swift.keptOwn km0 k' (fun _ => false) ∗
              "%Hii" ∷ ⌜0 ≤ sint.Z ii ∧ sint.Z ii ≤ sint.Z ids.len ∧
                k' = (q.2.2.entries.take (sint.nat ii)).foldl (swift.rec.r1e oldL q.2) k⌝ :
              IProp netDistGF) $$ [Hrng cmdId Hgi Hkept]
          · iexists W64 0, _, _, k
            iframe
            ipureintro; refine ⟨by word, by word, ?_⟩
            rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
          wp_for HI1'
          wp_if_destruct
          · have hil : sint.nat ii < q.2.2.entries.length := by word
            obtain ⟨e, he⟩ : ∃ e, q.2.2.entries[sint.nat ii]? = some e :=
              ⟨_, List.getElem?_eq_getElem hil⟩
            rw [ite_eq_left (show 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ids.len from ⟨Hii.1, Hif⟩)]
            wp_apply (wp_load_slice_index (V := swift.CommandId) ids (sint.Z ii) _ _ (ofCmdId e.id)
              Hii.1) $$ [Hids] as -
            · iframe #; ipureintro
              rw [show (sint.Z ii).toNat = sint.nat ii by word, List.getElem?_map, he]; rfl
            have hphb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ph.len := by constructor <;> word
            rw [ite_eq_left hphb]
            wp_apply (wp_load_slice_index (V := w64) ph (sint.Z ii) _ _ e.phase Hii.1) $$ [Hph] as -
            · iframe #; ipureintro
              rw [show (sint.Z ii).toNat = sint.nat ii by word, List.getElem?_map, he]; rfl
            have hrepiff : rep = BitVec.srem mc (W32 (sint.Z (W64 (N : Int)))) ↔ q.2.1 = oldL := by
              constructor
              · intro h; have h1 := Hqf.1; rw [h, hoL] at h1; omega
              · intro h; apply BitVec.eq_of_toInt_eq
                change sint.Z rep = sint.Z _
                rw [hoL, Hqf.1, h]
            have hqP : q ∈ prs := hAperm.mem_iff.mp hqA
            have hph3 := (Hok.ents q.2 (List.mem_map_of_mem hqP) e (List.mem_of_getElem? he)).1
            wp_bind (If (If _ _ _) _ _)
            iapply (wp_wand (Φ := fun v => iprop(⌜v = #(sp.okPhase oldL q.2 e)⌝ ∗
              ph_ptr ↦ e.phase ∗ a_ptr ↦ q.1 ∗
              oldLeader_ptr ↦ BitVec.srem mc (W32 (sint.Z (W64 (N : Int))))))) $$ [ph a oldLeader]
            · wp_if_destruct
              · iframe; ipureintro; congr 1; simp [sp.okPhase, Hif]
              · have h2 : e.phase.toNat ≠ 2 := fun h => Hif (BitVec.eq_of_toNat_eq h)
                wp_if_destruct
                · iframe; ipureintro; congr 1
                  have h3 : e.phase.toNat = 3 := by rw [Hif]; rfl
                  simp [sp.okPhase, h3]
                · have h3 : e.phase.toNat ≠ 3 := fun h => Hif (BitVec.eq_of_toNat_eq h)
                  wp_if_destruct
                  · have hl : q.2.1 = oldL := by
                      have h1 := Hqf.1; rw [hoL] at h1; omega
                    iframe; ipureintro; congr 1
                    simp only [sp.okPhase, h2, h3, hl, beq_self_eq_true, Bool.true_and,
                      Bool.false_or, beq_iff_eq]
                    by_cases h1 : e.phase = W64 1
                    · rw [h1]; simp
                    · have h1' : e.phase.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq h)
                      rw [beq_false_of_ne h1', beq_false_of_ne h2, beq_false_of_ne h3]
                      simp only [Bool.or_false, decide_eq_false_iff_not]; exact h1
                  · have hl : q.2.1 ≠ oldL := fun h => Hif (hrepiff.mpr h)
                    iframe; ipureintro; congr 1
                    simp [sp.okPhase, h2, h3, hl]
            iintro %v ⟨%hv, ph, a, oldLeader⟩
            subst hv
            have htk : (q.2.2.entries.take (sint.nat (ii + W64 1))).foldl (swift.rec.r1e oldL q.2) k =
                swift.rec.r1e oldL q.2 ((q.2.2.entries.take (sint.nat ii)).foldl
                  (swift.rec.r1e oldL q.2) k) e := by
              rw [show sint.nat (ii + W64 1) = sint.nat ii + 1 by word]
              exact swift.rec.foldl_take_succ _ _ _ _ _ he
            cases hok : sp.okPhase oldL q.2 e
            · -- not kept by rule 1
              wp_auto
              wp_for_post
              iframe
              iexists ii + W64 1, _, _, k'
              iframe
              ipureintro
              refine ⟨by word, by word, ?_⟩
              rw [htk, ← Hii.2.2]; unfold swift.rec.r1e; rw [hok]; rfl
            · wp_auto
              iunfold swift.keptOwn at Hkept
              icases Hkept with ⟨%mk, Hm, %Hmk, Hkents⟩
              wp_apply (wp_map_lookup2 _ _ km0 mk (ofCmdId e.id)) $$ Hm as Hm
              have hmke := Hmk.2 (ofCmdId e.id)
              simp only [toCmdId_ofCmdId] at hmke
              -- Go's test: the model's `setIt1`
              wp_bind (If (Val _) (Val #true) _)
              iapply (wp_wand (Φ := fun v => iprop(⌜v = #(swift.rec.setIt1 k' e)⌝ ∗
                e_ptr ↦ (mk !! ofCmdId e.id).getD (Perennial.zero_val Loc) ∗ ph_ptr ↦ e.phase ∗
                swift.keptEnts k' (fun _ => false) mk))) $$ [e ph Hkents]
              · cases hx : mk !! ofCmdId e.id with
                | none =>
                  rw [hx] at hmke
                  have hg : k'.get e.id = none := by
                    cases h : k'.get e.id with
                    | none => rfl
                    | some _ => rw [h] at hmke; cases hmke
                  wp_auto
                  iframe
                  ipureintro; unfold swift.rec.setIt1; rw [hg]
                | some p =>
                  rw [hx] at hmke
                  obtain ⟨old, hold⟩ : ∃ old, k'.get e.id = some old :=
                    Option.isSome_iff_exists.mp hmke.symm
                  icases (BigSepM.bigSepM_lookup_acc
                    (show Iris.Std.PartialMap.get? mk (ofCmdId e.id) = some p from hx)).1
                    $$ Hkents with ⟨⟨%o', %ho', Hre⟩, Hkents⟩
                  simp only [toCmdId_ofCmdId] at ho'
                  rw [hold] at ho'; cases ho'
                  iunfold swift.recOwn at Hre
                  icases Hre with ⟨%pho, %clso, %vso, %dslo, Hpo, #Hvso, Hdslo, %Hpho⟩
                  simp only [Option.getD_some, Option.isSome_some]
                  wp_auto
                  have hset : swift.rec.setIt1 k' e =
                      (decide (pho ≠ W64 3) && decide (e.phase = W64 3)) := by
                    unfold swift.rec.setIt1; rw [hold]
                    show (old.phase != 3 && e.phase.toNat == 3) = _
                    have h1 : (old.phase != 3) = decide (pho ≠ W64 3) := by
                      rw [← Hpho.1, Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_eq]
                      constructor
                      · intro h h'; apply h; rw [h']; rfl
                      · intro h h'; apply h; word
                    have h2 : (e.phase.toNat == 3) = decide (e.phase = W64 3) := by
                      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
                      constructor
                      · intro h; exact BitVec.eq_of_toNat_eq h
                      · intro h; rw [h]; rfl
                    rw [h1, h2]
                  rw [hset]
                  wp_if_destruct
                  · iframe
                    isplitr
                    · ipureintro; congr 1
                    iapply Hkents; iexists old; isplitr
                    · ipureintro; simp [hold]
                    iunfold swift.recOwn; iexists _, clso, vso, dslo
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    iframe Hpo Hvso Hdslo
                    ipureintro; exact Hpho
                  · iframe
                    isplitr
                    · ipureintro; congr 1; simp only [ne_eq, Hif, not_false_eq_true,
                        decide_true, Bool.true_and]
                    iapply Hkents; iexists old; isplitr
                    · ipureintro; simp [hold]
                    iunfold swift.recOwn; iexists _, clso, vso, dslo
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    iframe Hpo Hvso Hdslo
                    ipureintro; exact Hpho
              iintro %v ⟨%hv, e, ph, Hkents⟩
              subst hv
              cases hs : swift.rec.setIt1 k' e
              · -- kept as is
                wp_auto
                wp_for_post
                iframe
                iexists ii + W64 1, _, _, k'
                iframe
                isplitl [Hm Hkents]
                · iapply swift.kept_close km0 k' _ mk Hmk $$ [Hm Hkents]; iframe
                ipureintro
                refine ⟨by word, by word, ?_⟩
                rw [htk, ← Hii.2.2, swift.rec.r1e_keep hok hs]
              · -- set: a new entry from the report
                ihave #He := (BigSepL.bigSepL_lookup (Φ := fun i e => iprop(∃ (c : state.Command)
                  (sd : swift.SDep), ⌜cmL[i]? = some c ∧ dpL[i]? = some sd⌝ ∗
                  swift.repEntryObj c sd e)) he) $$ Hents
                icases He with ⟨%c, %sd, %hcsd, #He⟩
                iunfold swift.repEntryObj at He
                icases He with ⟨%vs, %hc, #Hvs, #Hsd⟩
                have hcml : sint.nat ii < cmL.length := by rw [Hqf.2.2.1]; exact hil
                ihave %Hcml := ownSlice_len $$ Hcm
                ihave %Hdpl := ownSlice_len $$ Hdp
                have hcmb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z cm.len := by
                  constructor <;> word
                wp_auto
                rw [ite_eq_left hcmb]
                wp_apply (wp_load_slice_index (V := state.Command) cm (sint.Z ii) cmL _ c hcmb.1)
                  $$ [Hcm] as -
                · iframe #; ipureintro
                  rw [show (sint.Z ii).toNat = sint.nat ii by word]; exact hcsd.1
                have hdpb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z dp.len := by
                  constructor <;> word
                rw [ite_eq_left hdpb]
                icases ownSlice_elem_acc (V := swift.SDep) (sint.Z ii) sd dp _ dpL hdpb.1
                  (by rw [show (sint.Z ii).toNat = sint.nat ii by word]; exact hcsd.2) $$ Hdp
                  with ⟨Hsde, -⟩
                iStructNamed Hsde
                wp_auto
                wp_apply (wp_mapInsert _ km0 mk (ofCmdId e.id) «$r0_ptr») $$ Hm as Hm
                ihave Hnew : swift.recOwn «$r0_ptr» ⟨e.phase.toNat, e.cmd, e.dep, 0⟩ false $$ [«$r0»]
                · iunfold swift.recOwn
                  iexists e.phase, W64 0, vs, sd.Dep'
                  rw [hc]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  iframe «$r0» Hvs Hsd
                  ipureintro; exact ⟨trivial, hph3, rfl, by omega⟩
                ihave Hrest : swift.keptEnts k' (fun _ => false) (GMap.delete (ofCmdId e.id) mk)
                  $$ [Hkents]
                · cases hx : mk !! ofCmdId e.id with
                  | none => rw [GMap.delete_notin mk _ hx]; iexact Hkents
                  | some p0 =>
                    icases (BigSepM.bigSepM_delete
                      (show Iris.Std.PartialMap.get? mk (ofCmdId e.id) = some p0 from hx)).1
                      $$ Hkents with ⟨-, Hkents⟩
                    iexact Hkents
                ihave Hkept := swift.kept_set km0 k' (fun _ => false) mk (ofCmdId e.id) «$r0_ptr»
                  ⟨e.phase.toNat, e.cmd, e.dep, 0⟩ false Hmk $$ [Hm Hrest Hnew]
                · iframe
                rw [swift.updO_const, toCmdId_ofCmdId]
                wp_for_post
                iframe
                iexists ii + W64 1, _, _, _
                iframe
                ipureintro
                refine ⟨by word, by word, ?_⟩
                rw [htk, ← Hii.2.2, swift.rec.r1e_set hok hs]
          · -- the report's entries done
            have hii : sint.nat ii = q.2.2.entries.length := by word
            rw [hii, List.take_length] at Hii
            wp_for_post
            iframe
            iexists j + W64 1, _, k'
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rw [Hii.2.2, show sint.nat (j + W64 1) = sint.nat j + 1 by word,
              swift.rec.foldl_take_succ _ _ _ _ _ hq, Hj.2.2]
        · -- rule 1 done: `kept` is the model's `rule1`
          have hjlen : sint.nat j = prsU.length := by word
          rw [hjlen, List.take_length, ← swift.rec.rule1_eq] at Hj
          have hk1 : k = sp.rule1 oldL (prsU.map Prod.snd) := Hj.2.2
          -- `R`: the reports of `U` in the old ballot's fast quorum
          wp_bind (App (Val (GoInstruction (CompositeLiteral
            (go.GoType.SliceType (go.GoType.PointerType swift.MNewLeaderAckN.ty))))) (Val (LiteralValueV _)))
          iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType swift.MNewLeaderAckN.ty) []
          wp_auto
          isplitl []
          · ipureintro; rfl
          iintro %rsl0 ⟨Hrs0, Hrcap0⟩
          wp_auto
          obtain ⟨pR, hpR⟩ : ∃ f : swift.rec.Pr → Bool,
              f = fun q => decide (q.2.1 ∈ sp.AQ N maxC) := ⟨_, rfl⟩
          ihave HIR : (∃ (j : w64) (rsl : GoSlice) (av : Loc),
              "j" ∷ i_ptr ↦ j ∗ "a" ∷ a_ptr ↦ av ∗ "R" ∷ R_ptr ↦ rsl ∗
              "Hrs" ∷ rsl ↦* (((prsU.take (sint.nat j)).filter pR).map Prod.fst) ∗
              "Hrcap" ∷ ownSliceCap Loc rsl (DFrac.own 1) ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z usl.len⌝ : IProp netDistGF)
            $$ [i a R Hrs0 Hrcap0]
          · iexists W64 0, _, _
            rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil, List.map_nil]
            iframe
            ipureintro; word
          wp_for HIR
          wp_if_destruct
          · have hjl : sint.nat j < prsU.length := by word
            obtain ⟨q, hq⟩ : ∃ q, prsU[sint.nat j]? = some q := ⟨_, List.getElem?_eq_getElem hjl⟩
            have hqA : q ∈ prsA := by
              have := List.mem_of_getElem? hq; rw [hprsU] at this; exact (List.mem_filter.mp this).1
            rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z usl.len from ⟨Hj.1, Hif⟩)]
            wp_apply (wp_load_slice_index (V := Loc) usl (sint.Z j) _ _ q.1 Hj.1) $$ [Hus] as Hus
            · iframe; ipureintro
              rw [show (sint.Z j).toNat = sint.nat j by word, List.getElem?_map, hq]; rfl
            ihave #Hq := (BigSepL.bigSepL_mem (Φ := fun q : swift.rec.Pr => swift.ackObj q.1 q.2) hqA) $$ HprsA
            iunfold swift.ackObj at Hq
            icases Hq with ⟨%rep, %bl, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, #Hp, -, -, -, -, %Hqf, -⟩
            iStructNamed Hp
            wp_auto
            wp_method_call
            wp_call
            wp_auto
            wp_apply (wp_qContains aqp DFrac.discard _ rep) $$ [Haq] as -
            · iexact Haq
            have hqP : q ∈ prs := hAperm.mem_iff.mp hqA
            have hrq := Hok.rep q.2 (List.mem_map_of_mem hqP)
            have hpRq : decide (rep ∈ (replica.quorum.aqOf N (sint.Z mc).toNat).map
                replica.quorum.w32n) = pR q := by
              rw [swift.rec.mem_aq_iff N _ Hok.hN rep q.2.1 hrq.1 Hqf.1, hpR,
                show (sint.Z mc).toNat = maxC by omega]
            rw [hpRq]
            have htake : prsU.take (sint.nat (j + W64 1)) = prsU.take (sint.nat j) ++ [q] := by
              rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hq]; rfl
            cases hpq : pR q
            · wp_auto
              wp_for_post
              iframe
              iexists j + W64 1, _, _
              rw [htake, List.filter_append, List.filter_cons, hpq]
              simp only [Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
              iframe
              ipureintro; word
            · wp_auto
              wp_bind (App (Val (GoInstruction (CompositeLiteral
                (go.GoType.SliceType (go.GoType.PointerType swift.MNewLeaderAckN.ty))))) (Val (LiteralValueV _)))
              iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType swift.MNewLeaderAckN.ty) [q.1]
              wp_auto
              isplitl []
              · ipureintro; rfl
              iintro %lsl ⟨Hlsl, -⟩
              wp_auto
              wp_apply wp_slice_append $$ [Hrs Hrcap Hlsl] as %nsl ⟨Hrs, Hrcap, -⟩
              · iframe
              wp_for_post
              iframe
              iexists j + W64 1, _, _
              rw [htake, List.filter_append, List.filter_cons, hpq]
              simp only [↓reduceIte, List.filter_nil, List.map_append, List.map_cons, List.map_nil]
              iframe
              ipureintro; word
          · have hjlen : sint.nat j = prsU.length := by word
            rw [hjlen, List.take_length]
            obtain ⟨prsR, hprsR⟩ : ∃ l, l = prsU.filter pR := ⟨_, rfl⟩
            rw [← hprsR]
            -- rule 2
            ipersist Hrs
            ipersist Hus
            ipersist Has
            wp_bind (If (Val _) _ _)
            iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ leaderInU_ptr ↦ li ∗
                R_ptr ↦ rsl ∗ kept_ptr ↦ km0 ∗
                swift.keptOwn km0 (sp.rule2 k li (prsR.map Prod.snd)) (fun _ => false))))
              $$ [leaderInU R kept Hkept]
            · cases li
              · wp_auto
                ihave %Hrl := ownSlice_len $$ Hrs
                simp only [List.length_map] at Hrl
                wp_if_destruct
                · have hR0 := Hif
                  obtain ⟨r0, rs, hr0⟩ : ∃ r0 rs, prsR = r0 :: rs := by
                    cases prsR with
                    | nil => exfalso; simp at Hrl; have := Hrl.1; word
                    | cons r0 rs => exact ⟨r0, rs, rfl⟩
                  have hr0U : r0 ∈ prsU := by
                    have : r0 ∈ prsR := by rw [hr0]; simp
                    rw [hprsR] at this; exact (List.mem_filter.mp this).1
                  have hr0A : r0 ∈ prsA := by
                    rw [hprsU] at hr0U; exact (List.mem_filter.mp hr0U).1
                  have hr0P : r0 ∈ prs := hAperm.mem_iff.mp hr0A
                  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len from
                    ⟨by decide, Hif⟩)]
                  wp_apply (wp_load_slice_index (V := Loc) rsl (sint.Z (W64 0)) _ _ r0.1 (by decide))
                    $$ [Hrs] as -
                  · iframe #; ipureintro; rw [hr0]; rfl
                  ihave #Hq := (BigSepL.bigSepL_mem (Φ := fun q : swift.rec.Pr => swift.ackObj q.1 q.2)
                    hr0A) $$ HprsA
                  iunfold swift.ackObj at Hq
                  icases Hq with ⟨%rep0, %bl0, %cb0, %ids0, %ph0, %cm0, %dp0, %cmL0, %dpL0, #Hp0, #Hids0,
                    #Hph0, #Hcm0, #Hdp0, %Hqf0, #Hents0⟩
                  ihave #Hp0' := Hp0
                  iStructNamed Hp0'
                  wp_auto
                  rename_i gip
                  irename i => Hrng
                  irename i => Hgi
                  ihave %Hidsl0 := ownSlice_len $$ Hids0
                  ihave %Hphl0 := ownSlice_len $$ Hph0
                  simp only [List.length_map] at Hidsl0 Hphl0
                  obtain ⟨rsS, hrsS⟩ : ∃ l, l = rs.map Prod.snd := ⟨_, rfl⟩
                  ihave HI2 : (∃ (ii : w64) (cid : swift.CommandId) (gi : w64) (k' : sp.Kept),
                      "ii" ∷ i_ptr ↦ ii ∗ "cmdId" ∷ cmdId_ptr ↦ cid ∗ "gi" ∷ gip ↦ gi ∗
                      "Hkept" ∷ swift.keptOwn km0 k' (fun _ => false) ∗
                      "%Hii" ∷ ⌜0 ≤ sint.Z ii ∧ sint.Z ii ≤ sint.Z ids0.len ∧
                        k' = (r0.2.2.entries.take (sint.nat ii)).foldl (swift.rec.r2e rsS) k⌝ :
                      IProp netDistGF) $$ [Hrng cmdId Hgi Hkept]
                  · iexists W64 0, _, _, k
                    iframe
                    ipureintro; refine ⟨by word, by word, ?_⟩
                    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
                  wp_for HI2
                  wp_if_destruct
                  · have hil : sint.nat ii < r0.2.2.entries.length := by word
                    obtain ⟨e, he⟩ : ∃ e, r0.2.2.entries[sint.nat ii]? = some e :=
                      ⟨_, List.getElem?_eq_getElem hil⟩
                    rw [ite_eq_left (show 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ids0.len from ⟨Hii.1, Hif⟩)]
                    wp_apply (wp_load_slice_index (V := swift.CommandId) ids0 (sint.Z ii) _ _
                      (ofCmdId e.id) Hii.1) $$ [Hids0] as -
                    · iframe #; ipureintro
                      rw [show (sint.Z ii).toNat = sint.nat ii by word, List.getElem?_map, he]; rfl
                    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len from
                      ⟨by decide, hR0⟩)]
                    wp_apply (wp_load_slice_index (V := Loc) rsl (sint.Z (W64 0)) _ _ r0.1 (by decide))
                      $$ [Hrs] as -
                    · iframe #; ipureintro; rw [hr0]; rfl
                    have hphb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ph0.len := by constructor <;> word
                    rw [ite_eq_left hphb]
                    wp_apply (wp_load_slice_index (V := w64) ph0 (sint.Z ii) _ _ e.phase Hii.1)
                      $$ [Hph0] as -
                    · iframe #; ipureintro
                      rw [show (sint.Z ii).toNat = sint.nat ii by word, List.getElem?_map, he]; rfl
                    have hentsP := Hok.ents r0.2 (List.mem_map_of_mem hr0P) e (List.mem_of_getElem? he)
                    have htk : (r0.2.2.entries.take (sint.nat (ii + W64 1))).foldl (swift.rec.r2e rsS) k =
                        swift.rec.r2e rsS ((r0.2.2.entries.take (sint.nat ii)).foldl
                          (swift.rec.r2e rsS) k) e := by
                      rw [show sint.nat (ii + W64 1) = sint.nat ii + 1 by word]
                      exact swift.rec.foldl_take_succ _ _ _ _ _ he
                    wp_if_destruct
                    · have hph1 : e.phase.toNat = 1 := by rw [Hif]; rfl
                      iunfold swift.keptOwn at Hkept
                      icases Hkept with ⟨%mk, Hm, %Hmk, Hkents⟩
                      wp_apply (wp_map_lookup2 _ _ km0 mk (ofCmdId e.id)) $$ Hm as Hm
                      have hmke := Hmk.2 (ofCmdId e.id)
                      simp only [toCmdId_ofCmdId] at hmke
                      cases hx : mk !! ofCmdId e.id with
                      | some p =>
                        rw [hx] at hmke
                        simp only [Option.isSome_some, _root_.decide_true]
                        wp_auto
                        wp_for_post
                        iframe
                        iexists ii + W64 1, _, _, k'
                        iframe
                        isplitl [Hm Hkents]
                        · iapply swift.kept_close km0 k' _ mk Hmk $$ [Hm Hkents]; iframe
                        ipureintro
                        refine ⟨by word, by word, ?_⟩
                        rw [htk, ← Hii.2.2, swift.rec.r2e_skip]
                        right; rw [← hmke]; rfl
                      | none =>
                        rw [hx] at hmke
                        have hg : k'.get e.id = none := by
                          cases h : k'.get e.id with
                          | none => rfl
                          | some _ => rw [h] at hmke; cases hmke
                        wp_auto
                        rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len from
                          ⟨by decide, hR0⟩)]
                        wp_apply (wp_load_slice_index (V := Loc) rsl (sint.Z (W64 0)) _ _ r0.1 (by decide))
                          $$ [Hrs] as -
                        · iframe #; ipureintro; rw [hr0]; rfl
                        ihave #He := (BigSepL.bigSepL_lookup (Φ := fun i e => iprop(∃ (c : state.Command)
                          (sd : swift.SDep), ⌜cmL0[i]? = some c ∧ dpL0[i]? = some sd⌝ ∗
                          swift.repEntryObj c sd e)) he) $$ Hents0
                        icases He with ⟨%c, %sd, %hcsd, #He⟩
                        iunfold swift.repEntryObj at He
                        icases He with ⟨%vs, %hc, #Hvs, #Hsd⟩
                        ihave %Hdpl := ownSlice_len $$ Hdp0
                        have hdpb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z dp0.len := by
                          constructor <;> word
                        rw [ite_eq_left hdpb]
                        icases ownSlice_elem_acc (V := swift.SDep) (sint.Z ii) sd dp0 _ dpL0 hdpb.1
                          (by rw [show (sint.Z ii).toNat = sint.nat ii by word]; exact hcsd.2) $$ Hdp0
                          with ⟨Hsde, -⟩
                        iStructNamed Hsde
                        wp_auto
                        ihave %Hrwf := ownSlice_wf $$ Hrs
                        have hsb : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z rsl.len ∧
                            sint.Z rsl.len ≤ sint.Z rsl.cap := by
                          refine ⟨by decide, ?_, Hrwf.2⟩
                          have h0 : sint.Z (W64 0) = 0 := rfl
                          have h1 : sint.Z (W64 1) = 1 := rfl
                          rw [h1]; rw [h0] at hR0; omega
                        rw [ite_eq_left hsb]
                        ihave #Hrs1 : (slice.slice rsl Loc (W64 1) rsl.len ↦*□ rs.map Prod.fst) $$ [Hrs]
                        · icases (ownSlice_slice (V := Loc) (W64 1) rsl.len rsl DFrac.discard _
                            ⟨hsb.1, hsb.2.1, Int.le_refl _⟩).1 $$ Hrs with ⟨-, H1, -⟩
                          have hsub : subslice (sint.nat (W64 1)) (sint.nat rsl.len)
                              ((r0 :: rs).map Prod.fst) = rs.map Prod.fst := by
                            have h1 := Hrl.1; rw [hr0] at h1
                            rw [← h1]
                            simp only [subslice, show sint.nat (W64 1) = 1 from rfl]
                            rw [List.take_of_length_le (by simp)]; simp
                          rw [← hsub, ← hr0]
                          iexact H1
                        wp_auto
                        ihave %Hrs1l := ownSlice_len $$ Hrs1
                        have hsl : (slice.slice rsl Loc (W64 1) rsl.len).len = rsl.len - W64 1 := rfl
                        simp only [List.length_map, hsl] at Hrs1l
                        wp_bind (App (App (App (Val doFor) _) _) _)
                        iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
                            same_ptr ↦ (rsS.all (fun a => a.2.entries.any (swift.rec.r2test e))) ∗
                            dep_ptr ↦ sd.Dep' ∗ cmdId_ptr ↦ ofCmdId e.id))) $$ [same dep i a cmdId]
                        · ihave HS : (∃ (j : w64) (av : Loc), "j" ∷ i_ptr ↦ j ∗ "a" ∷ a_ptr ↦ av ∗
                              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧
                                sint.Z j ≤ sint.Z (rsl.len - W64 1) ∧
                                (rsS.take (sint.nat j)).all
                                  (fun a => a.2.entries.any (swift.rec.r2test e)) = true⌝ :
                              IProp netDistGF) $$ [i a]
                          · iexists W64 0, _
                            iframe
                            ipureintro; refine ⟨by word, by word, ?_⟩
                            rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
                          wp_for HS
                          wp_if_destruct
                          · have hjl : sint.nat j < rs.length := by
                              rw [Hrs1l.1]; exact swift.rec.nat_lt_of_lt _ _ Hj.1 Hif
                            obtain ⟨q, hq⟩ : ∃ q, rs[sint.nat j]? = some q :=
                              ⟨_, List.getElem?_eq_getElem hjl⟩
                            have hqA : q ∈ prsA := by
                              have h1 : q ∈ prsR := by rw [hr0]; exact List.mem_cons_of_mem _ (List.mem_of_getElem? hq)
                              rw [hprsR] at h1
                              have h2 := (List.mem_filter.mp h1).1
                              rw [hprsU] at h2; exact (List.mem_filter.mp h2).1
                            rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j <
                              sint.Z (rsl.len - W64 1) from ⟨Hj.1, Hif⟩)]
                            wp_apply (wp_load_slice_index (V := Loc) _ (sint.Z j) _ _ q.1 Hj.1)
                              $$ [Hrs1] as -
                            · iframe #; ipureintro
                              rw [show (sint.Z j).toNat = sint.nat j by word, List.getElem?_map, hq]; rfl
                            ihave #Hq := (BigSepL.bigSepL_mem (Φ := fun q : swift.rec.Pr =>
                              swift.ackObj q.1 q.2) hqA) $$ HprsA
                            iunfold swift.ackObj at Hq
                            icases Hq with ⟨%rep, %bl, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, #Hp, #Hids,
                              #Hph, #Hcm, #Hdp, %Hqf, #Hents⟩
                            ihave #Hp' := Hp
                            iStructNamed Hp'
                            wp_auto
                            ihave %Hidsl := ownSlice_len $$ Hids
                            ihave %Hphl := ownSlice_len $$ Hph
                            ihave %Hdpl' := ownSlice_len $$ Hdp
                            simp only [List.length_map] at Hidsl Hphl
                            have hqP : q ∈ prs := hAperm.mem_iff.mp hqA
                            wp_bind (App (App (App (Val doFor) _) _) _)
                            iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
                                found_ptr ↦ q.2.2.entries.any (swift.rec.r2test e) ∗
                                dep_ptr ↦ sd.Dep' ∗ cmdId_ptr ↦ ofCmdId e.id ∗ a_ptr ↦ q.1)))
                              $$ [found dep i id k cmdId a]
                            · ihave HF : (∃ (kk : w64) (idv : swift.CommandId) (kv : w64),
                                  "kk" ∷ i_ptr ↦ kk ∗ "id" ∷ id_ptr ↦ idv ∗ "kv" ∷ k_ptr ↦ kv ∗
                                  "%Hk" ∷ ⌜0 ≤ sint.Z kk ∧ sint.Z kk ≤ sint.Z ids.len ∧
                                    (q.2.2.entries.take (sint.nat kk)).any (swift.rec.r2test e) = false⌝ :
                                  IProp netDistGF) $$ [i id k]
                              · iexists W64 0, _, _
                                iframe
                                ipureintro; refine ⟨by word, by word, ?_⟩
                                rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
                              wp_for HF
                              wp_if_destruct
                              · have hkl : sint.nat kk < q.2.2.entries.length := by
                                  rw [Hidsl.1]; exact swift.rec.nat_lt_of_lt _ _ Hk.1 Hif
                                obtain ⟨e', he'⟩ : ∃ e', q.2.2.entries[sint.nat kk]? = some e' :=
                                  ⟨_, List.getElem?_eq_getElem hkl⟩
                                rw [ite_eq_left (show 0 ≤ sint.Z kk ∧ sint.Z kk < sint.Z ids.len from
                                  ⟨Hk.1, Hif⟩)]
                                wp_apply (wp_load_slice_index (V := swift.CommandId) ids (sint.Z kk) _ _
                                  (ofCmdId e'.id) Hk.1) $$ [Hids] as -
                                · iframe #; ipureintro
                                  rw [show (sint.Z kk).toNat = sint.nat kk by word, List.getElem?_map, he']; rfl
                                wp_bind (If (If _ _ _) _ (Val #false))
                                iapply (wp_wand (Φ := fun v => iprop(⌜v = #(swift.rec.r2test e e')⌝ ∗
                                    dep_ptr ↦ sd.Dep' ∗ k_ptr ↦ kk ∗ cmdId_ptr ↦ ofCmdId e.id ∗
                                    a_ptr ↦ q.1))) $$ [dep kv cmdId a]
                                · wp_if_destruct
                                  · have hcl := Hif
                                    wp_if_destruct
                                    · have hid : e'.id = e.id := by
                                        have hseq : e'.id.seq = e.id.seq := by
                                          simpa [ofCmdId] using Hif
                                        rw [show e'.id = ⟨e'.id.cl, e'.id.seq⟩ from rfl,
                                          show e.id = ⟨e.id.cl, e.id.seq⟩ from rfl, hcl, hseq]
                                      have hphk : 0 ≤ sint.Z kk ∧ sint.Z kk < sint.Z ph.len := by
                                        constructor <;> word
                                      rw [ite_eq_left hphk]
                                      wp_apply (wp_load_slice_index (V := w64) ph (sint.Z kk) _ _ e'.phase Hk.1)
                                        $$ [Hph] as -
                                      · iframe #; ipureintro
                                        rw [show (sint.Z kk).toNat = sint.nat kk by word, List.getElem?_map, he']; rfl
                                      wp_if_destruct
                                      · have hph1' : e'.phase.toNat = 1 := by rw [Hif]; rfl
                                        ihave #He' := (BigSepL.bigSepL_lookup (Φ := fun i e => iprop(∃ (c : state.Command)
                                          (sd : swift.SDep), ⌜cmL[i]? = some c ∧ dpL[i]? = some sd⌝ ∗
                                          swift.repEntryObj c sd e)) he') $$ Hents
                                        icases He' with ⟨%c', %sd', %hcsd', #He'⟩
                                        iunfold swift.repEntryObj at He'
                                        icases He' with ⟨%vs', %hc', #Hvs', #Hsd'⟩
                                        have hdpk : 0 ≤ sint.Z kk ∧ sint.Z kk < sint.Z dp.len := by
                                          constructor <;> word
                                        rw [ite_eq_left hdpk]
                                        icases ownSlice_elem_acc (V := swift.SDep) (sint.Z kk) sd' dp _ dpL hdpk.1
                                          (by rw [show (sint.Z kk).toNat = sint.nat kk by word]; exact hcsd'.2)
                                          $$ Hdp with ⟨Hsde', -⟩
                                        iStructNamed Hsde'
                                        wp_auto
                                        have hnd' := (Hok.ents q.2 (List.mem_map_of_mem hqP) e'
                                          (List.mem_of_getElem? he')).2.2 hph1'
                                        wp_apply (wp_Equals dep_ptr sd.Dep' sd'.Dep' (DFrac.own 1) DFrac.discard
                                          DFrac.discard (e.dep.map ofCmdId) (e'.dep.map ofCmdId)) $$ [dep] as ⟨dep, -, -⟩
                                        · iframe #
                                          iframe
                                          ipureintro
                                          exact ⟨swift.rec.nodup_map_of (hentsP.2.2 hph1),
                                            swift.rec.nodup_map_of hnd'⟩
                                        iframe
                                        ipureintro; congr 1
                                        simp only [swift.rec.map_to_of, swift.rec.r2test, hid, hph1',
                                          beq_self_eq_true, Bool.true_and]
                                      · have hph1' : e'.phase.toNat ≠ 1 := fun h => Hif (BitVec.eq_of_toNat_eq h)
                                        iframe
                                        ipureintro; congr 1
                                        simp [swift.rec.r2test, hph1']
                                    · have hid : e'.id ≠ e.id := by
                                        intro h; apply Hif; rw [h]
                                      iframe
                                      ipureintro; congr 1
                                      simp [swift.rec.r2test, hid]
                                  · have hid : e'.id ≠ e.id := by
                                      intro h; apply Hif; rw [h]
                                    iframe
                                    ipureintro; congr 1
                                    simp [swift.rec.r2test, hid]
                                iintro %v ⟨%hv, dep, kv, cmdId, a⟩
                                subst hv
                                have htk2 : (q.2.2.entries.take (sint.nat (kk + W64 1))).any (swift.rec.r2test e) =
                                    ((q.2.2.entries.take (sint.nat kk)).any (swift.rec.r2test e) ||
                                      swift.rec.r2test e e') := by
                                  rw [swift.rec.nat_succ_of_lt _ _ Hk.1 Hif, List.take_add_one, he']
                                  simp
                                cases ht : swift.rec.r2test e e'
                                · wp_auto
                                  wp_for_post
                                  iframe
                                  iexists kk + W64 1, _, _
                                  iframe
                                  ipureintro
                                  refine ⟨by word, by word, ?_⟩
                                  rw [htk2, Hk.2.2, ht]
                                · wp_auto
                                  wp_for_post
                                  have hany : q.2.2.entries.any (swift.rec.r2test e) = true :=
                                    List.any_eq_true.mpr ⟨e', List.mem_of_getElem? he', ht⟩
                                  rw [hany]
                                  iframe
                                  try (ipureintro; trivial)
                              · have hkk : sint.nat kk = q.2.2.entries.length := by rw [Hidsl.1]; word
                                rw [hkk, List.take_length] at Hk
                                rw [Hk.2.2]
                                iframe
                            iintro %v ⟨%hv, found, dep, cmdId, a⟩
                            subst hv
                            wp_auto
                            have hqrs : q.2 ∈ rsS := by
                              rw [hrsS]; exact List.mem_map_of_mem (List.mem_of_getElem? hq)
                            have htk3 : (rsS.take (sint.nat (j + W64 1))).all
                                (fun a => a.2.entries.any (swift.rec.r2test e)) =
                                ((rsS.take (sint.nat j)).all (fun a => a.2.entries.any (swift.rec.r2test e)) &&
                                  q.2.2.entries.any (swift.rec.r2test e)) := by
                              have hq' : rsS[sint.nat j]? = some q.2 := by
                                rw [hrsS, List.getElem?_map, hq]; rfl
                              rw [swift.rec.nat_succ_of_lt _ _ Hj.1 Hif, List.take_add_one, hq']
                              simp
                            cases hf : q.2.2.entries.any (swift.rec.r2test e)
                            · wp_auto
                              wp_for_post
                              have hall : rsS.all (fun a => a.2.entries.any (swift.rec.r2test e)) = false := by
                                rw [Bool.eq_false_iff]; intro h
                                have := List.all_eq_true.mp h q.2 hqrs
                                rw [hf] at this; cases this
                              rw [hall]
                              iframe
                              try (ipureintro; trivial)
                            · wp_auto
                              wp_for_post
                              iframe
                              iexists j + W64 1, _
                              iframe
                              ipureintro
                              refine ⟨by word, by word, ?_⟩
                              rw [htk3, Hj.2.2, hf]
                          · have hjj : sint.nat j = rsS.length := by
                              rw [hrsS, List.length_map, Hrs1l.1]; word
                            rw [hjj, List.take_length] at Hj
                            rw [Hj.2.2]
                            iframe
                            try (ipureintro; trivial)
                        iintro %v ⟨%hv, same, dep, cmdId⟩
                        subst hv
                        wp_auto
                        have hgo := swift.rec.r2e_go (rs := rsS) hph1 hg
                        cases hall : rsS.all (fun a => a.2.entries.any (swift.rec.r2test e))
                        · wp_auto
                          wp_for_post
                          iframe
                          iexists ii + W64 1, _, _, k'
                          iframe
                          isplitl [Hm Hkents]
                          · iapply swift.kept_close km0 k' _ mk Hmk $$ [Hm Hkents]; iframe
                          ipureintro
                          refine ⟨by word, by word, ?_⟩
                          rw [htk, ← Hii.2.2, hgo, hall]; rfl
                        · wp_auto
                          rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len from
                            ⟨by decide, hR0⟩)]
                          wp_apply (wp_load_slice_index (V := Loc) rsl (sint.Z (W64 0)) _ _ r0.1 (by decide))
                            $$ [Hrs] as -
                          · iframe #; ipureintro; rw [hr0]; rfl
                          ihave %Hcml0 := ownSlice_len $$ Hcm0
                          have hcmb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z cm0.len := by
                            constructor <;> word
                          rw [ite_eq_left hcmb]
                          wp_apply (wp_load_slice_index (V := state.Command) cm0 (sint.Z ii) cmL0 _ c hcmb.1)
                            $$ [Hcm0] as -
                          · iframe #; ipureintro
                            rw [show (sint.Z ii).toNat = sint.nat ii by word]; exact hcsd.1
                          wp_apply (wp_mapInsert _ km0 mk (ofCmdId e.id) «$r0_ptr») $$ Hm as Hm
                          ihave Hnew : swift.recOwn «$r0_ptr» ⟨2, e.cmd, e.dep, 1⟩ false $$ [«$r0»]
                          · iunfold swift.recOwn
                            iexists W64 2, W64 1, vs, sd.Dep'
                            rw [hc]
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            iframe «$r0» Hvs Hsd
                            ipureintro; exact ⟨rfl, by omega, rfl, by omega⟩
                          ihave Hkept := swift.kept_insert km0 k' (fun _ => false) mk (ofCmdId e.id) «$r0_ptr»
                            ⟨2, e.cmd, e.dep, 1⟩ false Hmk hx $$ [Hm Hkents Hnew]
                          · iframe
                          rw [swift.updO_const, toCmdId_ofCmdId]
                          wp_for_post
                          iframe
                          iexists ii + W64 1, _, _, _
                          iframe
                          ipureintro
                          refine ⟨by word, by word, ?_⟩
                          rw [htk, ← Hii.2.2, hgo, hall]; rfl
                    · -- not pre-accepted
                      wp_for_post
                      iframe
                      iexists ii + W64 1, _, _, k'
                      iframe
                      ipureintro
                      refine ⟨by word, by word, ?_⟩
                      rw [htk, ← Hii.2.2, swift.rec.r2e_skip]
                      left; intro h; apply Hif; exact BitVec.eq_of_toNat_eq h
                  · have hii : sint.nat ii = r0.2.2.entries.length := by rw [Hidsl0.1]; word
                    rw [hii, List.take_length] at Hii
                    have h2 : sp.rule2 k false (prsR.map Prod.snd) = k' := by
                      rw [hr0, List.map_cons, ← hrsS, swift.rec.rule2_eq k r0.2 rsS, ← Hii.2.2]
                    rw [h2]
                    iframe
                    try (ipureintro; trivial)
                · have hnil : prsR = [] := by
                    cases prsR with
                    | nil => rfl
                    | cons r0 rs => exfalso; simp at Hrl; have := Hrl.1; word
                  rw [hnil]
                  iframe
              · wp_auto
                iframe
                try (ipureintro; trivial)
            iintro %v ⟨%hv, leaderInU, R, kept, Hkept⟩
            subst hv
            wp_auto
            -- the closure (rule 3)
            obtain ⟨Um, hUm⟩ : ∃ l, l = prsU.map Prod.snd := ⟨_, rfl⟩
            obtain ⟨Rm, hRm⟩ : ∃ l, l = prsR.map Prod.snd := ⟨_, rfl⟩
            obtain ⟨Am, hAm⟩ : ∃ l, l = prsA.map Prod.snd := ⟨_, rfl⟩
            obtain ⟨k2, hk2⟩ : ∃ k', k' = sp.rule2 k li Rm := ⟨_, rfl⟩
            rw [← hRm, ← hk2]
            have hRU : ∀ a ∈ Rm, a ∈ Um := by
              intro a ha; rw [hRm, hprsR] at ha; rw [hUm]
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
              exact List.mem_map_of_mem (List.mem_filter.mp hq).1
            have hUa : ∀ a ∈ Um, a ∈ Am := by
              intro a ha; rw [hUm, hprsU] at ha; rw [hAm]
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
              exact List.mem_map_of_mem (List.mem_filter.mp hq).1
            have hAperm' : Am.Perm (prs.map Prod.snd) := by rw [hAm]; exact hAperm.map _
            have hcmd : sp.CmdFrom Am k2 := by
              rw [hk2]
              refine sp.rule2_cmd Am k li Rm (fun a ha => hUa a (hRU a ha)) ?_
              rw [hk1, ← hUm]; exact sp.rule1_cmd Am oldL Um hUa
            iunfold swift.keptOwn at Hkept
            icases Hkept with ⟨%mk, Hm, %Hmk, Hkents⟩
            obtain ⟨A, hA, hcov, hfuel, hk2len⟩ := swift.rec.closure_setup (prs.map Prod.snd) li
              Rm Um Am hRU hUa hAperm' k2 hcmd Hmk.1
            have hsz : GMap.size mk ≤ 2 ^ 62 := by
              rw [swift.keptPure_size Hmk]; have := Hok.size; omega
            wp_apply (wp_sortedIds km0 mk (DFrac.own 1)) $$ [Hm] as %wsl0 %ids ⟨Hm, Hws, Hwcap, %Hids⟩
            · iframe; ipureintro; exact hsz
            have hperm := swift.keys_perm k2 ids Hids.1 Hmk.1 (fun c => by rw [Hids.2.1, Hmk.2 c])
            have hw0 : sp.sortIds (k2.map Prod.fst) = ids.map toCmdId := Hids.2.2 _ hperm
            obtain ⟨B, hB⟩ : ∃ f, f = sp.recBest li Rm Um Am := ⟨_, rfl⟩
            obtain ⟨w0, hw0'⟩ : ∃ l, l = ids.map toCmdId := ⟨_, rfl⟩
            have hci0 := swift.rec.CI_init B A k2 w0 (by rw [hw0']; exact hperm.symm) Hmk.1
            ihave Hkept := swift.kept_close km0 k2 (fun _ => false) mk Hmk $$ [Hm Hkents]
            · iframe
            ipersist best
            ihave HC : (∃ (n : Nat) (kc : sp.Kept) (wl : List sp.CmdId) (oc : sp.CmdId → Bool)
                (wsl : GoSlice),
                "work" ∷ work_ptr ↦ wsl ∗ "Hws" ∷ wsl ↦* wl.map ofCmdId ∗
                "Hwcap" ∷ ownSliceCap swift.CommandId wsl (DFrac.own 1) ∗
                "Hkept" ∷ swift.keptOwn km0 kc oc ∗
                "%Hci" ∷ ⌜swift.rec.CI B A k2 w0 (w0.length + sp.unkept A k2) n kc wl oc⌝ :
                IProp netDistGF) $$ [work Hws Hwcap Hkept]
            · iexists 0, k2, w0, (fun _ => false), wsl0
              have hwm : w0.map ofCmdId = ids := by
                rw [hw0', List.map_map, show (ofCmdId ∘ toCmdId) = id from funext fun _ => rfl,
                  List.map_id]
              rw [hwm]
              iframe
              ipureintro; exact hci0
            wp_for HC
            wp_if_destruct
            · have hlen0 : sint.Z (W64 0) < sint.Z wsl.len := by
                first
                | (simpa using Hif)
                | (have h := Hif; simp only [to_val_inj] at h; simpa using h)
              ihave %Hwl := ownSlice_len $$ Hws
              simp only [List.length_map] at Hwl
              obtain ⟨c, w, rfl⟩ : ∃ c w, wl = c :: w := by
                cases wl with
                | nil =>
                  exfalso
                  have h1 := swift.rec.nat_lt_of_lt (W64 0) wsl.len (by decide) hlen0
                  have h2 := Hwl.1
                  rw [show sint.nat (W64 0) = 0 from rfl] at h1
                  simp at h2; omega
                | cons c w => exact ⟨c, w, rfl⟩
              have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z wsl.len := ⟨by decide, hlen0⟩
              rw [ite_eq_left hb0]
              wp_apply (wp_load_slice_index (V := swift.CommandId) wsl (sint.Z (W64 0)) _ _ (ofCmdId c)
                (by decide)) $$ [Hws] as Hws
              · iframe; ipureintro; rfl
              ihave %Hwwf := ownSlice_wf $$ Hws
              have hsb : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z wsl.len ∧
                  sint.Z wsl.len ≤ sint.Z wsl.cap := by
                refine ⟨by decide, ?_, Hwwf.2⟩
                have h0 : sint.Z (W64 0) = 0 := rfl
                have h1 : sint.Z (W64 1) = 1 := rfl
                rw [h1]; rw [h0] at hlen0; omega
              rw [ite_eq_left hsb]
              icases ownSlice_slice_with_cap (V := swift.CommandId) (W64 1) wsl.len wsl _
                ⟨hsb.1, hsb.2.1, Int.le_refl _⟩ $$ [Hws Hwcap] with ⟨-, Hws, Hwcap⟩
              · iframe
              have hsub : subslice (sint.nat (W64 1)) (sint.nat wsl.len) ((c :: w).map ofCmdId) =
                  w.map ofCmdId := by
                rw [← Hwl.1]
                simp only [subslice, show sint.nat (W64 1) = 1 from rfl]
                rw [List.take_of_length_le (by simp)]; simp
              rw [hsub]
              wp_auto
              obtain ⟨hit, hμ, hwnd, hwk, hof, hot⟩ := Hci
              iunfold swift.keptOwn at Hkept
              icases Hkept with ⟨%mk, Hm, %Hmk, Hkents⟩
              obtain ⟨ec, hec⟩ : ∃ e, kc.get c = some e :=
                Option.isSome_iff_exists.mp (hwk c (by simp))
              obtain ⟨pc, hpc⟩ : ∃ p, mk !! ofCmdId c = some p := by
                have := Hmk.2 (ofCmdId c); rw [toCmdId_ofCmdId, hec] at this
                exact Option.isSome_iff_exists.mp this
              wp_apply (wp_map_lookup1 _ _ km0 mk (ofCmdId c)) $$ Hm as Hm
              rw [hpc]
              simp only [Option.getD_some]
              wp_bind (App (Val (GoInstruction (CompositeLiteral swift.Dep.ty))) (Val (LiteralValueV _)))
              iapply wp_slice_literal (V := swift.CommandId) (st := swift.Dep.ty) (t := swift.CommandId.ty) []
              wp_auto
              isplitl []
              · ipureintro; rfl
              iintro %dsl0 ⟨Hd0, Hdcap0⟩
              icases (BigSepM.bigSepM_delete
                (show Iris.Std.PartialMap.get? mk (ofCmdId c) = some pc from hpc)).1
                $$ Hkents with ⟨⟨%ec', %hec', Hre⟩, Hkents⟩
              rw [toCmdId_ofCmdId, hec] at hec'; cases hec'
              rw [toCmdId_ofCmdId, hof c (by simp)]
              iunfold swift.recOwn at Hre
              simp only [Bool.false_eq_true, ↓reduceIte]
              icases Hre with ⟨%phc, %clsc, %vsc, %dslc, Hpc, #Hvsc, #Hdslc, %Hphc⟩
              wp_auto
              ihave %Hdslcl := ownSlice_len $$ Hdslc
              simp only [List.length_map] at Hdslcl
              ihave HD : (∃ (jj : w64) (dv : swift.CommandId) (kg : sp.Kept) (og : sp.CmdId → Bool)
                  (mk' : GMap swift.CommandId Loc) (wsl' dsl' : GoSlice) (wl' dl : List sp.CmdId),
                  "jj" ∷ i_ptr ↦ jj ∗ "d" ∷ d_ptr ↦ dv ∗ "work" ∷ work_ptr ↦ wsl' ∗
                  "Hws" ∷ wsl' ↦* wl'.map ofCmdId ∗
                  "Hwcap" ∷ ownSliceCap swift.CommandId wsl' (DFrac.own 1) ∗
                  "dep" ∷ dep_ptr ↦ dsl' ∗ "Hdep" ∷ dsl' ↦* dl.map ofCmdId ∗
                  "Hdcap" ∷ ownSliceCap swift.CommandId dsl' (DFrac.own 1) ∗
                  "Hm" ∷ km0 ↦$ mk' ∗ "Hkents" ∷ swift.keptEnts kg og (GMap.delete (ofCmdId c) mk') ∗
                  "%Hd" ∷ ⌜0 ≤ sint.Z jj ∧ sint.Z jj ≤ sint.Z dslc.len ∧
                    (ec.dep.take (sint.nat jj)).foldl (sp.closeDep B c) (kc, w, []) = (kg, wl', dl) ∧
                    swift.keptPure kg mk' ∧ mk' !! ofCmdId c = some pc ∧
                    (∀ y ∈ wl', og y = false) ∧ (∀ y, y ∉ wl' → og y = oc y)⌝ : IProp netDistGF)
                $$ [i d work Hws Hwcap dep Hd0 Hdcap0 Hm Hkents]
              · iexists W64 0, _, kc, oc, mk, (slice.slice wsl swift.CommandId (W64 1) wsl.len), _, w, []
                simp only [List.map_nil]
                iframe
                ipureintro
                refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl,
                  Hmk, hpc, fun y hy => hof y (List.mem_cons_of_mem _ hy), fun _ _ => trivial⟩
              wp_for HD
              wp_if_destruct
              · have hjl : sint.nat jj < ec.dep.length := by
                  rw [Hdslcl.1]; exact swift.rec.nat_lt_of_lt _ _ Hd.1 Hif
                obtain ⟨dd, hdd⟩ : ∃ x, ec.dep[sint.nat jj]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
                rw [ite_eq_left (show 0 ≤ sint.Z jj ∧ sint.Z jj < sint.Z dslc.len from ⟨Hd.1, Hif⟩)]
                wp_apply (wp_load_slice_index (V := swift.CommandId) dslc (sint.Z jj) _ _
                  (ofCmdId dd) Hd.1) $$ [Hdslc] as -
                · iframe #; ipureintro
                  rw [show (sint.Z jj).toNat = sint.nat jj by word, List.getElem?_map, hdd]; rfl
                have htk : (ec.dep.take (sint.nat (jj + W64 1))).foldl (sp.closeDep B c) (kc, w, []) =
                    sp.closeDep B c (kg, wl', dl) dd := by
                  rw [swift.rec.nat_succ_of_lt _ _ Hd.1 Hif, swift.rec.foldl_take_succ _ _ _ _ _ hdd,
                    Hd.2.2.1]
                wp_bind (If (Val _) _ (Val #false))
                iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (dd = c))⌝))) $$ []
                · wp_if_destruct
                  · ipureintro; congr 1
                    apply decide_eq_decide.mpr
                    constructor
                    · intro h
                      rw [show dd = ⟨dd.cl, dd.seq⟩ from rfl, show c = ⟨c.cl, c.seq⟩ from rfl, Hif, h]
                    · intro h; rw [h]
                  · ipureintro; congr 1
                    symm; apply decide_eq_false
                    intro h; apply Hif; rw [h]
                iintro %v %hv
                subst hv
                obtain ⟨hj0, hjl', hfold, hkp, hmc, hog1, hog2⟩ := Hd
                by_cases hdc : dd = c
                · rw [show decide (dd = c) = true from decide_eq_true hdc]
                  wp_auto
                  wp_for_post
                  iframe
                  iexists jj + W64 1, _, kg, og, mk', wsl', dsl', wl', dl
                  iframe
                  ipureintro
                  refine ⟨by word, by word, ?_, hkp, hmc, hog1, hog2⟩
                  rw [htk, hdc, swift.rec.closeDep_self]
                · rw [show decide (dd = c) = false from decide_eq_false hdc]
                  wp_auto
                  wp_apply (wp_map_lookup2 _ _ km0 mk' (ofCmdId dd)) $$ Hm as Hm
                  have hmkd := hkp.2 (ofCmdId dd)
                  rw [toCmdId_ofCmdId] at hmkd
                  cases hx : mk' !! ofCmdId dd with
                  | some px =>
                    rw [hx] at hmkd
                    simp only [Option.isSome_some, Bool.not_true]
                    wp_auto
                    wp_bind (App (Val (GoInstruction (CompositeLiteral
                      (go.GoType.SliceType swift.CommandId.ty)))) (Val (LiteralValueV _)))
                    iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [ofCmdId dd]
                    wp_auto
                    isplitl []
                    · ipureintro; rfl
                    iintro %lsl ⟨Hlsl, -⟩
                    wp_auto
                    wp_apply wp_slice_append $$ [Hdep Hdcap Hlsl] as %ndsl ⟨Hdep, Hdcap, -⟩
                    · iframe
                    wp_for_post
                    iframe
                    iexists jj + W64 1, _, kg, og, mk', wsl', ndsl, wl', dl ++ [dd]
                    rw [List.map_append]
                    iframe
                    ipureintro
                    refine ⟨by word, by word, ?_, hkp, hmc, hog1, hog2⟩
                    rw [htk, swift.rec.closeDep_kept hdc hmkd.symm]
                  | none =>
                    rw [hx] at hmkd
                    have hkn : kg.get dd = none := by
                      cases h : kg.get dd with
                      | none => rfl
                      | some _ => rw [h] at hmkd; cases hmkd
                    simp only [Option.isSome_none, Bool.not_false]
                    rw [show (!decide (false = true)) = true by decide]
                    wp_pure
                    wp_bind (Let (BNamed "$a0") _ _)
                    iapply (wp_wand (Φ := fun v => iprop(∃ pb : Loc, ⌜v = #pb⌝ ∗ leaderInU_ptr ↦ li ∗
                        R_ptr ↦ rsl ∗ U_ptr ↦ usl ∗ acks_ptr ↦ asl ∗ d_ptr ↦ ofCmdId dd ∗
                        swift.optOwn pb (B dd)))) $$ [leaderInU R U acks d]
                    · wp_auto
                      -- `best(d)`: first `R[0]`'s entry when rule 2 applies
                      wp_bind (If (If (Val _) _ _) _ _)
                      iapply (wp_wand (Φ := fun v => iprop(leaderInU_ptr ↦ li ∗ R_ptr ↦ rsl ∗
                          d_ptr ↦ ofCmdId dd ∗
                          ((⌜v = executeVal ∧ swift.rec.r0find li Rm dd = none⌝ ∗
                              «$res0_ptr» ↦ Perennial.zero_val Loc) ∨
                            (⌜v = returnVal #()⌝ ∗ ∃ pb, «$res0_ptr» ↦ pb ∗ swift.optOwn pb (B dd))))))
                        $$ [leaderInU R d «$res0»]
                      · ihave %Hrl := ownSlice_len $$ Hrs
                        simp only [List.length_map] at Hrl
                        cases li
                        · wp_auto
                          wp_if_destruct
                          · have hR0 := Hif
                            obtain ⟨r0, rs, hr0⟩ : ∃ r0 rs, prsR = r0 :: rs := by
                              cases prsR with
                              | nil => exfalso; simp at Hrl; have := Hrl.1; word
                              | cons r0 rs => exact ⟨r0, rs, rfl⟩
                            have hr0A : r0 ∈ prsA := by
                              have h1 : r0 ∈ prsR := by rw [hr0]; simp
                              rw [hprsR] at h1
                              have h2 := (List.mem_filter.mp h1).1
                              rw [hprsU] at h2; exact (List.mem_filter.mp h2).1
                            rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len from
                              ⟨by decide, hR0⟩)]
                            wp_apply (wp_load_slice_index (V := Loc) rsl (sint.Z (W64 0)) _ _ r0.1 (by decide))
                              $$ [Hrs] as -
                            · iframe #; ipureintro; rw [hr0]; rfl
                            ihave #Hq := (BigSepL.bigSepL_mem (Φ := fun q : swift.rec.Pr =>
                              swift.ackObj q.1 q.2) hr0A) $$ HprsA
                            iunfold swift.ackObj at Hq
                            icases Hq with ⟨%rep0, %bl0, %cb0, %ids0, %ph0, %cm0, %dp0, %cmL0, %dpL0, #Hp0,
                              #Hids0, #Hph0, #Hcm0, #Hdp0, %Hqf0, #Hents0⟩
                            ihave #Hp0' := Hp0
                            iStructNamed Hp0'
                            wp_auto
                            rename_i gip
                            irename i => Hrng
                            irename i => Hgi
                            ihave %Hidsl0 := ownSlice_len $$ Hids0
                            simp only [List.length_map] at Hidsl0
                            have hr0P : r0 ∈ prs := hAperm.mem_iff.mp hr0A
                            ihave HF1 : (∃ (ii : w64) (idv : swift.CommandId) (gi : w64),
                                "ii" ∷ i_ptr ↦ ii ∗ "id" ∷ id_ptr ↦ idv ∗ "gi" ∷ gip ↦ gi ∗
                                "%Hf" ∷ ⌜0 ≤ sint.Z ii ∧ sint.Z ii ≤ sint.Z ids0.len ∧
                                  (r0.2.2.entries.take (sint.nat ii)).find? (·.id == dd) = none⌝ :
                                IProp netDistGF) $$ [Hrng id Hgi]
                            · iexists W64 0, _, _
                              iframe
                              ipureintro; refine ⟨by word, by word, ?_⟩
                              rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
                            wp_for HF1
                            wp_if_destruct
                            · have hil : sint.nat ii < r0.2.2.entries.length := by
                                rw [Hidsl0.1]; exact swift.rec.nat_lt_of_lt _ _ Hf.1 Hif
                              obtain ⟨e, he⟩ : ∃ e, r0.2.2.entries[sint.nat ii]? = some e :=
                                ⟨_, List.getElem?_eq_getElem hil⟩
                              rw [ite_eq_left (show 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ids0.len from
                                ⟨Hf.1, Hif⟩)]
                              wp_apply (wp_load_slice_index (V := swift.CommandId) ids0 (sint.Z ii) _ _
                                (ofCmdId e.id) Hf.1) $$ [Hids0] as -
                              · iframe #; ipureintro
                                rw [show (sint.Z ii).toNat = sint.nat ii by word, List.getElem?_map, he]; rfl
                              wp_bind (If (Val _) _ (Val #false))
                              iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (e.id = dd))⌝))) $$ []
                              · wp_if_destruct
                                · ipureintro; congr 1
                                  apply decide_eq_decide.mpr
                                  constructor
                                  · intro h
                                    rw [show e.id = ⟨e.id.cl, e.id.seq⟩ from rfl,
                                      show dd = ⟨dd.cl, dd.seq⟩ from rfl, Hif, h]
                                  · intro h; rw [h]
                                · ipureintro; congr 1
                                  symm; apply decide_eq_false
                                  intro h; apply Hif; rw [h]
                              iintro %v %hv
                              subst hv
                              by_cases hid : e.id = dd
                              · rw [show decide (e.id = dd) = true from decide_eq_true hid]
                                wp_auto
                                have hR0' : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len :=
                                  ⟨by decide, hR0⟩
                                rw [ite_eq_left hR0']
                                wp_apply (wp_load_slice_index (V := Loc) rsl (sint.Z (W64 0)) _ _ r0.1
                                  (by decide)) $$ [Hrs] as -
                                · iframe #; ipureintro; rw [hr0]; rfl
                                ihave %Hphl0 := ownSlice_len $$ Hph0
                                simp only [List.length_map] at Hphl0
                                have hphb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ph0.len := by
                                  constructor <;> word
                                rw [ite_eq_left hphb]
                                wp_apply (wp_load_slice_index (V := w64) ph0 (sint.Z ii) _ _ e.phase Hf.1)
                                  $$ [Hph0] as -
                                · iframe #; ipureintro
                                  rw [show (sint.Z ii).toNat = sint.nat ii by word, List.getElem?_map, he]; rfl
                                ihave #He := (BigSepL.bigSepL_lookup (Φ := fun i e => iprop(∃ (c : state.Command)
                                  (sd : swift.SDep), ⌜cmL0[i]? = some c ∧ dpL0[i]? = some sd⌝ ∗
                                  swift.repEntryObj c sd e)) he) $$ Hents0
                                icases He with ⟨%cx, %sd, %hcsd, #He⟩
                                iunfold swift.repEntryObj at He
                                icases He with ⟨%vs, %hc, #Hvs, #Hsd⟩
                                rw [ite_eq_left hR0']
                                wp_apply (wp_load_slice_index (V := Loc) rsl (sint.Z (W64 0)) _ _ r0.1
                                  (by decide)) $$ [Hrs] as -
                                · iframe #; ipureintro; rw [hr0]; rfl
                                ihave %Hcml0 := ownSlice_len $$ Hcm0
                                have hcmb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z cm0.len := by
                                  constructor <;> word
                                rw [ite_eq_left hcmb]
                                wp_apply (wp_load_slice_index (V := state.Command) cm0 (sint.Z ii) cmL0 _ cx
                                  hcmb.1) $$ [Hcm0] as -
                                · iframe #; ipureintro
                                  rw [show (sint.Z ii).toNat = sint.nat ii by word]; exact hcsd.1
                                rw [ite_eq_left hR0']
                                wp_apply (wp_load_slice_index (V := Loc) rsl (sint.Z (W64 0)) _ _ r0.1
                                  (by decide)) $$ [Hrs] as -
                                · iframe #; ipureintro; rw [hr0]; rfl
                                ihave %Hdpl0 := ownSlice_len $$ Hdp0
                                have hdpb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z dp0.len := by
                                  constructor <;> word
                                rw [ite_eq_left hdpb]
                                icases ownSlice_elem_acc (V := swift.SDep) (sint.Z ii) sd dp0 _ dpL0 hdpb.1
                                  (by rw [show (sint.Z ii).toNat = sint.nat ii by word]; exact hcsd.2) $$ Hdp0
                                  with ⟨Hsde, -⟩
                                iStructNamed Hsde
                                wp_auto
                                wp_for_post
                                have hfind : swift.rec.r0find false Rm dd = some e := by
                                  simp only [swift.rec.r0find, hRm, hr0, List.map_cons, Bool.false_eq_true,
                                    ↓reduceIte]
                                  exact swift.rec.find_take_succ_some Hf.2.2 he hid
                                have hbd : B dd = some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩ := by
                                  rw [hB]; exact swift.rec.recBest_found hfind
                                have hph3 := (Hok.ents r0.2 (List.mem_map_of_mem hr0P) e
                                  (List.mem_of_getElem? he)).1
                                ihave Hnew : swift.recOwn «$r0_ptr» ⟨e.phase.toNat, e.cmd, e.dep, 2⟩ false
                                  $$ [«$r0»]
                                · iunfold swift.recOwn
                                  iexists e.phase, W64 2, vs, sd.Dep'
                                  rw [hc]
                                  simp only [Bool.false_eq_true, ↓reduceIte]
                                  iframe «$r0» Hvs Hsd
                                  ipureintro
                                  exact ⟨by first | rfl | trivial, hph3, by first | rfl | trivial, by omega⟩
                                iframe
                                iright
                                isplitr
                                · ipureintro; rfl
                                iexists «$r0_ptr»
                                rw [hbd]
                                simp only [swift.optOwn]
                                iframe
                              · rw [show decide (e.id = dd) = false from decide_eq_false hid]
                                wp_auto
                                wp_for_post
                                iframe
                                iexists ii + W64 1, _, _
                                iframe
                                ipureintro
                                refine ⟨by word, by word, ?_⟩
                                rw [swift.rec.nat_succ_of_lt _ _ Hf.1 Hif]
                                exact swift.rec.find_take_succ_none Hf.2.2 he hid
                            · have hii : sint.nat ii = r0.2.2.entries.length := by rw [Hidsl0.1]; word
                              rw [hii, List.take_length] at Hf
                              iframe
                              ileft
                              iframe
                              ipureintro
                              refine ⟨trivial, ?_⟩
                              simp only [swift.rec.r0find, hRm, hr0, List.map_cons, Bool.false_eq_true,
                                ↓reduceIte]
                              exact Hf.2.2
                          · have hnil : prsR = [] := by
                              cases prsR with
                              | nil => rfl
                              | cons r0 rs => exfalso; simp at Hrl; have := Hrl.1; word
                            iframe
                            ileft
                            iframe
                            ipureintro
                            refine ⟨trivial, ?_⟩
                            simp [swift.rec.r0find, hRm, hnil]
                        · wp_auto
                          iframe
                          ileft
                          iframe
                          ipureintro
                          exact ⟨rfl, rfl⟩
                      iintro %v ⟨leaderInU, R, d, Hv⟩
                      icases Hv with (⟨%hv, «$res0»⟩ | ⟨%hv, %pb, «$res0», Hb⟩)
                      · obtain ⟨hv, hnf⟩ := hv
                        subst hv
                        wp_auto
                        wp_bind (App (Val (GoInstruction (CompositeLiteral
                          (go.GoType.SliceType (go.GoType.SliceType
                            (go.GoType.PointerType swift.MNewLeaderAckN.ty)))))) (Val (LiteralValueV _)))
                        iapply wp_slice_literal (V := GoSlice)
                          (t := go.GoType.SliceType (go.GoType.PointerType swift.MNewLeaderAckN.ty)) [usl, asl]
                        wp_auto
                        isplitl []
                        · ipureintro; rfl
                        iintro %lsl ⟨Hlsl, -⟩
                        wp_auto
                        ihave %Hlsll := ownSlice_len $$ Hlsl
                        ihave %HUl := ownSlice_len $$ Hus
                        ihave %HAl := ownSlice_len $$ Has
                        simp only [List.length_map] at HUl HAl
                        simp only [List.length_cons, List.length_nil] at Hlsll
                        ihave HL : (∃ (t : w64) (lv : GoSlice),
                            "t" ∷ i_ptr ↦ t ∗ "list" ∷ list_ptr ↦ lv ∗ "b" ∷ b_ptr ↦ Perennial.zero_val Loc ∗
                            "%Ht" ∷ ⌜0 ≤ sint.Z t ∧ sint.Z t ≤ 2 ∧
                              (1 ≤ sint.nat t → sp.recPick Um dd = none) ∧
                              (2 ≤ sint.nat t → sp.recPick Am dd = none)⌝ : IProp netDistGF)
                          $$ [i list b]
                        · iexists W64 0, _
                          iframe
                          ipureintro
                          refine ⟨by decide, by decide, ?_, ?_⟩ <;> intro h <;>
                            rw [show sint.nat (W64 0) = 0 from rfl] at h <;> omega
                        wp_for HL
                        wp_if_destruct
                        · have ht2 := swift.rec.lt_two_of Hlsll.1 Hif
                          obtain ⟨Lp, ls, hls, hLsub, hcase⟩ : ∃ (Lp : List swift.rec.Pr) (ls : GoSlice),
                              [usl, asl][sint.nat t]? = some ls ∧ (∀ q ∈ Lp, q ∈ prsA) ∧
                              ((sint.nat t = 0 ∧ ls = usl ∧ Lp = prsU) ∨
                                (sint.nat t = 1 ∧ ls = asl ∧ Lp = prsA)) := by
                            by_cases h0 : sint.nat t = 0
                            · refine ⟨prsU, usl, by rw [h0]; rfl, ?_, Or.inl ⟨h0, rfl, rfl⟩⟩
                              intro q hq; rw [hprsU] at hq; exact (List.mem_filter.mp hq).1
                            · have h1 : sint.nat t = 1 := by
                                have h3 : sint.nat t = (sint.Z t).toNat := rfl
                                rw [h3] at h0 ⊢; omega
                              exact ⟨prsA, asl, by rw [h1]; rfl, fun q hq => hq, Or.inr ⟨h1, rfl, rfl⟩⟩
                          ihave #Hls : (ls ↦*□ Lp.map Prod.fst) $$ []
                          · rcases hcase with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
                            · iexact Hus
                            · iexact Has
                          ihave %Hlsl' := ownSlice_len $$ Hls
                          simp only [List.length_map] at Hlsl'
                          rw [ite_eq_left ⟨Ht.1, Hif⟩]
                          wp_apply (wp_load_slice_index (V := GoSlice) _ (sint.Z t) _ _ ls Ht.1) $$ [Hlsl]
                            as Hlsl
                          · iframe; ipureintro; exact hls
                          ihave HM : (∃ (jj : w64) (av bv : Loc) (bo : Option sp.RecEntry),
                              "jj" ∷ i_ptr ↦ jj ∗ "a" ∷ a_ptr ↦ av ∗ "b" ∷ b_ptr ↦ bv ∗
                              "Hb" ∷ swift.optOwn bv bo ∗
                              "%Hm" ∷ ⌜0 ≤ sint.Z jj ∧ sint.Z jj ≤ sint.Z ls.len ∧
                                bo = (Lp.take (sint.nat jj)).foldl
                                  (fun b q => q.2.2.entries.foldl (swift.rec.pickStep dd) b) none⌝ :
                              IProp netDistGF) $$ [i a b]
                          · iexists W64 0, _, _, none
                            iframe
                            iunfold swift.optOwn
                            ipureintro
                            refine ⟨rfl, by decide, by word, ?_⟩
                            rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
                          wp_for HM
                          wp_if_destruct
                          · have hjl : sint.nat jj < Lp.length := by
                              rw [Hlsl'.1]; exact swift.rec.nat_lt_of_lt _ _ Hm.1 Hif
                            obtain ⟨q, hq⟩ : ∃ q, Lp[sint.nat jj]? = some q :=
                              ⟨_, List.getElem?_eq_getElem hjl⟩
                            have hqA : q ∈ prsA := hLsub q (List.mem_of_getElem? hq)
                            have hqP : q ∈ prs := hAperm.mem_iff.mp hqA
                            rw [ite_eq_left (show 0 ≤ sint.Z jj ∧ sint.Z jj < sint.Z ls.len from ⟨Hm.1, Hif⟩)]
                            wp_apply (wp_load_slice_index (V := Loc) ls (sint.Z jj) _ _ q.1 Hm.1) $$ [Hls] as -
                            · iframe #; ipureintro
                              rw [show (sint.Z jj).toNat = sint.nat jj by word, List.getElem?_map, hq]; rfl
                            ihave #Hq := (BigSepL.bigSepL_mem (Φ := fun q : swift.rec.Pr =>
                              swift.ackObj q.1 q.2) hqA) $$ HprsA
                            iunfold swift.ackObj at Hq
                            icases Hq with ⟨%rep, %bl, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, #Hp,
                              #Hids, #Hph, #Hcm, #Hdp, %Hqf, #Hents⟩
                            ihave #Hp' := Hp
                            iStructNamed Hp'
                            wp_auto
                            rename_i gip
                            irename i => Hrng
                            irename i => Hgi
                            ihave %Hidsl := ownSlice_len $$ Hids
                            simp only [List.length_map] at Hidsl
                            have htkm : (Lp.take (sint.nat (jj + W64 1))).foldl
                                (fun b q => q.2.2.entries.foldl (swift.rec.pickStep dd) b) none =
                                q.2.2.entries.foldl (swift.rec.pickStep dd) bo := by
                              rw [swift.rec.nat_succ_of_lt _ _ Hm.1 Hif,
                                swift.rec.foldl_take_succ _ _ _ _ _ hq, ← Hm.2.2]
                            ihave HI3 : (∃ (ii : w64) (idv : swift.CommandId) (gi : w64) (bv' : Loc)
                                (bo' : Option sp.RecEntry),
                                "ii" ∷ i_ptr ↦ ii ∗ "id" ∷ id_ptr ↦ idv ∗ "gi" ∷ gip ↦ gi ∗
                                "b" ∷ b_ptr ↦ bv' ∗ "Hb" ∷ swift.optOwn bv' bo' ∗
                                "%Hi3" ∷ ⌜0 ≤ sint.Z ii ∧ sint.Z ii ≤ sint.Z ids.len ∧
                                  bo' = (q.2.2.entries.take (sint.nat ii)).foldl (swift.rec.pickStep dd) bo⌝ :
                                IProp netDistGF) $$ [Hrng id Hgi b Hb]
                            · iexists W64 0, _, _, bv, bo
                              iframe
                              ipureintro; refine ⟨by word, by word, ?_⟩
                              rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
                            wp_for HI3
                            wp_if_destruct
                            · have hil : sint.nat ii < q.2.2.entries.length := by
                                rw [Hidsl.1]; exact swift.rec.nat_lt_of_lt _ _ Hi3.1 Hif
                              obtain ⟨e, he⟩ : ∃ e, q.2.2.entries[sint.nat ii]? = some e :=
                                ⟨_, List.getElem?_eq_getElem hil⟩
                              have hents := Hok.ents q.2 (List.mem_map_of_mem hqP) e (List.mem_of_getElem? he)
                              rw [ite_eq_left (show 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ids.len from ⟨Hi3.1, Hif⟩)]
                              wp_apply (wp_load_slice_index (V := swift.CommandId) ids (sint.Z ii) _ _
                                (ofCmdId e.id) Hi3.1) $$ [Hids] as -
                              · iframe #; ipureintro
                                rw [show (sint.Z ii).toNat = sint.nat ii by word, List.getElem?_map, he]; rfl
                              wp_bind (If (Val _) _ (Val #false))
                              iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (e.id = dd))⌝))) $$ []
                              · wp_if_destruct
                                · ipureintro; congr 1
                                  apply decide_eq_decide.mpr
                                  constructor
                                  · intro h
                                    rw [show e.id = ⟨e.id.cl, e.id.seq⟩ from rfl,
                                      show dd = ⟨dd.cl, dd.seq⟩ from rfl, Hif, h]
                                  · intro h; rw [h]
                                · ipureintro; congr 1
                                  symm; apply decide_eq_false
                                  intro h; apply Hif; rw [h]
                              iintro %v %hv
                              subst hv
                              have htk3 : (q.2.2.entries.take (sint.nat (ii + W64 1))).foldl
                                  (swift.rec.pickStep dd) bo = swift.rec.pickStep dd bo' e := by
                                rw [swift.rec.nat_succ_of_lt _ _ Hi3.1 Hif,
                                  swift.rec.foldl_take_succ _ _ _ _ _ he, ← Hi3.2.2]
                              by_cases hid : e.id = dd
                              · rw [show decide (e.id = dd) = true from decide_eq_true hid]
                                wp_auto
                                wp_bind (If _ (Val #true) _)
                                iapply (wp_wand (Φ := fun v => iprop(⌜v = #(swift.rec.pickCond bo' e)⌝ ∗
                                    b_ptr ↦ bv' ∗ swift.optOwn bv' bo' ∗ a_ptr ↦ q.1 ∗ gip ↦ ii))) $$ [b Hb a gi]
                                · ihave %Hphl := ownSlice_len $$ Hph
                                  simp only [List.length_map] at Hphl
                                  cases bo' with
                                  | none =>
                                    iunfold swift.optOwn at Hb
                                    icases Hb with %Hb
                                    subst Hb
                                    rw [show decide (null = null) = true from decide_eq_true rfl]
                                    wp_auto
                                    iframe
                                    iunfold swift.optOwn
                                    ipureintro; exact ⟨rfl, rfl⟩
                                  | some b0 =>
                                    iunfold swift.optOwn at Hb
                                    iunfold swift.recOwn at Hb
                                    icases Hb with ⟨%phb, %clsb, %vsb, %dslb, Hpb, #Hvsb, Hdslb, %Hphb⟩
                                    ihave %Hbn := typedPointsto_not_null $$ Hpb
                                    rw [show decide (bv' = null) = false from decide_eq_false Hbn]
                                    wp_auto
                                    have hphb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ph.len := by
                                      constructor <;> word
                                    rw [ite_eq_left hphb]
                                    wp_apply (wp_load_slice_index (V := w64) ph (sint.Z ii) _ _ e.phase Hi3.1)
                                      $$ [Hph] as -
                                    · iframe #; ipureintro
                                      rw [show (sint.Z ii).toNat = sint.nat ii by word, List.getElem?_map, he]; rfl
                                    have hcmp : decide (sint.Z phb < sint.Z e.phase) =
                                        swift.rec.pickCond (some b0) e := by
                                      have h1 : phb.toNat ≤ 3 := by
                                        have := Hphb.1; have := Hphb.2.1
                                        rw [show uint.nat phb = phb.toNat from rfl] at *; omega
                                      rw [swift.rec.sint_small phb h1, swift.rec.sint_small e.phase hents.1]
                                      unfold swift.rec.pickCond
                                      apply decide_eq_decide.mpr
                                      rw [← Hphb.1, show uint.nat phb = phb.toNat from rfl]; omega
                                    rw [hcmp]
                                    iframe
                                    isplitr
                                    · ipureintro; rfl
                                    simp only [swift.optOwn]
                                    iunfold swift.recOwn
                                    iexists phb, clsb, vsb, dslb
                                    iframe
                                    iframe #
                                    ipureintro; exact Hphb
                                iintro %v ⟨%hv, b, Hb, a, gi⟩
                                subst hv
                                rw [swift.rec.pickStep_eq hid] at htk3
                                cases hpc : swift.rec.pickCond bo' e
                                · rw [hpc] at htk3
                                  simp only [Bool.false_eq_true, ↓reduceIte] at htk3
                                  wp_auto
                                  wp_for_post
                                  iframe
                                  iexists ii + W64 1, _, _, bv', bo'
                                  iframe
                                  ipureintro
                                  refine ⟨by word, by word, ?_⟩
                                  rw [htk3]
                                · rw [hpc] at htk3
                                  simp only [↓reduceIte] at htk3
                                  wp_auto
                                  ihave %Hphl := ownSlice_len $$ Hph
                                  simp only [List.length_map] at Hphl
                                  have hphb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ph.len := by
                                    constructor <;> word
                                  rw [ite_eq_left hphb]
                                  wp_apply (wp_load_slice_index (V := w64) ph (sint.Z ii) _ _ e.phase Hi3.1)
                                    $$ [Hph] as -
                                  · iframe #; ipureintro
                                    rw [show (sint.Z ii).toNat = sint.nat ii by word, List.getElem?_map, he]; rfl
                                  ihave #He := (BigSepL.bigSepL_lookup (Φ := fun i e => iprop(∃ (c : state.Command)
                                    (sd : swift.SDep), ⌜cmL[i]? = some c ∧ dpL[i]? = some sd⌝ ∗
                                    swift.repEntryObj c sd e)) he) $$ Hents
                                  icases He with ⟨%cx, %sd, %hcsd, #He⟩
                                  iunfold swift.repEntryObj at He
                                  icases He with ⟨%vs, %hc, #Hvs, #Hsd⟩
                                  ihave %Hcml := ownSlice_len $$ Hcm
                                  have hcmb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z cm.len := by
                                    constructor <;> word
                                  rw [ite_eq_left hcmb]
                                  wp_apply (wp_load_slice_index (V := state.Command) cm (sint.Z ii) cmL _ cx
                                    hcmb.1) $$ [Hcm] as -
                                  · iframe #; ipureintro
                                    rw [show (sint.Z ii).toNat = sint.nat ii by word]; exact hcsd.1
                                  ihave %Hdpl := ownSlice_len $$ Hdp
                                  have hdpb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z dp.len := by
                                    constructor <;> word
                                  rw [ite_eq_left hdpb]
                                  icases ownSlice_elem_acc (V := swift.SDep) (sint.Z ii) sd dp _ dpL hdpb.1
                                    (by rw [show (sint.Z ii).toNat = sint.nat ii by word]; exact hcsd.2) $$ Hdp
                                    with ⟨Hsde, -⟩
                                  iStructNamed Hsde
                                  wp_auto
                                  ihave Hnew : swift.optOwn «$r0_ptr» (some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩)
                                    $$ [«$r0»]
                                  · simp only [swift.optOwn]
                                    iunfold swift.recOwn
                                    iexists e.phase, W64 2, vs, sd.Dep'
                                    rw [hc]
                                    simp only [Bool.false_eq_true, ↓reduceIte]
                                    iframe «$r0» Hvs Hsd
                                    ipureintro
                                    exact ⟨by first | rfl | trivial, hents.1, by first | rfl | trivial, by omega⟩
                                  wp_for_post
                                  iframe
                                  iexists ii + W64 1, _, _, «$r0_ptr», _
                                  iframe
                                  ipureintro
                                  refine ⟨by word, by word, ?_⟩
                                  rw [htk3]
                              · rw [show decide (e.id = dd) = false from decide_eq_false hid]
                                wp_auto
                                wp_for_post
                                iframe
                                iexists ii + W64 1, _, _, bv', bo'
                                iframe
                                ipureintro
                                refine ⟨by word, by word, ?_⟩
                                rw [htk3, swift.rec.pickStep_ne hid]
                            · have hii : sint.nat ii = q.2.2.entries.length := by rw [Hidsl.1]; word
                              rw [hii, List.take_length] at Hi3
                              wp_for_post
                              iframe
                              iexists jj + W64 1, _, bv', bo'
                              iframe
                              ipureintro
                              refine ⟨by word, by word, ?_⟩
                              rw [htkm, Hi3.2.2]
                          · have hjj : sint.nat jj = Lp.length := by rw [Hlsl'.1]; word
                            rw [hjj, List.take_length, ← swift.rec.recPick_pr] at Hm
                            have hbB : ∀ b0, sp.recPick (Lp.map Prod.snd) dd = some b0 → B dd = some b0 := by
                              intro b0
                              intro hb0
                              rw [hB, swift.rec.recBest_nf hnf]
                              rcases hcase with ⟨h0, -, rfl⟩ | ⟨h1, -, rfl⟩
                              · rw [← hUm] at hb0; rw [hb0]
                              · rw [← hAm] at hb0
                                rw [Ht.2.2.1 (by omega), hb0]
                            cases hbo : bo with
                            | none =>
                              rw [hbo] at Hm
                              iunfold swift.optOwn at Hb
                              icases Hb with %Hb
                              subst Hb
                              rw [show decide (null = null) = true from decide_eq_true rfl]
                              wp_auto
                              wp_for_post
                              iframe
                              iexists t + W64 1, _
                              iframe
                              ipureintro
                              refine ⟨by word, by have := ht2; word, ?_, ?_⟩
                              · intro _
                                rcases hcase with ⟨h0, -, rfl⟩ | ⟨h1, -, rfl⟩
                                · rw [hUm]; exact Hm.2.2.symm
                                · exact Ht.2.2.1 (by omega)
                              · intro h2
                                rcases hcase with ⟨h0, -, rfl⟩ | ⟨h1, -, rfl⟩
                                · exfalso; rw [swift.rec.nat_succ_of_lt _ _ Ht.1 (by omega)] at h2; omega
                                · rw [hAm]; exact Hm.2.2.symm
                            | some b0 =>
                              rw [hbo] at Hm
                              have hbd := hbB b0 Hm.2.2.symm
                              iunfold swift.optOwn at Hb
                              ihave %Hbn : ⌜bv ≠ null⌝ $$ [Hb]
                              · iunfold swift.recOwn at Hb
                                icases Hb with ⟨%_, %_, %_, %_, Hpb, -⟩
                                iapply typedPointsto_not_null $$ Hpb
                              rw [show decide (bv = null) = false from decide_eq_false Hbn]
                              wp_auto
                              wp_for_post
                              iexists bv
                              rw [hbd]
                              simp only [swift.optOwn]
                              iframe
                              try (ipureintro; trivial)
                        · have ht2 := swift.rec.ge_two_of Hlsll.1 Hif
                          have hnone : B dd = none := by
                            rw [hB, swift.rec.recBest_nf hnf, Ht.2.2.1 (by
                              have h3 : sint.nat t = (sint.Z t).toNat := rfl
                              rw [h3]; omega), Ht.2.2.2 (by
                              have h3 : sint.nat t = (sint.Z t).toNat := rfl
                              rw [h3]; omega)]
                          iexists null
                          rw [hnone]
                          simp only [swift.optOwn]
                          iframe
                          try (ipureintro; trivial)
                      · subst hv
                        wp_auto
                        iexists pb
                        iframe
                        try (ipureintro; trivial)
                    iintro %v ⟨%pb, %hv, leaderInU, R, U, acks, d, Hb⟩
                    subst hv
                    wp_auto
                    cases hbd : B dd with
                    | none =>
                      iunfold swift.optOwn at Hb
                      icases Hb with %Hb
                      subst Hb
                      rw [show decide (null = null) = true from decide_eq_true rfl]
                      wp_auto
                      wp_for_post
                      iframe
                      iexists jj + W64 1, _, kg, og, mk', wsl', dsl', wl', dl
                      iframe
                      ipureintro
                      refine ⟨by word, by word, ?_, hkp, hmc, hog1, hog2⟩
                      rw [htk, swift.rec.closeDep_none hdc hkn hbd]
                    | some bd =>
                      iunfold swift.optOwn at Hb
                      ihave %Hpbn : ⌜pb ≠ null⌝ $$ [Hb]
                      · iunfold swift.recOwn at Hb
                        icases Hb with ⟨%_, %_, %_, %_, Hpb, -⟩
                        iapply typedPointsto_not_null $$ Hpb
                      rw [show decide (pb = null) = false from decide_eq_false Hpbn]
                      wp_auto
                      wp_apply (wp_mapInsert _ km0 mk' (ofCmdId dd) pb) $$ Hm as Hm
                      have hcd : ofCmdId c ≠ ofCmdId dd := by
                        intro h; apply hdc; exact ((swift.rec.ofCmdId_eq_iff _ _).mp h).symm
                      have hxd : (GMap.delete (ofCmdId c) mk') !! ofCmdId dd = none := by
                        rw [GMap.lookup_delete_ne _ hcd]; exact hx
                      ihave Hkents := swift.keptEnts_insert kg og _ (ofCmdId dd) pb bd false hxd
                        $$ [Hkents Hb]
                      · iframe
                      rw [← GMap.delete_insert_ne _ _ hcd, toCmdId_ofCmdId]
                      wp_bind (App (Val (GoInstruction (CompositeLiteral
                        (go.GoType.SliceType swift.CommandId.ty)))) (Val (LiteralValueV _)))
                      iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [ofCmdId dd]
                      wp_auto
                      isplitl []
                      · ipureintro; rfl
                      iintro %lsl ⟨Hlsl, -⟩
                      wp_auto
                      wp_apply wp_slice_append $$ [Hws Hwcap Hlsl] as %nwsl ⟨Hws, Hwcap, -⟩
                      · iframe
                      wp_bind (App (Val (GoInstruction (CompositeLiteral
                        (go.GoType.SliceType swift.CommandId.ty)))) (Val (LiteralValueV _)))
                      iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [ofCmdId dd]
                      wp_auto
                      isplitl []
                      · ipureintro; rfl
                      iintro %lsl2 ⟨Hlsl2, -⟩
                      wp_auto
                      wp_apply wp_slice_append $$ [Hdep Hdcap Hlsl2] as %ndsl ⟨Hdep, Hdcap, -⟩
                      · iframe
                      wp_for_post
                      iframe
                      iexists jj + W64 1, _, kg.set dd bd, swift.updO og dd false, _, nwsl, ndsl,
                        wl' ++ [dd], dl ++ [dd]
                      rw [List.map_append, List.map_append]
                      iframe
                      ipureintro
                      refine ⟨by word, by word, ?_, ?_, ?_, ?_, ?_⟩
                      · rw [htk, swift.rec.closeDep_new hdc hkn hbd]
                      · have := swift.keptPure_insert hkp (ofCmdId dd) pb bd
                        rwa [toCmdId_ofCmdId] at this
                      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hcd)]; exact hmc
                      · intro y hy; unfold swift.updO
                        by_cases hyd : y = dd
                        · simp [hyd]
                        · simp only [hyd, ↓reduceIte]
                          exact hog1 y (by simpa [hyd] using hy)
                      · intro y hy; unfold swift.updO
                        have hyd : y ≠ dd := fun h => hy (by simp [h])
                        simp only [hyd, ↓reduceIte]
                        exact hog2 y (fun h => hy (List.mem_append_left _ h))
              · have hjj : sint.nat jj = ec.dep.length := by rw [Hdslcl.1]; word
                obtain ⟨hj0, hjl', hfold, hkp, hmc, hog1, hog2⟩ := Hd
                rw [hjj, List.take_length] at hfold
                have hcov' : ∀ y, (B y).isSome → y ∈ A := by rw [hB]; exact hcov
                have hci := swift.rec.CI_step hA hcov' ⟨hit, hμ, hwnd, hwk, hof, hot⟩ hec og
                  (by rw [hfold]; exact hog1) (by rw [hfold]; exact hog2)
                rw [hfold] at hci
                ihave Hnew : swift.recOwn pc { ec with dep := dl } true $$ [Hpc Hdep Hdcap]
                · iunfold swift.recOwn
                  iexists phc, clsc, vsc, dsl'
                  simp only [↓reduceIte]
                  iframe
                  iframe #
                  ipureintro; exact Hphc
                ihave Hkept := swift.kept_set km0 kg og mk' (ofCmdId c) pc { ec with dep := dl } true hkp
                  $$ [Hm Hkents Hnew]
                · rw [GMap.insert_id _ _ _ hmc]
                  iframe
                rw [toCmdId_ofCmdId]
                wp_for_post
                iframe
                iexists n + 1, _, wl', _, wsl'
                iframe
                ipureintro
                exact hci
            · have hlen0 : ¬ (sint.Z (W64 0) < sint.Z wsl.len) := by
                first
                | (simpa using Hif)
                | (intro h; apply Hif; simp [h])
              ihave %Hwl := ownSlice_len $$ Hws
              have hwl : wl = [] := by
                cases wl with
                | nil => rfl
                | cons c w =>
                  exfalso; apply hlen0
                  have h2 := Hwl.1
                  simp at h2
                  have h0 : sint.Z (W64 0) = 0 := rfl
                  rw [h0, show sint.nat wsl.len = (sint.Z wsl.len).toNat from rfl] at *
                  omega
              subst hwl
              have hμf : w0.length + sp.unkept A k2 <
                  ((prs.map Prod.snd).flatMap (·.2.entries)).length + k2.length + 1 := by
                have h1 : w0.length = k2.length := by
                  rw [hw0', List.length_map]; have := hperm.length_eq; simp at this; omega
                have h2 := swift.rec.unkept_le A k2
                omega
              rw [hw0', ← hw0] at Hci hμf
              obtain ⟨hcl, hallo⟩ := swift.rec.CI_done Hci _ hμf
              ihave Hkept := swift.kept_o_congr km0 kc oc (fun _ => true) hallo $$ Hkept
              -- rule 3b
              have hAreps : ∀ a ∈ Am, a ∈ prs.map Prod.snd := fun a ha => hAperm'.mem_iff.mp ha
              have hcmd3 : sp.CmdFrom Am kc := by
                rw [← hcl]; unfold sp.closure
                exact sp.iter_closeStep_cmd (fun d => by
                  rw [hB]; exact sp.recBest_ok Am li Rm Um (fun a ha => hUa a (hRU a ha)) hUa d) _ _ hcmd
              ihave %Hkc := (show swift.keptOwn km0 kc (fun _ => true) ⊢ ⌜(kc.map Prod.fst).Nodup⌝ by
                iintro H; iunfold swift.keptOwn at H; icases H with ⟨%_, -, %Hp, -⟩
                ipureintro; exact Hp.1) $$ Hkept
              have hKS3 : swift.rec.KS kc kc := ⟨fun _ => rfl, Hkc, swift.rec.noscan_of Hok hAreps hcmd3⟩
              wp_bind (If (If (Val _) _ _) _ _)
              iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ leaderInU_ptr ↦ li ∗
                  R_ptr ↦ rsl ∗ kept_ptr ↦ km0 ∗
                  swift.keptOwn km0 (sp.rule3b li Rm kc) (fun _ => true) ∗
                  ⌜swift.rec.KS kc (sp.rule3b li Rm kc)⌝))) $$ [leaderInU R kept Hkept]
              · ihave %Hrl := ownSlice_len $$ Hrs
                simp only [List.length_map] at Hrl
                cases li
                · wp_auto
                  wp_if_destruct
                  · have hR0 := Hif
                    obtain ⟨r0, rs, hr0⟩ : ∃ r0 rs, prsR = r0 :: rs := by
                      cases prsR with
                      | nil => exfalso; simp at Hrl; have := Hrl.1; word
                      | cons r0 rs => exact ⟨r0, rs, rfl⟩
                    have hr0A : r0 ∈ prsA := by
                      have h1 : r0 ∈ prsR := by rw [hr0]; simp
                      rw [hprsR] at h1
                      have h2 := (List.mem_filter.mp h1).1
                      rw [hprsU] at h2; exact (List.mem_filter.mp h2).1
                    have hRm0 : Rm = r0.2 :: rs.map Prod.snd := by rw [hRm, hr0]; rfl
                    wp_apply (wp_map_make1 (K := swift.CommandId) (V := w64)) as %pm0 Hpm
                    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len from
                      ⟨by decide, hR0⟩)]
                    wp_apply (wp_load_slice_index (V := Loc) rsl (sint.Z (W64 0)) _ _ r0.1 (by decide))
                      $$ [Hrs] as -
                    · iframe #; ipureintro; rw [hr0]; rfl
                    ihave #Hq := (BigSepL.bigSepL_mem (Φ := fun q : swift.rec.Pr => swift.ackObj q.1 q.2)
                      hr0A) $$ HprsA
                    iunfold swift.ackObj at Hq
                    icases Hq with ⟨%rep0, %bl0, %cb0, %ids0, %ph0, %cm0, %dp0, %cmL0, %dpL0, #Hp0,
                      #Hids0, #Hph0, #Hcm0, #Hdp0, %Hqf0, #Hents0⟩
                    ihave #Hp0' := Hp0
                    iStructNamed Hp0'
                    wp_auto
                    rename_i gip
                    irename i => Hrng
                    irename i => Hgi
                    ihave %Hidsl0 := ownSlice_len $$ Hids0
                    simp only [List.length_map] at Hidsl0
                    ihave HP : (∃ (ii : w64) (cid : swift.CommandId) (gi : w64) (pm : GMap swift.CommandId w64),
                        "ii" ∷ i_ptr ↦ ii ∗ "cmdId" ∷ cmdId_ptr ↦ cid ∗ "gi" ∷ gip ↦ gi ∗
                        "Hpm" ∷ pm0 ↦$ pm ∗
                        "%Hp" ∷ ⌜0 ≤ sint.Z ii ∧ sint.Z ii ≤ sint.Z ids0.len ∧ ∀ x, pm !! x =
                          ((r0.2.2.entries.take (sint.nat ii)).findIdx? (·.id == toCmdId x)).map
                            (fun i => W64 (i : Int))⌝ : IProp netDistGF) $$ [Hrng cmdId Hgi Hpm]
                    · iexists W64 0, _, _, ∅
                      iframe
                      ipureintro; refine ⟨by word, by word, ?_⟩
                      intro x; rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
                    wp_for HP
                    wp_if_destruct
                    · have hil : sint.nat ii < r0.2.2.entries.length := by
                        rw [Hidsl0.1]; exact swift.rec.nat_lt_of_lt _ _ Hp.1 Hif
                      obtain ⟨e, he⟩ : ∃ e, r0.2.2.entries[sint.nat ii]? = some e :=
                        ⟨_, List.getElem?_eq_getElem hil⟩
                      rw [ite_eq_left (show 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ids0.len from ⟨Hp.1, Hif⟩)]
                      wp_apply (wp_load_slice_index (V := swift.CommandId) ids0 (sint.Z ii) _ _
                        (ofCmdId e.id) Hp.1) $$ [Hids0] as -
                      · iframe #; ipureintro
                        rw [show (sint.Z ii).toNat = sint.nat ii by word, List.getElem?_map, he]; rfl
                      wp_apply (wp_map_lookup2 _ _ pm0 pm (ofCmdId e.id)) $$ Hpm as Hpm
                      have hstep := swift.rec.findIdx_take_succ r0.2.2.entries (sint.nat ii) e he
                      rw [← swift.rec.nat_succ_of_lt _ _ Hp.1 Hif] at hstep
                      cases hx : pm !! ofCmdId e.id with
                      | some pv =>
                        simp only [Option.isSome_some, Bool.not_true]
                        wp_auto
                        wp_for_post
                        iframe
                        iexists ii + W64 1, _, _, pm
                        iframe
                        ipureintro
                        refine ⟨by word, by word, ?_⟩
                        intro x
                        rw [hstep, Hp.2.2 x]
                        cases hfx : (r0.2.2.entries.take (sint.nat ii)).findIdx? (·.id == toCmdId x) with
                        | some i => rfl
                        | none =>
                          have hne : (e.id == toCmdId x) = false := by
                            rw [beq_eq_false_iff_ne]; intro h
                            have := Hp.2.2 x; rw [hfx] at this
                            rw [show x = ofCmdId e.id by rw [h]; rfl, hx] at this; cases this
                          simp [hne]
                      | none =>
                        simp only [Option.isSome_none, Bool.not_false]
                        wp_auto
                        wp_apply (wp_mapInsert _ pm0 pm (ofCmdId e.id) ii) $$ Hpm as Hpm
                        wp_for_post
                        iframe
                        iexists ii + W64 1, _, _, _
                        iframe
                        ipureintro
                        refine ⟨by word, by word, ?_⟩
                        intro x
                        rw [hstep]
                        by_cases hxe : x = ofCmdId e.id
                        · subst hxe
                          rw [GMap.lookup_insert]
                          have := Hp.2.2 (ofCmdId e.id); rw [hx] at this
                          have h0 : (r0.2.2.entries.take (sint.nat ii)).findIdx?
                              (·.id == toCmdId (ofCmdId e.id)) = none := by
                            cases h : (r0.2.2.entries.take (sint.nat ii)).findIdx?
                              (·.id == toCmdId (ofCmdId e.id)) with
                            | none => rfl
                            | some _ => rw [h] at this; cases this
                          rw [h0]
                          simp only [toCmdId_ofCmdId, beq_self_eq_true, ↓reduceIte]
                          simp; word
                        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxe), Hp.2.2 x]
                          have hne : (e.id == toCmdId x) = false := by
                            rw [beq_eq_false_iff_ne]; intro h; apply hxe; rw [h]; rfl
                          cases (r0.2.2.entries.take (sint.nat ii)).findIdx? (·.id == toCmdId x) <;>
                            simp [hne]
                    · have hii : sint.nat ii = r0.2.2.entries.length := by rw [Hidsl0.1]; word
                      rw [hii, List.take_length] at Hp
                      have hpos : ∀ x, pm !! x = (sp.recPos r0.2 (toCmdId x)).map (fun i => W64 (i : Int)) :=
                        fun x => Hp.2.2 x
                      iunfold swift.keptOwn at Hkept
                      icases Hkept with ⟨%mk, Hm, %Hmk, Hkents⟩
                      wp_apply (wp_sortedIds km0 mk (DFrac.own 1)) $$ [Hm] as %isl %ids ⟨Hm, Hids, -, %Hids⟩
                      · iframe; ipureintro
                        rw [swift.keptPure_size Hmk]
                        obtain ⟨_, _, _, _, h4⟩ :=
                          swift.rec.closure_setup _ false Rm Um Am hRU hUa hAperm' kc hcmd3 Hkc
                        have := Hok.size; omega
                      have hperm := swift.keys_perm kc ids Hids.1 Hkc (fun c => by rw [Hids.2.1, Hmk.2 c])
                      have hidsM : sp.sortIds (kc.map Prod.fst) = ids.map toCmdId := Hids.2.2 _ hperm
                      have hr3 : sp.rule3b false Rm kc =
                          (ids.map toCmdId).foldl (sp.rule3bCmd r0.2 (ids.map toCmdId)) kc := by
                        rw [hRm0]; unfold sp.rule3b; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hidsM]
                      ihave %Hisl := ownSlice_len $$ Hids
                      ihave HC3 : (∃ (n : w64) (cv : swift.CommandId) (kg : sp.Kept),
                          "n" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ cv ∗ "Hm" ∷ km0 ↦$ mk ∗
                          "Hkents" ∷ swift.keptEnts kg (fun _ => true) mk ∗
                          "%Hc3" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z isl.len ∧
                            kg = ((ids.map toCmdId).take (sint.nat n)).foldl
                              (sp.rule3bCmd r0.2 (ids.map toCmdId)) kc ∧
                            swift.rec.KS kc kg ∧ swift.keptPure kg mk⌝ : IProp netDistGF)
                        $$ [i c Hm Hkents]
                      · iexists W64 0, _, kc
                        iframe
                        ipureintro
                        refine ⟨by word, by word, ?_, hKS3, Hmk⟩
                        rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
                      wp_for HC3
                      wp_if_destruct
                      · have hnl : sint.nat n < ids.length := by
                          rw [Hisl.1]; exact swift.rec.nat_lt_of_lt _ _ Hc3.1 Hif
                        obtain ⟨c, hc⟩ : ∃ c, ids[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem hnl⟩
                        rw [ite_eq_left (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z isl.len from ⟨Hc3.1, Hif⟩)]
                        wp_apply (wp_load_slice_index (V := swift.CommandId) isl (sint.Z n) _ _ c Hc3.1)
                          $$ [Hids] as Hids
                        · iframe; ipureintro
                          rw [show (sint.Z n).toNat = sint.nat n by word]; exact hc
                        wp_apply (wp_map_lookup2 _ _ pm0 pm c) $$ Hpm as Hpm
                        obtain ⟨hn0, hnl', hkg, hKSg, hkp⟩ := Hc3
                        have hck : (kg.get (toCmdId c)).isSome := by
                          rw [hKSg.1, ← Hmk.2 c, ← Hids.2.1]; exact List.mem_of_getElem? hc
                        obtain ⟨ec, hec⟩ := Option.isSome_iff_exists.mp hck
                        obtain ⟨pc0, hpc0⟩ : ∃ p, mk !! c = some p := by
                          have := hkp.2 c; rw [hec] at this; exact Option.isSome_iff_exists.mp this
                        have hidsn : (ids.map toCmdId)[sint.nat n]? = some (toCmdId c) := by
                          rw [List.getElem?_map, hc]; rfl
                        have htkc : ((ids.map toCmdId).take (sint.nat (n + W64 1))).foldl
                            (sp.rule3bCmd r0.2 (ids.map toCmdId)) kc =
                            sp.rule3bCmd r0.2 (ids.map toCmdId) kg (toCmdId c) := by
                          rw [swift.rec.nat_succ_of_lt _ _ hn0 Hif,
                            swift.rec.foldl_take_succ _ _ _ _ _ hidsn, ← hkg]
                        rw [swift.rec.r3cmd_eq hec] at htkc
                        wp_apply (wp_map_lookup1 _ _ km0 mk c) $$ Hm as Hm
                        rw [hpc0]
                        simp only [Option.getD_some]
                        icases (BigSepM.bigSepM_lookup_acc
                          (show Iris.Std.PartialMap.get? mk c = some pc0 from hpc0)).1
                          $$ Hkents with ⟨⟨%ec', %hec', Hre⟩, Hkents⟩
                        rw [hec] at hec'; cases hec'
                        iunfold swift.recOwn at Hre
                        simp only [↓reduceIte]
                        icases Hre with ⟨%phc, %clsc, %vsc, %dslc, Hpe, #Hvsc, Hdslc, %Hphc⟩
                        wp_auto
                        ihave Hkents := Hkents $$ [Hpe Hdslc]
                        · iexists ec
                          isplitr
                          · ipureintro; exact hec
                          iunfold swift.recOwn
                          iexists phc, clsc, vsc, dslc
                          simp only [↓reduceIte]
                          iframe
                          iframe #
                          ipureintro; exact Hphc
                        have hpcm := hpos c
                        wp_if_destruct
                        · -- class 0: skipped
                          have hc0 : ec.cls = 0 := by rw [← Hphc.2.2.1]; rfl
                          wp_for_post
                          iframe
                          iexists n + W64 1, _, kg
                          iframe
                          ipureintro
                          refine ⟨by word, by word, ?_, hKSg, hkp⟩
                          rw [htkc]; cases sp.recPos r0.2 (toCmdId c) <;> simp [hc0]
                        · have hc0 : ec.cls ≠ 0 := by
                            intro h; apply Hif; apply BitVec.eq_of_toNat_eq
                            have := Hphc.2.2.1; rw [h] at this; exact this
                          cases hrp : sp.recPos r0.2 (toCmdId c) with
                          | none =>
                            rw [hrp] at hpcm
                            have hnone : (pm !! c).isSome = false := by rw [hpcm]; rfl
                            simp only [hnone, Bool.false_eq_true, decide_false, Bool.not_false]
                            wp_auto
                            wp_for_post
                            iframe
                            iexists n + W64 1, _, kg
                            iframe
                            ipureintro
                            refine ⟨by word, by word, ?_, hKSg, hkp⟩
                            rw [htkc, hrp]
                          | some pcN =>
                            rw [hrp] at hpcm htkc
                            simp only [hc0, beq_iff_eq, ↓reduceIte] at htkc
                            have hsome : (pm !! c).isSome = true := by rw [hpcm]; rfl
                            have hpcv : (pm !! c).getD (Perennial.zero_val w64) = W64 (pcN : Int) := by
                              rw [hpcm]; rfl
                            simp only [hsome, hpcv, _root_.decide_true, Bool.not_true]
                            wp_auto
                            ihave HW : (∃ (m : w64) (wv : swift.CommandId) (kw : sp.Kept),
                                "m" ∷ i_ptr ↦ m ∗ "w" ∷ w_ptr ↦ wv ∗ "Hm" ∷ km0 ↦$ mk ∗
                                "Hkents" ∷ swift.keptEnts kw (fun _ => true) mk ∗
                                "%Hw" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z isl.len ∧
                                  kw = ((ids.map toCmdId).take (sint.nat m)).foldl
                                    (sp.rule3bPair r0.2 (toCmdId c) pcN) kg ∧
                                  swift.rec.KS kc kw ∧ swift.keptPure kw mk⌝ : IProp netDistGF)
                              $$ [i w Hm Hkents]
                            · iexists W64 0, _, kg
                              iframe
                              ipureintro
                              refine ⟨by word, by word, ?_, hKSg, hkp⟩
                              rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
                            wp_for HW
                            wp_if_destruct
                            · -- one pair `(c, w)` (`rule3bPair`): the tests (`w == c`, the
                              -- positions, `inConflict`), `Contains`/`recReaches`, the append
                              obtain ⟨hm0, hml, hkw, hKSw, hkpw⟩ := Hw
                              have hml' : sint.nat m < ids.length := by
                                rw [Hisl.1]; exact swift.rec.nat_lt_of_lt _ _ hm0 Hif
                              obtain ⟨w, hw⟩ : ∃ w, ids[sint.nat m]? = some w := ⟨_, List.getElem?_eq_getElem hml'⟩
                              rw [ite_eq_left (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z isl.len from ⟨hm0, Hif⟩)]
                              wp_apply (wp_load_slice_index (V := swift.CommandId) isl (sint.Z m) _ _ w hm0)
                                $$ [Hids] as Hids
                              · iframe; ipureintro
                                rw [show (sint.Z m).toNat = sint.nat m by word]; exact hw
                              wp_apply (wp_map_lookup2 _ _ pm0 pm w) $$ Hpm as Hpm
                              have hidsm : (ids.map toCmdId)[sint.nat m]? = some (toCmdId w) := by
                                rw [List.getElem?_map, hw]; rfl
                              have htkw : ((ids.map toCmdId).take (sint.nat (m + W64 1))).foldl
                                  (sp.rule3bPair r0.2 (toCmdId c) pcN) kg =
                                  sp.rule3bPair r0.2 (toCmdId c) pcN kw (toCmdId w) := by
                                rw [swift.rec.nat_succ_of_lt _ _ hm0 Hif, swift.rec.foldl_take_succ _ _ _ _ _ hidsm, ← hkw]
                              wp_bind (If (Val _) _ (Val #false))
                              iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (w = c))⌝))) $$ []
                              · wp_if_destruct
                                · ipureintro; congr 1
                                  apply decide_eq_decide.mpr
                                  constructor
                                  · intro h; cases w; cases c; simp_all
                                  · intro h; rw [h]
                                · ipureintro; congr 1
                                  symm; apply decide_eq_false
                                  intro h; apply Hif; rw [h]
                              iintro %v %hv
                              subst hv
                              by_cases hwc : w = c
                              · -- `w == c`: skipped
                                rw [show decide (w = c) = true from decide_eq_true hwc]
                                wp_auto
                                wp_for_post
                                iframe
                                iexists m + W64 1, _, kw
                                iframe
                                ipureintro
                                refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                                rw [htkw, hwc]
                                unfold sp.rule3bPair
                                split
                                · simp
                                · rfl
                              rw [show decide (w = c) = false from decide_eq_false hwc]
                              wp_auto
                              have hpw := hpos w
                              have hrlt : ∀ x p, sp.recPos r0.2 x = some p → p < sint.nat ids0.len := by
                                intro x p hx
                                unfold sp.recPos at hx
                                rw [← Hidsl0.1]; exact (List.findIdx?_eq_some_iff_getElem.mp hx).1
                              cases hrw : sp.recPos r0.2 (toCmdId w) with
                              | none =>
                                rw [hrw] at hpw
                                have hnone : (pm !! w).isSome = false := by rw [hpw]; rfl
                                simp only [hnone, Bool.false_eq_true, decide_false, Bool.not_false]
                                wp_auto
                                wp_for_post
                                iframe
                                iexists m + W64 1, _, kw
                                iframe
                                ipureintro
                                refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                                rw [htkw]
                                unfold sp.rule3bPair
                                split
                                · rename_i hp; rw [hrw] at hp; cases hp
                                · rfl
                              | some pwN =>
                                rw [hrw] at hpw
                                have hsomew : (pm !! w).isSome = true := by rw [hpw]; rfl
                                have hpwv : (pm !! w).getD (Perennial.zero_val w64) = W64 (pwN : Int) := by
                                  rw [hpw]; rfl
                                have hpwlt := hrlt _ _ hrw
                                have hpclt := hrlt _ _ hrp
                                simp only [hsomew, hpwv, _root_.decide_true, Bool.not_true]
                                wp_auto
                                have hcmp : decide (sint.Z (W64 (pcN : Int)) < sint.Z (W64 (pwN : Int))) = decide (pcN < pwN) := by
                                  apply decide_eq_decide.mpr
                                  have h1 : sint.Z (W64 (pcN : Int)) = pcN := by word
                                  have h2 : sint.Z (W64 (pwN : Int)) = pwN := by word
                                  rw [h1, h2]; omega
                                rw [hcmp]
                                -- the two entries
                                have hwmk : (mk !! w).isSome = true := (Hids.2.1 w).mp (List.mem_of_getElem? hw)
                                obtain ⟨ew, hew⟩ : ∃ e, kw.get (toCmdId w) = some e := by
                                  have := hkpw.2 w; rw [hwmk] at this; exact Option.isSome_iff_exists.mp this.symm
                                obtain ⟨ecw, hecw⟩ : ∃ e, kw.get (toCmdId c) = some e := by
                                  have := hkpw.2 c; rw [hpc0] at this; exact Option.isSome_iff_exists.mp this.symm
                                obtain ⟨pw0, hpw0⟩ := Option.isSome_iff_exists.mp hwmk
                                have hwc' : (toCmdId w == toCmdId c) = false := by
                                  rw [beq_eq_false_iff_ne]; intro h; exact hwc (swift.toCmdId_inj h)
                                have hstep := swift.rec.r3pair_eq (r0 := r0.2) (pc := pcN) hew hecw
                                rw [hrw] at hstep
                                simp only [hwc', Bool.false_or] at hstep
                                by_cases hgt : pcN < pwN
                                · simp only [show decide (pcN < pwN) = true from decide_eq_true hgt]
                                  wp_auto
                                  wp_for_post
                                  iframe
                                  iexists m + W64 1, _, kw
                                  iframe
                                  ipureintro
                                  refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                                  rw [htkw, hstep]; simp [hgt]
                                simp only [show decide (pcN < pwN) = false from decide_eq_false hgt]
                                wp_auto
                                -- `inConflict(kept[w].cmd, kept[c].cmd)`
                                wp_apply (wp_map_lookup1 _ _ km0 mk w) $$ Hm as Hm
                                rw [hpw0]
                                simp only [Option.getD_some]
                                icases (BigSepM.bigSepM_lookup_acc
                                  (show Iris.Std.PartialMap.get? mk w = some pw0 from hpw0)).1
                                  $$ Hkents with ⟨⟨%ew', %hew', Hre⟩, Hkents⟩
                                rw [hew] at hew'; cases hew'
                                iunfold swift.recOwn at Hre
                                simp only [↓reduceIte]
                                icases Hre with ⟨%phw, %clsw, %vsw, %dslw, Hpw, #Hvsw, Hdslw, %Hphw⟩
                                wp_auto
                                ihave Hkents := Hkents $$ [Hpw Hdslw]
                                · iexists ew
                                  isplitr
                                  · ipureintro; exact hew
                                  iunfold swift.recOwn
                                  iexists phw, clsw, vsw, dslw
                                  simp only [↓reduceIte]
                                  iframe
                                  iframe #
                                  ipureintro; exact Hphw
                                wp_apply (wp_map_lookup1 _ _ km0 mk c) $$ Hm as Hm
                                rw [hpc0]
                                simp only [Option.getD_some]
                                icases (BigSepM.bigSepM_lookup_acc
                                  (show Iris.Std.PartialMap.get? mk c = some pc0 from hpc0)).1
                                  $$ Hkents with ⟨⟨%ec', %hec', Hre⟩, Hkents⟩
                                rw [hecw] at hec'; cases hec'
                                iunfold swift.recOwn at Hre
                                simp only [↓reduceIte]
                                icases Hre with ⟨%phc', %clsc', %vsc', %dslc', Hpc', #Hvsc', Hdslc', %Hphc'⟩
                                wp_auto
                                ihave Hkents := Hkents $$ [Hpc' Hdslc']
                                · iexists ecw
                                  isplitr
                                  · ipureintro; exact hecw
                                  iunfold swift.recOwn
                                  iexists phc', clsc', vsc', dslc'
                                  simp only [↓reduceIte]
                                  iframe
                                  iframe #
                                  ipureintro; exact Hphc'
                                wp_apply (wp_inConflict ew.cmd ecw.cmd vsw vsc')
                                · ipureintro
                                  exact ⟨hKSw.2.2 _ _ hew, hKSw.2.2 _ _ hecw⟩
                                by_cases hcf : sp.Cmd.conflict ew.cmd ecw.cmd = false
                                · rw [hcf]
                                  wp_auto
                                  wp_for_post
                                  iframe
                                  iexists m + W64 1, _, kw
                                  iframe
                                  ipureintro
                                  refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                                  rw [htkw, hstep]; simp [hgt, hcf]
                                have hcf' : sp.Cmd.conflict ew.cmd ecw.cmd = true := by simpa using hcf
                                rw [hcf']
                                wp_auto
                                -- `kept[c].dep.Contains(w)`
                                wp_apply (wp_map_lookup1 _ _ km0 mk c) $$ Hm as Hm
                                rw [hpc0]
                                simp only [Option.getD_some]
                                icases (BigSepM.bigSepM_lookup_acc
                                  (show Iris.Std.PartialMap.get? mk c = some pc0 from hpc0)).1
                                  $$ Hkents with ⟨⟨%ec2, %hec2, Hre⟩, Hkents⟩
                                rw [hecw] at hec2; cases hec2
                                iunfold swift.recOwn at Hre
                                simp only [↓reduceIte]
                                icases Hre with ⟨%phc2, %clsc2, %vsc2, %dslc2, Hpc2, #Hvsc2, ⟨Hdl2, Hdcap2⟩, %Hphc2⟩
                                ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpc2
                                iStructNamed Hpc2
                                wp_apply (wp_Contains _ dslc2 (DFrac.own 1) (DFrac.own 1) (ecw.dep.map ofCmdId) w) $$ [dep Hdl2]
                                  as ⟨dep, Hdl2⟩
                                · iframe
                                ihave Hpc2 : pc0 ↦ swift.recEntry.mk phc2 (state.Command.mk ecw.cmd.op ecw.cmd.key vsc2) dslc2 clsc2
                                  $$ [phase cmd dep class']
                                · iapply typedPointsto_combine _ _ _ Hnn
                                  simp only [TypedPointsto.typedPointstoDef]
                                  iframe
                                have hcont : decide (w ∈ ecw.dep.map ofCmdId) = ecw.dep.contains (toCmdId w) := by
                                  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.contains_iff_mem]
                                  constructor
                                  · intro h; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h; simpa using hy
                                  · intro h; exact List.mem_map.mpr ⟨_, h, ofCmdId_toCmdId w⟩
                                rw [hcont]
                                by_cases hct : ecw.dep.contains (toCmdId w) = true
                                · rw [hct]
                                  wp_auto
                                  ihave Hkents := Hkents $$ [Hpc2 Hdl2 Hdcap2]
                                  · iexists ecw
                                    isplitr
                                    · ipureintro; exact hecw
                                    iunfold swift.recOwn
                                    iexists phc2, clsc2, vsc2, dslc2
                                    simp only [↓reduceIte]
                                    iframe
                                    iframe #
                                    ipureintro; exact Hphc2
                                  wp_for_post
                                  iframe
                                  iexists m + W64 1, _, kw
                                  iframe
                                  ipureintro
                                  refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                                  rw [htkw, hstep]; simp [hgt, hcf', show toCmdId w ∈ ecw.dep by simpa using hct]
                                have hct' : ecw.dep.contains (toCmdId w) = false := by simpa using hct
                                rw [hct']
                                wp_auto
                                ihave Hkents := Hkents $$ [Hpc2 Hdl2 Hdcap2]
                                · iexists ecw
                                  isplitr
                                  · ipureintro; exact hecw
                                  iunfold swift.recOwn
                                  iexists phc2, clsc2, vsc2, dslc2
                                  simp only [↓reduceIte]
                                  iframe
                                  iframe #
                                  ipureintro; exact Hphc2
                                wp_apply (wp_recReaches km0 kw (fun _ => true) mk w c) $$ [Hm Hkents] as Hk
                                · iframe
                                  iunfold swift.keptAt
                                  iframe
                                  ipureintro; exact hkpw
                                iunfold swift.keptAt at Hk
                                icases Hk with ⟨Hm, -, Hkents⟩
                                by_cases hrr : sp.recReaches kw (toCmdId w) (toCmdId c) = true
                                · rw [hrr]
                                  wp_auto
                                  wp_for_post
                                  iframe
                                  iexists m + W64 1, _, kw
                                  iframe
                                  ipureintro
                                  refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                                  rw [htkw, hstep]; simp [hgt, hcf', hct', hrr]
                                have hrr' : sp.recReaches kw (toCmdId w) (toCmdId c) = false := by simpa using hrr
                                rw [hrr']
                                wp_auto
                                -- `kept[c].dep = append(kept[c].dep, w)`
                                wp_apply (wp_map_lookup1 _ _ km0 mk c) $$ Hm as Hm
                                rw [hpc0]
                                simp only [Option.getD_some]
                                icases (BigSepM.bigSepM_delete
                                  (show Iris.Std.PartialMap.get? mk c = some pc0 from hpc0)).1
                                  $$ Hkents with ⟨⟨%ec3, %hec3, Hre⟩, Hkents⟩
                                rw [hecw] at hec3; cases hec3
                                iunfold swift.recOwn at Hre
                                simp only [↓reduceIte]
                                icases Hre with ⟨%phc3, %clsc3, %vsc3, %dslc3, Hpc3, #Hvsc3, ⟨Hdl3, Hdcap3⟩, %Hphc3⟩
                                wp_auto
                                wp_bind (App (Val (GoInstruction (CompositeLiteral
                                  (go.GoType.SliceType swift.CommandId.ty)))) (Val (LiteralValueV _)))
                                iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [w]
                                wp_auto
                                isplitl []
                                · ipureintro; rfl
                                iintro %lsl ⟨Hlsl, -⟩
                                wp_auto
                                wp_apply wp_slice_append $$ [Hdl3 Hdcap3 Hlsl] as %ndsl ⟨Hdl3, Hdcap3, -⟩
                                · iframe
                                wp_apply (wp_map_lookup1 _ _ km0 mk c) $$ Hm as Hm
                                rw [hpc0]
                                simp only [Option.getD_some]
                                wp_auto
                                ihave Hnew : swift.recOwn pc0 { ecw with dep := ecw.dep ++ [toCmdId w] } true
                                  $$ [Hpc3 Hdl3 Hdcap3]
                                · iunfold swift.recOwn
                                  iexists phc3, clsc3, vsc3, ndsl
                                  simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil, ofCmdId_toCmdId]
                                  iframe
                                  iframe #
                                  ipureintro; exact Hphc3
                                ihave Hkents := swift.keptEnts_upd kw (fun _ => true) mk c pc0 _ hpc0 $$ [Hkents Hnew]
                                · iframe
                                wp_for_post
                                iframe
                                iexists m + W64 1, _, _
                                iframe
                                ipureintro
                                refine ⟨by word, by word, ?_, hKSw.setDep hecw _, swift.keptPure_upd hkpw c pc0 _ hpc0⟩
                                rw [htkw, hstep]; simp [hgt, hcf', hrr', show toCmdId w ∉ ecw.dep by simpa using hct']
                            · have hmm : sint.nat m = (ids.map toCmdId).length := by
                                rw [List.length_map, Hisl.1]; word
                              rw [hmm, List.take_length] at Hw
                              obtain ⟨-, -, hkw, hKSw, hkpw⟩ := Hw
                              wp_for_post
                              iframe
                              iexists n + W64 1, _, kw
                              iframe
                              ipureintro
                              refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                              rw [htkc, hkw]
                      · have hnn : sint.nat n = (ids.map toCmdId).length := by
                          rw [List.length_map, Hisl.1]; word
                        rw [hnn, List.take_length, ← hr3] at Hc3
                        obtain ⟨-, -, hkg, hKSg, hkp⟩ := Hc3
                        subst hkg
                        iframe
                        isplitl [Hm Hkents]
                        · iapply swift.kept_close km0 _ _ mk hkp $$ [Hm Hkents]; iframe
                        ipureintro; exact hKSg
                  · have hnil : prsR = [] := by
                      cases prsR with
                      | nil => rfl
                      | cons r0 rs => exfalso; simp at Hrl; have := Hrl.1; word
                    have : Rm = [] := by rw [hRm, hnil]; rfl
                    rw [this]
                    iframe
                    ipureintro; exact hKS3
                · wp_auto
                  iframe
                  ipureintro; exact ⟨rfl, hKS3⟩
              iintro %v ⟨%hv, leaderInU, R, kept, Hkept, %hKS3b⟩
              subst hv
              wp_auto
              -- rule 4
              obtain ⟨k3b, hk3b⟩ : ∃ k, k = sp.rule3b li Rm kc := ⟨_, rfl⟩
              rw [← hk3b] at hKS3b ⊢
              iunfold swift.keptOwn at Hkept
              icases Hkept with ⟨%mk, Hm, %Hmk, Hkents⟩
              wp_apply (wp_sortedIds km0 mk (DFrac.own 1)) $$ [Hm] as %isl %ids ⟨Hm, Hids, -, %Hids⟩
              · iframe; ipureintro
                rw [swift.keptPure_size Hmk, swift.rec.KS_len hKS3b Hkc]
                obtain ⟨_, _, _, _, h4⟩ :=
                  swift.rec.closure_setup _ li Rm Um Am hRU hUa hAperm' kc hcmd3 Hkc
                have := Hok.size; omega
              have hperm4 := swift.keys_perm k3b ids Hids.1 Hmk.1 (fun c => by rw [Hids.2.1, Hmk.2 c])
              have hidsM4 : sp.sortIds (k3b.map Prod.fst) = ids.map toCmdId := Hids.2.2 _ hperm4
              ihave %Hisl := ownSlice_len $$ Hids
              ihave HC4 : (∃ (n : w64) (cv : swift.CommandId) (kg : sp.Kept),
                  "n" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ cv ∗ "Hm" ∷ km0 ↦$ mk ∗
                  "Hkents" ∷ swift.keptEnts kg (fun _ => true) mk ∗
                  "%Hc4" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z isl.len ∧
                    kg = ((ids.map toCmdId).take (sint.nat n)).foldl
                      (sp.rule4Cmd (ids.map toCmdId)) k3b ∧
                    swift.rec.KS kc kg ∧ swift.keptPure kg mk⌝ : IProp netDistGF)
                $$ [i c Hm Hkents]
              · iexists W64 0, _, k3b
                iframe
                ipureintro
                refine ⟨by word, by word, ?_, hKS3b, Hmk⟩
                rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
              wp_for HC4
              wp_if_destruct
              · have hnl : sint.nat n < ids.length := by
                  rw [Hisl.1]; exact swift.rec.nat_lt_of_lt _ _ Hc4.1 Hif
                obtain ⟨c, hc⟩ : ∃ c, ids[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem hnl⟩
                rw [ite_eq_left (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z isl.len from ⟨Hc4.1, Hif⟩)]
                wp_apply (wp_load_slice_index (V := swift.CommandId) isl (sint.Z n) _ _ c Hc4.1)
                  $$ [Hids] as Hids
                · iframe; ipureintro
                  rw [show (sint.Z n).toNat = sint.nat n by word]; exact hc
                obtain ⟨hn0, hnl', hkg, hKSg, hkp⟩ := Hc4
                have hck : (kg.get (toCmdId c)).isSome := by
                  rw [hKSg.1, ← hKS3b.1, ← Hmk.2 c, ← Hids.2.1]; exact List.mem_of_getElem? hc
                obtain ⟨ec, hec⟩ := Option.isSome_iff_exists.mp hck
                obtain ⟨pc0, hpc0⟩ : ∃ p, mk !! c = some p := by
                  have := hkp.2 c; rw [hec] at this; exact Option.isSome_iff_exists.mp this
                have hidsn : (ids.map toCmdId)[sint.nat n]? = some (toCmdId c) := by
                  rw [List.getElem?_map, hc]; rfl
                have htkc : ((ids.map toCmdId).take (sint.nat (n + W64 1))).foldl
                    (sp.rule4Cmd (ids.map toCmdId)) k3b =
                    sp.rule4Cmd (ids.map toCmdId) kg (toCmdId c) := by
                  rw [swift.rec.nat_succ_of_lt _ _ hn0 Hif,
                    swift.rec.foldl_take_succ _ _ _ _ _ hidsn, ← hkg]
                rw [swift.rec.r4cmd_eq hec] at htkc
                wp_apply (wp_map_lookup1 _ _ km0 mk c) $$ Hm as Hm
                rw [hpc0]
                simp only [Option.getD_some]
                icases (BigSepM.bigSepM_lookup_acc
                  (show Iris.Std.PartialMap.get? mk c = some pc0 from hpc0)).1
                  $$ Hkents with ⟨⟨%ec', %hec', Hre⟩, Hkents⟩
                rw [hec] at hec'; cases hec'
                iunfold swift.recOwn at Hre
                simp only [↓reduceIte]
                icases Hre with ⟨%phc, %clsc, %vsc, %dslc, Hpe, #Hvsc, Hdslc, %Hphc⟩
                wp_auto
                ihave Hkents := Hkents $$ [Hpe Hdslc]
                · iexists ec
                  isplitr
                  · ipureintro; exact hec
                  iunfold swift.recOwn
                  iexists phc, clsc, vsc, dslc
                  simp only [↓reduceIte]
                  iframe
                  iframe #
                  ipureintro; exact Hphc
                wp_if_destruct
                · -- class 0: skipped
                  have hc0 : ec.cls = 0 := by rw [← Hphc.2.2.1]; rfl
                  wp_for_post
                  iframe
                  iexists n + W64 1, _, kg
                  iframe
                  ipureintro
                  refine ⟨by word, by word, ?_, hKSg, hkp⟩
                  rw [htkc]; simp [hc0]
                · have hc0 : ec.cls ≠ 0 := by
                    intro h; apply Hif; apply BitVec.eq_of_toNat_eq
                    have := Hphc.2.2.1; rw [h] at this; exact this
                  simp only [hc0, beq_iff_eq, ↓reduceIte] at htkc
                  ihave HW : (∃ (m : w64) (wv : swift.CommandId) (kw : sp.Kept),
                      "m" ∷ i_ptr ↦ m ∗ "a" ∷ a_ptr ↦ wv ∗ "Hm" ∷ km0 ↦$ mk ∗
                      "Hkents" ∷ swift.keptEnts kw (fun _ => true) mk ∗
                      "%Hw" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z isl.len ∧
                        kw = ((ids.map toCmdId).take (sint.nat m)).foldl
                          (sp.rule4Pair (toCmdId c)) kg ∧
                        swift.rec.KS kc kw ∧ swift.keptPure kw mk⌝ : IProp netDistGF)
                    $$ [i a Hm Hkents]
                  · iexists W64 0, _, kg
                    iframe
                    ipureintro
                    refine ⟨by word, by word, ?_, hKSg, hkp⟩
                    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
                  wp_for HW
                  wp_if_destruct
                  · -- one pair `(c, a)` (`rule4Pair`)
                    obtain ⟨hm0, hml, hkw, hKSw, hkpw⟩ := Hw
                    have hml' : sint.nat m < ids.length := by
                      rw [Hisl.1]; exact swift.rec.nat_lt_of_lt _ _ hm0 Hif
                    obtain ⟨a, ha⟩ : ∃ a, ids[sint.nat m]? = some a := ⟨_, List.getElem?_eq_getElem hml'⟩
                    rw [ite_eq_left (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z isl.len from ⟨hm0, Hif⟩)]
                    wp_apply (wp_load_slice_index (V := swift.CommandId) isl (sint.Z m) _ _ a hm0)
                      $$ [Hids] as Hids
                    · iframe; ipureintro
                      rw [show (sint.Z m).toNat = sint.nat m by word]; exact ha
                    have hidsm : (ids.map toCmdId)[sint.nat m]? = some (toCmdId a) := by
                      rw [List.getElem?_map, ha]; rfl
                    have htkw : ((ids.map toCmdId).take (sint.nat (m + W64 1))).foldl
                        (sp.rule4Pair (toCmdId c)) kg =
                        sp.rule4Pair (toCmdId c) kw (toCmdId a) := by
                      rw [swift.rec.nat_succ_of_lt _ _ hm0 Hif, swift.rec.foldl_take_succ _ _ _ _ _ hidsm, ← hkw]
                    -- the two entries
                    have hamk : (mk !! a).isSome = true := (Hids.2.1 a).mp (List.mem_of_getElem? ha)
                    obtain ⟨ea, hea⟩ : ∃ e, kw.get (toCmdId a) = some e := by
                      have := hkpw.2 a; rw [hamk] at this; exact Option.isSome_iff_exists.mp this.symm
                    obtain ⟨ecw, hecw⟩ : ∃ e, kw.get (toCmdId c) = some e := by
                      have := hkpw.2 c; rw [hpc0] at this; exact Option.isSome_iff_exists.mp this.symm
                    obtain ⟨pa0, hpa0⟩ := Option.isSome_iff_exists.mp hamk
                    have hstep : sp.rule4Pair (toCmdId c) kw (toCmdId a) =
                        if (ea.cls != 0) || !(sp.Cmd.conflict ea.cmd ecw.cmd) then kw
                        else if !(sp.recReaches kw (toCmdId c) (toCmdId a)) && !(sp.recReaches kw (toCmdId a) (toCmdId c))
                          then kw.set (toCmdId c) { ecw with dep := ecw.dep ++ [toCmdId a] }
                        else kw := by
                      unfold sp.rule4Pair; rw [hea, hecw]
                    -- `kept[a].class != 0`
                    wp_apply (wp_map_lookup1 _ _ km0 mk a) $$ Hm as Hm
                    rw [hpa0]
                    simp only [Option.getD_some]
                    icases (BigSepM.bigSepM_lookup_acc
                      (show Iris.Std.PartialMap.get? mk a = some pa0 from hpa0)).1
                      $$ Hkents with ⟨⟨%ea', %hea', Hre⟩, Hkents⟩
                    rw [hea] at hea'; cases hea'
                    iunfold swift.recOwn at Hre
                    simp only [↓reduceIte]
                    icases Hre with ⟨%pha, %clsa, %vsa, %dsla, Hpa, #Hvsa, Hdsla, %Hpha⟩
                    wp_auto
                    ihave Hkents := Hkents $$ [Hpa Hdsla]
                    · iexists ea
                      isplitr
                      · ipureintro; exact hea
                      iunfold swift.recOwn
                      iexists pha, clsa, vsa, dsla
                      simp only [↓reduceIte]
                      iframe
                      iframe #
                      ipureintro; exact Hpha
                    have hcls : decide (clsa = W64 0) = (ea.cls == 0) := by
                      rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
                      constructor
                      · intro h; rw [← Hpha.2.2.1, h]; rfl
                      · intro h; apply BitVec.eq_of_toNat_eq; have := Hpha.2.2.1; rw [h] at this; exact this
                    rw [hcls]
                    by_cases hca : ¬ ea.cls = 0
                    · simp only [show (ea.cls == 0) = false by simpa using hca, Bool.not_false]
                      wp_auto
                      wp_for_post
                      iframe
                      iexists m + W64 1, _, kw
                      iframe
                      ipureintro
                      refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                      rw [htkw, hstep]; simp [hca]
                    have hca : ea.cls = 0 := by simpa using hca
                    simp only [show (ea.cls == 0) = true by simpa using hca, Bool.not_true]
                    wp_auto
                    -- `inConflict(kept[a].cmd, kept[c].cmd)`
                    wp_apply (wp_map_lookup1 _ _ km0 mk a) $$ Hm as Hm
                    rw [hpa0]
                    simp only [Option.getD_some]
                    icases (BigSepM.bigSepM_lookup_acc
                      (show Iris.Std.PartialMap.get? mk a = some pa0 from hpa0)).1
                      $$ Hkents with ⟨⟨%ea', %hea', Hre⟩, Hkents⟩
                    rw [hea] at hea'; cases hea'
                    iunfold swift.recOwn at Hre
                    simp only [↓reduceIte]
                    icases Hre with ⟨%pha, %clsa, %vsa, %dsla, Hpa, #Hvsa, Hdsla, %Hpha⟩
                    wp_auto
                    ihave Hkents := Hkents $$ [Hpa Hdsla]
                    · iexists ea
                      isplitr
                      · ipureintro; exact hea
                      iunfold swift.recOwn
                      iexists pha, clsa, vsa, dsla
                      simp only [↓reduceIte]
                      iframe
                      iframe #
                      ipureintro; exact Hpha
                    wp_apply (wp_map_lookup1 _ _ km0 mk c) $$ Hm as Hm
                    rw [hpc0]
                    simp only [Option.getD_some]
                    icases (BigSepM.bigSepM_lookup_acc
                      (show Iris.Std.PartialMap.get? mk c = some pc0 from hpc0)).1
                      $$ Hkents with ⟨⟨%ec', %hec', Hre⟩, Hkents⟩
                    rw [hecw] at hec'; cases hec'
                    iunfold swift.recOwn at Hre
                    simp only [↓reduceIte]
                    icases Hre with ⟨%phc', %clsc', %vsc', %dslc', Hpc', #Hvsc', Hdslc', %Hphc'⟩
                    wp_auto
                    ihave Hkents := Hkents $$ [Hpc' Hdslc']
                    · iexists ecw
                      isplitr
                      · ipureintro; exact hecw
                      iunfold swift.recOwn
                      iexists phc', clsc', vsc', dslc'
                      simp only [↓reduceIte]
                      iframe
                      iframe #
                      ipureintro; exact Hphc'
                    wp_apply (wp_inConflict ea.cmd ecw.cmd vsa vsc')
                    · ipureintro
                      exact ⟨hKSw.2.2 _ _ hea, hKSw.2.2 _ _ hecw⟩
                    by_cases hcf : sp.Cmd.conflict ea.cmd ecw.cmd = false
                    · rw [hcf]
                      wp_auto
                      wp_for_post
                      iframe
                      iexists m + W64 1, _, kw
                      iframe
                      ipureintro
                      refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                      rw [htkw, hstep]; simp [hca, hcf]
                    have hcf' : sp.Cmd.conflict ea.cmd ecw.cmd = true := by simpa using hcf
                    rw [hcf']
                    wp_auto
                    -- `!recReaches(kept, c, a) && !recReaches(kept, a, c)`
                    wp_apply (wp_recReaches km0 kw (fun _ => true) mk c a) $$ [Hm Hkents] as Hk
                    · iframe
                      iunfold swift.keptAt
                      iframe
                      ipureintro; exact hkpw
                    by_cases hr1 : sp.recReaches kw (toCmdId c) (toCmdId a) = true
                    · rw [hr1]
                      wp_auto
                      iunfold swift.keptAt at Hk
                      icases Hk with ⟨Hm, -, Hkents⟩
                      wp_for_post
                      iframe
                      iexists m + W64 1, _, kw
                      iframe
                      ipureintro
                      refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                      rw [htkw, hstep]; simp [hca, hcf', hr1]
                    have hr1' : sp.recReaches kw (toCmdId c) (toCmdId a) = false := by simpa using hr1
                    rw [hr1']
                    wp_auto
                    wp_apply (wp_recReaches km0 kw (fun _ => true) mk a c) $$ [Hk] as Hk
                    · iframe
                    iunfold swift.keptAt at Hk
                    icases Hk with ⟨Hm, -, Hkents⟩
                    by_cases hr2 : sp.recReaches kw (toCmdId a) (toCmdId c) = true
                    · rw [hr2]
                      wp_auto
                      wp_for_post
                      iframe
                      iexists m + W64 1, _, kw
                      iframe
                      ipureintro
                      refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                      rw [htkw, hstep]; simp [hca, hcf', hr1', hr2]
                    have hr2' : sp.recReaches kw (toCmdId a) (toCmdId c) = false := by simpa using hr2
                    rw [hr2']
                    wp_auto
                    -- `kept[c].dep = append(kept[c].dep, a)`
                    wp_apply (wp_map_lookup1 _ _ km0 mk c) $$ Hm as Hm
                    rw [hpc0]
                    simp only [Option.getD_some]
                    icases (BigSepM.bigSepM_delete
                      (show Iris.Std.PartialMap.get? mk c = some pc0 from hpc0)).1
                      $$ Hkents with ⟨⟨%ec3, %hec3, Hre⟩, Hkents⟩
                    rw [hecw] at hec3; cases hec3
                    iunfold swift.recOwn at Hre
                    simp only [↓reduceIte]
                    icases Hre with ⟨%phc3, %clsc3, %vsc3, %dslc3, Hpc3, #Hvsc3, ⟨Hdl3, Hdcap3⟩, %Hphc3⟩
                    wp_auto
                    wp_bind (App (Val (GoInstruction (CompositeLiteral
                      (go.GoType.SliceType swift.CommandId.ty)))) (Val (LiteralValueV _)))
                    iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [a]
                    wp_auto
                    isplitl []
                    · ipureintro; rfl
                    iintro %lsl ⟨Hlsl, -⟩
                    wp_auto
                    wp_apply wp_slice_append $$ [Hdl3 Hdcap3 Hlsl] as %ndsl ⟨Hdl3, Hdcap3, -⟩
                    · iframe
                    wp_apply (wp_map_lookup1 _ _ km0 mk c) $$ Hm as Hm
                    rw [hpc0]
                    simp only [Option.getD_some]
                    wp_auto
                    ihave Hnew : swift.recOwn pc0 { ecw with dep := ecw.dep ++ [toCmdId a] } true
                      $$ [Hpc3 Hdl3 Hdcap3]
                    · iunfold swift.recOwn
                      iexists phc3, clsc3, vsc3, ndsl
                      simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil, ofCmdId_toCmdId]
                      iframe
                      iframe #
                      ipureintro; exact Hphc3
                    ihave Hkents := swift.keptEnts_upd kw (fun _ => true) mk c pc0 _ hpc0 $$ [Hkents Hnew]
                    · iframe
                    wp_for_post
                    iframe
                    iexists m + W64 1, _, _
                    iframe
                    ipureintro
                    refine ⟨by word, by word, ?_, hKSw.setDep hecw _, swift.keptPure_upd hkpw c pc0 _ hpc0⟩
                    rw [htkw, hstep]; simp [hca, hcf', hr1', hr2']
                  · have hmm : sint.nat m = (ids.map toCmdId).length := by
                      rw [List.length_map, Hisl.1]; word
                    rw [hmm, List.take_length] at Hw
                    obtain ⟨-, -, hkw, hKSw, hkpw⟩ := Hw
                    wp_for_post
                    iframe
                    iexists n + W64 1, _, kw
                    iframe
                    ipureintro
                    refine ⟨by word, by word, ?_, hKSw, hkpw⟩
                    rw [htkc, hkw]
              · have hnn : sint.nat n = (ids.map toCmdId).length := by
                  rw [List.length_map, Hisl.1]; word
                rw [hnn, List.take_length] at Hc4
                obtain ⟨-, -, hkg, hKSg, hkp⟩ := Hc4
                have hr4 : sp.rule4 (ids.map toCmdId) k3b = kg := by rw [hkg]; rfl
                ihave Hkept := swift.kept_close km0 kg (fun _ => true) mk hkp $$ [Hm Hkents]
                · iframe
                -- the order (`recOrder`)
                wp_apply (wp_recOrder km0 kg (fun _ => true) isl ids (DFrac.own 1)) $$ [Hkept Hids]
                  as %osl ⟨Hkept, Hids, Hord, Hocap⟩
                · iframe
                  ipureintro
                  refine ⟨Hids.1, fun c hc => ?_⟩
                  rw [hKSg.1, ← hKS3b.1, ← Hmk.2 c]; exact (Hids.2.1 c).mp hc
                -- the MSync's maps along the order
                wp_apply (wp_map_make1 (K := swift.CommandId) (V := w64)) as %phm Hphm
                wp_apply (wp_map_make1 (K := swift.CommandId) (V := state.Command)) as %cmm Hcmm
                wp_apply (wp_map_make1 (K := swift.CommandId) (V := GoSlice)) as %dpm Hdpm
                wp_apply (wp_map_make1 (K := w64) (V := GoInterface)) as %kmm Hkmm
                -- the order's commands are kept, distinct; each a put or a get
                obtain ⟨O, hO⟩ : ∃ O, O = sp.recOrder kg (ids.map toCmdId) := ⟨_, rfl⟩
                rw [← hO]
                have hOk : ∀ c ∈ O, (kg.get c).isSome := by
                  intro c hc
                  rw [hO] at hc
                  have h1 := sp.recOrder_sub _ _ _ hc
                  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp h1
                  rw [hKSg.1, ← hKS3b.1, ← Hmk.2 c']; exact (Hids.2.1 c').mp hc'
                have hOnd : O.Nodup := by rw [hO]; exact sp.PState.recOrder_nodup _ _
                have hOlen : O.length < 2 ^ 31 := by
                  have h1 := (List.subperm_of_subset hOnd (fun x hx => by
                    rw [hO] at hx; exact sp.recOrder_sub _ _ _ hx)).length_le
                  have h2 := hperm4.length_eq
                  simp only [List.length_map] at h1 h2
                  rw [swift.rec.KS_len hKS3b Hkc] at h2
                  obtain ⟨_, _, _, _, h4⟩ :=
                    swift.rec.closure_setup _ li Rm Um Am hRU hUa hAperm' kc hcmd3 Hkc
                  have := Hok.size; omega
                have hcmd4 : sp.CmdFrom Am kg := by
                  rw [← hr4]; exact sp.rule4_cmd _ _ _ (by rw [hk3b]; exact sp.rule3b_cmd _ _ _ _ hcmd3)
                have hpg4 := swift.rec.putget_of Hok hAreps hcmd4
                ihave %Hosl := ownSlice_len $$ Hord
                simp only [List.length_map] at Hosl
                iunfold swift.keptOwn at Hkept
                icases Hkept with ⟨%mk4, Hm4, %Hmk4, Hkents4⟩
                ihave HkI0 := swift.keysIn_nil
                ihave HO : (∃ (j : w64) (cv : swift.CommandId) (PH : GMap swift.CommandId w64)
                    (CM : GMap swift.CommandId state.Command) (DP : GMap swift.CommandId GoSlice)
                    (kM : GMap w64 GoInterface),
                    "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ cv ∗ "Hphm" ∷ phm ↦$ PH ∗ "Hcmm" ∷ cmm ↦$ CM ∗
                    "Hdpm" ∷ dpm ↦$ DP ∗ "Hkmm" ∷ kmm ↦$ kM ∗
                    "HkI" ∷ swift.keysIn kM ((O.take (sint.nat j)).filterMap
                      (fun c => (kg.get c).map (fun e => (c, e.cmd)))) ∗
                    "Hents" ∷ ([∗list] p ∈ sp.lkAlong ((O.take (sint.nat j)).filterMap
                        (fun c => (kg.get c).map (fun e => (c, e.cmd)))),
                      ∃ (vs dsl : GoSlice),
                        ⌜CM !! ofCmdId p.1 = some (state.Command.mk p.2.1.op p.2.1.key vs) ∧
                          DP !! ofCmdId p.1 = some dsl⌝ ∗
                        vs ↦*□ p.2.1.val ∗ dsl ↦*□ (p.2.2.map ofCmdId)) ∗
                    "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z osl.len ∧
                      (∀ x, (PH !! x).isSome = true ↔ toCmdId x ∈ O.take (sint.nat j)) ∧
                      (∀ x v, PH !! x = some v → v = W64 3) ∧
                      ∀ x, (CM !! x).isSome = (PH !! x).isSome ∧
                        (DP !! x).isSome = (PH !! x).isSome⌝ : IProp netDistGF)
                  $$ [i c Hphm Hcmm Hdpm Hkmm HkI0]
                · iexists W64 0, _, ∅, ∅, ∅, ∅
                  rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
                  simp only [List.filterMap_nil]
                  iframe
                  isplitl [HkI0]
                  · iexact HkI0
                  isplitr
                  · simp [sp.lkAlong]; iempintro
                  ipureintro
                  refine ⟨by word, by word, fun x => by simp, fun x v h => by simp at h,
                    fun x => by simp⟩
                wp_for HO
                by_cases Hif : sint.Z j < sint.Z osl.len
                · simp only [decide_eq_true Hif, ↓reduceIte]
                  wp_pures; cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
                  obtain ⟨hj0, hjl, hPH, hPV, hCD⟩ := Hj
                  have hjO : sint.nat j < O.length := by rw [Hosl.1]; exact swift.rec.nat_lt_of_lt _ _ hj0 Hif
                  obtain ⟨c, hc⟩ : ∃ c, O[sint.nat j]? = some c := ⟨_, List.getElem?_eq_getElem hjO⟩
                  rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z osl.len from ⟨hj0, Hif⟩)]
                  wp_apply (wp_load_slice_index (V := swift.CommandId) osl (sint.Z j) _ _ (ofCmdId c) hj0)
                    $$ [Hord] as Hord
                  · iframe; ipureintro
                    rw [show (sint.Z j).toNat = sint.nat j by word, List.getElem?_map, hc]; rfl
                  -- `e := kept[c]`
                  have hck := hOk c (List.mem_of_getElem? hc)
                  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hck
                  obtain ⟨p, hp⟩ : ∃ p, mk4 !! ofCmdId c = some p := by
                    have := Hmk4.2 (ofCmdId c); rw [toCmdId_ofCmdId, he] at this
                    exact Option.isSome_iff_exists.mp this
                  have hpg := hpg4 c e he
                  have hop : e.cmd.op ≠ swift.opSCAN := by
                    rcases hpg with h | h
                    · unfold sp.Cmd.isPut sp.opPUT at h; simp at h; rw [h]; decide
                    · unfold sp.Cmd.isGet sp.opGET at h; simp at h; rw [h]; decide
                  wp_apply (wp_map_lookup1 _ _ km0 mk4 (ofCmdId c)) $$ Hm4 as Hm4
                  rw [hp]
                  simp only [Option.getD_some]
                  icases (BigSepM.bigSepM_lookup_acc
                    (show Iris.Std.PartialMap.get? mk4 (ofCmdId c) = some p from hp)).1
                    $$ Hkents4 with ⟨⟨%e', %he', Hre⟩, Hkback⟩
                  rw [toCmdId_ofCmdId, he] at he'; cases he'
                  iunfold swift.recOwn at Hre
                  simp only [↓reduceIte]
                  icases Hre with ⟨%phe, %clse, %vse, %dsle, Hpe, #Hvse, Hdsle, %Hphe⟩
                  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
                  iapply wp_slice_literal (V := swift.CommandId) []
                  wp_auto
                  isplitl []
                  · ipureintro; rfl
                  iintro %dsl ⟨Hdsl, Hdcap⟩
                  wp_auto
                  wp_apply (wp_keysOf e.cmd vse) $$ [] as %ksl Hksl
                  · ipureintro; exact hop
                  ihave %Hkl := ownSlice_len _ _ _ $$ Hksl
                  obtain ⟨pre, hpre⟩ : ∃ s, s = (O.take (sint.nat j)).filterMap
                      (fun c => (kg.get c).map (fun e => (c, e.cmd))) := ⟨_, rfl⟩
                  rw [← hpre]
                  ihave HL : (∃ (i : w64) (kv : w64),
                      "i" ∷ i_ptr ↦ i ∗ "k" ∷ k_ptr ↦ kv ∗
                      "HL" ∷ ((⌜i = W64 0⌝ ∗ kmm ↦$ kM ∗ swift.keysIn kM pre ∗
                          (∃ d0 : GoSlice, dep_ptr ↦ d0 ∗ d0 ↦* ([] : List swift.CommandId) ∗
                            ownSliceCap swift.CommandId d0 (DFrac.own 1))) ∨
                        (⌜i = W64 1⌝ ∗ ∃ (dp : GoSlice) (kM' : GMap w64 GoInterface),
                          dep_ptr ↦ dp ∗ kmm ↦$ kM' ∗ swift.keysIn kM' (pre ++ [(c, e.cmd)]) ∗
                          dp ↦* ((sp.lkDeps pre e.cmd).map ofCmdId) ∗
                          ownSliceCap swift.CommandId dp (DFrac.own 1))) : IProp netDistGF)
                    $$ [i k Hkmm HkI dep Hdsl Hdcap]
                  · iexists (W64 0), _
                    iframe i k
                    ileft
                    iframe Hkmm HkI
                    isplitr
                    · ipureintro; rfl
                    iexists _; iframe
                  wp_for HL
                  have hlen1 : sint.Z ksl.len = 1 := by
                    have := Hkl.1; simp at this; word
                  icases HL with (⟨%Hi0, Hkmm, HkI, ⟨%d0, dep, Hd0, Hd0c⟩⟩ |
                    ⟨%Hi1, %dp, %kM', dep, Hkmm, HkI, Hdp, Hdpc⟩)
                  rotate_left
                  · -- after the key: the maps' entries
                    subst Hi1
                    rw [decide_eq_false (by rw [hlen1]; decide)]
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    wp_auto
                    ipersist Hdp
                    wp_apply (wp_mapInsert _ phm PH (ofCmdId c) (W64 3)) $$ Hphm as Hphm
                    try wp_auto
                    wp_apply (wp_mapInsert _ cmm CM (ofCmdId c) _) $$ Hcmm as Hcmm
                    try wp_auto
                    wp_apply (wp_mapInsert _ dpm DP (ofCmdId c) dp) $$ Hdpm as Hdpm
                    try wp_auto
                    ihave Hkents4 := Hkback $$ [Hpe Hdsle]
                    · iexists e
                      isplitr
                      · ipureintro; rw [toCmdId_ofCmdId]; exact he
                      iunfold swift.recOwn
                      iexists phe, clse, vse, dsle
                      simp only [↓reduceIte]
                      iframe
                      iframe #
                      ipureintro; exact Hphe
                    have hcj : c ∉ O.take (sint.nat j) := swift.rec.notin_take hOnd hc
                    have hpre' : (O.take (sint.nat (j + W64 1))).filterMap
                        (fun c => (kg.get c).map (fun e => (c, e.cmd))) = pre ++ [(c, e.cmd)] := by
                      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, swift.rec.fm_take_succ _ _ _ _ hc, he,
                        ← hpre]
                      rfl
                    have hnin : ∀ q ∈ sp.lkAlong pre, q.1 ≠ c := by
                      intro q hq hqc
                      apply hcj
                      have h1 : q.1 ∈ pre.map Prod.fst := by
                        rw [← sp.lkAlong_ids pre, List.map_map]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
                      rw [hpre] at h1
                      rw [← hqc]; exact swift.rec.fm_fst h1
                    wp_for_post
                    iframe
                    iexists j + W64 1, _, _, _, _, _
                    rw [hpre', sp.lkAlong_snoc]
                    iframe
                    isplitl [Hents]
                    · iapply BigSepL.bigSepL_snoc.2
                      isplitl [Hents]
                      · iapply (BigSepL.bigSepL_mono ?_) $$ Hents
                        intro k q hq
                        have hqc : q.1 ≠ c := hnin q (List.mem_of_getElem? hq)
                        have hne : ofCmdId c ≠ ofCmdId q.1 := fun h => hqc (by
                          have := congrArg toCmdId h; simpa [toCmdId_ofCmdId] using this.symm)
                        iintro ⟨%vs, %dsl', %Hl, #Hvs, #Hdsl'⟩
                        iexists vs, dsl'
                        rw [GMap.lookup_insert_ne _ _ hne, GMap.lookup_insert_ne _ _ hne]
                        iframe #
                        ipureintro; exact Hl
                      · iexists vse, dp
                        rw [GMap.lookup_insert, GMap.lookup_insert]
                        iframe #
                        ipureintro; exact ⟨rfl, rfl⟩
                    ipureintro
                    refine ⟨by word, by word, fun x => ?_, fun x v h => ?_, fun x => ?_⟩
                    rotate_right
                    · by_cases hx : x = ofCmdId c
                      · subst hx; simp [GMap.lookup_insert]
                      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx), GMap.lookup_insert_ne _ _ (Ne.symm hx),
                          GMap.lookup_insert_ne _ _ (Ne.symm hx)]
                        exact hCD x
                    rotate_left
                    · by_cases hx : x = ofCmdId c
                      · subst hx; rw [GMap.lookup_insert] at h; exact (Option.some.inj h).symm
                      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx)] at h; exact hPV x v h
                    rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hc]
                    by_cases hx : x = ofCmdId c
                    · subst hx; simp [GMap.lookup_insert, toCmdId_ofCmdId]
                    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx), hPH x]
                      have : toCmdId x ≠ c := fun h => hx (by rw [← h, ofCmdId_toCmdId])
                      simp [this]
                  subst Hi0
                  rw [decide_eq_true (by rw [hlen1]; decide)]
                  simp only [↓reduceIte]
                  wp_auto
                  rw [if_pos ⟨by decide, by rw [hlen1]; decide⟩]
                  wp_apply wp_load_slice_index (t := state.Key.ty) ksl (sint.Z (W64 0)) [e.cmd.key] _ e.cmd.key
                    (by decide) $$ [Hksl] as Hksl
                  · iframe Hksl; ipureintro; rfl
                  try wp_auto
                  iunfold swift.keysIn at HkI
                  icases HkI with ⟨HkE, %Hkcov⟩
                  ihave HkI : swift.keysIn kM pre $$ [HkE]
                  · iunfold swift.keysIn; iframe HkE; ipureintro; exact Hkcov
                  wp_apply wp_map_lookup2 $$ [$Hkmm] as Hkmm
                  wp_join iprop(∃ (kl : Loc) (kMn : GMap w64 GoInterface),
                      k_ptr ↦ e.cmd.key ∗ keys_ptr ↦ kmm ∗
                      info_ptr ↦ (interface.ok ⟨go.GoType.PointerType swift.lightKeyInfo.ty, #kl⟩ : GoInterface) ∗
                      kmm ↦$ kMn ∗
                      swift.lki.lkiOwn kl (swift.lkOf pre e.cmd.key).1 (swift.lkOf pre e.cmd.key).2 ∗
                      (swift.lki.lkiOwn kl
                          (swift.lki.addTo e.cmd.op (ofCmdId c) (swift.lkOf pre e.cmd.key).1
                            (swift.lkOf pre e.cmd.key).2).1
                          (swift.lki.addTo e.cmd.op (ofCmdId c) (swift.lkOf pre e.cmd.key).1
                            (swift.lkOf pre e.cmd.key).2).2 -∗
                        swift.keysIn kMn (pre ++ [(c, e.cmd)])))
                    with [k keys info Hkmm HkI] as ⟨%kl, %kMn, k, keys, info, Hkmm, Hlki, Hkback'⟩
                  · -- the key has a `lightKeyInfo`
                    obtain ⟨ki, hki⟩ := Option.isSome_iff_exists.mp Hif
                    ihave ⟨%kl, %Hkl, Hlki, Hkback'⟩ := swift.keysIn_lookup kM pre c e.cmd ki hki $$ HkI
                    rw [hki, Hkl]
                    simp only [Option.getD_some]
                    try wp_auto
                    try wp_join_done
                    iexists kl, kM
                    iframe
                  · -- a fresh `lightKeyInfo`
                    have hnone : kM !! e.cmd.key = none := by simpa using Hif
                    have h0 := Hkcov e.cmd.key hnone
                    wp_apply wp_newLKI as %kl Hlki
                    try wp_auto
                    wp_apply wp_mapInsert $$ [$Hkmm] as Hkmm
                    try wp_auto
                    try wp_join_done
                    iexists kl, _
                    iframe
                    isplitl [Hlki]
                    · rw [h0]; iexact Hlki
                    iintro Hl
                    rw [h0]
                    iapply swift.keysIn_new kM pre c e.cmd kl hnone
                    iframe
                  -- `dep = append(dep, info.getConflictCmds(e.cmd)...)`
                  try wp_auto
                  wp_apply wp_lkiGet $$ [$Hlki] as %csl ⟨Hlki, #Hcsl⟩
                  try wp_auto
                  wp_apply (wp_slice_append (dq := DFrac.discard)) $$ [$Hd0 $Hd0c $Hcsl] as %nsl ⟨Hnsl, Hnslc, -⟩
                  try wp_auto
                  -- `info.add(e.cmd, c)`
                  have hClen : (swift.lkOf pre e.cmd.key).2.length + 1 < 2 ^ 63 := by
                    have := swift.lkOf_len pre e.cmd.key
                    have h2 : pre.length ≤ O.length := by
                      rw [hpre]; exact Nat.le_trans (List.length_filterMap_le _ _) (List.length_take_le' _ _)
                    omega
                  wp_apply (wp_lkiAdd kl _ _ (state.Command.mk e.cmd.op e.cmd.key vse) (ofCmdId c)) $$ [$Hlki] as Hlki
                  · ipureintro; exact hClen
                  ihave HkI' := Hkback' $$ [Hlki]
                  · iExactEq Hlki; rfl
                  try wp_auto
                  wp_for_post
                  iframe
                  iexists (W64 0 + W64 1), e.cmd.key
                  iframe i k
                  iright
                  isplitr
                  · ipureintro; decide
                  iexists nsl, kMn
                  iframe
                  iExactEq Hnsl
                  rw [← swift.lkOf_conflict pre e.cmd hpg]
                  simp
                · -- the order done: the `MSync`
                  simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]
                  ipersist «$r0»
                  ipersist Hphm
                  ipersist Hcmm
                  ipersist Hdpm
                  obtain ⟨hj0, hjl, hPH, hPV, hCD⟩ := Hj
                  have hjO : sint.nat j = O.length := by rw [Hosl.1]; word
                  rw [hjO, List.take_length] at hPH
                  rw [hjO, List.take_length]
                  have hcs : (O.filterMap (fun c => (kg.get c).map (fun e => (c, e.cmd)))).map Prod.fst = O :=
                    swift.rec.fm_fst_all hOk
                  have hM : sp.recoverSync N (prs.map Prod.snd) =
                      sp.lkAlong (O.filterMap (fun c => (kg.get c).map (fun e => (c, e.cmd)))) := by
                    have hA : sp.recAcks (prs.map Prod.snd) = Am := by rw [hAm, hAsnd]
                    have hmx : sp.recMaxC Am = maxC := by rw [hmaxC, hA]
                    have hU : sp.recU Am = Um := by
                      rw [hUm, hprsU, hpU]; unfold sp.recU; rw [hmx, hAm, List.filter_map]; rfl
                    have hli' : Um.any (fun a => a.1 == oldL) = li := by
                      rw [hli, hUm, List.any_map]; rfl
                    have hR' : Um.filter (fun a => decide (a.1 ∈ sp.AQ N maxC)) = Rm := by
                      rw [hRm, hprsR, hpR, hUm, List.filter_map]; rfl
                    have hk1' : sp.rule1 oldL Um = k := by rw [hk1, hUm]
                    unfold sp.recoverSync
                    simp only []
                    rw [hA, hmx, hU, ← hoLd, hli', hR', hk1', ← hk2, ← hB, hcl, ← hk3b, hidsM4, hr4, ← hO]
                  wp_auto
                  iapply HΦ
                  iframe Hbal
                  iunfold swift.syncSent
                  ihave ⟨Hents, Hents2⟩ : (([∗list] p ∈ (sp.lkAlong (O.filterMap (fun c => (kg.get c).map (fun (e : sp.RecEntry) => (c, e.cmd)))) : List (sp.CmdId × sp.Cmd × List sp.CmdId)), iprop(∃ (vs dsl : GoSlice),
                        ⌜CM !! ofCmdId p.1 = some (state.Command.mk p.2.1.op p.2.1.key vs) ∧
                          DP !! ofCmdId p.1 = some dsl⌝ ∗
                        vs ↦*□ p.2.1.val ∗ dsl ↦*□ (p.2.2.map ofCmdId))) ∗
                      ([∗list] p ∈ (sp.lkAlong (O.filterMap (fun c => (kg.get c).map (fun (e : sp.RecEntry) => (c, e.cmd)))) : List (sp.CmdId × sp.Cmd × List sp.CmdId)), iprop(∃ (vs dsl : GoSlice),
                        ⌜CM !! ofCmdId p.1 = some (state.Command.mk p.2.1.op p.2.1.key vs) ∧
                          DP !! ofCmdId p.1 = some dsl⌝ ∗
                        vs ↦*□ p.2.1.val ∗ dsl ↦*□ (p.2.2.map ofCmdId))) : IProp netDistGF) $$ [Hents]
                  · iapply BigSepL.bigSepL_sep_eqv.1
                    iapply (BigSepL.bigSepL_mono_of_forall ?_) $$ Hents
                    intro k x
                    iintro #H
                    isplitl
                    · iexact H
                    · iexact H
                  isplitl [Hents]
                  · iunfold swift.syncMaps
                    iexists me, bal, phm, cmm, dpm, PH, CM, DP
                    rw [hM]
                    iframe #
                    have hids' : (sp.lkAlong (O.filterMap (fun c => (kg.get c).map (fun e => (c, e.cmd))))).map Prod.fst = O := by
                      have h1 := congrArg (List.map Prod.fst)
                        (sp.lkAlong_ids (O.filterMap (fun c => (kg.get c).map (fun e => (c, e.cmd)))))
                      rw [List.map_map] at h1
                      exact h1.trans hcs
                    isplitr
                    · ipureintro
                      refine ⟨rfl, by rw [hids']; exact hOnd, fun x => by rw [hids']; exact hPH x⟩
                    iexact Hents
                  iexists phm, cmm, dpm, PH, CM, DP
                  iframe #
                  isplitr
                  · ipureintro
                    have hids'' : (sp.lkAlong (O.filterMap (fun c => (kg.get c).map (fun e => (c, e.cmd))))).map Prod.fst = O := by
                      have h1 := congrArg (List.map Prod.fst)
                        (sp.lkAlong_ids (O.filterMap (fun c => (kg.get c).map (fun e => (c, e.cmd)))))
                      rw [List.map_map] at h1
                      exact h1.trans hcs
                    rw [hM, hids'']
                    exact ⟨hPV, hOnd, hPH, hCD⟩
                  rw [hM]
                  iunfold swift.syncEnts
                  iexact Hents2

end proof
end Perennial.github_com.imdea_software.swiftpaxos

