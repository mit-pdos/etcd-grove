/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/MarshalAcks.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift messages' writers, part 3: `(*Ack).Marshal` and `(*MFastAck).Marshal` (the entries
of `MOptAcks` and `MAcks`), over the `PutVarint` hypothesis (Proof/swift/MarshalSpecs.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalBase

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv wire

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

set_option goose.wp.extras true

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `(*Ack).Marshal(wire)`: `Ack.enc` (an `MOptAcks` entry). -/
theorem swift.Ack.Marshal.wp (wp_pv : swift.PutVarint.specH (hG := hG))
    (t : Loc) (dq : DFrac) (a : swift.Ack) (A : sp.Ack) (hwf : A.wf)
    (wr : GoInterface) (S Q : List w8 → IProp netDistGF) (W : List w8) :
    {{ sinkOk wr S Q ∗ S W ∗ bufio.prefixClosed Q ∗ □ Q (W ++ A.enc) ∗ t ↦{dq} a ∗
        swift.ackRepr a A }}
      (App (Val (t @!! go.GoType.PointerType swift.Ack.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ A.enc) ∗ t ↦{dq} a }} := by
  wp_start as ⟨#Hsink, HS, #Hpc, #HQ, Ht, Hrep⟩
  iunfold swift.ackRepr at Hrep
  icases Hrep with ⟨%Hid, #HD, #Hcs⟩
  obtain ⟨hid, hseq⟩ := Hid
  have hbody : W ++ A.enc = W ++ (sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum' ++
      sp.varintLen A.dep.length ++ (A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length ++
      A.cs.flatten ++ sp.le64 a.Seqnum') := by
    simp only [sp.Ack.enc, sp.encCmdId, sp.encDep, sp.encHashes, ← hid, ← hseq, swift.toCmdId,
      List.append_assoc]
  ihave %Htn := typedPointsto_not_null $$ Ht
  icases typedPointsto_split _ _ _ $$ Ht with Ht
  simp only [TypedPointsto.typedPointstoDef]
  icases Ht with ⟨CmdId, Dep, Checksum, Seqnum, -⟩
  ihave %Hcn := typedPointsto_not_null $$ CmdId
  icases typedPointsto_split _ _ _ $$ CmdId with CmdId
  simp only [TypedPointsto.typedPointstoDef]
  icases CmdId with ⟨ClientId, SeqNum, -⟩
  wp_auto
  ihave Hsl := slice_array b_ptr 10 (Perennial.zero_val (GoArray w8 10)) (by decide) $$ b
  rw [show (Perennial.zero_val (GoArray w8 10)).arr = List.replicate 10 (W8 0) from rfl]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl,
    show W64 10 - W64 0 = W64 10 from rfl]
  icases slice_pre b_ptr (W64 10) (W64 8) _ ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
  obtain ⟨lb, hlb', hlb⟩ := take_of_len (List.replicate 10 (W8 0)) (W64 8) 8 (by simp) rfl
  rw [hlb']
  mstoreb
  mstoreb
  mstoreb
  mstoreb
  mstoreb
  mstoreb
  mstoreb
  mstoreb
  rw [set8 _ hlb, le32x2_sbytes]
  iunfold sinkOk at Hsink
  icases Hsink with ⟨%e, %He, #HW⟩
  subst He
  try wp_auto
  wp_apply HW $$ HS [] Hb as %nn0 %err0 HS Hb
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨sp.varintLen A.dep.length ++ (A.dep.map sp.encCmdId).flatten ++
      sp.varintLen A.cs.length ++ A.cs.flatten ++ sp.le64 a.Seqnum', by rw [hbody]; simp⟩
  ihave Hsl := Hback $$ %_ Hb %(by simp [sp.le32, u32Le_length]; rfl)
  ihave %Hal1 := ownSlice_len $$ Hsl
  simp only at Hal1
  ihave %Hl1 := ownSlice_len $$ HD
  have hn1 : sint.nat a.Dep'.len = A.dep.length := by simpa using Hl1.1.symm
  have h621 : sint.Z a.Dep'.len < 2 ^ 62 := by
    have := (show A.dep.length < 2 ^ 62 from hwf.1); have : sint.Z a.Dep'.len = (sint.nat a.Dep'.len : Int) := by word
    omega
  try wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl]
  wp_apply wp_pv _ _ a.Dep'.len $$ [Hsl] as %wlen1 ⟨%Hwl1, Hsl⟩
  · iframe Hsl; ipureintro
    refine ⟨by rw [Hal1.1]; decide, Hl1.2, h621⟩
  rw [hn1] at Hwl1
  isimp only [hn1] at Hsl
  have hvl1 := varintLen_length (A.dep.length) (by have := (show A.dep.length < 2 ^ 62 from hwf.1); omega)
  rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen1 by rw [Hwl1]; exact Int.natCast_nonneg _)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 10) = 10 := rfl; omega⟩)]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl,
    show wlen1 - W64 0 = wlen1 by word]
  icases slice_pre b_ptr (W64 10) wlen1 _ ⟨by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 10) = 10 := rfl; omega⟩ $$ Hsl with ⟨Hv1, Hback⟩
  have hwn1 : sint.nat wlen1 = (sp.varintLen (A.dep.length)).length := by
    have : sint.Z wlen1 = (sint.nat wlen1 : Int) := by word
    omega
  rw [hwn1, List.take_left]
  wp_auto
  wp_apply HW $$ HS [] Hv1 as %nn1 %err1 HS Hv1
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨(A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length ++ A.cs.flatten ++ sp.le64 a.Seqnum', by rw [hbody]; simp⟩
  ihave Hsl := Hback $$ %_ Hv1 %(by first | rfl | exact hwn1.symm)
  ihave %Hal1' := ownSlice_len $$ Hsl
  simp only at Hal1'
  ihave HL : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice) (tv : w32),
      "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗ "tmp32" ∷ tmp32_ptr ↦ tv ∗
      "HS" ∷ S ((W ++ (sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ ((A.dep.take k).map sp.encCmdId).flatten) ∗
      "Hsl" ∷ slice.mk b_ptr (W64 10) (W64 10) ↦* arr ∗
      "%Hk" ∷ ⌜arr.length = sint.nat (W64 10) ∧ k ≤ A.dep.length⌝ : IProp netDistGF) $$ [i bs tmp32 HS Hsl]
  · iexists 0, _, _, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; simp
    ipureintro; exact ⟨Hal1'.1, by omega⟩
  wp_for HL
  try wp_auto
  wp_if_destruct
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : sint.Z (W64 (k : Int)) < sint.Z a.Dep'.len := by
      first | exact Hif | simpa using Hif | exact of_decide_eq_true (IntoValInj.intoVal_inj Hif)
    have hcl : sint.Z a.Dep'.len = A.dep.length := by
      have : sint.Z a.Dep'.len = (sint.nat a.Dep'.len : Int) := by word
      omega
    have hk64 : sint.Z (W64 (k : Int)) = k := by
      have := (show A.dep.length < 2 ^ 62 from hwf.1); word
    have hkn : k < A.dep.length := by omega
    have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
    have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z a.Dep'.len := ⟨hk0, Hif⟩
    obtain ⟨d, hd⟩ : ∃ d, A.dep[k]? = some d := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hd' : (A.dep.map swift.ofCmdId)[(sint.Z (W64 (k : Int))).toNat]? = some (swift.ofCmdId d) := by
      rw [hk64]; simp [hd]
    have htake : ((A.dep.take (k + 1)).map sp.encCmdId).flatten = ((A.dep.take k).map sp.encCmdId).flatten ++ (sp.le32 d.cl ++ sp.le32 d.seq) := by
      rw [List.take_add_one, hd]; simp [sp.encCmdId]
    have hsplit : A.dep = A.dep.take k ++ d :: A.dep.drop (k + 1) := by
      have hk' : A.dep[k] = d := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hd)
      rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
    have hflat : (A.dep.map sp.encCmdId).flatten =
        ((A.dep.take k).map sp.encCmdId).flatten ++ (sp.le32 d.cl ++ sp.le32 d.seq) ++ ((A.dep.drop (k + 1)).map sp.encCmdId).flatten := by
      rw [congrArg (fun l => (List.map sp.encCmdId l).flatten) hsplit]
      simp [sp.encCmdId]
    have hp2 : ((W ++ (sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ ((A.dep.take k).map sp.encCmdId).flatten) ++ (sp.le32 d.cl ++ sp.le32 d.seq) <+: W ++ A.enc := by
      refine ⟨((A.dep.drop (k + 1)).map sp.encCmdId).flatten ++ sp.varintLen A.cs.length ++ A.cs.flatten ++ sp.le64 a.Seqnum', ?_⟩
      rw [hbody, hflat]; simp
    generalize hY : (W ++ (sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ ((A.dep.take k).map sp.encCmdId).flatten = Y
    rw [hY] at hp2
    have hp1 : Y ++ sp.le32 d.cl <+: W ++ A.enc :=
      List.IsPrefix.trans ⟨sp.le32 d.seq, by simp⟩ hp2
    icases slice_pre b_ptr (W64 10) (W64 4) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
    obtain ⟨lb, hlb', hlb⟩ := take_of_len arr (W64 4) 4 (by rw [hk1]; decide) rfl
    rw [hlb']
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 4 - W64 0 = W64 4 from rfl,
      show W64 10 - W64 0 = W64 10 from rfl]
    try wp_auto
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
    try wp_auto
    wp_apply wp_load_cl _ _ _ _ _ hk0 hd' $$ [HD] as -
    · iexact HD
    try wp_auto
    mstoreb
    mstoreb
    mstoreb
    mstoreb
    first | rw [set4 _ hlb, le32_sbytes] | rw [set4' _ hlb, le32_sbytes]
    try wp_auto
    wp_apply HW $$ HS [] Hb as %nn1 %err1 HS Hb
    · iapply Qp $$ Hpc HQ
      ipureintro
      exact hp1
    try wp_auto
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
    try wp_auto
    wp_apply wp_load_seq _ _ _ _ _ hk0 hd' $$ [HD] as -
    · iexact HD
    try wp_auto
    mstoreb
    mstoreb
    mstoreb
    mstoreb
    first | rw [set4 _ (by simp [sp.le32, u32Le_length]), le32_sbytes] | rw [set4' _ (by simp [sp.le32, u32Le_length]), le32_sbytes]
    try wp_auto
    wp_apply HW $$ HS [] Hb as %nn2 %err2 HS Hb
    · iapply Qp $$ Hpc HQ
      ipureintro
      simpa using hp2
    ihave Hsl := Hback $$ %_ Hb %(by simp [sp.le32, u32Le_length]; rfl)
    wp_for_post
    iframe
    rw [hkk]
    iexists k + 1, _, _, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; rw [htake, ← hY]; simp [swift.ofCmdId]
    ipureintro
    exact ⟨len_restore _ _ _ _ (by simp [sp.le32, u32Le_length]; rfl) hk1 (by decide), by omega⟩
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z a.Dep'.len := by
      first
      | exact Hif
      | simpa using Hif
      | exact fun h => Hif (by rw [decide_eq_true h])
      | exact of_decide_eq_false (IntoValInj.intoVal_inj Hif)
    have hkn : k = A.dep.length := by
      have : sint.Z (W64 (k : Int)) = k := by have := (show A.dep.length < 2 ^ 62 from hwf.1); word
      have : sint.Z a.Dep'.len = (sint.nat a.Dep'.len : Int) := by word
      omega
    subst hkn
    rw [List.take_length]
    ihave %Hal2 := ownSlice_len $$ Hsl
    simp only at Hal2
    ihave %Hl2 := ownSlice_len $$ Hcs
    have hn2 : sint.nat a.Checksum'.len = A.cs.length := by simpa using Hl2.1.symm
    have h622 : sint.Z a.Checksum'.len < 2 ^ 62 := by
      have := (show A.cs.length < 2 ^ 62 from hwf.2.1); have : sint.Z a.Checksum'.len = (sint.nat a.Checksum'.len : Int) := by word
      omega
    try wp_auto
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl]
    wp_apply wp_pv _ _ a.Checksum'.len $$ [Hsl] as %wlen2 ⟨%Hwl2, Hsl⟩
    · iframe Hsl; ipureintro
      refine ⟨by rw [Hal2.1]; decide, Hl2.2, h622⟩
    rw [hn2] at Hwl2
    isimp only [hn2] at Hsl
    have hvl2 := varintLen_length (A.cs.length) (by have := (show A.cs.length < 2 ^ 62 from hwf.2.1); omega)
    rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen2 by rw [Hwl2]; exact Int.natCast_nonneg _)]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl2]; exact Int.natCast_nonneg _,
      by rw [Hwl2]; have : sint.Z (W64 10) = 10 := rfl; omega⟩)]
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl,
      show wlen2 - W64 0 = wlen2 by word]
    icases slice_pre b_ptr (W64 10) wlen2 _ ⟨by rw [Hwl2]; exact Int.natCast_nonneg _,
      by rw [Hwl2]; have : sint.Z (W64 10) = 10 := rfl; omega⟩ $$ Hsl with ⟨Hv2, Hback⟩
    have hwn2 : sint.nat wlen2 = (sp.varintLen (A.cs.length)).length := by
      have : sint.Z wlen2 = (sint.nat wlen2 : Int) := by word
      omega
    rw [hwn2, List.take_left]
    wp_auto
    wp_apply HW $$ HS [] Hv2 as %nn2 %err2 HS Hv2
    · iapply Qp $$ Hpc HQ
      ipureintro
      exact ⟨A.cs.flatten ++ sp.le64 a.Seqnum', by rw [hbody]; simp⟩
    ihave Hsl := Hback $$ %_ Hv2 %(by first | rfl | exact hwn2.symm)
    ihave %Hal2' := ownSlice_len $$ Hsl
    simp only at Hal2'
    ihave HL : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice),
        "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
        "HS" ∷ S (((W ++ (sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ (A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length) ++ (A.cs.take k).flatten) ∗
        "Hsl" ∷ slice.mk b_ptr (W64 10) (W64 10) ↦* arr ∗
        "%Hk" ∷ ⌜arr.length = sint.nat (W64 10) ∧ k ≤ A.cs.length⌝ : IProp netDistGF) $$ [i bs HS Hsl]
    · iexists 0, _, _
      iframe
      isplitl [HS]
      · iExactEq HS; congr 1; simp
      ipureintro; exact ⟨Hal2'.1, by omega⟩
    wp_for HL
    try wp_auto
    wp_if_destruct
    · obtain ⟨hk1, hk2⟩ := Hk
      have Hif : sint.Z (W64 (k : Int)) < sint.Z a.Checksum'.len := by
        first | exact Hif | simpa using Hif | exact of_decide_eq_true (IntoValInj.intoVal_inj Hif)
      have hcl : sint.Z a.Checksum'.len = A.cs.length := by
        have : sint.Z a.Checksum'.len = (sint.nat a.Checksum'.len : Int) := by word
        omega
      have hk64 : sint.Z (W64 (k : Int)) = k := by
        have := (show A.cs.length < 2 ^ 62 from hwf.2.1); word
      have hkn : k < A.cs.length := by omega
      have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
      have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      obtain ⟨h, hh⟩ : ∃ h, A.cs[k]? = some h := ⟨_, List.getElem?_eq_getElem hkn⟩
      have hh32 : h.length = 32 := hwf.2.2 h (List.mem_of_getElem? hh)
      obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, rfl⟩ : ∃ z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : w8, h = [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
        match h, hh32 with
        | [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31], _ => exact ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, rfl⟩
      have hh' : A.cs[(sint.Z (W64 (k : Int))).toNat]? = some [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
        rw [hk64]; simpa using hh
      have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z a.Checksum'.len := ⟨hk0, Hif⟩
      have hsplit : A.cs = A.cs.take k ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] :: A.cs.drop (k + 1) := by
        have hk' : A.cs[k] = _ := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hh)
        rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
      have hflat : A.cs.flatten = (A.cs.take k).flatten ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] ++ (A.cs.drop (k + 1)).flatten := by
        rw [congrArg List.flatten hsplit]
        simp
      have htake : (A.cs.take (k + 1)).flatten = (A.cs.take k).flatten ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
        rw [List.take_add_one, List.flatten_append, List.getElem?_eq_getElem hkn]
        simp [List.getElem?_eq_getElem hkn] at hh
        simp [hh]
      have hpk : (((W ++ (sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ (A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length) ++ (A.cs.take k).flatten) ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] <+: W ++ A.enc := by
        refine ⟨(A.cs.drop (k + 1)).flatten ++ sp.le64 a.Seqnum', ?_⟩
        rw [hbody, hflat]; simp
      generalize hY : ((W ++ (sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ (A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length) ++ (A.cs.take k).flatten = Y
      rw [hY] at hpk
      ihave #HQk : □ Q (Y ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31]) $$ []
      · iapply Qp $$ Hpc HQ
        ipureintro
        simpa using hpk
      icases slice_pre b_ptr (W64 10) (W64 1) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
      obtain ⟨y, hy⟩ := take1_of_len arr (by rw [hk1]; decide)
      rw [hy]
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 1 - W64 0 = W64 1 from rfl,
        show W64 10 - W64 0 = W64 10 from rfl]
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      have hSe : Y ++ [z0] ++ [z1] ++ [z2] ++ [z3] ++ [z4] ++ [z5] ++ [z6] ++ [z7] ++ [z8] ++ [z9] ++ [z10] ++ [z11] ++ [z12] ++ [z13] ++ [z14] ++ [z15] ++ [z16] ++ [z17] ++ [z18] ++ [z19] ++ [z20] ++ [z21] ++ [z22] ++ [z23] ++ [z24] ++ [z25] ++ [z26] ++ [z27] ++ [z28] ++ [z29] ++ [z30] ++ [z31] =
          ((W ++ (sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ (A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length) ++ (A.cs.take (k + 1)).flatten := by
        rw [htake, ← hY]; simp
      rw [hSe]
      ihave Hsl := Hback $$ %_ Hb %rfl
      wp_for_post
      iframe
      rw [hkk]
      iexists k + 1, _, _
      iframe
      ipureintro
      exact ⟨len_restore _ _ _ _ rfl hk1 (by decide), by omega⟩
    · obtain ⟨hk1, hk2⟩ := Hk
      have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z a.Checksum'.len := by
        first
        | exact Hif
        | simpa using Hif
        | exact fun h => Hif (by rw [decide_eq_true h])
        | exact of_decide_eq_false (IntoValInj.intoVal_inj Hif)
      have hkn : k = A.cs.length := by
        have : sint.Z (W64 (k : Int)) = k := by have := (show A.cs.length < 2 ^ 62 from hwf.2.1); word
        have : sint.Z a.Checksum'.len = (sint.nat a.Checksum'.len : Int) := by word
        omega
      subst hkn
      rw [List.take_length]
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl,
        show W64 10 - W64 0 = W64 10 from rfl]
      icases slice_pre b_ptr (W64 10) (W64 8) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
      obtain ⟨lb, hlb', hlb⟩ := take_of_len arr (W64 8) 8 (by rw [hk1]; decide) rfl
      rw [hlb']
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      first | rw [set8 _ hlb, le64_sbytes] | rw [set8' _ hlb, le64_sbytes]
      try wp_auto
      wp_apply HW $$ HS [] Hb as %nn5 %err5 HS Hb
      · iapply Qp $$ Hpc HQ
        ipureintro
        exact ⟨[], by rw [hbody]; simp⟩
      iapply HΦ
      isplitl [HS]
      · iExactEq HS; rw [hbody]; simp
      iapply typedPointsto_combine _ _ _ Htn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
      iapply typedPointsto_combine _ _ _ Hcn
      simp only [TypedPointsto.typedPointstoDef]
      iframe


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `(*MFastAck).Marshal(wire)`: `FastAck.enc` (an `MAcks` entry). -/
theorem swift.MFastAck.Marshal.wp (wp_pv : swift.PutVarint.specH (hG := hG))
    (t : Loc) (dq : DFrac) (a : swift.MFastAck) (A : sp.FastAck) (hwf : A.wf)
    (wr : GoInterface) (S Q : List w8 → IProp netDistGF) (W : List w8) :
    {{ sinkOk wr S Q ∗ S W ∗ bufio.prefixClosed Q ∗ □ Q (W ++ A.enc) ∗ t ↦{dq} a ∗
        swift.fastAckRepr a A }}
      (App (Val (t @!! go.GoType.PointerType swift.MFastAck.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ A.enc) ∗ t ↦{dq} a }} := by
  wp_start as ⟨#Hsink, HS, #Hpc, #HQ, Ht, Hrep⟩
  iunfold swift.fastAckRepr at Hrep
  icases Hrep with ⟨%Hid, #HD, #Hcs⟩
  obtain ⟨hrep, hbal, hid, hseq⟩ := Hid
  have hbody : W ++ A.enc = W ++ (sp.le32 a.Replica' ++ sp.le32 a.Ballot' ++
      sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum' ++
      sp.varintLen A.dep.length ++ (A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length ++
      A.cs.flatten ++ sp.le64 a.Seqnum') := by
    simp only [sp.FastAck.enc, sp.encCmdId, sp.encDep, sp.encHashes, ← hrep, ← hbal, ← hid, ← hseq,
      swift.toCmdId, List.append_assoc]
  ihave %Htn := typedPointsto_not_null $$ Ht
  icases typedPointsto_split _ _ _ $$ Ht with Ht
  simp only [TypedPointsto.typedPointstoDef]
  icases Ht with ⟨Replica, Ballot, CmdId, Dep, Checksum, Seqnum, -⟩
  ihave %Hcn := typedPointsto_not_null $$ CmdId
  icases typedPointsto_split _ _ _ $$ CmdId with CmdId
  simp only [TypedPointsto.typedPointstoDef]
  icases CmdId with ⟨ClientId, SeqNum, -⟩
  wp_auto
  ihave Hsl := slice_array b_ptr 16 (Perennial.zero_val (GoArray w8 16)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 16)).arr = List.replicate 16 (W8 0) from rfl]
  mstore
  mstore
  mstore
  mstore
  mstore
  mstore
  mstore
  mstore
  mstore
  mstore
  mstore
  mstore
  mstore
  mstore
  mstore
  mstore
  rw [set16 _ (by simp), le32x4_sbytes]
  iunfold sinkOk at Hsink
  icases Hsink with ⟨%e, %He, #HW⟩
  subst He
  try wp_auto
  wp_apply HW $$ HS [] Hsl as %nn0 %err0 HS Hsl
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨sp.varintLen A.dep.length ++ (A.dep.map sp.encCmdId).flatten ++
      sp.varintLen A.cs.length ++ A.cs.flatten ++ sp.le64 a.Seqnum', by rw [hbody]; simp⟩
  ihave %Hal1 := ownSlice_len $$ Hsl
  simp only at Hal1
  ihave %Hl1 := ownSlice_len $$ HD
  have hn1 : sint.nat a.Dep'.len = A.dep.length := by simpa using Hl1.1.symm
  have h621 : sint.Z a.Dep'.len < 2 ^ 62 := by
    have := (show A.dep.length < 2 ^ 62 from hwf.1); have : sint.Z a.Dep'.len = (sint.nat a.Dep'.len : Int) := by word
    omega
  try wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl]
  wp_apply wp_pv _ _ a.Dep'.len $$ [Hsl] as %wlen1 ⟨%Hwl1, Hsl⟩
  · iframe Hsl; ipureintro
    refine ⟨by rw [Hal1.1]; decide, Hl1.2, h621⟩
  rw [hn1] at Hwl1
  isimp only [hn1] at Hsl
  have hvl1 := varintLen_length (A.dep.length) (by have := (show A.dep.length < 2 ^ 62 from hwf.1); omega)
  rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen1 by rw [Hwl1]; exact Int.natCast_nonneg _)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 16) = 16 := rfl; omega⟩)]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl,
    show wlen1 - W64 0 = wlen1 by word]
  icases slice_pre b_ptr (W64 16) wlen1 _ ⟨by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 16) = 16 := rfl; omega⟩ $$ Hsl with ⟨Hv1, Hback⟩
  have hwn1 : sint.nat wlen1 = (sp.varintLen (A.dep.length)).length := by
    have : sint.Z wlen1 = (sint.nat wlen1 : Int) := by word
    omega
  rw [hwn1, List.take_left]
  wp_auto
  wp_apply HW $$ HS [] Hv1 as %nn1 %err1 HS Hv1
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨(A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length ++ A.cs.flatten ++ sp.le64 a.Seqnum', by rw [hbody]; simp⟩
  ihave Hsl := Hback $$ %_ Hv1 %(by first | rfl | exact hwn1.symm)
  ihave %Hal1' := ownSlice_len $$ Hsl
  simp only at Hal1'
  ihave HL : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice) (tv : w32),
      "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗ "tmp32" ∷ tmp32_ptr ↦ tv ∗
      "HS" ∷ S ((W ++ (sp.le32 a.Replica' ++ sp.le32 a.Ballot' ++ sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ ((A.dep.take k).map sp.encCmdId).flatten) ∗
      "Hsl" ∷ slice.mk b_ptr (W64 16) (W64 16) ↦* arr ∗
      "%Hk" ∷ ⌜arr.length = sint.nat (W64 16) ∧ k ≤ A.dep.length⌝ : IProp netDistGF) $$ [i bs tmp32 HS Hsl]
  · iexists 0, _, _, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; simp
    ipureintro; exact ⟨Hal1'.1, by omega⟩
  wp_for HL
  try wp_auto
  wp_if_destruct
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : sint.Z (W64 (k : Int)) < sint.Z a.Dep'.len := by
      first | exact Hif | simpa using Hif | exact of_decide_eq_true (IntoValInj.intoVal_inj Hif)
    have hcl : sint.Z a.Dep'.len = A.dep.length := by
      have : sint.Z a.Dep'.len = (sint.nat a.Dep'.len : Int) := by word
      omega
    have hk64 : sint.Z (W64 (k : Int)) = k := by
      have := (show A.dep.length < 2 ^ 62 from hwf.1); word
    have hkn : k < A.dep.length := by omega
    have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
    have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z a.Dep'.len := ⟨hk0, Hif⟩
    obtain ⟨d, hd⟩ : ∃ d, A.dep[k]? = some d := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hd' : (A.dep.map swift.ofCmdId)[(sint.Z (W64 (k : Int))).toNat]? = some (swift.ofCmdId d) := by
      rw [hk64]; simp [hd]
    have htake : ((A.dep.take (k + 1)).map sp.encCmdId).flatten = ((A.dep.take k).map sp.encCmdId).flatten ++ (sp.le32 d.cl ++ sp.le32 d.seq) := by
      rw [List.take_add_one, hd]; simp [sp.encCmdId]
    have hsplit : A.dep = A.dep.take k ++ d :: A.dep.drop (k + 1) := by
      have hk' : A.dep[k] = d := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hd)
      rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
    have hflat : (A.dep.map sp.encCmdId).flatten =
        ((A.dep.take k).map sp.encCmdId).flatten ++ (sp.le32 d.cl ++ sp.le32 d.seq) ++ ((A.dep.drop (k + 1)).map sp.encCmdId).flatten := by
      rw [congrArg (fun l => (List.map sp.encCmdId l).flatten) hsplit]
      simp [sp.encCmdId]
    have hp2 : ((W ++ (sp.le32 a.Replica' ++ sp.le32 a.Ballot' ++ sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ ((A.dep.take k).map sp.encCmdId).flatten) ++ (sp.le32 d.cl ++ sp.le32 d.seq) <+: W ++ A.enc := by
      refine ⟨((A.dep.drop (k + 1)).map sp.encCmdId).flatten ++ sp.varintLen A.cs.length ++ A.cs.flatten ++ sp.le64 a.Seqnum', ?_⟩
      rw [hbody, hflat]; simp
    generalize hY : (W ++ (sp.le32 a.Replica' ++ sp.le32 a.Ballot' ++ sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ ((A.dep.take k).map sp.encCmdId).flatten = Y
    rw [hY] at hp2
    have hp1 : Y ++ sp.le32 d.cl <+: W ++ A.enc :=
      List.IsPrefix.trans ⟨sp.le32 d.seq, by simp⟩ hp2
    icases slice_pre b_ptr (W64 16) (W64 4) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
    obtain ⟨lb, hlb', hlb⟩ := take_of_len arr (W64 4) 4 (by rw [hk1]; decide) rfl
    rw [hlb']
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 4 - W64 0 = W64 4 from rfl,
      show W64 16 - W64 0 = W64 16 from rfl]
    try wp_auto
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
    try wp_auto
    wp_apply wp_load_cl _ _ _ _ _ hk0 hd' $$ [HD] as -
    · iexact HD
    try wp_auto
    mstoreb
    mstoreb
    mstoreb
    mstoreb
    first | rw [set4 _ hlb, le32_sbytes] | rw [set4' _ hlb, le32_sbytes]
    try wp_auto
    wp_apply HW $$ HS [] Hb as %nn1 %err1 HS Hb
    · iapply Qp $$ Hpc HQ
      ipureintro
      exact hp1
    try wp_auto
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
    try wp_auto
    wp_apply wp_load_seq _ _ _ _ _ hk0 hd' $$ [HD] as -
    · iexact HD
    try wp_auto
    mstoreb
    mstoreb
    mstoreb
    mstoreb
    first | rw [set4 _ (by simp [sp.le32, u32Le_length]), le32_sbytes] | rw [set4' _ (by simp [sp.le32, u32Le_length]), le32_sbytes]
    try wp_auto
    wp_apply HW $$ HS [] Hb as %nn2 %err2 HS Hb
    · iapply Qp $$ Hpc HQ
      ipureintro
      simpa using hp2
    ihave Hsl := Hback $$ %_ Hb %(by simp [sp.le32, u32Le_length]; rfl)
    wp_for_post
    iframe
    rw [hkk]
    iexists k + 1, _, _, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; rw [htake, ← hY]; simp [swift.ofCmdId]
    ipureintro
    exact ⟨len_restore _ _ _ _ (by simp [sp.le32, u32Le_length]; rfl) hk1 (by decide), by omega⟩
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z a.Dep'.len := by
      first
      | exact Hif
      | simpa using Hif
      | exact fun h => Hif (by rw [decide_eq_true h])
      | exact of_decide_eq_false (IntoValInj.intoVal_inj Hif)
    have hkn : k = A.dep.length := by
      have : sint.Z (W64 (k : Int)) = k := by have := (show A.dep.length < 2 ^ 62 from hwf.1); word
      have : sint.Z a.Dep'.len = (sint.nat a.Dep'.len : Int) := by word
      omega
    subst hkn
    rw [List.take_length]
    ihave %Hal2 := ownSlice_len $$ Hsl
    simp only at Hal2
    ihave %Hl2 := ownSlice_len $$ Hcs
    have hn2 : sint.nat a.Checksum'.len = A.cs.length := by simpa using Hl2.1.symm
    have h622 : sint.Z a.Checksum'.len < 2 ^ 62 := by
      have := (show A.cs.length < 2 ^ 62 from hwf.2.1); have : sint.Z a.Checksum'.len = (sint.nat a.Checksum'.len : Int) := by word
      omega
    try wp_auto
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl]
    wp_apply wp_pv _ _ a.Checksum'.len $$ [Hsl] as %wlen2 ⟨%Hwl2, Hsl⟩
    · iframe Hsl; ipureintro
      refine ⟨by rw [Hal2.1]; decide, Hl2.2, h622⟩
    rw [hn2] at Hwl2
    isimp only [hn2] at Hsl
    have hvl2 := varintLen_length (A.cs.length) (by have := (show A.cs.length < 2 ^ 62 from hwf.2.1); omega)
    rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen2 by rw [Hwl2]; exact Int.natCast_nonneg _)]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl2]; exact Int.natCast_nonneg _,
      by rw [Hwl2]; have : sint.Z (W64 16) = 16 := rfl; omega⟩)]
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl,
      show wlen2 - W64 0 = wlen2 by word]
    icases slice_pre b_ptr (W64 16) wlen2 _ ⟨by rw [Hwl2]; exact Int.natCast_nonneg _,
      by rw [Hwl2]; have : sint.Z (W64 16) = 16 := rfl; omega⟩ $$ Hsl with ⟨Hv2, Hback⟩
    have hwn2 : sint.nat wlen2 = (sp.varintLen (A.cs.length)).length := by
      have : sint.Z wlen2 = (sint.nat wlen2 : Int) := by word
      omega
    rw [hwn2, List.take_left]
    wp_auto
    wp_apply HW $$ HS [] Hv2 as %nn2 %err2 HS Hv2
    · iapply Qp $$ Hpc HQ
      ipureintro
      exact ⟨A.cs.flatten ++ sp.le64 a.Seqnum', by rw [hbody]; simp⟩
    ihave Hsl := Hback $$ %_ Hv2 %(by first | rfl | exact hwn2.symm)
    ihave %Hal2' := ownSlice_len $$ Hsl
    simp only at Hal2'
    ihave HL : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice),
        "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
        "HS" ∷ S (((W ++ (sp.le32 a.Replica' ++ sp.le32 a.Ballot' ++ sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ (A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length) ++ (A.cs.take k).flatten) ∗
        "Hsl" ∷ slice.mk b_ptr (W64 16) (W64 16) ↦* arr ∗
        "%Hk" ∷ ⌜arr.length = sint.nat (W64 16) ∧ k ≤ A.cs.length⌝ : IProp netDistGF) $$ [i bs HS Hsl]
    · iexists 0, _, _
      iframe
      isplitl [HS]
      · iExactEq HS; congr 1; simp
      ipureintro; exact ⟨Hal2'.1, by omega⟩
    wp_for HL
    try wp_auto
    wp_if_destruct
    · obtain ⟨hk1, hk2⟩ := Hk
      have Hif : sint.Z (W64 (k : Int)) < sint.Z a.Checksum'.len := by
        first | exact Hif | simpa using Hif | exact of_decide_eq_true (IntoValInj.intoVal_inj Hif)
      have hcl : sint.Z a.Checksum'.len = A.cs.length := by
        have : sint.Z a.Checksum'.len = (sint.nat a.Checksum'.len : Int) := by word
        omega
      have hk64 : sint.Z (W64 (k : Int)) = k := by
        have := (show A.cs.length < 2 ^ 62 from hwf.2.1); word
      have hkn : k < A.cs.length := by omega
      have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
      have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      obtain ⟨h, hh⟩ : ∃ h, A.cs[k]? = some h := ⟨_, List.getElem?_eq_getElem hkn⟩
      have hh32 : h.length = 32 := hwf.2.2 h (List.mem_of_getElem? hh)
      obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, rfl⟩ : ∃ z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : w8, h = [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
        match h, hh32 with
        | [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31], _ => exact ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, rfl⟩
      have hh' : A.cs[(sint.Z (W64 (k : Int))).toNat]? = some [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
        rw [hk64]; simpa using hh
      have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z a.Checksum'.len := ⟨hk0, Hif⟩
      have hsplit : A.cs = A.cs.take k ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] :: A.cs.drop (k + 1) := by
        have hk' : A.cs[k] = _ := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hh)
        rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
      have hflat : A.cs.flatten = (A.cs.take k).flatten ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] ++ (A.cs.drop (k + 1)).flatten := by
        rw [congrArg List.flatten hsplit]
        simp
      have htake : (A.cs.take (k + 1)).flatten = (A.cs.take k).flatten ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
        rw [List.take_add_one, List.flatten_append, List.getElem?_eq_getElem hkn]
        simp [List.getElem?_eq_getElem hkn] at hh
        simp [hh]
      have hpk : (((W ++ (sp.le32 a.Replica' ++ sp.le32 a.Ballot' ++ sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ (A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length) ++ (A.cs.take k).flatten) ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] <+: W ++ A.enc := by
        refine ⟨(A.cs.drop (k + 1)).flatten ++ sp.le64 a.Seqnum', ?_⟩
        rw [hbody, hflat]; simp
      generalize hY : ((W ++ (sp.le32 a.Replica' ++ sp.le32 a.Ballot' ++ sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ (A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length) ++ (A.cs.take k).flatten = Y
      rw [hY] at hpk
      ihave #HQk : □ Q (Y ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31]) $$ []
      · iapply Qp $$ Hpc HQ
        ipureintro
        simpa using hpk
      icases slice_pre b_ptr (W64 16) (W64 1) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
      obtain ⟨y, hy⟩ := take1_of_len arr (by rw [hk1]; decide)
      rw [hy]
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 1 - W64 0 = W64 1 from rfl,
        show W64 16 - W64 0 = W64 16 from rfl]
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      hbyte
      have hSe : Y ++ [z0] ++ [z1] ++ [z2] ++ [z3] ++ [z4] ++ [z5] ++ [z6] ++ [z7] ++ [z8] ++ [z9] ++ [z10] ++ [z11] ++ [z12] ++ [z13] ++ [z14] ++ [z15] ++ [z16] ++ [z17] ++ [z18] ++ [z19] ++ [z20] ++ [z21] ++ [z22] ++ [z23] ++ [z24] ++ [z25] ++ [z26] ++ [z27] ++ [z28] ++ [z29] ++ [z30] ++ [z31] =
          ((W ++ (sp.le32 a.Replica' ++ sp.le32 a.Ballot' ++ sp.le32 a.CmdId'.ClientId' ++ sp.le32 a.CmdId'.SeqNum') ++ sp.varintLen A.dep.length) ++ (A.dep.map sp.encCmdId).flatten ++ sp.varintLen A.cs.length) ++ (A.cs.take (k + 1)).flatten := by
        rw [htake, ← hY]; simp
      rw [hSe]
      ihave Hsl := Hback $$ %_ Hb %rfl
      wp_for_post
      iframe
      rw [hkk]
      iexists k + 1, _, _
      iframe
      ipureintro
      exact ⟨len_restore _ _ _ _ rfl hk1 (by decide), by omega⟩
    · obtain ⟨hk1, hk2⟩ := Hk
      have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z a.Checksum'.len := by
        first
        | exact Hif
        | simpa using Hif
        | exact fun h => Hif (by rw [decide_eq_true h])
        | exact of_decide_eq_false (IntoValInj.intoVal_inj Hif)
      have hkn : k = A.cs.length := by
        have : sint.Z (W64 (k : Int)) = k := by have := (show A.cs.length < 2 ^ 62 from hwf.2.1); word
        have : sint.Z a.Checksum'.len = (sint.nat a.Checksum'.len : Int) := by word
        omega
      subst hkn
      rw [List.take_length]
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl,
        show W64 16 - W64 0 = W64 16 from rfl]
      icases slice_pre b_ptr (W64 16) (W64 8) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
      obtain ⟨lb, hlb', hlb⟩ := take_of_len arr (W64 8) 8 (by rw [hk1]; decide) rfl
      rw [hlb']
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      first | rw [set8 _ hlb, le64_sbytes] | rw [set8' _ hlb, le64_sbytes]
      try wp_auto
      wp_apply HW $$ HS [] Hb as %nn5 %err5 HS Hb
      · iapply Qp $$ Hpc HQ
        ipureintro
        exact ⟨[], by rw [hbody]; simp⟩
      iapply HΦ
      isplitl [HS]
      · iExactEq HS; rw [hbody]; simp
      iapply typedPointsto_combine _ _ _ Htn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
      iapply typedPointsto_combine _ _ _ Hcn
      simp only [TypedPointsto.typedPointstoDef]
      iframe


end proofs

end Perennial.github_com.imdea_software.swiftpaxos
