/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/MarshalFac.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift messages' writers, part 2: `(*MFastAckClient).Marshal` and `(*MReply).Marshal`
(`swift.MFastAckClient.marshalH`, Proof/swift/Batcher.lean; `swift.MReply.marshalH`,
Proof/swift/ReplyChan.lean), over the `PutVarint` hypothesis (Proof/swift/MarshalSpecs.lean).
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
theorem swift.MFastAckClient.Marshal.wp (wp_pv : swift.PutVarint.specH (hG := hG))
    (l : Loc) (r b : w32) (x : swift.CommandId) (csl : GoSlice) (cs : List sp.Hash)
    (hwf : sp.hashesWf cs)
    (wr : GoInterface) (S Q : List w8 → IProp netDistGF) (W : List w8) :
    {{ sinkOk wr S Q ∗ S W ∗ bufio.prefixClosed Q ∗
        □ Q (W ++ (sp.Msg.fastAckClient r b (swift.toCmdId x) cs).body) ∗
        l ↦ swift.MFastAckClient.mk r b x csl ∗ csl ↦* cs.map swift.handler.shashOf }}
      (App (Val (l @!! go.GoType.PointerType swift.MFastAckClient.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ (sp.Msg.fastAckClient r b (swift.toCmdId x) cs).body) ∗
        l ↦ swift.MFastAckClient.mk r b x csl ∗ csl ↦* cs.map swift.handler.shashOf }} := by
  wp_start as ⟨#Hsink, HS, #Hpc, #HQ, Ht, Hcs⟩
  ihave %Htn := typedPointsto_not_null $$ Ht
  icases typedPointsto_split _ _ _ $$ Ht with Ht
  simp only [TypedPointsto.typedPointstoDef]
  icases Ht with ⟨Replica, Ballot, CmdId, Checksum, -⟩
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
  have hbody : W ++ (sp.Msg.fastAckClient r b (swift.toCmdId x) cs).body =
      (W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum')) ++
        sp.varintLen cs.length ++ cs.flatten := by
    simp only [sp.Msg.body, sp.encCmdId, sp.encHashes, swift.toCmdId, List.append_assoc]
  ihave #HQ1 := Qpre Q _ _ _ (hbody.trans (List.append_assoc _ _ _)) $$ [$Hpc $HQ]
  wp_pures
  wp_apply HW $$ HS HQ1 Hsl as %nn %err HS Hsl
  ihave %Hcl := ownSlice_len $$ Hcs
  have hn : sint.nat csl.len = cs.length := by simpa using Hcl.1.symm
  have hn62 : sint.Z csl.len < 2 ^ 62 := by
    have := hwf.1; have : sint.Z csl.len = (sint.nat csl.len : Int) := by word
    omega
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl]
  wp_apply wp_pv _ _ csl.len $$ [Hsl] as %wlen ⟨%Hwl, Hsl⟩
  · iframe Hsl; ipureintro
    refine ⟨by simp [sp.le32, u32Le_length], Hcl.2, hn62⟩
  rw [hn] at Hwl
  isimp only [hn] at Hsl
  have hvl := varintLen_length cs.length (by have := hwf.1; omega)
  rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen by rw [Hwl]; exact Int.natCast_nonneg _)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl]; exact Int.natCast_nonneg _,
    by rw [Hwl]; have : sint.Z (W64 16) = 16 := rfl; omega⟩)]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl,
    show wlen - W64 0 = wlen by word]
  icases slice_pre b_ptr (W64 16) wlen _ ⟨by rw [Hwl]; exact Int.natCast_nonneg _,
    by rw [Hwl]; have : sint.Z (W64 16) = 16 := rfl; omega⟩ $$ Hsl with ⟨Hv, Hback⟩
  have hwn : sint.nat wlen = (sp.varintLen cs.length).length := by
    have : sint.Z wlen = (sint.nat wlen : Int) := by word
    omega
  rw [hwn, List.take_left]
  ihave #HQ2 := Qpre Q _ _ _ (hbody) $$ [$Hpc $HQ]
  wp_auto
  wp_apply HW $$ HS HQ2 Hv as %nn2 %err2 HS Hv
  ihave Hsl := Hback $$ %_ Hv %(by first | rfl | exact hwn.symm)
  ihave HL : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice),
      "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
      "HS" ∷ S ((W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum') ++
        sp.varintLen cs.length) ++ (cs.take k).flatten) ∗
      "Hsl" ∷ slice.mk b_ptr (W64 16) (W64 16) ↦* arr ∗
      "Hcs" ∷ csl ↦* cs.map swift.handler.shashOf ∗
      "%Hk" ∷ ⌜arr.length = 16 ∧ k ≤ cs.length⌝ : IProp netDistGF) $$ [i bs HS Hsl Hcs]
  · iexists 0, _, _
    simp only [List.take_zero, List.flatten_nil, List.append_nil]
    iframe
    ipureintro; simp [sp.le32, u32Le_length]; omega
  wp_for HL
  wp_if_destruct
  · obtain ⟨hk1, hk2⟩ := Hk
    have hk64 : sint.Z (W64 (k : Int)) = k := by
      have := hwf.1; word
    have hcl : sint.Z csl.len = cs.length := by
      have : sint.Z csl.len = (sint.nat csl.len : Int) := by word
      omega
    have hkn : k < cs.length := by omega
    have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
    have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    obtain ⟨h, hh⟩ : ∃ h, cs[k]? = some h := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hh32 : h.length = 32 := hwf.2 h (List.mem_of_getElem? hh)
    obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, rfl⟩ : ∃ z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : w8, h = [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
      match h, hh32 with
      | [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31], _ => exact ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, rfl⟩
    have hh' : cs[(sint.Z (W64 (k : Int))).toNat]? = some [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
      rw [hk64]; simpa using hh
    have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z csl.len := ⟨hk0, Hif⟩
    have hsplit : cs = cs.take k ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] :: cs.drop (k + 1) := by
      have hk' : cs[k] = _ := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hh)
      rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
    have hflat : cs.flatten = (cs.take k).flatten ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] ++ (cs.drop (k + 1)).flatten := by
      rw [congrArg List.flatten hsplit]
      simp
    have htake : (cs.take (k + 1)).flatten = (cs.take k).flatten ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
      rw [List.take_add_one, List.flatten_append, List.getElem?_eq_getElem hkn]
      simp [List.getElem?_eq_getElem hkn] at hh
      simp [hh]
    generalize hY : (W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum') ++
        sp.varintLen cs.length) ++ (cs.take k).flatten = Y
    ihave #HQk : □ Q (Y ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31]) $$ []
    · iapply Qp $$ Hpc HQ
      ipureintro
      rw [hbody, hflat, ← hY]
      exact ⟨(cs.drop (k + 1)).flatten, by simp⟩
    icases slice_pre b_ptr (W64 16) (W64 1) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
    obtain ⟨y, hy⟩ : ∃ y, arr.take (sint.nat (W64 1)) = [y] := by
      match arr, hk1 with
      | a :: _, _ => exact ⟨a, rfl⟩
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
        (W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum') ++
          sp.varintLen cs.length) ++ (cs.take (k + 1)).flatten := by
      rw [htake, ← hY]; simp
    rw [hSe]
    ihave Hsl := Hback $$ %_ Hb %rfl
    wp_for_post
    iframe
    rw [hkk]
    iexists k + 1, _, _
    isplitl [i]
    · iexact i
    isplitl [bs]
    · iexact bs
    isplitl [HS]
    · iexact HS
    isplitl [Hsl]
    · iexact Hsl
    isplitl [Hcs]
    · iexact Hcs
    ipureintro
    refine ⟨?_, by omega⟩
    simp only [List.length_append, List.length_singleton, List.length_drop, hk1]
    rfl
  · obtain ⟨hk1, hk2⟩ := Hk
    have hkn : k = cs.length := by
      have : sint.Z (W64 (k : Int)) = k := by have := hwf.1; word
      have : sint.Z csl.len = (sint.nat csl.len : Int) := by word
      omega
    subst hkn
    rw [List.take_length, show (W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++
      sp.le32 x.SeqNum') ++ sp.varintLen cs.length) ++ cs.flatten =
      W ++ (sp.Msg.fastAckClient r b (swift.toCmdId x) cs).body by
        rw [hbody]]
    iapply HΦ
    iframe HS Hcs
    iapply typedPointsto_combine _ _ _ Htn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
    iapply typedPointsto_combine _ _ _ Hcn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

/-- **`swift.MFastAckClient.marshalH`**, over `PutVarint`'s hypothesis. -/
theorem swift.MFastAckClient.marshal_proof (wp_pv : swift.PutVarint.specH (hG := hG)) :
    swift.MFastAckClient.marshalH (hG := hG) := by
  intro l r b x csl cs hwf
  unfold sp.marshalOk
  iexists ⟨go.GoType.PointerType swift.MFastAckClient.ty, #l⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %wr %S %Q %W %Φ ⟨Hl, Hcs⟩ #Hsink HS #Hpc #HQ HΦ
  wp_apply swift.MFastAckClient.Marshal.wp wp_pv l r b x csl cs hwf wr S Q W $$
    [$Hsink $HS $Hpc $HQ $Hl $Hcs] as ⟨HS, Hl, Hcs⟩
  iapply HΦ $$ [$Hl $Hcs] HS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem swift.MReply.Marshal.wp (wp_pv : swift.PutVarint.specH (hG := hG))
    (l : Loc) (r b : w32) (x : swift.CommandId) (csl vsl : GoSlice) (cs : List sp.Hash)
    (v : List w8) (hwf : sp.hashesWf cs ∧ v.length < 2 ^ 62)
    (wr : GoInterface) (S Q : List w8 → IProp netDistGF) (W : List w8) :
    {{ sinkOk wr S Q ∗ S W ∗ bufio.prefixClosed Q ∗
        □ Q (W ++ (sp.Msg.reply r b (swift.toCmdId x) cs v).body) ∗
        l ↦ swift.MReply.mk r b x csl vsl ∗ csl ↦* cs.map swift.handler.shashOf ∗ vsl ↦*□ v }}
      (App (Val (l @!! go.GoType.PointerType swift.MReply.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ (sp.Msg.reply r b (swift.toCmdId x) cs v).body) ∗
        l ↦ swift.MReply.mk r b x csl vsl ∗ csl ↦* cs.map swift.handler.shashOf }} := by
  wp_start as ⟨#Hsink, HS, #Hpc, #HQ, Ht, Hcs, #Hv⟩
  ihave %Htn := typedPointsto_not_null $$ Ht
  icases typedPointsto_split _ _ _ $$ Ht with Ht
  simp only [TypedPointsto.typedPointstoDef]
  icases Ht with ⟨Replica, Ballot, CmdId, Checksum, Rep, -⟩
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
  have hbody : W ++ (sp.Msg.reply r b (swift.toCmdId x) cs v).body =
      (W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum') ++ sp.varintLen cs.length) ++ (cs.flatten ++ sp.encBytes v) := by
    simp only [sp.Msg.body, sp.encCmdId, sp.encHashes, swift.toCmdId, List.append_assoc]
  ihave #HQ1 := Qpre Q (W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum')) _
    (sp.varintLen cs.length ++ cs.flatten ++ sp.encBytes v)
    (by rw [hbody]; simp only [List.append_assoc]) $$ [$Hpc $HQ]
  wp_pures
  wp_apply HW $$ HS HQ1 Hsl as %nn %err HS Hsl
  ihave %Hcl := ownSlice_len $$ Hcs
  have hn : sint.nat csl.len = cs.length := by simpa using Hcl.1.symm
  have hn62 : sint.Z csl.len < 2 ^ 62 := by
    have := hwf.1.1; have : sint.Z csl.len = (sint.nat csl.len : Int) := by word
    omega
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl]
  wp_apply wp_pv _ _ csl.len $$ [Hsl] as %wlen ⟨%Hwl, Hsl⟩
  · iframe Hsl; ipureintro
    refine ⟨by simp [sp.le32, u32Le_length], Hcl.2, hn62⟩
  rw [hn] at Hwl
  isimp only [hn] at Hsl
  have hvl := varintLen_length cs.length (by have := hwf.1.1; omega)
  rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen by rw [Hwl]; exact Int.natCast_nonneg _)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl]; exact Int.natCast_nonneg _,
    by rw [Hwl]; have : sint.Z (W64 16) = 16 := rfl; omega⟩)]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl,
    show wlen - W64 0 = wlen by word]
  icases slice_pre b_ptr (W64 16) wlen _ ⟨by rw [Hwl]; exact Int.natCast_nonneg _,
    by rw [Hwl]; have : sint.Z (W64 16) = 16 := rfl; omega⟩ $$ Hsl with ⟨Hv1, Hback⟩
  have hwn : sint.nat wlen = (sp.varintLen cs.length).length := by
    have : sint.Z wlen = (sint.nat wlen : Int) := by word
    omega
  rw [hwn, List.take_left]
  ihave #HQ2 := Qpre Q (W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum') ++ sp.varintLen cs.length) _ (cs.flatten ++ sp.encBytes v) hbody $$ [$Hpc $HQ]
  wp_auto
  wp_apply HW $$ HS HQ2 Hv1 as %nn2 %err2 HS Hv1
  ihave Hsl := Hback $$ %_ Hv1 %(by first | rfl | exact hwn.symm)
  ihave HL : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice),
      "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
      "HS" ∷ S ((W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum') ++ sp.varintLen cs.length) ++ (cs.take k).flatten) ∗
      "Hsl" ∷ slice.mk b_ptr (W64 16) (W64 16) ↦* arr ∗
      "Hcs" ∷ csl ↦* cs.map swift.handler.shashOf ∗
      "%Hk" ∷ ⌜arr.length = 16 ∧ k ≤ cs.length⌝ : IProp netDistGF) $$ [i bs HS Hsl Hcs ]
  · iexists 0, _, _
    simp only [List.take_zero, List.flatten_nil, List.append_nil]
    iframe
    ipureintro; simp [sp.le32, u32Le_length]; omega
  wp_for HL
  wp_if_destruct
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : sint.Z (W64 (k : Int)) < sint.Z csl.len := by
      first | exact Hif | simpa using Hif
    have hcl : sint.Z csl.len = cs.length := by
      have : sint.Z csl.len = (sint.nat csl.len : Int) := by word
      omega
    have hk64 : sint.Z (W64 (k : Int)) = k := by
      have := hwf.1.1; word
    have hkn : k < cs.length := by omega
    have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
    have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    obtain ⟨h, hh⟩ : ∃ h, cs[k]? = some h := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hh32 : h.length = 32 := hwf.1.2 h (List.mem_of_getElem? hh)
    obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, rfl⟩ : ∃ z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : w8, h = [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
      match h, hh32 with
      | [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31], _ => exact ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, rfl⟩
    have hh' : cs[(sint.Z (W64 (k : Int))).toNat]? = some [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
      rw [hk64]; simpa using hh
    have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z csl.len := ⟨hk0, Hif⟩
    have hsplit : cs = cs.take k ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] :: cs.drop (k + 1) := by
      have hk' : cs[k] = _ := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hh)
      rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
    have hflat : cs.flatten = (cs.take k).flatten ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] ++ (cs.drop (k + 1)).flatten := by
      rw [congrArg List.flatten hsplit]
      simp
    have htake : (cs.take (k + 1)).flatten = (cs.take k).flatten ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31] := by
      rw [List.take_add_one, List.flatten_append, List.getElem?_eq_getElem hkn]
      simp [List.getElem?_eq_getElem hkn] at hh
      simp [hh]
    generalize hY : (W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum') ++ sp.varintLen cs.length) ++ (cs.take k).flatten = Y
    ihave #HQk : □ Q (Y ++ [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31]) $$ []
    · iapply Qp $$ Hpc HQ
      ipureintro
      rw [hbody, hflat, ← hY]
      exact ⟨(cs.drop (k + 1)).flatten ++ sp.encBytes v, by simp⟩
    icases slice_pre b_ptr (W64 16) (W64 1) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
    obtain ⟨y, hy⟩ : ∃ y, arr.take (sint.nat (W64 1)) = [y] := by
      match arr, hk1 with
      | a :: _, _ => exact ⟨a, rfl⟩
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
        (W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum') ++ sp.varintLen cs.length) ++ (cs.take (k + 1)).flatten := by
      rw [htake, ← hY]; simp
    rw [hSe]
    ihave Hsl := Hback $$ %_ Hb %rfl
    wp_for_post
    iframe
    rw [hkk]
    iexists k + 1, _, _
    iframe
    ipureintro
    refine ⟨?_, by omega⟩
    simp only [List.length_append, List.length_singleton, List.length_drop, hk1]
    rfl
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z csl.len := by
      first | exact Hif | simpa using Hif
    have hkn : k = cs.length := by
      have : sint.Z (W64 (k : Int)) = k := by have := hwf.1.1; word
      have : sint.Z csl.len = (sint.nat csl.len : Int) := by word
      omega
    subst hkn
    rw [List.take_length]
    -- the result: its length's varint, then its bytes
    ihave %Hvl := ownSlice_len $$ Hv
    have hvn : sint.nat vsl.len = v.length := Hvl.1.symm
    have hv62 : sint.Z vsl.len < 2 ^ 62 := by
      have := hwf.2; have : sint.Z vsl.len = (sint.nat vsl.len : Int) := by word
      omega
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl]
    wp_apply wp_pv _ _ vsl.len $$ [Hsl] as %wlen3 ⟨%Hwl3, Hsl⟩
    · iframe Hsl; ipureintro
      exact ⟨by omega, Hvl.2, hv62⟩
    rw [hvn] at Hwl3
    isimp only [hvn] at Hsl
    have hvl3 := varintLen_length v.length (by have := hwf.2; omega)
    rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen3 by rw [Hwl3]; exact Int.natCast_nonneg _)]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl3]; exact Int.natCast_nonneg _,
      by rw [Hwl3]; have : sint.Z (W64 16) = 16 := rfl; omega⟩)]
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl,
      show wlen3 - W64 0 = wlen3 by word]
    icases slice_pre b_ptr (W64 16) wlen3 _ ⟨by rw [Hwl3]; exact Int.natCast_nonneg _,
      by rw [Hwl3]; have : sint.Z (W64 16) = 16 := rfl; omega⟩ $$ Hsl with ⟨Hv3, Hback⟩
    have hwn3 : sint.nat wlen3 = (sp.varintLen v.length).length := by
      have : sint.Z wlen3 = (sint.nat wlen3 : Int) := by word
      omega
    rw [hwn3, List.take_left]
    wp_auto
    wp_apply HW $$ HS [] Hv3 as %nn3 %err3 HS Hv3
    · iapply Qp $$ Hpc HQ
      ipureintro
      rw [hbody]
      exact ⟨v, by simp [sp.encBytes]⟩
    ihave Hsl := Hback $$ %_ Hv3 %(by first | rfl | exact hwn3.symm)
    ihave HL : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice),
        "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
        "HS" ∷ S ((W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum') ++
          sp.varintLen cs.length ++ cs.flatten ++ sp.varintLen v.length) ++ v.take k) ∗
        "Hsl" ∷ slice.mk b_ptr (W64 16) (W64 16) ↦* arr ∗
        "%Hk" ∷ ⌜arr.length = 16 ∧ k ≤ v.length⌝ : IProp netDistGF) $$ [i bs HS Hsl]
    · iexists 0, _, _
      iframe
      isplitl [HS]
      · iExactEq HS; congr 1; simp
      ipureintro; simp; omega
    wp_for HL
    wp_if_destruct
    · obtain ⟨hk1, hk2⟩ := Hk
      have Hif : sint.Z (W64 (k : Int)) < sint.Z vsl.len := by
        first | exact Hif | simpa using Hif
      have hcl : sint.Z vsl.len = v.length := by
        have : sint.Z vsl.len = (sint.nat vsl.len : Int) := by word
        omega
      have hk64 : sint.Z (W64 (k : Int)) = k := by
        have := hwf.2; word
      have hkn : k < v.length := by omega
      have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
      have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z vsl.len := ⟨hk0, Hif⟩
      obtain ⟨c, hc⟩ : ∃ c, v[k]? = some c := ⟨_, List.getElem?_eq_getElem hkn⟩
      have hc' : v[(sint.Z (W64 (k : Int))).toNat]? = some c := by rw [hk64]; simpa using hc
      have htk : v.take (k + 1) = v.take k ++ [c] := by
        rw [List.take_add_one, hc]; rfl
      have hpre : (W ++ (sp.le32 r ++ sp.le32 b ++ sp.le32 x.ClientId' ++ sp.le32 x.SeqNum') ++
          sp.varintLen cs.length ++ cs.flatten ++ sp.varintLen v.length) ++ v.take (k + 1) <+:
          W ++ (sp.Msg.reply r b (swift.toCmdId x) cs v).body := by
        refine ⟨v.drop (k + 1), ?_⟩
        rw [hbody]
        simp only [sp.encBytes, List.append_assoc, List.take_append_drop]
      icases slice_pre b_ptr (W64 16) (W64 1) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
      obtain ⟨y, hy⟩ : ∃ y, arr.take (sint.nat (W64 1)) = [y] := by
        match arr, hk1 with
        | a :: _, _ => exact ⟨a, rfl⟩
      rw [hy]
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 1 - W64 0 = W64 1 from rfl,
        show W64 16 - W64 0 = W64 16 from rfl]
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
      try wp_auto
      wp_apply wp_load_slice_index vsl _ v _ c hk0 $$ [Hv] as -
      · iframe Hv; ipureintro; exact hc'
      wp_apply wp_store_slice_index _ _ _ _ $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp only [List.length_singleton]; decide
      rw [List.set_cons_zero]
      try wp_auto
      wp_apply HW $$ HS [] Hb as %nn4 %err4 HS Hb
      · iapply Qp $$ Hpc HQ
        ipureintro
        rw [List.append_assoc, ← htk]
        exact hpre
      rw [List.append_assoc _ (v.take k) [c], ← htk]
      ihave Hsl := Hback $$ %_ Hb %rfl
      wp_for_post
      iframe
      rw [hkk]
      iexists k + 1, _, _
      iframe
      ipureintro
      refine ⟨?_, by omega⟩
      simp only [List.length_append, List.length_singleton, List.length_drop, hk1]
      rfl
    · obtain ⟨hk1, hk2⟩ := Hk
      have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z vsl.len := by
        first | exact Hif | simpa using Hif
      have hkn : k = v.length := by
        have : sint.Z (W64 (k : Int)) = k := by have := hwf.2; word
        have : sint.Z vsl.len = (sint.nat vsl.len : Int) := by word
        omega
      subst hkn
      rw [List.take_length]
      iapply HΦ
      isplitl [HS]
      · iExactEq HS; rw [hbody]; simp [sp.encBytes]
      iframe Hcs
      iapply typedPointsto_combine _ _ _ Htn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
      iapply typedPointsto_combine _ _ _ Hcn
      simp only [TypedPointsto.typedPointstoDef]
      iframe


/-- **`swift.MReply.marshalH`**, over `PutVarint`'s hypothesis. -/
theorem swift.MReply.marshal_proof (wp_pv : swift.PutVarint.specH (hG := hG)) :
    swift.MReply.marshalH (hG := hG) := by
  intro l r b x csl vsl cs v hwf
  unfold sp.marshalOk
  iexists ⟨go.GoType.PointerType swift.MReply.ty, #l⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %wr %S %Q %W %Φ ⟨Hl, Hcs, #Hv⟩ #Hsink HS #Hpc #HQ HΦ
  wp_apply swift.MReply.Marshal.wp wp_pv l r b x csl vsl cs v hwf wr S Q W $$
    [$Hsink $HS $Hpc $HQ $Hl $Hcs $Hv] as ⟨HS, Hl, Hcs⟩
  iapply HΦ $$ [$Hl $Hcs $Hv] HS

end proofs
end Perennial.github_com.imdea_software.swiftpaxos
