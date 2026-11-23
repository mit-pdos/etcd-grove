/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/MarshalOpt.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift messages' writers, part 4: `(*MOptAcks).Marshal` and `(*MAcks).Marshal`
(`swift.MOptAcks.marshalH`, `swift.MAcks.marshalH`, Proof/swift/Batcher.lean), over the `PutVarint`
hypothesis (Proof/swift/MarshalSpecs.lean); their entries through Proof/swift/MarshalAcks.lean.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalAcks

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv wire

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

set_option goose.wp.extras true

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `(*MOptAcks).Marshal(wire)`: `.optAcks`' body (its entries through `(*Ack).Marshal`). -/
theorem swift.MOptAcks.Marshal.wp (wp_pv : swift.PutVarint.specH (hG := hG))
    (l : Loc) (r b : w32) (asl : GoSlice) (ps : List (swift.Ack × sp.Ack))
    (hwf : sp.Msg.wf (.optAcks r b (ps.map Prod.snd)))
    (wr : GoInterface) (S Q : List w8 → IProp netDistGF) (W : List w8) :
    {{ sinkOk wr S Q ∗ S W ∗ bufio.prefixClosed Q ∗
        □ Q (W ++ (sp.Msg.optAcks r b (ps.map Prod.snd)).body) ∗
        l ↦ swift.MOptAcks.mk r b asl ∗ asl ↦* ps.map Prod.fst ∗
        □ ([∗list] p ∈ ps, swift.ackRepr p.1 p.2) }}
      (App (Val (l @!! go.GoType.PointerType swift.MOptAcks.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ (sp.Msg.optAcks r b (ps.map Prod.snd)).body) ∗
        l ↦ swift.MOptAcks.mk r b asl ∗ asl ↦* ps.map Prod.fst }} := by
  wp_start as ⟨#Hsink, HS, #Hpc, #HQ, Ht, Has, #Hreps⟩
  obtain ⟨hlen, hwfa⟩ := hwf
  simp only [List.length_map] at hlen
  have hbody : W ++ (sp.Msg.optAcks r b (ps.map Prod.snd)).body = W ++ (sp.le32 r ++ sp.le32 b ++
      sp.varintLen ps.length ++ (ps.map (fun p => p.2.enc)).flatten) := by
    simp only [sp.Msg.body, List.length_map, List.map_map, List.append_assoc]
    rfl
  ihave %Htn := typedPointsto_not_null $$ Ht
  icases typedPointsto_split _ _ _ $$ Ht with Ht
  simp only [TypedPointsto.typedPointstoDef]
  icases Ht with ⟨Replica, Ballot, Acks, -⟩
  ihave #Hsink0 := Hsink
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
    exact ⟨sp.varintLen ps.length ++ (ps.map (fun p => p.2.enc)).flatten, by rw [hbody]; simp⟩
  ihave Hsl := Hback $$ %_ Hb %(by simp [sp.le32, u32Le_length]; rfl)
  ihave %Hal1 := ownSlice_len $$ Hsl
  simp only at Hal1
  ihave %Hl1 := ownSlice_len $$ Has
  have hn1 : sint.nat asl.len = ps.length := by simpa using Hl1.1.symm
  have h621 : sint.Z asl.len < 2 ^ 62 := by
    have := hlen; have : sint.Z asl.len = (sint.nat asl.len : Int) := by word
    omega
  try wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl]
  wp_apply wp_pv _ _ asl.len $$ [Hsl] as %wlen1 ⟨%Hwl1, Hsl⟩
  · iframe Hsl; ipureintro
    refine ⟨by rw [Hal1.1]; decide, Hl1.2, h621⟩
  rw [hn1] at Hwl1
  isimp only [hn1] at Hsl
  have hvl1 := varintLen_length (ps.length) (by have := hlen; omega)
  rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen1 by rw [Hwl1]; exact Int.natCast_nonneg _)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 10) = 10 := rfl; omega⟩)]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl,
    show wlen1 - W64 0 = wlen1 by word]
  icases slice_pre b_ptr (W64 10) wlen1 _ ⟨by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 10) = 10 := rfl; omega⟩ $$ Hsl with ⟨Hv1, Hback⟩
  have hwn1 : sint.nat wlen1 = (sp.varintLen (ps.length)).length := by
    have : sint.Z wlen1 = (sint.nat wlen1 : Int) := by word
    omega
  rw [hwn1, List.take_left]
  wp_auto
  wp_apply HW $$ HS [] Hv1 as %nn1 %err1 HS Hv1
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨(ps.map (fun p => p.2.enc)).flatten, by rw [hbody]; simp⟩
  ihave Hsl := Hback $$ %_ Hv1 %(by first | rfl | exact hwn1.symm)
  ihave %Hal1' := ownSlice_len $$ Hsl
  simp only at Hal1'
  ihave HL : (∃ (k : Nat),
      "i" ∷ i_ptr ↦ W64 k ∗
      "HS" ∷ S ((W ++ (sp.le32 r ++ sp.le32 b) ++ sp.varintLen ps.length) ++ ((ps.take k).map (fun p => p.2.enc)).flatten) ∗
      "Has" ∷ asl ↦* ps.map Prod.fst ∗
      "%Hk" ∷ ⌜k ≤ ps.length⌝ : IProp netDistGF) $$ [i HS Has]
  · iexists 0
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; simp
    ipureintro; omega
  wp_for HL
  try wp_auto
  wp_if_destruct
  · have Hif : sint.Z (W64 (k : Int)) < sint.Z asl.len := by
      first | exact Hif | simpa using Hif | exact of_decide_eq_true (IntoValInj.intoVal_inj Hif)
    have hcl : sint.Z asl.len = ps.length := by
      have : sint.Z asl.len = (sint.nat asl.len : Int) := by word
      omega
    have hk64 : sint.Z (W64 (k : Int)) = k := by word
    have hkn : k < ps.length := by omega
    have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
    have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z asl.len := ⟨hk0, Hif⟩
    obtain ⟨p, hp⟩ : ∃ p, ps[k]? = some p := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hp' : (ps.map Prod.fst)[(sint.Z (W64 (k : Int))).toNat]? = some p.1 := by
      rw [hk64]; simp [hp]
    have hsplit : ps = ps.take k ++ p :: ps.drop (k + 1) := by
      have hk' : ps[k] = p := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hp)
      rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
    have htake : ((ps.take (k + 1)).map (fun p => p.2.enc)).flatten = ((ps.take k).map (fun p => p.2.enc)).flatten ++ p.2.enc := by
      rw [List.take_add_one, hp]; simp
    have hpre : ((W ++ (sp.le32 r ++ sp.le32 b) ++ sp.varintLen ps.length) ++ ((ps.take k).map (fun p => p.2.enc)).flatten) ++ p.2.enc <+:
        W ++ (sp.Msg.optAcks r b (ps.map Prod.snd)).body := by
      refine ⟨((ps.drop (k + 1)).map (fun p => p.2.enc)).flatten, ?_⟩
      rw [hbody, congrArg (fun l => (List.map (fun p : swift.Ack × sp.Ack => p.2.enc) l).flatten) hsplit]
      simp
    have hpwf : p.2.wf := hwfa p.2 (List.mem_map.2 ⟨p, List.mem_of_getElem? hp, rfl⟩)
    try wp_auto
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
    try wp_auto
    icases ownSlice_elem_acc (sint.Z (W64 (k : Int))) p.1 asl _ _ hk0 hp' $$ Has with ⟨He, Has⟩
    ihave #Hrp := BigSepL.bigSepL_lookup (Φ := fun _ p => swift.ackRepr p.1 p.2) hp $$ Hreps
    wp_apply swift.Ack.Marshal.wp wp_pv _ _ p.1 p.2 hpwf _ S Q _ $$ [HS He] as ⟨HS, He⟩
    · iframe Hsink0 HS He Hpc Hrp
      iapply Qp $$ Hpc HQ
      ipureintro
      exact hpre
    ihave Has := Has $$ He
    rw [list_set_lookup_self _ _ _ hp']
    try wp_auto
    wp_for_post
    iframe
    rw [hkk]
    iexists k + 1
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; rw [htake]; simp
    ipureintro; omega
  · have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z asl.len := by
      first
      | exact Hif
      | simpa using Hif
      | exact fun h => Hif (by rw [decide_eq_true h])
      | exact of_decide_eq_false (IntoValInj.intoVal_inj Hif)
    have hkn : k = ps.length := by
      have : sint.Z (W64 (k : Int)) = k := by word
      have : sint.Z asl.len = (sint.nat asl.len : Int) := by word
      omega
    subst hkn
    rw [List.take_length]
    iapply HΦ
    isplitl [HS]
    · iExactEq HS; rw [hbody]; simp
    iframe Has
    iapply typedPointsto_combine _ _ _ Htn
    simp only [TypedPointsto.typedPointstoDef]
    iframe


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `(*MAcks).Marshal(wire)`: `.acks`' body (the fast acks through `(*MFastAck).Marshal`, the
light slow acks inline). -/
theorem swift.MAcks.Marshal.wp (wp_pv : swift.PutVarint.specH (hG := hG))
    (l : Loc) (fsl ssl : GoSlice) (fps : List (swift.MFastAck × sp.FastAck))
    (sps : List (swift.MLightSlowAck × sp.SlowAck))
    (hwf : sp.Msg.wf (.acks (fps.map Prod.snd) (sps.map Prod.snd)))
    (hsr : ∀ p ∈ sps, swift.slowAckRepr p.1 p.2)
    (wr : GoInterface) (S Q : List w8 → IProp netDistGF) (W : List w8) :
    {{ sinkOk wr S Q ∗ S W ∗ bufio.prefixClosed Q ∗ □ Q (W ++ (sp.Msg.acks (fps.map Prod.snd) (sps.map Prod.snd)).body) ∗
        typedPointsto l (swift.MAcks.mk fsl ssl) DFrac.discard ∗ fsl ↦* fps.map Prod.fst ∗
        ssl ↦* sps.map Prod.fst ∗ □ ([∗list] p ∈ fps, swift.fastAckRepr p.1 p.2) }}
      (App (Val (l @!! go.GoType.PointerType swift.MAcks.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ (sp.Msg.acks (fps.map Prod.snd) (sps.map Prod.snd)).body) ∗ fsl ↦* fps.map Prod.fst ∗ ssl ↦* sps.map Prod.fst }} := by
  wp_start as ⟨#Hsink, HS, #Hpc, #HQ, #Ht, Hfs, Hss, #Hreps⟩
  obtain ⟨⟨hflen, hfwf⟩, hslen⟩ := hwf
  simp only [List.length_map] at hflen hslen
  have hbody : W ++ (sp.Msg.acks (fps.map Prod.snd) (sps.map Prod.snd)).body = W ++ (sp.varintLen fps.length ++ (fps.map (fun p => p.2.enc)).flatten ++
      sp.varintLen sps.length ++ (sps.map (fun p => p.2.enc)).flatten) := by
    simp only [sp.Msg.body, List.length_map, List.map_map, List.append_assoc]
    rfl
  icases typedPointsto_split _ _ _ $$ Ht with Ht2
  simp only [TypedPointsto.typedPointstoDef]
  icases Ht2 with ⟨#FastAcks, #LightSlowAcks, -⟩
  ihave #Hsink0 := Hsink
  wp_auto
  ihave Hsl := slice_array b_ptr 10 (Perennial.zero_val (GoArray w8 10)) (by decide) $$ b
  rw [show (Perennial.zero_val (GoArray w8 10)).arr = List.replicate 10 (W8 0) from rfl]
  iunfold sinkOk at Hsink
  icases Hsink with ⟨%e, %He, #HW⟩
  subst He
  ihave %Hal1 := ownSlice_len $$ Hsl
  simp only at Hal1
  ihave %Hl1 := ownSlice_len $$ Hfs
  have hn1 : sint.nat fsl.len = fps.length := by simpa using Hl1.1.symm
  have h621 : sint.Z fsl.len < 2 ^ 62 := by
    have := hflen; have : sint.Z fsl.len = (sint.nat fsl.len : Int) := by word
    omega
  try wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl]
  wp_apply wp_pv _ _ fsl.len $$ [Hsl] as %wlen1 ⟨%Hwl1, Hsl⟩
  · iframe Hsl; ipureintro
    refine ⟨by rw [Hal1.1]; decide, Hl1.2, h621⟩
  rw [hn1] at Hwl1
  isimp only [hn1] at Hsl
  have hvl1 := varintLen_length (fps.length) (by have := hflen; omega)
  rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen1 by rw [Hwl1]; exact Int.natCast_nonneg _)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 10) = 10 := rfl; omega⟩)]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl,
    show wlen1 - W64 0 = wlen1 by word]
  icases slice_pre b_ptr (W64 10) wlen1 _ ⟨by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 10) = 10 := rfl; omega⟩ $$ Hsl with ⟨Hv1, Hback⟩
  have hwn1 : sint.nat wlen1 = (sp.varintLen (fps.length)).length := by
    have : sint.Z wlen1 = (sint.nat wlen1 : Int) := by word
    omega
  rw [hwn1, List.take_left]
  wp_auto
  wp_apply HW $$ HS [] Hv1 as %nn1 %err1 HS Hv1
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨(fps.map (fun p => p.2.enc)).flatten ++ sp.varintLen sps.length ++ (sps.map (fun p => p.2.enc)).flatten, by rw [hbody]; simp⟩
  ihave Hsl := Hback $$ %_ Hv1 %(by first | rfl | exact hwn1.symm)
  ihave %Hal1' := ownSlice_len $$ Hsl
  simp only at Hal1'
  ihave HL : (∃ (k : Nat),
      "i" ∷ i_ptr ↦ W64 k ∗
      "HS" ∷ S ((W ++ sp.varintLen fps.length) ++ ((fps.take k).map (fun p => p.2.enc)).flatten) ∗
      "Hfs" ∷ fsl ↦* fps.map Prod.fst ∗
      "%Hk" ∷ ⌜k ≤ fps.length⌝ : IProp netDistGF) $$ [i HS Hfs]
  · iexists 0
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; simp
    ipureintro; omega
  wp_for HL
  try wp_auto
  wp_if_destruct
  · have Hif : sint.Z (W64 (k : Int)) < sint.Z fsl.len := by
      first | exact Hif | simpa using Hif | exact of_decide_eq_true (IntoValInj.intoVal_inj Hif)
    have hcl : sint.Z fsl.len = fps.length := by
      have : sint.Z fsl.len = (sint.nat fsl.len : Int) := by word
      omega
    have hk64 : sint.Z (W64 (k : Int)) = k := by word
    have hkn : k < fps.length := by omega
    have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
    have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z fsl.len := ⟨hk0, Hif⟩
    obtain ⟨p, hp⟩ : ∃ p, fps[k]? = some p := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hp' : (fps.map Prod.fst)[(sint.Z (W64 (k : Int))).toNat]? = some p.1 := by
      rw [hk64]; simp [hp]
    have hsplit : fps = fps.take k ++ p :: fps.drop (k + 1) := by
      have hk' : fps[k] = p := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hp)
      rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
    have htake : ((fps.take (k + 1)).map (fun p => p.2.enc)).flatten = ((fps.take k).map (fun p => p.2.enc)).flatten ++ p.2.enc := by
      rw [List.take_add_one, hp]; simp
    have hpre : ((W ++ sp.varintLen fps.length) ++ ((fps.take k).map (fun p => p.2.enc)).flatten) ++ p.2.enc <+: W ++ (sp.Msg.acks (fps.map Prod.snd) (sps.map Prod.snd)).body := by
      refine ⟨((fps.drop (k + 1)).map (fun p => p.2.enc)).flatten ++ sp.varintLen sps.length ++
        (sps.map (fun p => p.2.enc)).flatten, ?_⟩
      rw [hbody, congrArg (fun l => (List.map (fun p : swift.MFastAck × sp.FastAck => p.2.enc) l).flatten) hsplit]
      simp
    have hpwf : p.2.wf := hfwf p.2 (List.mem_map.2 ⟨p, List.mem_of_getElem? hp, rfl⟩)
    try wp_auto
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
    try wp_auto
    icases ownSlice_elem_acc (sint.Z (W64 (k : Int))) p.1 fsl _ _ hk0 hp' $$ Hfs with ⟨He, Hfs⟩
    ihave #Hrp := BigSepL.bigSepL_lookup (Φ := fun _ p => swift.fastAckRepr p.1 p.2) hp $$ Hreps
    wp_apply swift.MFastAck.Marshal.wp wp_pv _ _ p.1 p.2 hpwf _ S Q _ $$ [HS He] as ⟨HS, He⟩
    · iframe Hsink0 HS He Hpc Hrp
      iapply Qp $$ Hpc HQ
      ipureintro
      exact hpre
    ihave Hfs := Hfs $$ He
    rw [list_set_lookup_self _ _ _ hp']
    try wp_auto
    wp_for_post
    iframe
    rw [hkk]
    iexists k + 1
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; rw [htake]; simp
    ipureintro; omega
  · have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z fsl.len := by
      first
      | exact Hif
      | simpa using Hif
      | exact fun h => Hif (by rw [decide_eq_true h])
      | exact of_decide_eq_false (IntoValInj.intoVal_inj Hif)
    have hkn : k = fps.length := by
      have : sint.Z (W64 (k : Int)) = k := by word
      have : sint.Z fsl.len = (sint.nat fsl.len : Int) := by word
      omega
    subst hkn
    rw [List.take_length]
    ihave %Hal2 := ownSlice_len $$ Hsl
    simp only at Hal2
    ihave %Hl2 := ownSlice_len $$ Hss
    have hn2 : sint.nat ssl.len = sps.length := by simpa using Hl2.1.symm
    have h622 : sint.Z ssl.len < 2 ^ 62 := by
      have := hslen; have : sint.Z ssl.len = (sint.nat ssl.len : Int) := by word
      omega
    try wp_auto
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl]
    wp_apply wp_pv _ _ ssl.len $$ [Hsl] as %wlen2 ⟨%Hwl2, Hsl⟩
    · iframe Hsl; ipureintro
      refine ⟨by rw [Hal2.1]; decide, Hl2.2, h622⟩
    rw [hn2] at Hwl2
    isimp only [hn2] at Hsl
    have hvl2 := varintLen_length (sps.length) (by have := hslen; omega)
    rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen2 by rw [Hwl2]; exact Int.natCast_nonneg _)]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl2]; exact Int.natCast_nonneg _,
      by rw [Hwl2]; have : sint.Z (W64 10) = 10 := rfl; omega⟩)]
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl,
      show wlen2 - W64 0 = wlen2 by word]
    icases slice_pre b_ptr (W64 10) wlen2 _ ⟨by rw [Hwl2]; exact Int.natCast_nonneg _,
      by rw [Hwl2]; have : sint.Z (W64 10) = 10 := rfl; omega⟩ $$ Hsl with ⟨Hv2, Hback⟩
    have hwn2 : sint.nat wlen2 = (sp.varintLen (sps.length)).length := by
      have : sint.Z wlen2 = (sint.nat wlen2 : Int) := by word
      omega
    rw [hwn2, List.take_left]
    wp_auto
    wp_apply HW $$ HS [] Hv2 as %nn2 %err2 HS Hv2
    · iapply Qp $$ Hpc HQ
      ipureintro
      exact ⟨(sps.map (fun p => p.2.enc)).flatten, by rw [hbody]; simp⟩
    ihave Hsl := Hback $$ %_ Hv2 %(by first | rfl | exact hwn2.symm)
    ihave %Hal2' := ownSlice_len $$ Hsl
    simp only at Hal2'
    ihave HL : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice),
        "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
        "HS" ∷ S (((W ++ sp.varintLen fps.length) ++ (fps.map (fun p => p.2.enc)).flatten ++ sp.varintLen sps.length) ++ ((sps.take k).map (fun p => p.2.enc)).flatten) ∗
        "Hsl" ∷ slice.mk b_ptr (W64 10) (W64 10) ↦* arr ∗
        "Hss" ∷ ssl ↦* sps.map Prod.fst ∗
        "%Hk" ∷ ⌜arr.length = sint.nat (W64 10) ∧ k ≤ sps.length⌝ : IProp netDistGF) $$ [i bs HS Hsl Hss]
    · iexists 0, _, _
      iframe
      isplitl [HS]
      · iExactEq HS; congr 1; simp
      ipureintro; exact ⟨Hal2'.1, by omega⟩
    wp_for HL
    try wp_auto
    wp_if_destruct
    · obtain ⟨hk1, hk2⟩ := Hk
      have Hif : sint.Z (W64 (k : Int)) < sint.Z ssl.len := by
        first | exact Hif | simpa using Hif | exact of_decide_eq_true (IntoValInj.intoVal_inj Hif)
      have hcl : sint.Z ssl.len = sps.length := by
        have : sint.Z ssl.len = (sint.nat ssl.len : Int) := by word
        omega
      have hk64 : sint.Z (W64 (k : Int)) = k := by word
      have hkn : k < sps.length := by omega
      have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
      have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z ssl.len := ⟨hk0, Hif⟩
      obtain ⟨p, hp⟩ : ∃ p, sps[k]? = some p := ⟨_, List.getElem?_eq_getElem hkn⟩
      have hp' : (sps.map Prod.fst)[(sint.Z (W64 (k : Int))).toNat]? = some p.1 := by
        rw [hk64]; simp [hp]
      obtain ⟨hr1, hr2, hr3⟩ := hsr p (List.mem_of_getElem? hp)
      have henc : p.2.enc = (sp.le32 p.1.Replica' ++ sp.le32 p.1.Ballot' ++ sp.le32 p.1.CmdId'.ClientId' ++ sp.le32 p.1.CmdId'.SeqNum') := by
        simp only [sp.SlowAck.enc, sp.encCmdId, ← hr1, ← hr2, ← hr3, swift.toCmdId, List.append_assoc]
      have hsplit : sps = sps.take k ++ p :: sps.drop (k + 1) := by
        have hk' : sps[k] = p := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hp)
        rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
      have htake : ((sps.take (k + 1)).map (fun p => p.2.enc)).flatten = ((sps.take k).map (fun p => p.2.enc)).flatten ++ (sp.le32 p.1.Replica' ++ sp.le32 p.1.Ballot' ++ sp.le32 p.1.CmdId'.ClientId' ++ sp.le32 p.1.CmdId'.SeqNum') := by
        rw [List.take_add_one, hp, ← henc]; simp
      have hpre4 : (((W ++ sp.varintLen fps.length) ++ (fps.map (fun p => p.2.enc)).flatten ++ sp.varintLen sps.length) ++ ((sps.take k).map (fun p => p.2.enc)).flatten) ++ (sp.le32 p.1.Replica' ++ sp.le32 p.1.Ballot' ++ sp.le32 p.1.CmdId'.ClientId' ++ sp.le32 p.1.CmdId'.SeqNum') <+: W ++ (sp.Msg.acks (fps.map Prod.snd) (sps.map Prod.snd)).body := by
        refine ⟨((sps.drop (k + 1)).map (fun p => p.2.enc)).flatten, ?_⟩
        rw [hbody, congrArg (fun l => (List.map (fun p : swift.MLightSlowAck × sp.SlowAck => p.2.enc) l).flatten) hsplit]
        simp [henc]
      generalize hY : ((W ++ sp.varintLen fps.length) ++ (fps.map (fun p => p.2.enc)).flatten ++ sp.varintLen sps.length) ++ ((sps.take k).map (fun p => p.2.enc)).flatten = Y
      rw [hY] at hpre4
      have hpre3 : ((Y ++ sp.le32 p.1.Replica') ++ sp.le32 p.1.Ballot') ++ sp.le32 p.1.CmdId'.ClientId' <+: W ++ (sp.Msg.acks (fps.map Prod.snd) (sps.map Prod.snd)).body :=
        List.IsPrefix.trans ⟨sp.le32 p.1.CmdId'.SeqNum', by simp⟩ hpre4
      have hpre2 : (Y ++ sp.le32 p.1.Replica') ++ sp.le32 p.1.Ballot' <+: W ++ (sp.Msg.acks (fps.map Prod.snd) (sps.map Prod.snd)).body :=
        List.IsPrefix.trans ⟨sp.le32 p.1.CmdId'.ClientId', by simp⟩ hpre3
      have hpre1 : Y ++ sp.le32 p.1.Replica' <+: W ++ (sp.Msg.acks (fps.map Prod.snd) (sps.map Prod.snd)).body :=
        List.IsPrefix.trans ⟨sp.le32 p.1.Ballot', by simp⟩ hpre2
      replace hpre4 : (((Y ++ sp.le32 p.1.Replica') ++ sp.le32 p.1.Ballot') ++ sp.le32 p.1.CmdId'.ClientId') ++ sp.le32 p.1.CmdId'.SeqNum' <+: W ++ (sp.Msg.acks (fps.map Prod.snd) (sps.map Prod.snd)).body := by
        simpa using hpre4
      icases slice_pre b_ptr (W64 10) (W64 4) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
      obtain ⟨lb, hlb', hlb⟩ := take_of_len arr (W64 4) 4 (by rw [hk1]; decide) rfl
      rw [hlb']
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 4 - W64 0 = W64 4 from rfl,
        show W64 10 - W64 0 = W64 10 from rfl]
      icases ownSlice_elem_acc (sint.Z (W64 (k : Int))) p.1 ssl _ _ hk0 hp' $$ Hss with ⟨He, Hss⟩
      ihave %Hen := typedPointsto_not_null $$ He
      icases typedPointsto_split _ _ _ $$ He with He
      simp only [TypedPointsto.typedPointstoDef]
      icases He with ⟨ERep, EBal, ECmd, -⟩
      ihave %Hecn := typedPointsto_not_null $$ ECmd
      icases typedPointsto_split _ _ _ $$ ECmd with ECmd
      simp only [TypedPointsto.typedPointstoDef]
      icases ECmd with ⟨ECl, ESq, -⟩
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
      try wp_auto
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      first | rw [set4 _ (by simp [hlb, sp.le32, u32Le_length]), le32_sbytes] | rw [set4' _ (by simp [hlb, sp.le32, u32Le_length]), le32_sbytes]
      try wp_auto
      wp_apply HW $$ HS [] Hb as %nng1 %errg1 HS Hb
      · iapply Qp $$ Hpc HQ
        ipureintro
        exact hpre1
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
      try wp_auto
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      first | rw [set4 _ (by simp [hlb, sp.le32, u32Le_length]), le32_sbytes] | rw [set4' _ (by simp [hlb, sp.le32, u32Le_length]), le32_sbytes]
      try wp_auto
      wp_apply HW $$ HS [] Hb as %nng2 %errg2 HS Hb
      · iapply Qp $$ Hpc HQ
        ipureintro
        exact hpre2
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
      try wp_auto
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      first | rw [set4 _ (by simp [hlb, sp.le32, u32Le_length]), le32_sbytes] | rw [set4' _ (by simp [hlb, sp.le32, u32Le_length]), le32_sbytes]
      try wp_auto
      wp_apply HW $$ HS [] Hb as %nng3 %errg3 HS Hb
      · iapply Qp $$ Hpc HQ
        ipureintro
        exact hpre3
      try wp_auto
      try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
      try wp_auto
      mstoreb
      mstoreb
      mstoreb
      mstoreb
      first | rw [set4 _ (by simp [hlb, sp.le32, u32Le_length]), le32_sbytes] | rw [set4' _ (by simp [hlb, sp.le32, u32Le_length]), le32_sbytes]
      try wp_auto
      wp_apply HW $$ HS [] Hb as %nng4 %errg4 HS Hb
      · iapply Qp $$ Hpc HQ
        ipureintro
        exact hpre4
      ihave He : typedPointsto (sliceIndexRef swift.MLightSlowAck (sint.Z (W64 (k : Int))) ssl) p.1 (DFrac.own 1) $$ [ERep EBal ECl ESq]
      · iapply typedPointsto_combine _ _ _ Hen
        simp only [TypedPointsto.typedPointstoDef]
        iframe
        isplitl [ECl ESq]
        · iapply typedPointsto_combine _ _ _ Hecn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        · iNamed
          ipureintro; trivial
      ihave Hss := Hss $$ He
      rw [list_set_lookup_self _ _ _ hp']
      ihave Hsl := Hback $$ %_ Hb %(by simp [sp.le32, u32Le_length]; rfl)
      try wp_auto
      wp_for_post
      iframe
      rw [hkk]
      iexists k + 1, _, _
      iframe
      isplitl [HS]
      · iExactEq HS; congr 1; rw [htake, ← hY]; simp
      ipureintro
      exact ⟨len_restore _ _ _ _ (by simp [sp.le32, u32Le_length]; rfl) hk1 (by decide), by omega⟩
    · obtain ⟨hk1, hk2⟩ := Hk
      have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z ssl.len := by
        first
        | exact Hif
        | simpa using Hif
        | exact fun h => Hif (by rw [decide_eq_true h])
        | exact of_decide_eq_false (IntoValInj.intoVal_inj Hif)
      have hkn : k = sps.length := by
        have : sint.Z (W64 (k : Int)) = k := by word
        have : sint.Z ssl.len = (sint.nat ssl.len : Int) := by word
        omega
      subst hkn
      rw [List.take_length]
      iapply HΦ
      isplitl [HS]
      · iExactEq HS; rw [hbody]; simp
      iframe


/-- **`swift.MOptAcks.marshalH`**, over `PutVarint`'s hypothesis. -/
theorem swift.MOptAcks.marshal_proof (wp_pv : swift.PutVarint.specH (hG := hG)) :
    swift.MOptAcks.marshalH (hG := hG) := by
  intro l r b asl ps hwf
  unfold sp.marshalOk
  iexists ⟨go.GoType.PointerType swift.MOptAcks.ty, #l⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %wr %S %Q %W %Φ ⟨Hl, Has, #Hreps⟩ #Hsink HS #Hpc #HQ HΦ
  wp_apply swift.MOptAcks.Marshal.wp wp_pv l r b asl ps hwf wr S Q W $$
    [$Hsink $HS $Hpc $HQ $Hl $Has $Hreps] as ⟨HS, Hl, Has⟩
  iapply HΦ $$ [$Hl $Has $Hreps] HS

/-- **`swift.MAcks.marshalH`**, over `PutVarint`'s hypothesis. -/
theorem swift.MAcks.marshal_proof (wp_pv : swift.PutVarint.specH (hG := hG)) :
    swift.MAcks.marshalH (hG := hG) := by
  intro l fsl ssl fps sps hwf hsr
  unfold sp.marshalOk
  iexists ⟨go.GoType.PointerType swift.MAcks.ty, #l⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %wr %S %Q %W %Φ ⟨#Hl, Hfs, Hss, #Hreps⟩ #Hsink HS #Hpc #HQ HΦ
  wp_apply swift.MAcks.Marshal.wp wp_pv l fsl ssl fps sps hwf hsr wr S Q W $$
    [$Hsink $HS $Hpc $HQ $Hl $Hfs $Hss $Hreps] as ⟨HS, Hfs, Hss⟩
  iapply HΦ $$ [$Hl $Hfs $Hss $Hreps] HS

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
