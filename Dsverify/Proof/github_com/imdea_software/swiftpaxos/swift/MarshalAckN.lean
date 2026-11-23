/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/MarshalAckN.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift messages' writers, part 5 (round N3, sv-swc): `(*SDep).Marshal` and
`(*MNewLeaderAckN).Marshal` (`swift.MNewLeaderAckN.marshalH`, Proof/swift/NewLeaderSpecs.lean),
over the `PutVarint` hypothesis (Proof/swift/MarshalSpecs.lean; proved, Proof/swift/PutVarint.lean).
The ack's four lists: the ids and the phases inline, the commands through `state.Command`'s
`Marshal` (`wp_Command_Marshal`), the dependencies through `(*SDep).Marshal`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalAcks
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewLeaderSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv wire

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

theorem set12 {A : Type} (l : List A) (hl : l.length = 12)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : A) :
    ((((((((((((l.set (Int.toNat 0) a0).set 1 a1).set 2 a2).set 3 a3).set 4 a4).set 5 a5).set 6
      a6).set 7 a7).set 8 a8).set 9 a9).set 10 a10).set 11 a11) =
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] := by
  match l, hl with
  | [_, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

theorem le32x3_sbytes (x y z : w32) :
    [W8 (sint.Z x), W8 (sint.Z (BitVec.sshiftRight' x (W64 8))),
      W8 (sint.Z (BitVec.sshiftRight' x (W64 16))), W8 (sint.Z (BitVec.sshiftRight' x (W64 24))),
      W8 (sint.Z y), W8 (sint.Z (BitVec.sshiftRight' y (W64 8))),
      W8 (sint.Z (BitVec.sshiftRight' y (W64 16))), W8 (sint.Z (BitVec.sshiftRight' y (W64 24))),
      W8 (sint.Z z), W8 (sint.Z (BitVec.sshiftRight' z (W64 8))),
      W8 (sint.Z (BitVec.sshiftRight' z (W64 16))), W8 (sint.Z (BitVec.sshiftRight' z (W64 24)))] =
      sp.le32 x ++ sp.le32 y ++ sp.le32 z := by
  rw [← le32_sbytes, ← le32_sbytes, ← le32_sbytes]; rfl

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

set_option goose.wp.extras true

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `(*SDep).Marshal(wire)`: `encDep` of its dependencies. -/
theorem swift.SDep.Marshal.wp (wp_pv : swift.PutVarint.specH (hG := hG))
    (t : Loc) (dq : DFrac) (sd : swift.SDep) (D : List sp.CmdId) (hwf : D.length < 2 ^ 62)
    (wr : GoInterface) (S Q : List w8 → IProp netDistGF) (W : List w8) :
    {{ sinkOk wr S Q ∗ S W ∗ bufio.prefixClosed Q ∗ □ Q (W ++ sp.encDep D) ∗ t ↦{dq} sd ∗
        sd.Dep' ↦*□ (D.map ofCmdId) }}
      (App (Val (t @!! go.GoType.PointerType swift.SDep.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ sp.encDep D) ∗ t ↦{dq} sd }} := by
  wp_start as ⟨#Hsink, HS, #Hpc, #HQ, Ht, #HD⟩
  have hbody : W ++ sp.encDep D = W ++ (sp.varintLen D.length ++ (D.map sp.encCmdId).flatten) := by
    simp only [sp.encDep]
  ihave %Htn := typedPointsto_not_null $$ Ht
  icases typedPointsto_split _ _ _ $$ Ht with Ht
  simp only [TypedPointsto.typedPointstoDef]
  icases Ht with ⟨Dep, -⟩
  wp_auto
  ihave Hsl := slice_array b_ptr 10 (Perennial.zero_val (GoArray w8 10)) (by decide) $$ b
  rw [show (Perennial.zero_val (GoArray w8 10)).arr = List.replicate 10 (W8 0) from rfl]
  iunfold sinkOk at Hsink
  icases Hsink with ⟨%e, %He, #HW⟩
  subst He
  ihave %Hl1 := ownSlice_len $$ HD
  have hn1 : sint.nat sd.Dep'.len = D.length := by simpa using Hl1.1.symm
  have h621 : sint.Z sd.Dep'.len < 2 ^ 62 := by
    have : sint.Z sd.Dep'.len = (sint.nat sd.Dep'.len : Int) := by word
    omega
  try wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl]
  wp_apply wp_pv _ _ sd.Dep'.len $$ [Hsl] as %wlen1 ⟨%Hwl1, Hsl⟩
  · iframe Hsl; ipureintro
    refine ⟨by simp, Hl1.2, h621⟩
  rw [hn1] at Hwl1
  isimp only [hn1] at Hsl
  have hvl1 := varintLen_length (D.length) (by omega)
  rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen1 by rw [Hwl1]; exact Int.natCast_nonneg _)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 10) = 10 := rfl; omega⟩)]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 10 - W64 0 = W64 10 from rfl,
    show wlen1 - W64 0 = wlen1 by word]
  icases slice_pre b_ptr (W64 10) wlen1 _ ⟨by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 10) = 10 := rfl; omega⟩ $$ Hsl with ⟨Hv1, Hback⟩
  have hwn1 : sint.nat wlen1 = (sp.varintLen (D.length)).length := by
    have : sint.Z wlen1 = (sint.nat wlen1 : Int) := by word
    omega
  rw [hwn1, List.take_left]
  wp_auto
  wp_apply HW $$ HS [] Hv1 as %nn1 %err1 HS Hv1
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨(D.map sp.encCmdId).flatten, by rw [hbody]; simp⟩
  ihave Hsl := Hback $$ %_ Hv1 %(by first | rfl | exact hwn1.symm)
  ihave %Hal1' := ownSlice_len $$ Hsl
  simp only at Hal1'
  ihave HL : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice),
      "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
      "HS" ∷ S ((W ++ sp.varintLen D.length) ++ ((D.take k).map sp.encCmdId).flatten) ∗
      "Hsl" ∷ slice.mk b_ptr (W64 10) (W64 10) ↦* arr ∗
      "%Hk" ∷ ⌜arr.length = sint.nat (W64 10) ∧ k ≤ D.length⌝ : IProp netDistGF) $$ [i bs HS Hsl]
  · iexists 0, _, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; simp
    ipureintro; exact ⟨Hal1'.1, by omega⟩
  wp_for HL
  try wp_auto
  wp_if_destruct
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : sint.Z (W64 (k : Int)) < sint.Z sd.Dep'.len := by
      first | exact Hif | simpa using Hif
    have hcl : sint.Z sd.Dep'.len = D.length := by
      have : sint.Z sd.Dep'.len = (sint.nat sd.Dep'.len : Int) := by word
      omega
    have hk64 : sint.Z (W64 (k : Int)) = k := by word
    have hkn : k < D.length := by omega
    have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
    have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z sd.Dep'.len := ⟨hk0, Hif⟩
    obtain ⟨d, hd⟩ : ∃ d, D[k]? = some d := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hd' : (D.map swift.ofCmdId)[(sint.Z (W64 (k : Int))).toNat]? = some (swift.ofCmdId d) := by
      rw [hk64]; simp [hd]
    have htake : ((D.take (k + 1)).map sp.encCmdId).flatten = ((D.take k).map sp.encCmdId).flatten ++ (sp.le32 d.cl ++ sp.le32 d.seq) := by
      rw [List.take_add_one, hd]; simp [sp.encCmdId]
    have hsplit : D = D.take k ++ d :: D.drop (k + 1) := by
      have hk' : D[k] = d := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hd)
      rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
    have hflat : (D.map sp.encCmdId).flatten =
        ((D.take k).map sp.encCmdId).flatten ++ (sp.le32 d.cl ++ sp.le32 d.seq) ++ ((D.drop (k + 1)).map sp.encCmdId).flatten := by
      rw [congrArg (fun l => (List.map sp.encCmdId l).flatten) hsplit]
      simp [sp.encCmdId]
    have hp2 : ((W ++ sp.varintLen D.length) ++ ((D.take k).map sp.encCmdId).flatten) ++ (sp.le32 d.cl ++ sp.le32 d.seq) <+: W ++ sp.encDep D := by
      refine ⟨((D.drop (k + 1)).map sp.encCmdId).flatten, ?_⟩
      rw [hbody, hflat]; simp
    generalize hY : (W ++ sp.varintLen D.length) ++ ((D.take k).map sp.encCmdId).flatten = Y
    rw [hY] at hp2
    have hp1 : Y ++ sp.le32 d.cl <+: W ++ sp.encDep D :=
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
    iexists k + 1, _, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; rw [htake, ← hY]; simp
    ipureintro
    exact ⟨len_restore _ _ _ _ (by simp [sp.le32, u32Le_length]; rfl) hk1 (by decide), by omega⟩
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z sd.Dep'.len := by
      first
      | exact Hif
      | simpa using Hif
      | exact fun h => Hif (by rw [decide_eq_true h])
    have hkn : k = D.length := by
      have : sint.Z (W64 (k : Int)) = k := by word
      have : sint.Z sd.Dep'.len = (sint.nat sd.Dep'.len : Int) := by word
      omega
    subst hkn
    rw [List.take_length]
    try rw [if_pos (by simp [Hif])]
    try wp_auto
    iapply HΦ
    isplitl [HS]
    · iExactEq HS; rw [hbody]; simp
    iapply typedPointsto_combine _ _ _ Htn
    simp only [TypedPointsto.typedPointstoDef]
    iframe


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `(*MNewLeaderAckN).Marshal(wire)`: `.newLeaderAckN`'s body. The ack is read-only (`ackObj`):
its ids, phases, commands (`state.Command`'s `Marshal`) and dependencies (`(*SDep).Marshal`). -/
theorem swift.MNewLeaderAckN.Marshal.wp (wp_pv : swift.PutVarint.specH (hG := hG))
    (t : Loc) (rep bl cb : w32) (ids ph cm dp : GoSlice) (es : List sp.RepEntry)
    (cmL : List state.Command) (dpL : List swift.SDep)
    (hwf : sp.Msg.wf (.newLeaderAckN rep bl cb es))
    (hcl : cmL.length = es.length) (hdl : dpL.length = es.length)
    (wr : GoInterface) (S Q : List w8 → IProp netDistGF) (W : List w8) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.binary ∗
        sinkOk wr S Q ∗ S W ∗ bufio.prefixClosed Q ∗
        □ Q (W ++ (sp.Msg.newLeaderAckN rep bl cb es).body) ∗
        t ↦□ swift.MNewLeaderAckN.mk rep bl cb ids ph cm dp ∗
        ids ↦*□ (es.map (fun e => ofCmdId e.id)) ∗ ph ↦*□ (es.map (·.phase)) ∗
        cm ↦*□ cmL ∗ dp ↦*□ dpL ∗
        □ ([∗list] i ↦ e ∈ es, ∃ (c : state.Command) (sd : swift.SDep),
          ⌜cmL[i]? = some c ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj c sd e) }}
      (App (Val (t @!! go.GoType.PointerType swift.MNewLeaderAckN.ty @!! go!"Marshal")) (Val #wr))
    {{ RET #(); S (W ++ (sp.Msg.newLeaderAckN rep bl cb es).body) }} := by
  wp_start as ⟨#Hsink, HS, #Hpc, #HQ, #Ht, #HI, #HP, #HC, #HDp, #Hents⟩
  obtain ⟨hlen, hwfe⟩ := hwf
  have hbody : W ++ (sp.Msg.newLeaderAckN rep bl cb es).body = W ++
      (sp.le32 rep ++ sp.le32 bl ++ sp.le32 cb ++
        sp.varintLen es.length ++ (es.map (fun e => sp.encCmdId e.id)).flatten ++
        sp.varintLen es.length ++ (es.map (fun e => sp.le64 e.phase)).flatten ++
        sp.varintLen es.length ++ (es.map (fun e => sp.encCmd e.cmd)).flatten ++
        sp.varintLen es.length ++ (es.map (fun e => sp.encDep e.dep)).flatten) := by
    simp only [sp.Msg.body, sp.RepEntry.encCmds, List.append_assoc]
  icases typedPointsto_split _ _ _ $$ Ht with Ht2
  simp only [TypedPointsto.typedPointstoDef]
  icases Ht2 with ⟨#Replica, #Ballot, #Cballot, #CmdIds, #Phases, #Cmds, #Deps, -⟩
  ihave #Hsink0 := Hsink
  iunfold sinkOk at Hsink
  icases Hsink with ⟨%e, %He, #HW⟩
  subst He
  wp_auto
  -- the 12 bytes of `Replica`, `Ballot`, `Cballot`
  ihave Hsl := slice_array b_ptr 12 (Perennial.zero_val (GoArray w8 12)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 12)).arr = List.replicate 12 (W8 0) from rfl]
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
  rw [set12 _ (by simp), le32x3_sbytes]
  try wp_auto
  wp_apply HW $$ HS [] Hsl as %nn0 %err0 HS Hsl
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨_, by rw [hbody]; simp only [List.append_assoc]; rfl⟩
  ihave %Hal0 := ownSlice_len $$ Hsl
  simp only at Hal0
  -- the ids
  ihave %Hl1 := ownSlice_len $$ HI
  have hn1 : sint.nat ids.len = es.length := by simpa using Hl1.1.symm
  have h621 : sint.Z ids.len < 2 ^ 62 := by
    have : sint.Z ids.len = (sint.nat ids.len : Int) := by word
    omega
  try wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl]
  wp_apply wp_pv _ _ ids.len $$ [Hsl] as %wlen1 ⟨%Hwl1, Hsl⟩
  · iframe Hsl; ipureintro
    refine ⟨by rw [Hal0.1]; decide, Hl1.2, h621⟩
  rw [hn1] at Hwl1
  isimp only [hn1] at Hsl
  have hvl1 := varintLen_length (es.length) (by omega)
  rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen1 by rw [Hwl1]; exact Int.natCast_nonneg _)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 12) = 12 := rfl; omega⟩)]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl,
    show wlen1 - W64 0 = wlen1 by word]
  icases slice_pre b_ptr (W64 12) wlen1 _ ⟨by rw [Hwl1]; exact Int.natCast_nonneg _,
    by rw [Hwl1]; have : sint.Z (W64 12) = 12 := rfl; omega⟩ $$ Hsl with ⟨Hv1, Hback⟩
  have hwn1 : sint.nat wlen1 = (sp.varintLen (es.length)).length := by
    have : sint.Z wlen1 = (sint.nat wlen1 : Int) := by word
    omega
  rw [hwn1, List.take_left]
  wp_auto
  wp_apply HW $$ HS [] Hv1 as %nn1 %err1 HS Hv1
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨_, by rw [hbody]; simp only [List.append_assoc]; rfl⟩
  ihave Hsl := Hback $$ %_ Hv1 %(by first | rfl | exact hwn1.symm)
  ihave %Hal1' := ownSlice_len $$ Hsl
  simp only at Hal1'
  ihave HL : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice) (tv : w32),
      "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗ "tmp32" ∷ tmp32_ptr ↦ tv ∗
      "HS" ∷ S ((W ++ (sp.le32 rep ++ sp.le32 bl ++ sp.le32 cb) ++ sp.varintLen es.length) ++
        ((es.take k).map (fun e => sp.encCmdId e.id)).flatten) ∗
      "Hsl" ∷ slice.mk b_ptr (W64 12) (W64 12) ↦* arr ∗
      "%Hk" ∷ ⌜arr.length = sint.nat (W64 12) ∧ k ≤ es.length⌝ : IProp netDistGF)
    $$ [i bs tmp32 HS Hsl]
  · iexists 0, _, _, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; simp
    ipureintro; exact ⟨Hal1'.1, by omega⟩
  wp_for HL
  try wp_auto
  wp_if_destruct
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : sint.Z (W64 (k : Int)) < sint.Z ids.len := by
      first | exact Hif | simpa using Hif | exact of_decide_eq_true (go.IntoValInj.intoVal_inj Hif)
    have hcl' : sint.Z ids.len = es.length := by
      have : sint.Z ids.len = (sint.nat ids.len : Int) := by word
      omega
    have hk64 : sint.Z (W64 (k : Int)) = k := by word
    have hkn : k < es.length := by omega
    have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
    have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z ids.len := ⟨hk0, Hif⟩
    obtain ⟨en, hen⟩ : ∃ en, es[k]? = some en := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hd' : (es.map (fun e => ofCmdId e.id))[(sint.Z (W64 (k : Int))).toNat]? =
        some (ofCmdId en.id) := by
      rw [hk64]; simp [hen]
    have hd := en.id
    have htake : ((es.take (k + 1)).map (fun e => sp.encCmdId e.id)).flatten =
        ((es.take k).map (fun e => sp.encCmdId e.id)).flatten ++
          (sp.le32 en.id.cl ++ sp.le32 en.id.seq) := by
      rw [List.take_add_one, hen]; simp [sp.encCmdId]
    have hsplit : es = es.take k ++ en :: es.drop (k + 1) := by
      have hk' : es[k] = en := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hen)
      rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
    have hflat : (es.map (fun e => sp.encCmdId e.id)).flatten =
        ((es.take k).map (fun e => sp.encCmdId e.id)).flatten ++
          (sp.le32 en.id.cl ++ sp.le32 en.id.seq) ++
          ((es.drop (k + 1)).map (fun e => sp.encCmdId e.id)).flatten := by
      rw [congrArg (fun l => (List.map (fun e : sp.RepEntry => sp.encCmdId e.id) l).flatten) hsplit]
      simp [sp.encCmdId]
    have hp2 : ((W ++ (sp.le32 rep ++ sp.le32 bl ++ sp.le32 cb) ++ sp.varintLen es.length) ++
        ((es.take k).map (fun e => sp.encCmdId e.id)).flatten) ++
          (sp.le32 en.id.cl ++ sp.le32 en.id.seq) <+:
        W ++ (sp.Msg.newLeaderAckN rep bl cb es).body := by
      exact ⟨_, by rw [hbody, hflat]; simp only [List.append_assoc]; rfl⟩
    generalize hY : (W ++ (sp.le32 rep ++ sp.le32 bl ++ sp.le32 cb) ++ sp.varintLen es.length) ++
      ((es.take k).map (fun e => sp.encCmdId e.id)).flatten = Y
    rw [hY] at hp2
    have hp1 : Y ++ sp.le32 en.id.cl <+: W ++ (sp.Msg.newLeaderAckN rep bl cb es).body :=
      List.IsPrefix.trans ⟨sp.le32 en.id.seq, by simp⟩ hp2
    icases slice_pre b_ptr (W64 12) (W64 4) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
    obtain ⟨lb, hlb', hlb⟩ := take_of_len arr (W64 4) 4 (by rw [hk1]; decide) rfl
    rw [hlb']
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 4 - W64 0 = W64 4 from rfl,
      show W64 12 - W64 0 = W64 12 from rfl]
    try wp_auto
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
    try wp_auto
    wp_apply wp_load_cl _ _ _ _ _ hk0 hd' $$ [HI] as -
    · iexact HI
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
    wp_apply wp_load_seq _ _ _ _ _ hk0 hd' $$ [HI] as -
    · iexact HI
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
    · iExactEq HS; congr 1; rw [htake, ← hY]; simp
    ipureintro
    exact ⟨len_restore _ _ _ _ (by simp [sp.le32, u32Le_length]; rfl) hk1 (by decide), by omega⟩
  obtain ⟨hk1, hk2⟩ := Hk
  have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z ids.len := by
    first
    | exact Hif
    | simpa using Hif
    | exact fun h => Hif (by rw [decide_eq_true h])
    | exact of_decide_eq_false (go.IntoValInj.intoVal_inj Hif)
  have hkn : k = es.length := by
    have : sint.Z (W64 (k : Int)) = k := by word
    have : sint.Z ids.len = (sint.nat ids.len : Int) := by word
    omega
  subst hkn
  rw [List.take_length]
  try rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [decide_eq_false Hif]))]
  try wp_auto
  ihave %HalP2 := ownSlice_len $$ Hsl
  simp only at HalP2
  ihave %Hl2 := ownSlice_len $$ HP
  have hn2 : sint.nat ph.len = es.length := by simpa using Hl2.1.symm
  have h622 : sint.Z ph.len < 2 ^ 62 := by
    have : sint.Z ph.len = (sint.nat ph.len : Int) := by word
    omega
  try wp_auto
  try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl]
  wp_apply wp_pv _ _ ph.len $$ [Hsl] as %wlen2 ⟨%Hwl2, Hsl⟩
  · iframe Hsl; ipureintro
    refine ⟨by rw [HalP2.1]; decide, Hl2.2, h622⟩
  rw [hn2] at Hwl2
  isimp only [hn2] at Hsl
  rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen2 by rw [Hwl2]; exact Int.natCast_nonneg _)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl2]; exact Int.natCast_nonneg _,
    by rw [Hwl2]; have : sint.Z (W64 12) = 12 := rfl; omega⟩)]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl,
    show wlen2 - W64 0 = wlen2 by word]
  icases slice_pre b_ptr (W64 12) wlen2 _ ⟨by rw [Hwl2]; exact Int.natCast_nonneg _,
    by rw [Hwl2]; have : sint.Z (W64 12) = 12 := rfl; omega⟩ $$ Hsl with ⟨Hv2, Hback⟩
  have hwn2 : sint.nat wlen2 = (sp.varintLen (es.length)).length := by
    have : sint.Z wlen2 = (sint.nat wlen2 : Int) := by word
    omega
  rw [hwn2, List.take_left]
  wp_auto
  wp_apply HW $$ HS [] Hv2 as %nnv2 %errv2 HS Hv2
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨_, by rw [hbody]; simp only [List.append_assoc]; rfl⟩
  ihave Hsl := Hback $$ %_ Hv2 %(by first | rfl | exact hwn2.symm)
  ihave %Hal2' := ownSlice_len $$ Hsl
  simp only at Hal2'
  ihave HL2 : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice),
      "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
      "HS" ∷ S (((((W ++ (sp.le32 rep ++ sp.le32 bl ++ sp.le32 cb)) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.encCmdId e.id)).flatten) ++ sp.varintLen es.length) ++ ((es.take k).map (fun e => sp.le64 e.phase)).flatten) ∗
      "Hsl" ∷ slice.mk b_ptr (W64 12) (W64 12) ↦* arr ∗
      "%Hk" ∷ ⌜arr.length = sint.nat (W64 12) ∧ k ≤ es.length⌝ : IProp netDistGF)
    $$ [i bs HS Hsl]
  · iexists 0, _, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; simp
    ipureintro; exact ⟨Hal2'.1, by omega⟩
  wp_for HL2
  try wp_auto
  wp_if_destruct
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : sint.Z (W64 (k : Int)) < sint.Z ph.len := by
      first | exact Hif | simpa using Hif | exact of_decide_eq_true (go.IntoValInj.intoVal_inj Hif)
    have hcl' : sint.Z ph.len = es.length := by
      have : sint.Z ph.len = (sint.nat ph.len : Int) := by word
      omega
    have hk64 : sint.Z (W64 (k : Int)) = k := by word
    have hkn : k < es.length := by omega
    have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
    have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z ph.len := ⟨hk0, Hif⟩
    obtain ⟨en, hen⟩ : ∃ en, es[k]? = some en := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hsplit : es = es.take k ++ en :: es.drop (k + 1) := by
      have hk' : es[k] = en := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hen)
      rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
    have htake : ((es.take (k + 1)).map (fun e => sp.le64 e.phase)).flatten =
        ((es.take k).map (fun e => sp.le64 e.phase)).flatten ++ (fun e => sp.le64 e.phase) en := by
      rw [List.take_add_one, hen]; simp
    have hflat : (es.map (fun e => sp.le64 e.phase)).flatten =
        ((es.take k).map (fun e => sp.le64 e.phase)).flatten ++ (fun e => sp.le64 e.phase) en ++
          ((es.drop (k + 1)).map (fun e => sp.le64 e.phase)).flatten := by
      rw [congrArg (fun l => (List.map (fun e => sp.le64 e.phase) l).flatten) hsplit]
      simp
    have hp : (((((W ++ (sp.le32 rep ++ sp.le32 bl ++ sp.le32 cb)) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.encCmdId e.id)).flatten) ++ sp.varintLen es.length) ++ ((es.take k).map (fun e => sp.le64 e.phase)).flatten) ++ (fun e => sp.le64 e.phase) en <+:
        W ++ (sp.Msg.newLeaderAckN rep bl cb es).body :=
      ⟨_, by rw [hbody, hflat]; simp only [List.append_assoc]; rfl⟩
    have hd' : (es.map (·.phase))[(sint.Z (W64 (k : Int))).toNat]? = some en.phase := by
      rw [hk64]; simp [hen]
    icases slice_pre b_ptr (W64 12) (W64 8) arr ⟨by decide, by decide⟩ $$ Hsl with ⟨Hb, Hback⟩
    obtain ⟨lb, hlb', hlb⟩ := take_of_len arr (W64 8) 8 (by rw [hk1]; decide) rfl
    rw [hlb']
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl,
      show W64 12 - W64 0 = W64 12 from rfl]
    try wp_auto
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
    try wp_auto
    wp_apply (wp_load_slice_index (V := w64) ph (sint.Z (W64 (k : Int))) _ DFrac.discard en.phase hk0)
      $$ [HP] as -
    · iframe HP; ipureintro; exact hd'
    try wp_auto
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
    wp_apply HW $$ HS [] Hb as %nn1 %err1 HS Hb
    · iapply Qp $$ Hpc HQ
      ipureintro
      exact hp
    ihave Hsl := Hback $$ %_ Hb %(by simp [sp.le64, u64Le_length]; rfl)
    wp_for_post
    iframe
    rw [hkk]
    iexists k + 1, _, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; rw [htake]; simp
    ipureintro
    exact ⟨len_restore _ _ _ _ (by simp [sp.le64, u64Le_length]; rfl) hk1 (by decide), by omega⟩
  obtain ⟨hk1, hk2⟩ := Hk
  have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z ph.len := by
    first
    | exact Hif
    | simpa using Hif
    | exact fun h => Hif (by rw [decide_eq_true h])
    | exact of_decide_eq_false (go.IntoValInj.intoVal_inj Hif)
  have hkn : k = es.length := by
    have : sint.Z (W64 (k : Int)) = k := by word
    have : sint.Z ph.len = (sint.nat ph.len : Int) := by word
    omega
  subst hkn
  rw [List.take_length]
  try rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [decide_eq_false Hif]))]
  try wp_auto
  ihave %HalP3 := ownSlice_len $$ Hsl
  simp only at HalP3
  ihave %Hl3 := ownSlice_len $$ HC
  have hn3 : sint.nat cm.len = es.length := by rw [← hcl]; simpa using Hl3.1.symm
  have h623 : sint.Z cm.len < 2 ^ 62 := by
    have : sint.Z cm.len = (sint.nat cm.len : Int) := by word
    omega
  try wp_auto
  try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl]
  wp_apply wp_pv _ _ cm.len $$ [Hsl] as %wlen3 ⟨%Hwl3, Hsl⟩
  · iframe Hsl; ipureintro
    refine ⟨by rw [HalP3.1]; decide, Hl3.2, h623⟩
  rw [hn3] at Hwl3
  isimp only [hn3] at Hsl
  rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen3 by rw [Hwl3]; exact Int.natCast_nonneg _)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl3]; exact Int.natCast_nonneg _,
    by rw [Hwl3]; have : sint.Z (W64 12) = 12 := rfl; omega⟩)]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl,
    show wlen3 - W64 0 = wlen3 by word]
  icases slice_pre b_ptr (W64 12) wlen3 _ ⟨by rw [Hwl3]; exact Int.natCast_nonneg _,
    by rw [Hwl3]; have : sint.Z (W64 12) = 12 := rfl; omega⟩ $$ Hsl with ⟨Hv3, Hback⟩
  have hwn3 : sint.nat wlen3 = (sp.varintLen (es.length)).length := by
    have : sint.Z wlen3 = (sint.nat wlen3 : Int) := by word
    omega
  rw [hwn3, List.take_left]
  wp_auto
  wp_apply HW $$ HS [] Hv3 as %nnv3 %errv3 HS Hv3
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨_, by rw [hbody]; simp only [List.append_assoc]; rfl⟩
  ihave Hsl := Hback $$ %_ Hv3 %(by first | rfl | exact hwn3.symm)
  ihave %Hal3' := ownSlice_len $$ Hsl
  simp only at Hal3'
  ihave HL3 : (∃ (k : Nat) (arr : List w8) (bsv : GoSlice),
      "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
      "HS" ∷ S (((((((W ++ (sp.le32 rep ++ sp.le32 bl ++ sp.le32 cb)) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.encCmdId e.id)).flatten) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.le64 e.phase)).flatten) ++ sp.varintLen es.length) ++ ((es.take k).map (fun e => sp.encCmd e.cmd)).flatten) ∗
      "Hsl" ∷ slice.mk b_ptr (W64 12) (W64 12) ↦* arr ∗
      "%Hk" ∷ ⌜arr.length = sint.nat (W64 12) ∧ k ≤ es.length⌝ : IProp netDistGF)
    $$ [i bs HS Hsl]
  · iexists 0, _, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; simp
    ipureintro; exact ⟨Hal3'.1, by omega⟩
  wp_for HL3
  try wp_auto
  wp_if_destruct
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : sint.Z (W64 (k : Int)) < sint.Z cm.len := by
      first | exact Hif | simpa using Hif | exact of_decide_eq_true (go.IntoValInj.intoVal_inj Hif)
    have hcl' : sint.Z cm.len = es.length := by
      have : sint.Z cm.len = (sint.nat cm.len : Int) := by word
      omega
    have hk64 : sint.Z (W64 (k : Int)) = k := by word
    have hkn : k < es.length := by omega
    have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
    have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z cm.len := ⟨hk0, Hif⟩
    obtain ⟨en, hen⟩ : ∃ en, es[k]? = some en := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hsplit : es = es.take k ++ en :: es.drop (k + 1) := by
      have hk' : es[k] = en := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hen)
      rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
    have htake : ((es.take (k + 1)).map (fun e => sp.encCmd e.cmd)).flatten =
        ((es.take k).map (fun e => sp.encCmd e.cmd)).flatten ++ (fun e => sp.encCmd e.cmd) en := by
      rw [List.take_add_one, hen]; simp
    have hflat : (es.map (fun e => sp.encCmd e.cmd)).flatten =
        ((es.take k).map (fun e => sp.encCmd e.cmd)).flatten ++ (fun e => sp.encCmd e.cmd) en ++
          ((es.drop (k + 1)).map (fun e => sp.encCmd e.cmd)).flatten := by
      rw [congrArg (fun l => (List.map (fun e => sp.encCmd e.cmd) l).flatten) hsplit]
      simp
    have hp : (((((((W ++ (sp.le32 rep ++ sp.le32 bl ++ sp.le32 cb)) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.encCmdId e.id)).flatten) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.le64 e.phase)).flatten) ++ sp.varintLen es.length) ++ ((es.take k).map (fun e => sp.encCmd e.cmd)).flatten) ++ (fun e => sp.encCmd e.cmd) en <+:
        W ++ (sp.Msg.newLeaderAckN rep bl cb es).body :=
      ⟨_, by rw [hbody, hflat]; simp only [List.append_assoc]; rfl⟩
    ihave ⟨%c, %sd, %Hcs, #Hro⟩ := BigSepL.bigSepL_lookup (Φ := fun i e => iprop(∃ (c : state.Command)
        (sd : swift.SDep), ⌜cmL[i]? = some c ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj c sd e)) hen
      $$ Hents
    obtain ⟨hc, -⟩ := Hcs
    iunfold swift.repEntryObj at Hro
    icases Hro with ⟨%vs, %Hcm, #Hvs, -⟩
    subst Hcm
    have hc' : cmL[(sint.Z (W64 (k : Int))).toNat]? =
        some (state.Command.mk en.cmd.op en.cmd.key vs) := by
      rw [hk64]; exact hc
    try wp_auto
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
    try wp_auto
    icases ownSlice_elem_acc (sint.Z (W64 (k : Int))) _ cm _ _ hk0 hc' $$ HC with ⟨#He, -⟩
    wp_apply wp_Command_Marshal _ _ _ en.cmd _ S Q _ $$ [HS] as ⟨HS, -⟩
    · isplitl []
      · iexact Hsink0
      isplitl [HS]
      · iexact HS
      isplitl []
      · iexact Hpc
      isplitl []
      · iapply Qp $$ Hpc HQ
        ipureintro
        exact hp
      isplitl []
      · iexact He
      isplitl []
      · iexact Hvs
      ipureintro; exact ⟨rfl, rfl⟩
    try wp_auto
    wp_for_post
    iframe
    rw [hkk]
    iexists k + 1, _, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; rw [htake]; simp
    ipureintro
    exact ⟨hk1, by omega⟩
  obtain ⟨hk1, hk2⟩ := Hk
  have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z cm.len := by
    first
    | exact Hif
    | simpa using Hif
    | exact fun h => Hif (by rw [decide_eq_true h])
    | exact of_decide_eq_false (go.IntoValInj.intoVal_inj Hif)
  have hkn : k = es.length := by
    have : sint.Z (W64 (k : Int)) = k := by word
    have : sint.Z cm.len = (sint.nat cm.len : Int) := by word
    omega
  subst hkn
  rw [List.take_length]
  try rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [decide_eq_false Hif]))]
  try wp_auto
  ihave %HalP4 := ownSlice_len $$ Hsl
  simp only at HalP4
  ihave %Hl4 := ownSlice_len $$ HDp
  have hn4 : sint.nat dp.len = es.length := by rw [← hdl]; simpa using Hl4.1.symm
  have h624 : sint.Z dp.len < 2 ^ 62 := by
    have : sint.Z dp.len = (sint.nat dp.len : Int) := by word
    omega
  try wp_auto
  try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl]
  wp_apply wp_pv _ _ dp.len $$ [Hsl] as %wlen4 ⟨%Hwl4, Hsl⟩
  · iframe Hsl; ipureintro
    refine ⟨by rw [HalP4.1]; decide, Hl4.2, h624⟩
  rw [hn4] at Hwl4
  isimp only [hn4] at Hsl
  rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z wlen4 by rw [Hwl4]; exact Int.natCast_nonneg _)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [Hwl4]; exact Int.natCast_nonneg _,
    by rw [Hwl4]; have : sint.Z (W64 12) = 12 := rfl; omega⟩)]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl,
    show wlen4 - W64 0 = wlen4 by word]
  icases slice_pre b_ptr (W64 12) wlen4 _ ⟨by rw [Hwl4]; exact Int.natCast_nonneg _,
    by rw [Hwl4]; have : sint.Z (W64 12) = 12 := rfl; omega⟩ $$ Hsl with ⟨Hv4, Hback⟩
  have hwn4 : sint.nat wlen4 = (sp.varintLen (es.length)).length := by
    have : sint.Z wlen4 = (sint.nat wlen4 : Int) := by word
    omega
  rw [hwn4, List.take_left]
  wp_auto
  wp_apply HW $$ HS [] Hv4 as %nnv4 %errv4 HS Hv4
  · iapply Qp $$ Hpc HQ
    ipureintro
    exact ⟨_, by rw [hbody]; simp only [List.append_assoc]; rfl⟩
  ihave Hsl := Hback $$ %_ Hv4 %(by first | rfl | exact hwn4.symm)
  ihave %Hal4' := ownSlice_len $$ Hsl
  simp only at Hal4'
  ihave HL4 : (∃ (k : Nat) (arr : List w8),
      "i" ∷ i_ptr ↦ W64 k ∗
      "HS" ∷ S (((((((((W ++ (sp.le32 rep ++ sp.le32 bl ++ sp.le32 cb)) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.encCmdId e.id)).flatten) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.le64 e.phase)).flatten) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.encCmd e.cmd)).flatten) ++ sp.varintLen es.length) ++ ((es.take k).map (fun e => sp.encDep e.dep)).flatten) ∗
      "Hsl" ∷ slice.mk b_ptr (W64 12) (W64 12) ↦* arr ∗
      "%Hk" ∷ ⌜arr.length = sint.nat (W64 12) ∧ k ≤ es.length⌝ : IProp netDistGF)
    $$ [i HS Hsl]
  · iexists 0, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; simp
    ipureintro; exact ⟨Hal4'.1, by omega⟩
  wp_for HL4
  try wp_auto
  wp_if_destruct
  · obtain ⟨hk1, hk2⟩ := Hk
    have Hif : sint.Z (W64 (k : Int)) < sint.Z dp.len := by
      first | exact Hif | simpa using Hif | exact of_decide_eq_true (go.IntoValInj.intoVal_inj Hif)
    have hcl' : sint.Z dp.len = es.length := by
      have : sint.Z dp.len = (sint.nat dp.len : Int) := by word
      omega
    have hk64 : sint.Z (W64 (k : Int)) = k := by word
    have hkn : k < es.length := by omega
    have hk0 : 0 ≤ sint.Z (W64 (k : Int)) := by omega
    have hkk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    have hbnd : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z dp.len := ⟨hk0, Hif⟩
    obtain ⟨en, hen⟩ : ∃ en, es[k]? = some en := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hsplit : es = es.take k ++ en :: es.drop (k + 1) := by
      have hk' : es[k] = en := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hen)
      rw [← hk', ← List.drop_eq_getElem_cons hkn, List.take_append_drop]
    have htake : ((es.take (k + 1)).map (fun e => sp.encDep e.dep)).flatten =
        ((es.take k).map (fun e => sp.encDep e.dep)).flatten ++ (fun e => sp.encDep e.dep) en := by
      rw [List.take_add_one, hen]; simp
    have hflat : (es.map (fun e => sp.encDep e.dep)).flatten =
        ((es.take k).map (fun e => sp.encDep e.dep)).flatten ++ (fun e => sp.encDep e.dep) en ++
          ((es.drop (k + 1)).map (fun e => sp.encDep e.dep)).flatten := by
      rw [congrArg (fun l => (List.map (fun e => sp.encDep e.dep) l).flatten) hsplit]
      simp
    have hp : (((((((((W ++ (sp.le32 rep ++ sp.le32 bl ++ sp.le32 cb)) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.encCmdId e.id)).flatten) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.le64 e.phase)).flatten) ++ sp.varintLen es.length) ++ (es.map (fun e => sp.encCmd e.cmd)).flatten) ++ sp.varintLen es.length) ++ ((es.take k).map (fun e => sp.encDep e.dep)).flatten) ++ (fun e => sp.encDep e.dep) en <+:
        W ++ (sp.Msg.newLeaderAckN rep bl cb es).body :=
      ⟨_, by rw [hbody, hflat]; simp only [List.append_assoc]; rfl⟩
    ihave ⟨%c, %sd, %Hcs, #Hro⟩ := BigSepL.bigSepL_lookup (Φ := fun i e => iprop(∃ (c : state.Command)
        (sd : swift.SDep), ⌜cmL[i]? = some c ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj c sd e)) hen
      $$ Hents
    obtain ⟨-, hsd⟩ := Hcs
    iunfold swift.repEntryObj at Hro
    icases Hro with ⟨%vs, -, -, #Hdep⟩
    have hsd' : dpL[(sint.Z (W64 (k : Int))).toNat]? = some sd := by
      rw [hk64]; exact hsd
    have hdw : en.dep.length < 2 ^ 62 := (hwfe en (List.mem_of_getElem? hen)).2
    try wp_auto
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
    try wp_auto
    icases ownSlice_elem_acc (sint.Z (W64 (k : Int))) _ dp _ _ hk0 hsd' $$ HDp with ⟨#He, -⟩
    wp_apply swift.SDep.Marshal.wp wp_pv _ _ sd en.dep hdw _ S Q _ $$ [HS] as ⟨HS, -⟩
    · iframe Hsink0 HS Hpc He Hdep
      iapply Qp $$ Hpc HQ
      ipureintro
      exact hp
    try wp_auto
    wp_for_post
    iframe
    rw [hkk]
    iexists k + 1, _
    iframe
    isplitl [HS]
    · iExactEq HS; congr 1; rw [htake]; simp
    ipureintro
    exact ⟨hk1, by omega⟩
  obtain ⟨hk1, hk2⟩ := Hk
  have Hif : ¬ sint.Z (W64 (k : Int)) < sint.Z dp.len := by
    first
    | exact Hif
    | simpa using Hif
    | exact fun h => Hif (by rw [decide_eq_true h])
    | exact of_decide_eq_false (go.IntoValInj.intoVal_inj Hif)
  have hkn : k = es.length := by
    have : sint.Z (W64 (k : Int)) = k := by word
    have : sint.Z dp.len = (sint.nat dp.len : Int) := by word
    omega
  subst hkn
  rw [List.take_length]
  try rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [decide_eq_false Hif]))]
  try wp_auto
  iapply HΦ
  iExactEq HS
  rw [hbody]; simp only [List.append_assoc]


/-- **`swift.MNewLeaderAckN.marshalH`**, over `PutVarint`'s hypothesis. -/
theorem swift.MNewLeaderAckN.marshal_proofP (wp_pv : swift.PutVarint.specH (hG := hG)) :
    swift.MNewLeaderAckN.marshalH (hG := hG) := by
  intro p a rep bl cb hwf hrep hcb
  iintro #Hbin #Hack #HackB
  unfold sp.marshalOk
  iexists ⟨go.GoType.PointerType swift.MNewLeaderAckN.ty, #p⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %wr %S %Q %W %Φ #Hobj #Hsink HS #Hpc #HQ HΦ
  iunfold swift.ackObj at Hobj
  icases Hobj with ⟨%rep', %bl', %cb', %ids, %ph, %cm, %dp, %cmL, %dpL, #Hp, #HI, #HP, #HC, #HD,
    %Hf, #Hents⟩
  iunfold swift.ackBal at HackB
  icases HackB with ⟨%rep2, %cb2, %ids2, %ph2, %cm2, %dp2, #Hp2⟩
  icombine Hp Hp2 gives %Heq
  have hbl : bl' = bl := by injection Heq with _ h
  subst hbl
  obtain ⟨hr, hc, hcl, hdl⟩ := Hf
  have e1 : rep' = rep := BitVec.eq_of_toInt_eq (by
    show sint.Z rep' = sint.Z rep; rw [hr, hrep])
  have e2 : cb' = cb := BitVec.eq_of_toInt_eq (by
    show sint.Z cb' = sint.Z cb; rw [hc, hcb])
  subst e1 e2
  have hspec := swift.MNewLeaderAckN.Marshal.wp wp_pv p rep' bl' cb' ids ph cm dp a.2.entries cmL dpL hwf
    hcl hdl wr S Q W
  iapply hspec $$ [HS] [HΦ]
  · iframe Hbin Hsink HS Hpc HQ Hp HI HP HC HD
    imodintro
    iexact Hents
  inext
  iintro HS
  iapply HΦ $$ [] HS
  iunfold swift.ackObj
  iexists rep', bl', cb', ids, ph, cm, dp, cmL, dpL
  iframe Hp HI HP HC HD Hents
  ipureintro; exact ⟨hr, hc, hcl, hdl⟩

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
