/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/HandleReply.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleReply(r)` (swift/client.go:274): the leader's reply of ballot `b` for the client's
command `x`: its result is stored (`reps[x][b]`, recorded in `γr`), and it is the leader entry
of `x`'s fast set (with its checksum) and slow set (without).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleLightSlowAck

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions]

/-- A decoded `MReply` of the client's command `x` with its witness. -/
def replyArg (H : HC) (x : sp.CmdId) (l : Loc) : IProp netDistGF :=
  iprop(∃ (rv : swift.MReply) (hs : List sp.Hash) (v : List w8), l ↦□ rv ∗
    rv.Checksum' ↦*□ hs.map shashOf ∗ rv.Rep' ↦*□ v ∗
    ⌜cmdOf rv.CmdId' = x ∧ x.cl = H.cid ∧ ∀ h ∈ hs, h.length = 32⌝ ∗
    sp.msgOk H.γ H.γc H.γm (.reply rv.Replica' rv.Ballot' x hs v))

instance replyArg_persistent H x l : Persistent (replyArg H x l) := by
  unfold replyArg; haveI := sp.msgOk_persistent (γ := H.γ) (γc := H.γc) (γm := H.γm)
  infer_instance

abbrev handleReply.specI : Prop :=
  ∀ (H : HC) (x : sp.CmdId) (l : Loc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      ctxOk H ∗ quorumsOk H ∗ hst H ∗ replyArg H x l }}
    (App (Val (H.c @!! go.GoType.PointerType swift.Client.ty @!! go!"handleReply")) (Val #l))
  {{ RET #(); hst H }}

theorem handleReply.wp_proof
    (wp_hfa : handleFastAck.specI (hG := hG))
    (wp_init : initMsgSets.specI (hG := hG))
    (wp_Add : replica.mset.MsgSet.Add.specI (hG := hG))
    (wp_new : newFastAck.specI (hG := hG))
    (wp_copy : copyFastAck.specI (hG := hG)) :
    handleReply.specI (hG := hG) := by
  intro H x l
  haveI := cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hctx, #Hq, Hst, #Harg⟩
  iunfold hst at Hst
  icases Hst with ⟨Hcore, HF, HS, %bal, Hbal⟩
  ihave #Hctx0 := Hctx
  iunfold ctxOk at Hctx
  icases Hctx with ⟨#Hinv, #Hcfg, #Hb, #Hbv, #HcB, #HLg, #Hqt, #Hn, #Hhook, #Hpool, -⟩
  iunfold replyArg at Harg
  icases Harg with ⟨%rv, %hs, %v, #Hl, #Hcs, #Hrep, ⟨%Hx, %Hcl, %Hlen⟩, #Hw⟩
  ihave #Hf := Hl
  iStructNamed Hf
  iunfold core at Hcore
  icases Hcore with ⟨%dref, %rref, %aref, %D, %Rm, %Dn, %Gr, %As, %spn, Hdel, HD, Hreps, HRm,
    HRe, HspN, Hal, HAs, HDn, HGr, %Hok⟩
  wp_auto
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Unit)) $$ [$HD] as HD
  cases hDx : D.lookup rv.CmdId' with
  | some u =>
    simp only [Option.isSome_some, _root_.decide_true]
    wp_auto
    iapply HΦ
    unfold hst core
    iframe HF HS
    isplitl [Hdel HD Hreps HRm HRe HspN Hal HAs HDn HGr]
    · iexists dref, rref, aref, D, Rm, Dn, Gr, As, spn
      iframe; ipureintro; exact Hok
    iexists _; iframe Hbal
  | none =>
  simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
  wp_auto
  wp_apply wp_new as %f Hfz
  · iframe #
  isimp at Hfz
  ipersist Hfz
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := GoMap)) $$ [$HRm] as HRm
  wp_join iprop(∃ (ir : GoMap) (Rm' : GMap swift.CommandId GoMap) (im : GMap w32 GoSlice),
      byBallot_ptr ↦ ir ∗ rref ↦$ Rm' ∗ ir ↦$ im ∗ structFieldRef swift.Client go!"reps" H.c ↦ rref ∗
      c_ptr ↦ H.c ∗ cmdId_ptr ↦ rv.CmdId' ∗
      ([∗map] y ↦ ir' ∈ GMap.delete rv.CmdId' Rm', repsEntry H Gr y ir') ∗
      ⌜Rm'.lookup rv.CmdId' = some ir ∧ (∀ y, y ≠ rv.CmdId' → Rm'.lookup y = Rm.lookup y) ∧
        (∀ b', (cmdOf rv.CmdId', b') ∈ Gr → (im.lookup b').isSome)⌝ ∗
      □ (∀ b' vsl, ⌜im.lookup b' = some vsl⌝ → ∃ v' : List w8, vsl ↦*□ v' ∗
          ∃ r cs, sp.msgOk H.γ H.γc H.γm (.reply r b' (cmdOf rv.CmdId') cs v')))
    at (if: _ then _ else _) with [byBallot HRm HRe Hreps c cmdId]
    as ⟨%ir, %Rm', %im, byBallot, HRm, Him, Hreps, c, cmdId, HRe, %HRm', #Himv⟩
  · cases hRx : Rm.lookup rv.CmdId' with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
      wp_apply (wp_map_make1 (K := w32) (V := GoSlice)) as %nm Hnm
      wp_apply (wp_mapInsert (K := swift.CommandId) (V := GoMap)) $$ [$HRm] as HRm
      wp_join_done
      iexists nm, (<[rv.CmdId' := nm]> Rm), ∅
      iframe
      isplitl [HRe]
      · rw [GMap.delete_insert_eq, GMap.delete_notin Rm _ hRx]
        iexact HRe
      isplitr
      · ipureintro
        refine ⟨GMap.lookup_insert _ _ _, fun y hy => GMap.lookup_insert_ne _ _ (Ne.symm hy), ?_⟩
        intro b' hb'
        have := Hok.2.2 rv.CmdId' b' hb' hDx
        rw [hRx] at this; cases this
      imodintro
      iintro %b' %vsl %h
      simp at h
    | some ir =>
      simp only [Option.isSome_some, _root_.decide_true, Bool.not_true]
      wp_auto
      ihave ⟨Hent, HRe⟩ := (BigSepM.bigSepM_delete (Φ := repsEntry H Gr) hRx).1 $$ HRe
      iunfold repsEntry at Hent
      icases Hent with ⟨%im, Him, %Himb, #Himv⟩
      wp_join_done
      iexists ir, Rm, im
      iframe
      iframe #
      ipureintro
      exact ⟨hRx, fun _ _ => rfl, Himb⟩
  obtain ⟨hRx', hRy, Himb⟩ := HRm'
  wp_apply (wp_mapInsert (K := w32) (V := GoSlice)) $$ [$Him] as Him
  iapply fupd_wp
  imod (monoListAuthOwn_update_app (A := sp.CmdId × w32) [(cmdOf rv.CmdId', rv.Ballot')]) $$ HGr
    with ⟨HGr, #Hlb⟩
  imodintro
  ihave Hcore : core H $$ [Hdel HD Hreps HRm HRe Him HspN Hal HAs HDn HGr]
  · unfold core
    iexists dref, rref, aref, D, Rm', Dn, Gr ++ [(cmdOf rv.CmdId', rv.Ballot')], As, spn
    iframe
    isplitl [HRe Him]
    · iapply (BigSepM.bigSepM_delete (Φ := repsEntry H (Gr ++ [(cmdOf rv.CmdId', rv.Ballot')]))
        hRx').2
      isplitl [Him]
      · unfold repsEntry
        iexists (<[rv.Ballot' := rv.Rep']> im)
        iframe
        isplitr
        · ipureintro
          intro b' hb'
          by_cases hbb : b' = rv.Ballot'
          · subst hbb; simp
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm hbb)]
            rcases List.mem_append.mp hb' with h | h
            · exact Himb b' h
            · simp at h; exact absurd h hbb
        imodintro
        iintro %b' %vsl %hvb
        by_cases hbb : b' = rv.Ballot'
        · subst hbb
          rw [GMap.lookup_insert] at hvb; cases hvb
          iexists v; iframe #
          iexists rv.Replica', hs
          rw [Hx]; iexact Hw
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hbb)] at hvb
          iapply Himv; ipureintro; exact hvb
      iapply BigSepM.bigSepM_mono $$ HRe
      intro y ir' hy
      have hyx : y ≠ rv.CmdId' := by
        intro h; subst h; simp [Iris.Std.PartialMap.get?, Iris.Std.PartialMap.delete] at hy
      exact repsEntry_grow H Gr rv.CmdId' y rv.Ballot' ir' hyx
    ipureintro
    refine ⟨Hok.1, Hok.2.1, ?_⟩
    intro y b' hyb hyD
    by_cases hyx : y = rv.CmdId'
    · subst hyx; rw [hRx']; rfl
    · rw [hRy y hyx]
      rcases List.mem_append.mp hyb with h | h
      · exact Hok.2.2 y b' h hyD
      · simp at h; exact absurd (cmdOf_inj h.1) hyx
  subst Hx
  wp_apply wp_hfa H (cmdOf rv.CmdId') f true $$ [Hcore HF HS Hbal] as %b Hst
  · iframe #
    isplitl [Hcore HF HS Hbal]
    · unfold hst; iframe
    unfold fastArg
    simp only [↓reduceIte]
    unfold leaderP ackObj
    iexists _, hs, hs, v
    isplitr
    · iexists f; iframe #; ipureintro; exact ⟨rfl, Hlen⟩
    isplitr
    · ipureintro; exact ⟨rfl, Hcl, rfl, rfl⟩
    iframe #
    unfold repRec
    iexists _; iframe Hlb; ipureintro; simp
  ihave #Hff := Hfz
  iStructNamedSuffix Hff "f"
  iunfold hst at Hst
  icases Hst with ⟨Hcore, HF, HS, %bal2, Hbal⟩
  iunfold core at Hcore
  icases Hcore with ⟨%dref, %rref, %aref, %D, %Rm, %Dn, %Gr, %As, %spn, Hdel, HD, Hreps, HRm,
    HRe, HspN, Hal, HAs, HDn, HGr, %Hok⟩
  wp_auto
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Unit)) $$ [$HD] as HD
  cases hDx : D.lookup rv.CmdId' with
  | some u =>
    simp only [Option.isSome_some, _root_.decide_true]
    wp_auto
    iapply HΦ
    unfold hst core
    iframe HF HS
    isplitl [Hdel HD Hreps HRm HRe HspN Hal HAs HDn HGr]
    · iexists dref, rref, aref, D, Rm, Dn, Gr, As, spn
      iframe; ipureintro; exact Hok
    iexists _; iframe Hbal
  | none =>
  simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
  wp_auto
  wp_apply wp_copy $$ [] as %f2 Hf2
  · iframe #
  wp_auto
  isimp at Hf2
  ipersist Hf2
  ihave #Hf2f := Hf2
  iStructNamedSuffix Hf2f "g"
  wp_apply wp_init $$ [HF HS] as ⟨HF, HS⟩
  · iframe; iframe #
  iunfold pathsOwn at HS
  icases HS with ⟨%sref, %SP, Hsld, HSP, HSs, %Hset⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨ms, hms, hmsn⟩ := Hset
  wp_auto
  wp_apply (wp_map_lookup1 (K := swift.CommandId) (V := Loc)) $$ [$HSP] as HSP
  rw [show (SP !! rv.CmdId').getD (zero_val Loc) = ms by
    show (SP.lookup rv.CmdId').getD _ = ms; rw [hms]; rfl]
  ihave ⟨Hms, HSback⟩ := (BigSepM.bigSepM_lookup_acc (Φ := setOwn H false) hms).1 $$ HSs
  iunfold setOwn at Hms
  icases Hms with (%Hn | Hms)
  · exact absurd Hn hmsn
  wp_apply wp_Add $$ [Hms HspN Hal HAs HDn HGr Hdel HD Hreps HRm HRe] as %added ⟨Hms, Hcore⟩
  · iframe Hms
    isplitl [HspN Hal HAs HDn HGr Hdel HD Hreps HRm HRe]
    · unfold core
      iexists dref, rref, aref, D, Rm, Dn, Gr, As, spn
      iframe; ipureintro; exact Hok
    simp only [↓reduceIte]
    isplitr
    · ipureintro; simp
    imodintro
    unfold leaderP ackObj
    iexists _, ([] : List sp.Hash), hs, v
    isplitr
    · iexists f2; iframe #
      isplitr
      · ipureintro; simp
      simp only [List.map_nil]
      iapply ownSlice_nil
    isplitr
    · ipureintro; exact ⟨rfl, Hcl, rfl, rfl⟩
    iframe #
    unfold repRec
    iexists _; iframe Hlb; ipureintro; simp
  iapply HΦ
  unfold hst
  isplitl [Hcore]
  · iexact Hcore
  isplitl [HF]
  · iapply pathsOwn_weaken $$ HF
  isplitl [Hsld HSP HSback Hms]
  · unfold pathsOwn
    iexists sref, SP
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    isplitl
    · iapply HSback; unfold setOwn; iright; iexact Hms
    ipureintro; trivial
  iexists _; iexact Hbal

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
