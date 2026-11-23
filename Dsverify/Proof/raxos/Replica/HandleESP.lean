/-
Package `replica`: `Recorder.HandleESP` (the recorder's answer to an ESP request).
-/
module

public import Dsverify.Proof.raxos.Replica.Helpers
public import Dsverify.Proof.raxos.Replica.EspImpl

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]


set_option goose.wp.extras true

theorem i64Ok_sint (w : w64) : i64Ok (sint.Z w) := by
  unfold i64Ok; constructor <;> word

/-- The reply facts of `/Consensus/ESP` at recorder `r` for the request `m`. -/
def espReply (γ : QNames) (r : Int) (m : PM) (rr : RR) : IProp GF :=
  iprop(⌜rrOk rr⌝ ∗ (⌜rr = rrNotFound⌝ ∨
    ∃ p st, ⌜m.p = some p ∧ rr = rrOf st⌝ ∗ evIn γ (.record r m.index m.s p.val st)))

theorem wp_HandleESP (γ : QNames) (k : Nat) (re req : Loc) (m : PM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ isRecorder γ k re ∗
        repPM req .discard m ∗ ⌜pmOk m⌝ ∗ pmFacts γ m }}
      (App (Val (re @!! go.GoType.PointerType Recorder.ty @!! go!"HandleESP")) (Val #req))
    {{ (resp : Loc), RET #resp; ∃ rr, repRR resp .discard rr ∗ espReply γ k m rr }} := by
  wp_start as ⟨#Hre, #Hreq, %Hok, #Hfacts⟩
  ihave #Hre' := Hre
  iunfold isRecorder at Hre'
  icases Hre' with ⟨%cb, %γs, %ch, %γc, %mu, #Hcb, #Hst, #Hch, #Hchb, #Hname, #Hmu, #Hmux, #Hinv, %Hk⟩
  iunfold pmFacts at Hfacts
  icases Hfacts with ⟨%p, %me, %Hp, #Hsend, #Hbatches, #Hdec⟩
  iunfold repPM at Hreq
  icases Hreq with ⟨%x, %sps, #Hx, %Hxu, %Hxf, #HP, #Hsps, #Hslots⟩
  rw [Hp]
  iStructNamed Hx
  wp_auto
  wp_join with [re req response]
  · wp_if_destruct
    rotate_left
    · iframe
    wp_apply (wp_slice_make2 (V := w64) _) as %isl ⟨Hisl, Hicap⟩
    · ipureintro; word
    wp_apply (wp_slice_make2 (V := GoSlice) _) as %dsl ⟨Hdsl, Hdcap⟩
    · ipureintro; word
    wp_apply (wp_slice_make2 (V := w32) _) as %psl ⟨Hpsl, Hpcap⟩
    · ipureintro; word
    ihave %Hspl := ownSlice_len $$ Hsps
    ihave %Hsl : ⌜sps.length = m.slots.length⌝ $$ []
    · iunfold repList at Hslots; icases Hslots with ⟨%H, -⟩; ipureintro; exact H
    ihave HI : (∃ (i : w64) (is : List w64) (dss : List GoSlice) (ps : List w32)
        (isl dsl psl : GoSlice),
        "i" ∷ i_ptr ↦ i ∗
        "d" ∷ d_ptr ↦ ({ indexes' := isl, decisions' := dsl, proposers' := psl } : Decision) ∗
        "Hisl" ∷ isl ↦* is ∗ "Hicap" ∷ ownSliceCap w64 isl (DFrac.own 1) ∗
        "Hdsl" ∷ dsl ↦* dss ∗ "Hdcap" ∷ ownSliceCap GoSlice dsl (DFrac.own 1) ∗
        "Hpsl" ∷ psl ↦* ps ∗ "Hpcap" ∷ ownSliceCap w32 psl (DFrac.own 1) ∗
        "#Hacc" ∷ decAcc γ is ps dss ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z x.DecidedSlots'.len ∧ is.length = sint.nat i⌝ :
          IProp GF)
        $$ [i d Hisl Hicap Hdsl Hdcap Hpsl Hpcap]
    · iexists _, _, _, _, isl, dsl, psl
      simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
      iframe
      isplitl []
      · iapply decAcc_nil
      · ipureintro; refine ⟨by word, by word, by simp; rfl⟩
    wp_for HI
    wp_if_destruct
    · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z x.DecidedSlots'.len := ⟨Hi.1, by simpa [goose_wp_simp_extra] using Hif⟩
      list_elem sps (sint.nat i) as q
      list_elem m.slots (sint.nat i) as dd
      ihave #Hq : repPMSlot q .discard dd $$ []
      · iunfold repList at Hslots
        icases Hslots with ⟨-, Hs⟩
        ihave Hx := BigSepL.bigSepL_lookup (Φ := fun i p => iprop(∃ y, ⌜m.slots[i]? = some y⌝ ∗
          repPMSlot p DFrac.discard y)) Hq_lookup $$ Hs
        icases Hx with ⟨%y, %Hy, Hx⟩
        rw [Hdd_lookup] at Hy; cases Hy; iexact Hx
      ihave #Hddd : decided γ dd.index dd.ids $$ []
      · iapply BigSepL.bigSepL_lookup (Φ := fun _ d => decided γ d.index d.ids) Hdd_lookup $$ Hdec
      have Hddok : dslotOk dd := Hok.2.2.2.2 dd (List.mem_of_getElem? Hdd_lookup)
      iunfold repPMSlot at Hq
      icases Hq with ⟨%xq, #Hxq, %Hxqu, %Hxqf, #Hids⟩
      iStructNamed Hxq
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z i) sps _ q Hi.1 $$ [] as -
      · iframe #; ipureintro; exact Hq_lookup
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w64) (t := go.int) [xq.Index']
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, -⟩
      wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hisl $Hicap $Hl1] as %isl' ⟨Hisl, Hicap, -⟩
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z i) sps _ q Hi.1 $$ [] as -
      · iframe #; ipureintro; exact Hq_lookup
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType
        (go.GoType.SliceType go.string))))) (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoSlice) (t := go.GoType.SliceType go.string) [xq.Ids']
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %l2 ⟨Hl2, -⟩
      wp_apply wp_slice_append (V := GoSlice) _ _ _ _ _ $$ [$Hdsl $Hdcap $Hl2] as %dsl' ⟨Hdsl, Hdcap, -⟩
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z i) sps _ q Hi.1 $$ [] as -
      · iframe #; ipureintro; exact Hq_lookup
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int32))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w32) (t := go.int32) [_]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %l3 ⟨Hl3, -⟩
      wp_apply wp_slice_append (V := w32) _ _ _ _ _ $$ [$Hpsl $Hpcap $Hl3] as %psl' ⟨Hpsl, Hpcap, -⟩
      wp_for_post
      iframe
      iexists _, _, _, _, isl', dsl', psl'
      iframe
      isplitl []
      · iapply decAcc_snoc γ is ps dss xq.Index' _ xq.Ids' dd.ids Hddok.2.2 $$ [$Hacc $Hids]
        rw [Hxqf.1]; iexact Hddd
      · ipureintro; simp only [List.length_append, List.length_singleton]
        refine ⟨by word, by word, by word⟩
    · ihave %Hisl_len := ownSlice_len $$ Hisl
      ipersist Hisl
      ipersist Hdsl
      ipersist Hpsl
      wp_apply wp_bag_send γc ch _ (decisionP γ) $$ [$Hchb]
      · unfold decisionP
        isplitl []
        · iapply decidedSlotsP_of $$ [$Hisl $Hpsl $Hdsl $Hacc]
        · ipureintro; dsimp only; simp at Hif; word
      iframe
      ipureintro; rfl
  iunfold repProp at HP
  icases HP with ⟨%xp, %bps, #Hxp, %Hxpu, %Hxpf, #Hpids, #Hbps, #Hbreps⟩
  have Hpok : propOk p := Hok.2.2.2.1 p Hp
  ihave %Hbpl := ownSlice_len $$ Hbps
  ihave %Hipl := ownSlice_len $$ Hpids
  ihave %Hbl : ⌜bps.length = p.batches.length⌝ $$ []
  · iunfold repList at Hbreps; icases Hbreps with ⟨%H, -⟩; ipureintro; exact H
  ihave %Hnnp := typedPointsto_not_null $$ Hxp
  iStructNamedPrefix Hxp "P"
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ re_ptr ↦ re ∗ req_ptr ↦ req ∗
      response_ptr ↦ zero_val RecorderResponse ∗ «$res0_ptr» ↦ zero_val Loc) ∨
    (⌜v = returnVal #()⌝ ∗ re_ptr ↦ re ∗ req_ptr ↦ req ∗
      response_ptr ↦ ({ zero_val RecorderResponse with ClientBatchesNotFound' := true }) ∗
      «$res0_ptr» ↦ response_ptr))) with [re req response «$res0»]
  · repeat' wp_if_destruct
    all_goals try (ileft; iframe; done)
    wp_apply wp_findAllBatches γ k re _ p.ids $$ [$Hre $Hpids] as %b -
    cases b <;> wp_auto
    · iright; iframe; try (ipureintro; rfl)
    · ileft; iframe; try (ipureintro; rfl)
  · ileft; iframe; try (ipureintro; rfl)
  iintro (⟨%Hv, re, req, response, «$res0»⟩ | ⟨%Hv, re, req, response, «$res0»⟩)
  rotate_left
  · subst Hv
    ipersist response
    wp_auto
    iapply HΦ
    iexists rrNotFound
    isplitl []
    · unfold repRR
      iexists _
      iframe #
      simp only [rrNotFound, repOpt]
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; simp only [_root_.and_true]; rfl
      isplitr <;> ipureintro <;> rfl
    · unfold espReply
      isplitl []
      · ipureintro; refine ⟨⟨by decide, by decide⟩, nofun, nofun⟩
      · ileft; ipureintro; rfl
  subst Hv
  wp_auto
  wp_join with [re req response «$res0»]
  · ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ : IProp GF) $$ [i]
    · iexists _; iframe; ipureintro; word
    wp_for HI
    wp_if_destruct
    · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z xp.ClientBatches'.len := ⟨Hi, by simpa [goose_wp_simp_extra] using Hif⟩
      list_elem bps (sint.nat i) as q
      list_elem p.batches (sint.nat i) as b
      ihave #Hq : repPMBatch q .discard b $$ []
      · iunfold repList at Hbreps
        icases Hbreps with ⟨-, Hs⟩
        ihave Hx := BigSepL.bigSepL_lookup (Φ := fun i p' => iprop(∃ y, ⌜p.batches[i]? = some y⌝ ∗
          repPMBatch p' DFrac.discard y)) Hq_lookup $$ Hs
        icases Hx with ⟨%y, %Hy, Hx⟩
        rw [Hb_lookup] at Hy; cases Hy; iexact Hx
      ihave ⟨#Hbr, %Hbfit⟩ := BigSepL.bigSepL_lookup
        (Φ := fun _ b => iprop(batchReg γ b.id b ∗ ⌜batchFit b⌝)) Hb_lookup $$ Hbatches
      iunfold repPMBatch at Hq
      icases Hq with ⟨%xb, %mps, #Hxb, %Hxbu, %Hxbf, #Hmps, #Hmreps⟩
      iStructNamedPrefix Hxb "B"
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z i) bps _ q Hi $$ [] as -
      · iframe #; ipureintro; exact Hq_lookup
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z i) bps _ q Hi $$ [] as -
      · iframe #; ipureintro; exact Hq_lookup
      wp_apply wp_convertToClientBatchMessages re _ mps b.cmds $$ [$Hmps $Hmreps] as %ra ⟨%qs, Hra, #Hqs⟩
      ipersist Hra
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z i) bps _ q Hi $$ [] as -
      · iframe #; ipureintro; exact Hq_lookup
      wp_apply store_add_proof γ γs cb _ b $$ [$Hst $Hbr] as -
      · isplitl []
        · unfold repCBVal
          iexists qs
          iframe #
          ipureintro; exact ⟨Hxbf.1, Hxbf.2, rfl⟩
        · ipureintro; exact Hbfit
      wp_for_post
      iframe
      iexists _; iframe; ipureintro; word
    · iframe; try (ipureintro; rfl)
  ihave Hbd := evIn_bound γ ⊤ (by simp) (.send m.index me m.s p.val) $$ Hinv Hsend
  ihave Hbd := fupd_glob _ _ _ $$ Hbd
  imod Hbd with ⟨-, %Hbd⟩
  simp only [Ev.slot] at Hbd
  rw [← Hxf.2.1] at Hbd
  ihave #Hsend' : evIn γ (.send (sint.Z x.Index') me (sint.Z x.S') p.val) $$ []
  · rw [Hxf.2.1, Hxf.2.2]; iexact Hsend
  wp_apply +noauto wp_espImpl γ k re x.Index' x.S' x.P' .discard xp p.val me $$ [$Hre $Hsend']
    as %S %F %M ⟨-, %st, %HS, #HF, #HM, #Hrec⟩
  · isplitl []
    · iexact Hxp
    isplitl []
    · unfold valRep propValue
      isplitr
      · ipureintro; exact ⟨Hxpf.1, Hxpf.2.1, Hxpf.2.2, Hpok.2.2.2.1⟩
      · simp only [Prop'.val]; iexact Hpids
    · ipureintro; exact Hbd
  iapply wp_fupd
  wp_auto
  irename : (_ ↦ (RecorderResponse_Proposal.mk zeroValDef 0 slice.nil
    F.priority' F.proposer_id' F.thread_id' F.ids')) => HFp
  irename : (_ ↦ (RecorderResponse_Proposal.mk zeroValDef 0 slice.nil
    M.priority' M.proposer_id' M.thread_id' M.ids')) => HMp
  ipersist HFp
  ipersist HMp
  ipersist response
  imodintro
  iapply HΦ
  iunfold valRep at HF
  iunfold valRep at HM
  icases HF with ⟨%HFf, #HFi⟩
  icases HM with ⟨%HMf, #HMi⟩
  iexists (rrOf st)
  isplitl []
  · unfold repRR rrOf
    iexists _
    iframe response
    simp only [repOpt]
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨HS, trivial⟩
    isplitl []
    · unfold repRRProp rrPropOf; iexists _; iframe HFp; dsimp only
      iframe HFi; ipureintro; exact ⟨rfl, HFf.1, HFf.2.1, HFf.2.2.1⟩
    · unfold repRRProp rrPropOf; iexists _; iframe HMp; dsimp only
      iframe HMi; ipureintro; exact ⟨rfl, HMf.1, HMf.2.1, HMf.2.2.1⟩
  · unfold espReply
    isplitr
    · ipureintro
      refine ⟨?_, ?_, ?_⟩
      · simp only [rrOf]; rw [← HS]; exact i64Ok_sint _
      · intro q hq; simp only [rrOf, Option.some.injEq] at hq; subst hq
        unfold rrPropOk rrPropOf
        refine ⟨?_, ?_, ?_, HFf.2.2.2⟩
        · rw [← HFf.1]; exact i64Ok_sint _
        · rw [← HFf.2.1]; exact i64Ok_sint _
        · rw [← HFf.2.2.1]; exact i64Ok_sint _
      · intro q hq; simp only [rrOf, Option.some.injEq] at hq; subst hq
        unfold rrPropOk rrPropOf
        refine ⟨?_, ?_, ?_, HMf.2.2.2⟩
        · rw [← HMf.1]; exact i64Ok_sint _
        · rw [← HMf.2.1]; exact i64Ok_sint _
        · rw [← HMf.2.2.1]; exact i64Ok_sint _
    · iright
      iexists p, st
      isplitr
      · ipureintro; exact ⟨Hp, rfl⟩
      · rw [← Hxf.2.1, ← Hxf.2.2]; iexact Hrec

end proof

end Perennial.raxos
