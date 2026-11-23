/-
Package `proposer`: the conversions between message types (`getProposeClientBatches`,
`convertToClientBtchMessages`, `extractDecidedSlots`, `convertToClientBatches`,
`convertToClientBatchMessages`, `extractDecisionSlots`).
-/
module

public import Dsverify.Proof.raxos.Proposer.Persist

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

namespace prop

section conv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

/-- `convertToClientBtchMessages(messages)`. -/
theorem wp_convertToClientBtchMessages (p : Loc) (sl : GoSlice) (ps : List Loc)
    (ms : List GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sl ↦*□ ps ∗
        repList repCSingle ps .discard ms }}
      (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"convertToClientBtchMessages"))
        (Val #sl))
    {{ (r : GoSlice), RET #r; ∃ qs, r ↦*□ qs ∗ repList repPMSingle qs .discard ms }} := by
  wp_start as ⟨#Hsl, #Hms⟩
  wp_auto
  wp_apply wp_slice_make2 (V := Loc) (W64 0) as %rA ⟨HrA, HrAc⟩
  · ipureintro; decide
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hlen2 := repList_length _ _ _ _ $$ Hms
  simp only [List.replicate_zero]
  ipersist HrA
  ihave HI : (∃ (i : w64) (r : GoSlice) (qs : List Loc),
      "i" ∷ i_ptr ↦ i ∗ "rA" ∷ rA_ptr ↦ r ∗ "#Hr" ∷ r ↦*□ qs ∗
      "Hrc" ∷ ownSliceCap Loc r (DFrac.own 1) ∗
      "#Hq" ∷ repList repPMSingle qs .discard (ms.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp GF) $$ [i rA HrAc]
  · iexists W64 0, rA, []
    iframe
    iframe #
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    isplitr
    · iapply repList_nil
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z i < sint.Z sl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z sl.len <;> simp [h]
      first | done | (intro h'; cases h')
    list_elem ps (sint.nat i) as q
    ihave ⟨%m, %Hm, #Hqm⟩ := repList_lookup _ _ _ _ _ _ Hq_lookup $$ Hms
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, Hlt⟩)]
    wp_apply wp_load_slice_index sl (sint.Z i) ps _ q Hi.1 $$ [Hsl] as -
    · iframe #; ipureintro; exact Hq_lookup
    unfold repCSingle
    icases Hqm with ⟨%x, #Hx, %Hxm⟩
    wp_auto
    imod ptPMSingle_share ⊤ _ _ $$ «$sl0» with #«$sl0»
    wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) [«$sl0_ptr»]
    wp_auto
    rw [show go.arrayLiteralSize [KeyedElement none
      (ElementExpression (go.GoType.PointerType ProposerMessage_ClientBatch_SingleMessage.ty)
        #«$sl0_ptr»)] = 1 from rfl]
    isplitr
    · ipureintro; rfl
    iintro %sp ⟨Hsp, -⟩
    wp_apply wp_slice_append_persistent (V := Loc) r qs _ [«$sl0_ptr»] (DFrac.own 1)
      $$ [$Hr $Hrc Hsp] as %r' ⟨#Hr', Hrc', -⟩
    · iexact Hsp
    ihave #Hq2 : repList repPMSingle (qs ++ [«$sl0_ptr»]) .discard
        (List.take (sint.nat i) ms ++ [m]) $$ []
    · iapply repList_snoc $$ Hq
      unfold repPMSingle
      iexists _
      iframe «$sl0»
      ipureintro; exact ⟨rfl, by simp [Hxm]⟩
    wp_for_post
    iframe
    iexists i + W64 1, r', qs ++ [«$sl0_ptr»]
    iframe
    iframe #
    have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [Hi1, List.take_add_one, Hm, Option.toList_some]
    iframe #
    ipureintro; word
  · have Hge : ¬ sint.Z i < sint.Z sl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z sl.len <;> simp [h]
    iapply HΦ
    iexists qs
    iframe #
    rw [show sint.nat i = ms.length by word, List.take_length]
    iexact Hq

/-- `convertToClientBatchMessages(messages)`. -/
theorem wp_convertToClientBatchMessages (p : Loc) (sl : GoSlice) (ps : List Loc)
    (ms : List GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sl ↦*□ ps ∗
        repList repDRSingle ps .discard ms }}
      (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"convertToClientBatchMessages"))
        (Val #sl))
    {{ (r : GoSlice), RET #r; ∃ qs, r ↦*□ qs ∗ repList repCSingle qs .discard ms }} := by
  wp_start as ⟨#Hsl, #Hms⟩
  wp_auto
  wp_apply wp_slice_make2 (V := Loc) (W64 0) as %rA ⟨HrA, HrAc⟩
  · ipureintro; decide
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hlen2 := repList_length _ _ _ _ $$ Hms
  simp only [List.replicate_zero]
  ipersist HrA
  ihave HI : (∃ (i : w64) (r : GoSlice) (qs : List Loc),
      "i" ∷ i_ptr ↦ i ∗ "rtMessages" ∷ rtMessages_ptr ↦ r ∗ "#Hr" ∷ r ↦*□ qs ∗
      "Hrc" ∷ ownSliceCap Loc r (DFrac.own 1) ∗
      "#Hq" ∷ repList repCSingle qs .discard (ms.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp GF) $$ [i rtMessages HrAc]
  · iexists W64 0, rA, []
    iframe
    iframe #
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    isplitr
    · iapply repList_nil
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z i < sint.Z sl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z sl.len <;> simp [h]
      first | done | (intro h'; cases h')
    list_elem ps (sint.nat i) as q
    ihave ⟨%m, %Hm, #Hqm⟩ := repList_lookup _ _ _ _ _ _ Hq_lookup $$ Hms
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, Hlt⟩)]
    wp_apply wp_load_slice_index sl (sint.Z i) ps _ q Hi.1 $$ [Hsl] as -
    · iframe #; ipureintro; exact Hq_lookup
    unfold repDRSingle
    icases Hqm with ⟨%x, #Hx, %Hxm⟩
    wp_auto
    imod ptCSingle_share ⊤ _ _ $$ «$sl0» with #«$sl0»
    wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) [«$sl0_ptr»]
    wp_auto
    rw [show go.arrayLiteralSize [KeyedElement none
      (ElementExpression (go.GoType.PointerType raxos.proto.client.ClientBatch_SingleMessage.ty)
        #«$sl0_ptr»)] = 1 from rfl]
    isplitr
    · ipureintro; rfl
    iintro %sp ⟨Hsp, -⟩
    wp_apply wp_slice_append_persistent (V := Loc) r qs _ [«$sl0_ptr»] (DFrac.own 1)
      $$ [$Hr $Hrc Hsp] as %r' ⟨#Hr', Hrc', -⟩
    · iexact Hsp
    ihave #Hq2 : repList repCSingle (qs ++ [«$sl0_ptr»]) .discard
        (List.take (sint.nat i) ms ++ [m]) $$ []
    · iapply repList_snoc $$ Hq
      unfold repCSingle
      iexists _
      iframe «$sl0»
      ipureintro; exact ⟨rfl, by simp [Hxm]⟩
    wp_for_post
    iframe
    iexists i + W64 1, r', qs ++ [«$sl0_ptr»]
    iframe
    iframe #
    have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [Hi1, List.take_add_one, Hm, Option.toList_some]
    iframe #
    ipureintro; word
  · have Hge : ¬ sint.Z i < sint.Z sl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z sl.len <;> simp [h]
    iapply HΦ
    iexists qs
    iframe #
    rw [show sint.nat i = ms.length by word, List.take_length]
    iexact Hq

/-- `getProposeClientBatches(btch)`: the batches as `*ProposerMessage_ClientBatch`es. -/
theorem wp_getProposeClientBatches (γ : QNames) (p : Loc) (sl : GoSlice)
    (vs : List raxos.proto.client.ClientBatch) (bs : List Batch) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sl ↦*□ vs ∗ batchesP γ vs bs }}
      (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"getProposeClientBatches"))
        (Val #sl))
    {{ (r : GoSlice), RET #r; ∃ bps, r ↦*□ bps ∗ repList repPMBatch bps .discard bs }} := by
  wp_start as ⟨#Hsl, #Hbs⟩
  iunfold batchesP at Hbs
  icases Hbs with ⟨%Hbl, #Hbs⟩
  wp_auto
  wp_apply wp_slice_make2 (V := Loc) (W64 0) as %rA ⟨HrA, HrAc⟩
  · ipureintro; decide
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  simp only [List.replicate_zero]
  ipersist HrA
  ihave HI : (∃ (i : w64) (r : GoSlice) (qs : List Loc),
      "i" ∷ i_ptr ↦ i ∗ "rA" ∷ rA_ptr ↦ r ∗ "#Hr" ∷ r ↦*□ qs ∗
      "Hrc" ∷ ownSliceCap Loc r (DFrac.own 1) ∗
      "#Hq" ∷ repList repPMBatch qs .discard (bs.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp GF) $$ [i rA HrAc]
  · iexists W64 0, rA, []
    iframe
    iframe #
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    isplitr
    · iapply repList_nil
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z i < sint.Z sl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z sl.len <;> simp [h]
      first | done | (intro h'; cases h')
    list_elem vs (sint.nat i) as v
    ihave ⟨%b, %Hb, #Hvb, -⟩ := BigSepL.bigSepL_lookup (Φ := fun k v => iprop(∃ b, ⌜bs[k]? = some b⌝ ∗
      repCBVal v .discard b ∗ batchReg γ b.id b)) Hv_lookup $$ Hbs
    iunfold repCBVal at Hvb
    icases Hvb with ⟨%mps, %Hvf, #Hmps, #Hmr⟩
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi.1, Hlt⟩
    icases ownSlice_elem_acc (sint.Z i) v sl _ _ Hi.1 Hv_lookup $$ Hsl with ⟨Hve, -⟩
    iStructNamed Hve
    repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] | wp_auto)
    wp_apply wp_convertToClientBtchMessages p _ mps b.cmds $$ [] as %ms ⟨%qs2, #Hms, #Hms2⟩
    · iframe #
    repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] | wp_auto)
    imod ptPMBatch_share ⊤ _ _ $$ «$sl0» with #«$sl0»
    wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) [«$sl0_ptr»]
    wp_auto
    rw [show go.arrayLiteralSize [KeyedElement none
      (ElementExpression (go.GoType.PointerType ProposerMessage_ClientBatch.ty)
        #«$sl0_ptr»)] = 1 from rfl]
    isplitr
    · ipureintro; rfl
    iintro %sp ⟨Hsp, -⟩
    wp_apply wp_slice_append_persistent (V := Loc) r qs _ [«$sl0_ptr»] (DFrac.own 1)
      $$ [$Hr $Hrc Hsp] as %r' ⟨#Hr', Hrc', -⟩
    · iexact Hsp
    ihave #Hq2 : repList repPMBatch (qs ++ [«$sl0_ptr»]) .discard
        (List.take (sint.nat i) bs ++ [b]) $$ []
    · iapply repList_snoc $$ Hq
      unfold repPMBatch
      iexists _, qs2
      iframe #
      ipureintro; exact ⟨rfl, Hvf.1, Hvf.2.1⟩
    wp_for_post
    iframe
    iexists i + W64 1, r', qs ++ [«$sl0_ptr»]
    iframe
    iframe #
    have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [Hi1, List.take_add_one, Hb, Option.toList_some]
    iframe #
    ipureintro; word
  · have Hge : ¬ sint.Z i < sint.Z sl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z sl.len <;> simp [h]
    iapply HΦ
    iexists qs
    iframe #
    rw [show sint.nat i = bs.length by word, List.take_length]
    iexact Hq

/-- `extractDecidedSlots(indexes, decisions, proposers)`: the decided slots. -/
theorem wp_extractDecidedSlots (γ : QNames) (p : Loc) (isl dsl psl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ decidedSlotsP γ isl psl dsl }}
      (App (App (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"extractDecidedSlots"))
        (Val #isl)) (Val #dsl)) (Val #psl))
    {{ (r : GoSlice), RET #r; ∃ ds, dsRep γ r ds }} := by
  wp_start as #Hds
  iunfold decidedSlotsP at Hds
  icases Hds with ⟨%is, %ps, %dsls, %ds, #His, #Hps, #Hdsls, %Hlens, #Hdl⟩
  ihave %Hl1 := ownSlice_len _ _ _ $$ His
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hps
  ihave %Hl3 := ownSlice_len _ _ _ $$ Hdsls
  wp_auto
  have Hll : isl.len = dsl.len := by
    have a := Hl1.1; have b := Hl3.1; have c := Hlens.1; have d := Hlens.2.2
    word
  rw [_root_.decide_eq_true Hll]
  wp_auto
  wp_apply wp_slice_make2 (V := Loc) (W64 0) as %rA ⟨HrA, HrAc⟩
  · ipureintro; decide
  simp only [List.replicate_zero]
  ipersist HrA
  ihave HI : (∃ (i : w64) (r : GoSlice) (qs : List Loc) (dacc : List DSlot),
      "i" ∷ i_ptr ↦ i ∗ "rA" ∷ rA_ptr ↦ r ∗ "#Hr" ∷ r ↦*□ qs ∗
      "Hrc" ∷ ownSliceCap Loc r (DFrac.own 1) ∗
      "#Hq" ∷ repList repPMSlot qs .discard dacc ∗
      "#Hdec" ∷ ([∗list] d ∈ dacc, decided γ d.index d.ids) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z isl.len⌝ : IProp GF) $$ [i rA HrAc]
  · iexists W64 0, rA, [], []
    iframe
    iframe #
    isplitr
    · iapply repList_nil
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z i < sint.Z isl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z isl.len <;> simp [h]
      first | done | (intro h'; cases h')
    have Hn : sint.nat i < ds.length := by have := Hlens.1; have := Hl1.1; word
    list_elem ds (sint.nat i) as d
    ihave ⟨%dsl0, %ix, %Hdx, #Hdsl0, #Hdd⟩ := BigSepL.bigSepL_lookup (Φ := fun k d => iprop(∃ (sl : GoSlice) (i : w64), ⌜dsls[k]? = some sl ∧ is[k]? = some i ∧
      ∀ x ∈ d, strOk x⌝ ∗ sl ↦*□ d ∗ decided γ (sint.Z i) d)) Hd_lookup $$ Hdl
    list_elem ps (sint.nat i) as pp
    have hb1 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z isl.len := ⟨Hi.1, Hlt⟩
    have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z dsl.len := ⟨Hi.1, by rw [← Hll]; exact Hlt⟩
    have hb3 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z psl.len := ⟨Hi.1, by
      have := Hl2.1; have := Hlens.2.1; have := Hlens.1; have := Hl1.1; word⟩
    repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb1)] |
      rw [ite_eq_left_of_eq_true _ _ (eq_true hb2)] | rw [ite_eq_left_of_eq_true _ _ (eq_true hb3)] |
      (wp_apply wp_load_slice_index isl (sint.Z i) is _ ix Hi.1 $$ [His] as -;
        · iframe #; ipureintro; exact Hdx.2.1) |
      (wp_apply wp_load_slice_index dsl (sint.Z i) dsls _ dsl0 Hi.1 $$ [Hdsls] as -;
        · iframe #; ipureintro; exact Hdx.1) |
      (wp_apply wp_load_slice_index psl (sint.Z i) ps _ pp Hi.1 $$ [Hps] as -;
        · iframe #; ipureintro; exact Hpp_lookup) |
      wp_auto)
    imod ptPMSlot_share ⊤ _ _ $$ «$sl0» with #«$sl0»
    wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) [«$sl0_ptr»]
    wp_auto
    rw [show go.arrayLiteralSize [KeyedElement none
      (ElementExpression (go.GoType.PointerType ProposerMessage_DecidedSlot.ty)
        #«$sl0_ptr»)] = 1 from rfl]
    isplitr
    · ipureintro; rfl
    iintro %sp ⟨Hsp, -⟩
    wp_apply wp_slice_append_persistent (V := Loc) r qs _ [«$sl0_ptr»] (DFrac.own 1)
      $$ [$Hr $Hrc Hsp] as %r' ⟨#Hr', Hrc', -⟩
    · iexact Hsp
    ihave #Hq2 : repList repPMSlot (qs ++ [«$sl0_ptr»]) .discard
        (dacc ++ [⟨sint.Z ix, d, sint.Z (W64 (sint.Z pp) : w64)⟩]) $$ []
    · iapply repList_snoc $$ Hq
      unfold repPMSlot
      iexists _
      iframe #
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    wp_for_post
    iframe
    iexists i + W64 1, r', qs ++ [«$sl0_ptr»], _
    iframe
    iframe #
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; word
  · have Hge : ¬ sint.Z i < sint.Z isl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z isl.len <;> simp [h]
    iapply HΦ
    iexists dacc
    unfold dsRep
    iexists qs
    iframe #

/-- `extractDecisionSlots(indexes, decisions, proposers)`: the decided slots. -/
theorem wp_extractDecisionSlots (γ : QNames) (p : Loc) (isl dsl psl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ decidedSlotsP γ isl psl dsl }}
      (App (App (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"extractDecisionSlots"))
        (Val #isl)) (Val #dsl)) (Val #psl))
    {{ (r : GoSlice), RET #r; ∃ (sps : List Loc) (ds : List DSlot), r ↦*□ sps ∗
        repList repDecSlot sps .discard ds ∗ [∗list] d ∈ ds, decided γ d.index d.ids }} := by
  wp_start as #Hds
  iunfold decidedSlotsP at Hds
  icases Hds with ⟨%is, %ps, %dsls, %ds, #His, #Hps, #Hdsls, %Hlens, #Hdl⟩
  ihave %Hl1 := ownSlice_len _ _ _ $$ His
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hps
  ihave %Hl3 := ownSlice_len _ _ _ $$ Hdsls
  wp_auto
  have Hll : isl.len = dsl.len := by
    have a := Hl1.1; have b := Hl3.1; have c := Hlens.1; have d := Hlens.2.2
    word
  rw [_root_.decide_eq_true Hll]
  wp_auto
  wp_apply wp_slice_make2 (V := Loc) (W64 0) as %rA ⟨HrA, HrAc⟩
  · ipureintro; decide
  simp only [List.replicate_zero]
  ipersist HrA
  ihave HI : (∃ (i : w64) (r : GoSlice) (qs : List Loc) (dacc : List DSlot),
      "i" ∷ i_ptr ↦ i ∗ "arr" ∷ arr_ptr ↦ r ∗ "#Hr" ∷ r ↦*□ qs ∗
      "Hrc" ∷ ownSliceCap Loc r (DFrac.own 1) ∗
      "#Hq" ∷ repList repDecSlot qs .discard dacc ∗
      "#Hdec" ∷ ([∗list] d ∈ dacc, decided γ d.index d.ids) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z isl.len⌝ : IProp GF) $$ [i arr HrAc]
  · iexists W64 0, rA, [], []
    iframe
    iframe #
    isplitr
    · iapply repList_nil
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z i < sint.Z isl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z isl.len <;> simp [h]
      first | done | (intro h'; cases h')
    have Hn : sint.nat i < ds.length := by have := Hlens.1; have := Hl1.1; word
    list_elem ds (sint.nat i) as d
    ihave ⟨%dsl0, %ix, %Hdx, #Hdsl0, #Hdd⟩ := BigSepL.bigSepL_lookup (Φ := fun k d => iprop(∃ (sl : GoSlice) (i : w64), ⌜dsls[k]? = some sl ∧ is[k]? = some i ∧
      ∀ x ∈ d, strOk x⌝ ∗ sl ↦*□ d ∗ decided γ (sint.Z i) d)) Hd_lookup $$ Hdl
    list_elem ps (sint.nat i) as pp
    have hb1 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z isl.len := ⟨Hi.1, Hlt⟩
    have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z dsl.len := ⟨Hi.1, by rw [← Hll]; exact Hlt⟩
    have hb3 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z psl.len := ⟨Hi.1, by
      have := Hl2.1; have := Hlens.2.1; have := Hlens.1; have := Hl1.1; word⟩
    repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb1)] |
      rw [ite_eq_left_of_eq_true _ _ (eq_true hb2)] | rw [ite_eq_left_of_eq_true _ _ (eq_true hb3)] |
      (wp_apply wp_load_slice_index isl (sint.Z i) is _ ix Hi.1 $$ [His] as -;
        · iframe #; ipureintro; exact Hdx.2.1) |
      (wp_apply wp_load_slice_index dsl (sint.Z i) dsls _ dsl0 Hi.1 $$ [Hdsls] as -;
        · iframe #; ipureintro; exact Hdx.1) |
      (wp_apply wp_load_slice_index psl (sint.Z i) ps _ pp Hi.1 $$ [Hps] as -;
        · iframe #; ipureintro; exact Hpp_lookup) |
      wp_auto)
    imod ptDecSlot_share ⊤ _ _ $$ «$sl0» with #«$sl0»
    wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) [«$sl0_ptr»]
    wp_auto
    rw [show go.arrayLiteralSize [KeyedElement none
      (ElementExpression (go.GoType.PointerType Decisions_DecidedSlot.ty)
        #«$sl0_ptr»)] = 1 from rfl]
    isplitr
    · ipureintro; rfl
    iintro %sp ⟨Hsp, -⟩
    wp_apply wp_slice_append_persistent (V := Loc) r qs _ [«$sl0_ptr»] (DFrac.own 1)
      $$ [$Hr $Hrc Hsp] as %r' ⟨#Hr', Hrc', -⟩
    · iexact Hsp
    ihave #Hq2 : repList repDecSlot (qs ++ [«$sl0_ptr»]) .discard
        (dacc ++ [⟨sint.Z ix, d, sint.Z (W64 (sint.Z pp) : w64)⟩]) $$ []
    · iapply repList_snoc $$ Hq
      unfold repDecSlot
      iexists _
      iframe #
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    wp_for_post
    iframe
    iexists i + W64 1, r', qs ++ [«$sl0_ptr»], _
    iframe
    iframe #
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; word
  · have Hge : ¬ sint.Z i < sint.Z isl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z isl.len <;> simp [h]
    iapply HΦ
    iexists qs, dacc
    iframe #

/-- `convertToClientBatches(batches)`: the batches as `client.ClientBatch` values. -/
theorem wp_convertToClientBatches (p : Loc) (sl : GoSlice) (ps : List Loc) (bs : List Batch) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sl ↦*□ ps ∗
        repList repDRBatch ps .discard bs }}
      (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"convertToClientBatches"))
        (Val #sl))
    {{ (r : GoSlice), RET #r; ∃ vs : List raxos.proto.client.ClientBatch, r ↦*□ vs ∗
        ⌜vs.length = bs.length⌝ ∗
        [∗list] k ↦ v ∈ vs, ∃ b, ⌜bs[k]? = some b⌝ ∗ repCBVal v .discard b }} := by
  wp_start as ⟨#Hsl, #Hbs⟩
  wp_auto
  wp_apply wp_slice_make2 (V := raxos.proto.client.ClientBatch) (W64 0) as %rA ⟨HrA, HrAc⟩
  · ipureintro; decide
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hlen2 := repList_length _ _ _ _ $$ Hbs
  simp only [List.replicate_zero]
  ipersist HrA
  ihave HI : (∃ (i : w64) (r : GoSlice) (vs : List raxos.proto.client.ClientBatch),
      "i" ∷ i_ptr ↦ i ∗ "rtBtches" ∷ rtBtches_ptr ↦ r ∗ "#Hr" ∷ r ↦*□ vs ∗
      "Hrc" ∷ ownSliceCap raxos.proto.client.ClientBatch r (DFrac.own 1) ∗
      "#Hq" ∷ ([∗list] k ↦ v ∈ vs, ∃ b, ⌜bs[k]? = some b⌝ ∗ repCBVal v .discard b) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len ∧ vs.length = sint.nat i⌝ : IProp GF)
      $$ [i rtBtches HrAc]
  · iexists W64 0, rA, []
    iframe
    iframe #
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp; word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z i < sint.Z sl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z sl.len <;> simp [h]
      first | done | (intro h'; cases h')
    list_elem ps (sint.nat i) as q
    ihave ⟨%b, %Hb, #Hqb⟩ := repList_lookup _ _ _ _ _ _ Hq_lookup $$ Hbs
    unfold repDRBatch
    icases Hqb with ⟨%x, %mps, #Hx, %Hxu, %Hxf, #Hmps, #Hmr⟩
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi.1, Hlt⟩
    repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] |
      (wp_apply wp_load_slice_index sl (sint.Z i) ps _ q Hi.1 $$ [Hsl] as -;
        · iframe #; ipureintro; exact Hq_lookup) | wp_auto)
    wp_apply wp_convertToClientBatchMessages p _ mps b.cmds $$ [] as %ms ⟨%qs2, #Hms, #Hms2⟩
    · iframe #
    repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] |
      (wp_apply wp_load_slice_index sl (sint.Z i) ps _ q Hi.1 $$ [Hsl] as -;
        · iframe #; ipureintro; exact Hq_lookup) | wp_auto)
    obtain ⟨cv, hcv⟩ : ∃ cv : raxos.proto.client.ClientBatch, cv =
      { state' := zeroValDef, sizeCache' := 0, unknownFields' := slice.nil, Sender' := x.Sender',
        Messages' := ms, Id' := x.Id' } := ⟨_, rfl⟩
    rw [← hcv]
    wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := raxos.proto.client.ClientBatch) [cv]
    wp_auto
    rw [show go.arrayLiteralSize [KeyedElement none
      (ElementExpression raxos.proto.client.ClientBatch.ty #cv)] = 1 from rfl]
    isplitr
    · ipureintro; rfl
    iintro %sp ⟨Hsp, -⟩
    wp_apply wp_slice_append_persistent (V := raxos.proto.client.ClientBatch) r vs _ [cv] (DFrac.own 1)
      $$ [$Hr $Hrc Hsp] as %r' ⟨#Hr', Hrc', -⟩
    · iexact Hsp
    ihave #Hcv : repCBVal cv .discard b $$ []
    · unfold repCBVal
      iexists qs2
      rw [hcv]
      iframe #
      ipureintro; exact ⟨Hxf.1, Hxf.2, rfl⟩
    wp_for_post
    iframe
    iexists i + W64 1, r', vs ++ [cv]
    iframe
    iframe #
    isplitr
    · isplitr
      · ipureintro; rw [Nat.zero_add, Hi.2.2]; exact Hb
      iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; refine ⟨by word, by word, ?_⟩; simp [Hi.2.2]; word
  · have Hge : ¬ sint.Z i < sint.Z sl.len := by
      revert Hif; by_cases h : sint.Z i < sint.Z sl.len <;> simp [h]
    iapply HΦ
    iexists vs
    iframe #
    ipureintro; rw [Hi.2.2]; word

end conv

end prop

end Perennial.raxos
