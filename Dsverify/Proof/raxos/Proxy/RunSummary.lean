/-
Package `proxy`: `proposePreviousEpochSummary` (`proxymabhandler.go`, leader mode 2): at an
epoch's first slot from epoch `2n` on, the proxy proposes the summary `summaryId p` of the order
`calculateSequence` returns (a permutation of the replicas), registered first (`sum_register`),
with the leader flag `getLeaderWait` gives (and its evidence, `getLeaderSequence`'s `leadEv`).
-/
module

public import Dsverify.Proof.raxos.Proxy.RunProposeLemmas
public import Dsverify.Proof.raxos.Proxy.MabLeader
public import Dsverify.Proof.raxos.Proxy.SliceLit

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
variable [ha : hyp.AtoiSpec GF]

attribute [local instance] HeapGS.goose_globalGS

/-- `pr.proposePreviousEpochSummary(i)` at a summary slot `i` not decided here, with its init
token: the summary proposed (`init` event), the log extended to the slot, which records it. -/
def proposeSummary_spec : Prop :=
  ∀ (γ : QNames) (γs : GName) (cf : QConf) (k : Nat) (pr : Loc) (i : w64) (rl : GoSlice)
    (slots : List Slot) (L : List (Option (List GoString))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sharedConsts cf k pr ∗
      ⌜cf.ok ∧ 1 ≤ k ∧ k ≤ cf.n ∧ sumSlot cf.n cf.ep (sint.Z i) ∧ 1 ≤ sint.Z i ∧ sint.Z i ≤ 600 ∧
        ¬ (sint.Z i < slots.length ∧ ∃ s, slots[sint.nat i]? = some s ∧ s.decided' = true)⌝ ∗
      inv consN (consInv γ) ∗ inv smrN (smrInv γ) ∗ confIs γ cf ∗
      chanField ProposeRequest.ty pr go!"proxyToProposerChan" (proposeReqP γ k) ∗
      initTok γ k (sint.Z i) ∗ logRd γ γs cf pr rl slots L ∗ ownSliceCap Slot rl (DFrac.own 1) ∗
      epochOwn pr ∗ decState γ pr }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"proposePreviousEpochSummary"))
      (Val #i))
  {{ RET #(); ∃ (rl' : GoSlice) (slots' : List Slot) (m : Nat),
      logRd γ γs cf pr rl' slots' (L ++ List.replicate m none) ∗
      ownSliceCap Slot rl' (DFrac.own 1) ∗
      ⌜(m = 0 ∨ slots.length + m ≤ sint.nat i + 1) ∧ sint.nat i < slots'.length⌝ ∗
      epochOwn pr ∗ decState γ pr }} 
/-- `proposeSummary_spec`, from `calculateSequence`'s. -/
theorem wp_proposePreviousEpochSummary
    (wp_calc : calculateSequence_spec (GF := GF) (hG := hG)) :
    proposeSummary_spec (GF := GF) (hG := hG) := by
  intro γ γs cf k pr i rl slots L
  have wp_gls := wp_getLeaderSequence (GF := GF) (hG := hG)
  have wp_glw := wp_getLeaderWait (GF := GF) (hG := hG)
  wp_start as ⟨#Hc, %Hi, #Hcons, #Hsmri, #Hconf, #Hpch, Htok, Hlog, Hslcap, Hepo, Hdec⟩
  ihave #Hc2 := Hc
  iunfold sharedConsts at Hc2
  icases Hc2 with ⟨#Hname, -, -, -, #Hmode, -, #Hep, #Hnr⟩
  have Hok := Hi.1
  unfold QConf.ok at Hok
  wp_auto
  have Hepv : sint.Z (W64 (cf.ep : Int)) = cf.ep := by word
  have Hep0 : ¬ sint.Z (W64 (cf.ep : Int)) = 0 := by omega
  repeat' (first | wp_auto | simp only [Hep0, ↓reduceIte])
  have Hd := sdiv_small i (W64 cf.ep) (by omega) (by omega)
  rw [Hepv] at Hd
  have Hss := Hi.2.2.2.1
  have Hq0 : (sint.Z i).tdiv cf.ep ≤ sint.Z i := by
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; exact Int.ediv_le_self _ (by omega)
  wp_apply (wp_calc γ γs cf k pr (BitVec.sdiv i (W64 cf.ep)) rl slots L) $$ [Hlog Hepo]
    as %p ⟨%Hp, Hlog, Hepo⟩
  · iframe #; iframe; ipureintro
    exact ⟨Hi.1, Hi.2.1, Hi.2.2.1, by rw [Hd]; exact Hss.1, by rw [Hd]; omega⟩
  have Hsp : sumPerm p := by unfold sumPerm; rcases Hok.1 with h | h <;> rw [h] at Hp <;> simp [Hp]
  wp_apply (wp_slice_make2 (V := GoString)) as %sp0 ⟨-, -⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := raxos.proto.client.ClientBatch)) as %bp0 ⟨Hbp0, Hbp0cap⟩
  · ipureintro; word
  rw [← summaryId_seqStr]
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) [summaryId p]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sp ⟨Hsp, -⟩
  ipersist Hsp
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.GoType.SliceType (go.GoType.PointerType raxos.proto.client.ClientBatch_SingleMessage.ty)))))
    (Val (LiteralValueV _)))
  iapply (wp_slice_literal_ex (V := Loc)
    (t := go.GoType.PointerType raxos.proto.client.ClientBatch_SingleMessage.ty))
  wp_auto
  wp_alloc lm as Hlm
  wp_auto
  iexists [lm]
  isplitl []
  · ipureintro; rfl
  iintro %msl ⟨Hmsl, -⟩
  imod ptCSingle_share ⊤ _ _ ?st $$ Hlm with #Hlm
  case st => exact stateOk_zero _
  ipersist Hmsl
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.GoType.SliceType raxos.proto.client.ClientBatch.ty)))) (Val (LiteralValueV _)))
  iapply (wp_slice_literal (V := raxos.proto.client.ClientBatch)
    (t := raxos.proto.client.ClientBatch.ty) ?lb)
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := raxos.proto.client.ClientBatch) _ _ _ _ _ $$ [$Hbp0 $Hbp0cap $Hlit]
    as %bp1 ⟨Hbp1, Hbp1cap, -⟩
  -- the leader flag
  wp_apply (wp_gls γ γs cf k pr i rl slots L) $$ [Hlog] as %lsl %q ⟨Hlsl, %Hq, #Hld, Hlog⟩
  · iframe #; iframe; ipureintro; exact ⟨Hi.1, Hi.2.1, Hi.2.2.1, by omega, by omega⟩
  wp_apply (wp_glw cf k pr lsl q) $$ [$Hlsl]
  · iframe #; ipureintro; exact ⟨Hi.1, Hi.2.1, Hi.2.2.1, Hq⟩
  iintro ⟨%Hqi, -⟩
  have Hfl := rp_flag cf k q Hi.1 ⟨Hi.2.1, Hi.2.2.1⟩ Hq
  wp_auto
  wp_join iprop(∃ bl : Bool, "isLeader" ∷ isLeader_ptr ↦ bl ∗ "pr" ∷ pr_ptr ↦ pr ∗
      "%Hbl" ∷ ⌜bl = decide (q.head? = some k)⌝) with [isLeader pr]
    as ⟨%bl, isLeader, pr, %Hbl⟩
  · iexists true; iframe; ipureintro; simp [Hfl.1 Hif]
  · iexists false; iframe; ipureintro; simp only [Bool.false_eq, decide_eq_false_iff_not]
    exact fun h => Hif (Hfl.2 h)
  -- the summary's batch is registered; the proposal's init event
  imod (rs_sum_register γ cf p Hi.1 Hp) $$ Hsmri with #Hreg
  iunfold decState at Hdec
  icases Hdec with ⟨%ls, %ps, %ds, Hls, Hps, Hds, #Hdsp, Hlscap, Hpscap, Hdscap⟩
  subst Hbl
  imod (rs_cons_init γ cf (k : Int) (sint.Z i) [summaryId p] (decide (q.head? = some k)) Hi.1
    (by simp) (fun _ => ⟨p, Hp, rfl⟩)) $$ Hcons Hconf Htok Hld [] with #Hinit
  · iapply BigSepL.bigSepL_singleton.2
    iexists _; iexact Hreg
  ipersist Hbp1
  iunfold chanField at Hpch
  icases Hpch with ⟨%pch, %γp, #Hpchf, #Hpbag⟩
  wp_auto
  wp_apply wp_bag_send $$ [Hpbag]
  · iframe Hpbag
    iunfold proposeReqP
    iexists [summaryId p], _, [⟨summaryId p, -1, [summaryId p]⟩]
    dsimp only
    iframe #
    isplitl []
    · iunfold batchesP
      isplitr
      · ipureintro; exact ⟨by simp, by simpa using summary_batchFit p Hsp⟩
      simp only [List.replicate_zero, List.nil_append]
      iapply BigSepL.bigSepL_singleton.2
      iexists _
      isplitr
      · ipureintro; rfl
      isplitr
      · iunfold repCBVal
        iexists [lm]
        isplitr
        · ipureintro; exact ⟨show sint.Z (W64 (-1)) = -1 by rfl, rfl, rfl⟩
        isplitr
        · iexact Hmsl
        iunfold repList
        isplitr
        · ipureintro; rfl
        iapply BigSepL.bigSepL_singleton.2
        iexists _
        isplitr
        · ipureintro; rfl
        iunfold repCSingle
        iexists _
        iframe Hlm
        ipureintro; exact ⟨rfl, rfl⟩
      iexact Hreg
    ipureintro; rfl
  iunfold logRd at Hlog
  icases Hlog with ⟨Hrl, Hsl, Hlog⟩
  iunfold logP at Hlog
  icases Hlog with ⟨%HlenL, Hlog⟩
  have Hnd := Hi.2.2.2.2.2.2
  -- extend the log to the slot
  ihave HI : (∃ (rl' : GoSlice) (m : Nat),
      "Hrl" ∷ pr.[Proxy, go!"replicatedLog"] ↦ rl' ∗ "Hsl" ∷ rl' ↦* (slots ++ List.replicate m rp_s0) ∗
      "Hslcap" ∷ ownSliceCap Slot rl' (DFrac.own 1) ∗
      "Hlog" ∷ ([∗list] j ↦ s ∈ slots ++ List.replicate m rp_s0,
        ∃ o, ⌜(L ++ List.replicate m none)[j]? = some o⌝ ∗ slotP γ γs cf j s o) ∗
      "%Hm" ∷ ⌜m = 0 ∨ slots.length + m ≤ sint.nat i + 1⌝ : IProp GF) $$ [Hrl Hsl Hslcap Hlog]
  · iexists rl, 0
    simp only [List.replicate_zero, List.append_nil]
    iframe
    ipureintro; simp
  wp_for HI
  ihave %Hsl'len := ownSlice_len $$ Hsl
  wp_if_destruct
  · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType Slot.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Slot) (t := Slot.ty) [rp_s0]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := Slot) _ _ _ _ _ $$ [$Hsl $Hslcap $Hlit] as %rl'' ⟨Hsl, Hslcap, -⟩
    wp_for_post
    iframe
    iexists rl'', m + 1
    rw [List.replicate_succ', ← List.append_assoc, List.replicate_succ', ← List.append_assoc]
    iframe
    isplitl [Hlog]
    · iapply BigSepL.bigSepL_append.2
      isplitl [Hlog]
      · iapply BigSepL.bigSepL_impl $$ Hlog
        imodintro
        iintro %j %s0 %hj ⟨%o, %Ho, Hs⟩
        iexists o
        iframe Hs
        ipureintro
        have := (List.getElem?_eq_some_iff.1 hj).1
        simp only [List.length_append, List.length_replicate] at this
        rw [List.getElem?_append_left (by simp [← HlenL]; omega)]
        exact Ho
      iapply BigSepL.bigSepL_singleton.2
      iexists none
      isplitr
      · ipureintro
        simp only [Nat.zero_add, List.length_append, List.length_replicate]
        rw [List.getElem?_append_right (by simp [HlenL])]
        simp [HlenL]
      iapply rp_slotP_s0
    ipureintro
    right
    simp only [List.length_append, List.length_replicate] at Hsl'len
    word
  -- the slot records the proposed ids
  simp only [List.length_append, List.length_replicate] at Hsl'len
  have Hil : sint.nat i < (slots ++ List.replicate m rp_s0).length := by
    simp only [List.length_append, List.length_replicate]; word
  list_elem (slots ++ List.replicate m rp_s0) (sint.nat i) as sx
  have Hsxd := rp_slot_undecided slots m (sint.nat i) sx Hsx_lookup
    (fun h => Hnd ⟨by have := h.1; word, h.2⟩)
  icases BigSepL.bigSepL_insert_acc Hsx_lookup $$ Hlog with ⟨⟨%o, %Ho, Hslot⟩, Hlog⟩
  iunfold slotP at Hslot
  icases Hslot with ⟨%Hod, -⟩
  have Hon : o = none := by
    cases o with
    | none => rfl
    | some _ => rw [Hsxd] at Hod; simp at Hod
  subst Hon
  have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z rl'.len := ⟨by word, by word⟩
  icases ownSlice_elem_acc (sint.Z i) sx rl' _ _ Hb.1 (by simpa using Hsx_lookup) $$ Hsl
    with ⟨Hel, Hsl⟩
  repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
  wp_apply (wp_slice_make2 (V := w64)) as %ls' ⟨Hls', Hls'cap⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := w32)) as %ps' ⟨Hps', Hps'cap⟩
  · ipureintro; word
  wp_apply +noauto (wp_slice_make2 (V := GoSlice)) as %ds' ⟨Hds', Hds'cap⟩
  · ipureintro; word
  ipersist Hls'
  ipersist Hps'
  ipersist Hds'
  wp_auto
  ihave Hsl := Hsl $$ Hel
  ihave Hlog := Hlog $$ %(Slot.mk (slice.mk sp
      (W64 (go.arrayLiteralSize [KeyedElement none (ElementExpression go.string #(summaryId p))]))
      (W64 (go.arrayLiteralSize [KeyedElement none (ElementExpression go.string #(summaryId p))])))
      sx.decidedBatch' sx.decided' sx.committed' 0 0) [Hsp]
  · iexists none
    isplitr
    · ipureintro; exact Ho
    iunfold slotP
    isplitr
    · ipureintro; simpa using Hsxd
    iexists [summaryId p]
    iframe Hsp
    rw [decide_eq_true (show sumSlot cf.n cf.ep ((sint.nat i : Nat) : Int) by
      rw [show ((sint.nat i : Nat) : Int) = sint.Z i by word]; exact Hss)]
    simp only [↓reduceIte]; itrivial
  iapply HΦ
  iexists rl', _, m
  isplitl [Hrl Hsl Hlog]
  · iunfold logRd; iframe Hrl Hsl; iunfold logP
    isplitr
    · ipureintro; simp [HlenL]
    iexact Hlog
  iframe
  isplitr
  · ipureintro; exact ⟨Hm.imp id (fun h => by word), by simpa using Hil⟩
  iunfold decState
  iexists ls', ps', ds'
  iframe
  iunfold decidedSlotsP
  iexists List.replicate 0 (zero_val w64), List.replicate 0 (zero_val w32),
    List.replicate 0 (zero_val GoSlice), []
  isplitr
  · iexact Hls'
  isplitr
  · iexact Hps'
  isplitr
  · iexact Hds'
  isplitr
  · ipureintro; simp
  iapply BigSepL.bigSepL_nil.2; iempintro

end proofs

end Perennial.raxos
