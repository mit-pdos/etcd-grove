module

public import Dsverify.Proof.raxos.Replica.RecDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions]

/-- The proposal's value as a recorder `Value`. -/
def propValue (pv : ProposerMessage_Proposal) : Value :=
  ⟨pv.Priority', pv.ProposerId', pv.ThreadId', pv.Ids'⟩

/-- The empty value (`-1, -1, -1, nil`). -/
def botValue : Value := ⟨W64 (-1), W64 (-1), W64 (-1), slice.nil⟩

/-- A new slot (`espImpl`'s). -/
def initSlot : RecorderSlot := ⟨W64 0, botValue, botValue, botValue⟩

theorem valRep_bot : ⊢ valRep (GF := GF) botValue Val.bot := by
  unfold valRep botValue Val.bot
  isplitr
  · ipureintro; simp only [List.not_mem_nil, false_imp_iff, implies_true, _root_.and_true]
    refine ⟨?_, ?_, ?_⟩ <;> rfl
  · iapply ownSlice_nil

theorem slotRep_init : ⊢ slotRep (GF := GF) initSlot RecSt.init := by
  unfold slotRep initSlot RecSt.init
  isplitr
  · ipureintro; first | rfl | trivial
  isplitr
  · iapply valRep_bot
  isplitr
  · iapply valRep_bot
  · iapply valRep_bot

/-- `b`'s tag is below `a`'s (the recorder's `max` keeps `a`). -/
def vTagLt (b a : Value) : Prop :=
  sint.Z b.priority' < sint.Z a.priority' ∨ (sint.Z b.priority' = sint.Z a.priority' ∧
    (sint.Z b.proposer_id' < sint.Z a.proposer_id' ∨ (sint.Z b.proposer_id' = sint.Z a.proposer_id' ∧
      sint.Z b.thread_id' < sint.Z a.thread_id')))

instance (a b : Value) : Decidable (vTagLt a b) := by unfold vTagLt; infer_instance

theorem valRep_max (a : Value) (va : pure.Val) (pv : ProposerMessage_Proposal) (v : pure.Val) :
    valRep (GF := GF) a va ∗ valRep (propValue pv) v ⊢
      valRep (if vTagLt (propValue pv) a then a else propValue pv) (recMax va v) := by
  iintro ⟨Ha, Hp⟩
  unfold valRep
  icases Ha with ⟨%Ha, Hai⟩
  icases Hp with ⟨%Hp, Hpi⟩
  have hiff : vTagLt (propValue pv) a ↔ v.tagLt va := by
    unfold vTagLt Val.tagLt propValue at *; dsimp only at *
    rw [Ha.1, Ha.2.1, Ha.2.2.1, Hp.1, Hp.2.1, Hp.2.2.1]
  unfold recMax
  by_cases h : v.tagLt va
  · rw [if_pos (hiff.2 h), if_pos h]; iframe; ipureintro; exact Ha
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]; iframe; ipureintro; exact Hp

theorem slotRep_same (sv : RecorderSlot) (st : RecSt) (pv : ProposerMessage_Proposal)
    (v : pure.Val) :
    slotRep (GF := GF) sv st ∗ valRep (propValue pv) v ⊢
      slotRep { sv with A' := if vTagLt (propValue pv) sv.A' then sv.A' else propValue pv }
        (espStep st (sint.Z sv.S') v) := by
  iintro ⟨Hs, Hp⟩
  unfold slotRep
  icases Hs with ⟨%HS, HF, HA, HM⟩
  have : espStep st (sint.Z sv.S') v = { st with A := recMax st.A v } := by
    unfold espStep; rw [if_pos HS.symm]
  rw [this]
  isplitr
  · ipureintro; exact HS
  iframe HF HM
  iapply valRep_max $$ [$HA $Hp]

theorem slotRep_lt (sv : RecorderSlot) (st : RecSt) (pv : ProposerMessage_Proposal)
    (v : pure.Val) (s : w64) (mv : Value) (hlt : sint.Z sv.S' < sint.Z s)
    (hmv : mv = if sint.Z sv.S' + 1 < sint.Z s then botValue else sv.A') :
    slotRep (GF := GF) sv st ∗ valRep (propValue pv) v ⊢
      slotRep ⟨s, propValue pv, propValue pv, mv⟩ (espStep st (sint.Z s) v) := by
  subst hmv
  iintro ⟨Hs, #Hp⟩
  unfold slotRep
  icases Hs with ⟨%HS, HF, HA, HM⟩
  have : espStep st (sint.Z s) v =
      ⟨sint.Z s, v, v, if st.S + 1 < sint.Z s then Val.bot else st.A⟩ := by
    unfold espStep; rw [if_neg (by omega), if_pos (by omega)]
  rw [this]
  isplitr
  · ipureintro; first | rfl | trivial
  iframe Hp
  rw [HS]
  by_cases h : st.S + 1 < sint.Z s
  · rw [if_pos h, if_pos h]; iapply valRep_bot
  · rw [if_neg h, if_neg h]; iexact HA

theorem slotRep_gt (sv : RecorderSlot) (st : RecSt) (v : pure.Val) (s : w64)
    (hgt : sint.Z s < sint.Z sv.S') :
    slotRep (GF := GF) sv st ⊢ slotRep sv (espStep st (sint.Z s) v) := by
  iintro Hs
  ihave %HS : ⌜sint.Z sv.S' = st.S⌝ $$ [Hs]
  · unfold slotRep; icases Hs with ⟨%HS, -⟩; ipureintro; exact HS
  have : espStep st (sint.Z s) v = st := by
    unfold espStep; rw [if_neg (by omega), if_neg (by omega)]
  rw [this]; iexact Hs

set_option goose.wp.extras true

/-- The fields of a proposal `max` and `espImpl` read. -/
def propFields (pl : Loc) (dq : DFrac) (pv : ProposerMessage_Proposal) : IProp GF :=
  iprop(pl.[ProposerMessage_Proposal, go!"Priority"] ↦{dq} pv.Priority' ∗
    pl.[ProposerMessage_Proposal, go!"ProposerId"] ↦{dq} pv.ProposerId' ∗
    pl.[ProposerMessage_Proposal, go!"ThreadId"] ↦{dq} pv.ThreadId' ∗
    pl.[ProposerMessage_Proposal, go!"Ids"] ↦{dq} pv.Ids')

theorem wp_max (re pl : Loc) (dq : DFrac) (pv : ProposerMessage_Proposal) (old : Value) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ propFields pl dq pv }}
      (App (App (Val (re @!! go.GoType.PointerType Recorder.ty @!! go!"max")) (Val #old)) (Val #pl))
    {{ (v : Value), RET #v; propFields pl dq pv ∗
        ⌜v = if vTagLt (propValue pv) old then old else propValue pv⌝ }} := by
  wp_start as Hf
  unfold propFields
  icases Hf with ⟨Priority, ProposerId, ThreadId, Ids⟩
  wp_auto
  repeat' wp_if_destruct
  all_goals
    iapply HΦ
    isplitl
    · iframe
    · ipureintro
      by_cases h : vTagLt (propValue pv) old
      all_goals (simp only [h, ↓reduceIte]) <;>
        (unfold vTagLt propValue at h; dsimp only at h; first | rfl | (exfalso; word))

end proof

section proof2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions]

set_option goose.wp.extras true

/-- Step through code that indexes the slots at `idx`, its bounds check known (`h`). -/
local macro "idx_auto " h:ident : tactic =>
  `(tactic| repeat (first | wp_auto | simp only [$h:ident, _root_.and_self, ↓reduceIte]))

theorem wp_espImpl (γ : QNames) (k : Nat) (re : Loc) (idx s : w64) (pl : Loc)
    (pv : ProposerMessage_Proposal) (v : pure.Val) (me : Int) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ isRecorder γ k re ∗
        ptProp pl .discard pv ∗ valRep (propValue pv) v ∗ evIn γ (.send (sint.Z idx) me (sint.Z s) v) ∗
        ⌜1 ≤ sint.Z idx ∧ sint.Z idx ≤ 600⌝ }}
      (App (App (App (Val (re @!! go.GoType.PointerType Recorder.ty @!! go!"espImpl")) (Val #idx))
        (Val #s)) (Val #pl))
    {{ (S : w64) (F M : Value), RET (PairV (PairV #S #F) #M);
        ∃ st, ⌜sint.Z S = st.S⌝ ∗ valRep F st.F ∗ valRep M st.M ∗
          evIn γ (.record k (sint.Z idx) (sint.Z s) v st) }} := by
  wp_start as ⟨#Hre, #Hp, #Hv, #Hsend, %Hidx⟩
  iunfold isRecorder at Hre
  icases Hre with ⟨%cb, %γs, %ch, %γc, %mu, #Hcb, #Hst, #Hch, #Hchb, #Hname, #Hmu, #Hmux, #Hinv, %Hk⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmux] as ⟨Hlocked, HR⟩
  iunfold recInv at HR
  icases HR with ⟨%sl, %ss, %m, Hslots, Hsl, Hcap, Hhalf, #Hrel, %Hout⟩
  ihave HI : (∃ (sl' : GoSlice) (ss' : List RecorderSlot),
      "Hslots" ∷ re.[Recorder, go!"slots"] ↦ sl' ∗ "Hsl" ∷ sl' ↦* ss' ∗
      "Hcap" ∷ ownSliceCap RecorderSlot sl' (DFrac.own 1) ∗
      "#Hrel" ∷ □ (∀ (j : Nat) (s : RecorderSlot), ⌜ss'[j]? = some s⌝ -∗
        slotRep s ((m !! (j : Int)).getD RecSt.init)) ∗
      "%Hout" ∷ ⌜∀ i : Int, (i < 0 ∨ (ss'.length : Int) ≤ i) →
        (m !! i).getD RecSt.init = RecSt.init⌝ : IProp GF) $$ [Hslots Hsl Hcap]
  · iexists sl, ss
    iframe
    isplitl []
    · iexact Hrel
    · ipureintro; exact Hout
  iclear Hrel
  wp_for HI
  wp_if_destruct
  · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType RecorderSlot.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := RecorderSlot) (t := RecorderSlot.ty) [initSlot]
    wp_auto
    isplitl []
    · ipureintro; first | rfl | trivial
    iintro %lit_ptr ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := RecorderSlot) _ _ _ _ _ $$ [$Hsl $Hcap $Hlit] as %s1 ⟨Hsl, Hcap, -⟩
    wp_for_post
    iframe
    iexists s1, ss' ++ [initSlot]
    iframe
    isplitl []
    · imodintro
      iintro %j %s0 %Hj
      by_cases hj : j < ss'.length
      · rw [List.getElem?_append_left hj] at Hj
        iapply Hrel $$ %j %s0 %Hj
      · rw [List.getElem?_append_right (by omega)] at Hj
        have hj0 : j = ss'.length := by
          cases h : j - ss'.length with
          | zero => omega
          | succ n => rw [h] at Hj; simp at Hj
        subst hj0
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at Hj
        subst Hj
        rw [Hout _ (Or.inr (Int.le_refl _))]
        iapply slotRep_init
    · ipureintro
      intro i hi
      apply Hout
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      omega
  · ihave %Hlen := ownSlice_len $$ Hsl
    have Hb : 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z sl'.len := by
      constructor
      · omega
      · have := Hlen.2; word
    list_elem ss' (sint.nat idx) as sv
    have Hi : ((sint.nat idx : Nat) : Int) = sint.Z idx := by word
    ihave #Hsv : slotRep sv ((m !! sint.Z idx).getD RecSt.init) $$ []
    · rw [← Hi]; iapply Hrel $$ %(sint.nat idx) %sv %Hsv_lookup
    have Hidx' : (sint.Z idx).toNat = sint.nat idx := rfl
    icases ownSlice_elem_acc (sint.Z idx) sv sl' _ ss' Hb.1 (by rw [Hidx']; exact Hsv_lookup) $$ Hsl
      with ⟨Helem, Hsl⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_auto
    ihave Hpf := ptProp_fields _ _ $$ Hp
    iunfold fieldsProp at Hpf
    iNamed Hpf
    wp_join iprop(∃ sv' : RecorderSlot, "Helem" ∷ sliceIndexRef RecorderSlot (sint.Z idx) sl' ↦ sv' ∗
        "re" ∷ re_ptr ↦ re ∗ "p" ∷ p_ptr ↦ pl ∗ "s" ∷ s_ptr ↦ s ∗
        "index" ∷ index_ptr ↦ idx ∗ "Hslots" ∷ re.[Recorder, go!"slots"] ↦ sl' ∗
        "#Hsv'" ∷ slotRep sv' (espStep ((m !! sint.Z idx).getD RecSt.init) (sint.Z s) v))
      with [Helem re p s index Hslots] as ⟨%sv', Helem, re, p, s, index, Hslots, #Hsv'⟩
    · idx_auto Hb
      wp_apply wp_max $$ [] as %vm ⟨-, %Hvm⟩
      · unfold propFields; iframe #
      idx_auto Hb
      subst Hvm
      isplitr
      · ipureintro; first | rfl | trivial
      iexists _
      iframe
      iapply slotRep_same $$ [$Hsv $Hv]
    · idx_auto Hb
      wp_if_destruct
      · idx_auto Hb
        wp_if_destruct
        · idx_auto Hb
          isplitr
          · ipureintro; first | rfl | trivial
          iexists _
          iframe
          simp only [named]
          rw [show (⟨pv.Priority', pv.ProposerId', pv.ThreadId', pv.Ids'⟩ : Value) = propValue pv
            from rfl, show (⟨W64 (-1), W64 (-1), W64 (-1), slice.nil⟩ : Value) = botValue from rfl]
          iapply slotRep_lt sv _ pv v s botValue (by assumption) (by rw [if_pos (by word)]) $$ [$Hsv $Hv]
        · idx_auto Hb
          isplitr
          · ipureintro; first | rfl | trivial
          iexists _
          iframe
          simp only [named]
          rw [show (⟨pv.Priority', pv.ProposerId', pv.ThreadId', pv.Ids'⟩ : Value) = propValue pv
            from rfl]
          iapply slotRep_lt sv _ pv v s sv.A' (by assumption) (by rw [if_neg (by word)]) $$ [$Hsv $Hv]
      · isplitr
        · ipureintro; first | rfl | trivial
        iexists _
        iframe
        simp only [named]
        iapply slotRep_gt sv _ v s (by word) $$ [$Hsv]
    idx_auto Hb
    ihave Hsl := Hsl $$ Helem
    ihave Hcr := cons_record γ ⊤ (by simp) (k : Int) (sint.Z idx) me (sint.Z s) v m $$ Hinv Hhalf Hsend
    ihave Hcr := fupd_glob _ _ _ $$ Hcr
    imod Hcr with ⟨Hhalf, #Hrec⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmux $Hlocked Hslots Hsl Hcap Hhalf]
    · inext
      unfold recInv
      iexists sl', ss'.set (sint.Z idx).toNat sv',
        m.insert (sint.Z idx) (espStep ((m !! sint.Z idx).getD RecSt.init) (sint.Z s) v)
      iframe
      isplitl []
      · imodintro
        iintro %j %s0 %Hj
        by_cases hj : j = (sint.Z idx).toNat
        · subst hj
          rw [List.getElem?_set_self (by rw [Hlen.1]; word)] at Hj
          cases Hj
          rw [show (((sint.Z idx).toNat : Nat) : Int) = sint.Z idx by word, GMap.lookup_insert_eq,
            Option.getD_some]
          iexact Hsv'
        · rw [List.getElem?_set_ne (Ne.symm hj)] at Hj
          rw [GMap.lookup_insert_ne _ _ (by intro h; apply hj; word)]
          iapply Hrel $$ %j %s0 %Hj
      · ipureintro
        intro i hi
        simp only [List.length_set] at hi
        rw [GMap.lookup_insert_ne _ _ (by intro h; subst h; word)]
        exact Hout i hi
    iapply HΦ
    unfold slotRep
    icases Hsv' with ⟨%HS, HF, -, HM⟩
    iexists _
    iframe HF HM Hrec
    ipureintro
    word
    done
end proof2

end Perennial.raxos
