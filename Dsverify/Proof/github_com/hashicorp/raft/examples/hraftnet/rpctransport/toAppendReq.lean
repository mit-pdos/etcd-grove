/-
The proof of `rpctransport.toAppendReq`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toAppendReq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.toAppendReq.wp_proof
    (wp_copyBytes : github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes.spec (GF := GF) (hG := hG))
    (wp_toHeader : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.toAppendReq.spec (GF := GF) (hG := hG) := by
  intro a dq rq dq1 id ad ld vs
  wp_start as ⟨Ha, Hid, Had, Hld, Hlogs⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ha
  iStructNamed Ha
  irename Term => aTerm
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  unfold logsOwn
  icases Hlogs with ⟨%ps, Hps, Hpv⟩
  ihave %Hpsl := ownSlice_len _ _ _ $$ Hps
  ihave %Hvl := BigSepL2.bigSepL2_length $$ Hpv
  wp_auto
  ihave IH : (∃ (k : Nat) (esv : GoSlice) (cp : List Entry) (lp : Loc),
      "Hctr" ∷ i_ptr ↦ W64 k ∗ "es" ∷ es_ptr ↦ esv ∗ "l" ∷ l_ptr ↦ lp ∗
      "Hesv" ∷ esv ↦* cp ∗ "Hcap" ∷ ownSliceCap Entry esv (DFrac.own 1) ∗
      "%Hk" ∷ ⌜k ≤ ps.length⌝ ∗
      "Hcp" ∷ ([∗list] e;v ∈ cp;(vs.take k), entOwn e (DFrac.own 1) v) : IProp GF) $$ [i es l]
  · iexists 0, _, [], _
    iframe
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · ipureintro; omega
    simp only [List.take_zero]
    iapply BigSepL2.bigSepL2_nil.2
    iempintro
  wp_for IH
  split
  · rename_i Hc
    have hk : k < ps.length := by simp only [decide_eq_true_eq] at Hc; word
    obtain ⟨p0, Hp0⟩ : ∃ x, ps[k]? = some x := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨v0, Hv0⟩ : ∃ x, vs[k]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_auto
    rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply (wp_load_slice_index rq.Entries' (sint.Z (W64 k)) ps dq1 p0 (by word)) $$ [$Hps] with Hps
    · ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact Hp0
    ihave Hacc := BigSepL2.bigSepL2_lookup_acc Hp0 Hv0 $$ Hpv
    icases Hacc with ⟨Hone, Hback⟩
    unfold logOwn logOwnV
    icases Hone with ⟨%lv, Hl, %Hf, Hd, Hx⟩
    ihave %Hln := typedPointsto_not_null _ _ _ $$ Hl
    iStructNamed Hl
    irename : (structFieldRef github_com.hashicorp.raft.Log go!"Type" p0 ↦{dq1} lv.Type' : IProp GF) => HlTy
    (try (irename : ("_" ∷ True : IProp GF) => Hjunk2; iclear Hjunk2))
    wp_auto
    wp_apply wp_copyBytes $$ [$Hd] as %c1 ⟨Hd, Hc1⟩
    wp_apply wp_copyBytes $$ [$Hx] as %c2 ⟨Hx, Hc2⟩
    wp_apply (wp_slice_literal (V := Entry)
      [Entry.mk lv.Index' lv.Term' lv.Type' c1 c2])
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply (wp_slice_append (V := Entry)) $$ [$Hesv $Hcap $Hsl] as %es' ⟨Hesv, Hcap, -⟩
    wp_for_post
    iframe
    ihave Hpv := Hback $$ [Hd Hx HlTy Index Term Data Extensions AppendedAt]
    · iexists lv
      iframe Hd Hx
      isplitl [HlTy Index Term Data Extensions AppendedAt]
      · iapply typedPointsto_combine _ _ _ Hln
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro; exact Hf
    iframe Hpv
    iexists (k + 1), _, _, _
    iframe
    isplitl [Hctr]
    · have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hctr]; iframe
    isplitr
    · ipureintro; omega
    have htake : vs.take (k + 1) = vs.take k ++ [v0] := by
      rw [List.take_succ, Hv0]; rfl
    rw [htake]
    iapply BigSepL2.bigSepL2_snoc.2
    iframe Hcp
    unfold entOwn
    iframe Hc1 Hc2
    ipureintro; exact Hf
  · rename_i Hc
    have hk : k = ps.length := by simp only [decide_eq_true_eq] at Hc; word
    have htake : vs.take k = vs := List.take_of_length_le (by omega)
    rw [htake] at *
    wp_auto
    wp_apply wp_toHeader $$ [$Hid $Had] as %i %d ⟨Hid, Had, Hi, Hd⟩
    wp_apply wp_copyBytes $$ [$Hld] as %c ⟨Hld, Hc'⟩
    irename «$r0» => Hp
    iapply HΦ
    iframe Hid Had Hld
    isplitl [RPCHeader aTerm Leader PrevLogEntry PrevLogTerm Entries LeaderCommitIndex]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    isplitl [Hps Hpv]
    · iexists ps; iframe
    iexists i, d, c, esv
    iframe
    unfold entsOwn
    iexists cp
    iframe

end proof

end Perennial
