/-
The proof of `rpctransport.fromAppendReq`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromAppendReq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromHeader

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromAppendReq.wp_proof
    (wp_copyBytes : github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes.spec (GF := GF) (hG := hG))
    (wp_fromHeader : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromHeader.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromAppendReq.spec (GF := GF) (hG := hG) := by
  intro a dq w dq1 id ad ld vs
  wp_start as ⟨Ha, Hid, Had, Hld, Hents⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ha
  iStructNamed Ha
  irename Term => aTerm
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  unfold entsOwn
  icases Hents with ⟨%es0, Hes0, Hev⟩
  ihave %Hesl := ownSlice_len _ _ _ $$ Hes0
  ihave %Hvl := BigSepL2.bigSepL2_length $$ Hev
  wp_auto
  ihave IH : (∃ (k : Nat) (esv : GoSlice) (cp : List Loc) (ev : Entry),
      "Hctr" ∷ i_ptr ↦ W64 k ∗ "es" ∷ es_ptr ↦ esv ∗ "e" ∷ e_ptr ↦ ev ∗
      "Hesv" ∷ esv ↦* cp ∗ "Hcap" ∷ ownSliceCap Loc esv (DFrac.own 1) ∗
      "%Hk" ∷ ⌜k ≤ es0.length⌝ ∗
      "Hcp" ∷ ([∗list] q;v ∈ cp;(vs.take k), logOwn q (DFrac.own 1) v) : IProp GF) $$ [i es e]
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
    have hk : k < es0.length := by simp only [decide_eq_true_eq] at Hc; word
    obtain ⟨e0, He0⟩ : ∃ x, es0[k]? = some x := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨v0, Hv0⟩ : ∃ x, vs[k]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_auto
    rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply (wp_load_slice_index w.Entries' (sint.Z (W64 k)) es0 dq1 e0 (by word)) $$ [$Hes0] with Hes0
    · ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact He0
    ihave Hacc := BigSepL2.bigSepL2_lookup_acc He0 Hv0 $$ Hev
    icases Hacc with ⟨Hone, Hback⟩
    unfold entOwn
    icases Hone with ⟨%Hf, Hd, Hx⟩
    ihave %Hen := typedPointsto_not_null _ _ _ $$ e
    iStructNamed e
    irename : (structFieldRef Entry go!"Type" e_ptr ↦ e0.Type' : IProp GF) => HeTy
    (try (irename : ("_" ∷ True : IProp GF) => Hjunk2; iclear Hjunk2))
    (try wp_auto)
    wp_apply wp_copyBytes $$ [$Hd] as %c1 ⟨Hd, Hc1⟩
    wp_apply wp_copyBytes $$ [$Hx] as %c2 ⟨Hx, Hc2⟩
    irename «$sl0» => Hl
    wp_apply (wp_slice_literal (V := Loc) [«$sl0_ptr»])
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply (wp_slice_append (V := Loc)) $$ [$Hesv $Hcap $Hsl] as %es' ⟨Hesv, Hcap, -⟩
    wp_for_post
    iframe
    ihave Hev := Hback $$ [Hd Hx]
    · iframe Hd Hx; ipureintro; exact Hf
    iframe Hev
    iexists (k + 1), _, _, _
    iframe
    isplitl [Hctr]
    · have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hctr]; iframe
    isplitl [HeTy Index Term Data Extensions]
    · iapply typedPointsto_combine _ _ _ Hen
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    isplitr
    · ipureintro; omega
    have htake : vs.take (k + 1) = vs.take k ++ [v0] := by
      rw [List.take_succ, Hv0]; rfl
    rw [htake]
    iapply BigSepL2.bigSepL2_snoc.2
    iframe Hcp
    unfold logOwn logOwnV
    iexists _
    iframe Hl Hc1 Hc2
    ipureintro; exact Hf
  · rename_i Hc
    have hk : k = es0.length := by simp only [decide_eq_true_eq] at Hc; word
    have htake : vs.take k = vs := List.take_of_length_le (by omega)
    rw [htake] at *
    wp_auto
    wp_apply wp_fromHeader $$ [$Hid $Had] as %i %d ⟨Hid, Had, Hi, Hd⟩
    wp_apply wp_copyBytes $$ [$Hld] as %c ⟨Hld, Hc'⟩
    irename «$r0» => Hp
    iapply HΦ
    iframe Hid Had Hld
    isplitl [Hdr aTerm Leader PrevLogEntry PrevLogTerm Entries LeaderCommitIndex]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    isplitl [Hes0 Hev]
    · iexists es0; iframe
    iexists i, d, c, esv
    iframe
    unfold logsOwn
    iexists cp
    iframe

end proof

end Perennial
