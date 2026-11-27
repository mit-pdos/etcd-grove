/-
The proof of `rpctransport.AppendReqBound`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.AppendReqBound
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.BytesBound
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.hdrBound

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.AppendReqBound.wp_proof
    (wp_BytesBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.BytesBound.spec (GF := GF) (hG := hG))
    (wp_hdrBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.hdrBound.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.AppendReqBound.spec (GF := GF) (hG := hG) := by
  intro a dq w dq1 id ad ld vs
  wp_start as ⟨Ha, Hid, Had, Hld, Hents⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ha
  iStructNamed Ha
  irename Term => aTerm
  irename : ("_" ∷ True : IProp GF) => Hjunk
  iclear Hjunk
  unfold entsOwn
  icases Hents with ⟨%es, Hes, Hev⟩
  ihave %Hesl := ownSlice_len _ _ _ $$ Hes
  ihave %Hvl := BigSepL2.bigSepL2_length $$ Hev
  wp_auto
  wp_apply wp_hdrBound $$ [$Hdr $Hid $Had] as %r1 ⟨%Hr1, Hdr, Hid, Had⟩
  wp_apply wp_BytesBound $$ [$Hld] as %r2 ⟨%Hr2, Hld⟩
  have b1 := bytesBoundN_le ld.length
  have hh : hdrBoundN id ad ≤ 16 + 2 * (17 + 8 * 2 ^ 30) := by
    unfold hdrBoundN; have := bytesBoundN_le id.length; have := bytesBoundN_le ad.length; omega
  have h128 : uint.nat (W64 128) = 128 := by rfl
  have h64 : uint.nat (W64 64) = 64 := by rfl
  have hm0 : uint.nat (W64 128 + r1 + r2 + W64 64) = 128 + hdrBoundN id ad + bytesBoundN ld.length + 64 := by
    rw [w64_add_nat _ _ (by rw [w64_add_nat _ _ (by rw [w64_add_nat _ _ (by omega)]; omega),
      w64_add_nat _ _ (by omega)]; omega)]
    rw [w64_add_nat _ _ (by rw [w64_add_nat _ _ (by omega)]; omega), w64_add_nat _ _ (by omega)]
    omega
  ihave IH : (∃ (k : Nat) (nv : w64) (ev : Entry),
      "Hctr" ∷ i_ptr ↦ W64 k ∗ "n" ∷ n_ptr ↦ nv ∗ "e" ∷ e_ptr ↦ ev ∗
      "%Hk" ∷ ⌜k ≤ es.length ∧ aeBoundN id ad ld vs = entsBoundN (uint.nat nv) (vs.drop k) ∧
        uint.nat nv ≤ 2 ^ 36⌝ : IProp GF) $$ [i n e]
  · iexists 0, (W64 128 + r1 + r2 + W64 64), _
    iframe
    ipureintro
    refine ⟨by omega, ?_, ?_⟩
    · rw [hm0]; rfl
    · rw [hm0]; omega
  wp_for IH
  split
  · rename_i Hc
    obtain ⟨Hk1, Hk2, Hk3⟩ := Hk
    have hk : k < es.length := by simp only [decide_eq_true_eq] at Hc; word
    obtain ⟨ev0, Hev0⟩ : ∃ x, es[k]? = some x := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨v0, Hv0⟩ : ∃ x, vs[k]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_auto
    rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply (wp_load_slice_index w.Entries' (sint.Z (W64 k)) es dq1 ev0 (by word)) $$ [$Hes] with Hes
    · ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact Hev0
    ihave %Hen := typedPointsto_not_null _ _ _ $$ e
    iStructNamed e
    irename : (structFieldRef Entry go!"Type" e_ptr ↦ ev0.Type' : IProp GF) => HeTy
    irename : ("_" ∷ True : IProp GF) => Hjunk2
    iclear Hjunk2
    have Hdrop : List.drop k vs = v0 :: List.drop (k + 1) vs := by
      rw [List.drop_eq_getElem_cons (by omega)]
      congr
      exact (List.getElem_eq_iff _).mpr Hv0
    have hM : uint.Z (W64 1073741824) = 1073741824 := by word
    wp_if_destruct
    · wp_for_post
      iapply HΦ
      isplitr
      · ipureintro
        rw [Hk2, Hdrop, entsBoundN_cons, if_pos (by unfold maxReqN; word)]
      iframe Hid Had Hld
      isplitl [Hdr aTerm Leader PrevLogEntry PrevLogTerm Entries LeaderCommitIndex]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      iexists es
      iframe
    · ihave Hacc := BigSepL2.bigSepL2_lookup_acc Hev0 Hv0 $$ Hev
      icases Hacc with ⟨Hone, Hback⟩
      unfold entOwn
      icases Hone with ⟨%Hf, Hd, Hx⟩
      wp_apply wp_BytesBound $$ [$Hd] as %r3 ⟨%Hr3, Hd⟩
      wp_apply wp_BytesBound $$ [$Hx] as %r4 ⟨%Hr4, Hx⟩
      have b3 := bytesBoundN_le v0.data.length
      have b4 := bytesBoundN_le v0.ext.length
      have hnv : uint.nat nv ≤ 2 ^ 30 := by word
      wp_for_post
      iframe
      ihave Hev := Hback $$ [Hd Hx]
      · iframe Hd Hx; ipureintro; exact Hf
      iframe Hev
      iexists (k + 1), _, _
      iframe
      isplitl [Hctr]
      · have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
        rw [hctr]; iframe
      isplitl [Index Term HeTy Data Extensions]
      · iapply typedPointsto_combine _ _ _ Hen
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro
      have hsum : uint.nat (nv + W64 64 + r3 + r4) =
          uint.nat nv + 64 + bytesBoundN v0.data.length + bytesBoundN v0.ext.length := by
        rw [w64_add_nat _ _ (by rw [w64_add_nat _ _ (by rw [w64_add_nat _ _ (by word)]; word),
          w64_add_nat _ _ (by word)]; word)]
        rw [w64_add_nat _ _ (by rw [w64_add_nat _ _ (by word)]; word), w64_add_nat _ _ (by word)]
        word
      refine ⟨by omega, ?_, ?_⟩
      · rw [hsum, Hk2, Hdrop, entsBoundN_cons, if_neg (by unfold maxReqN; omega)]
      · rw [hsum]; omega
  · rename_i Hc
    obtain ⟨Hk1, Hk2, Hk3⟩ := Hk
    have hk : k = es.length := by simp only [decide_eq_true_eq] at Hc; word
    have hdrop : List.drop k vs = [] := by rw [List.drop_eq_nil_iff]; omega
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro
      rw [Hk2, hdrop]; rfl
    iframe Hid Had Hld
    isplitl [Hdr aTerm Leader PrevLogEntry PrevLogTerm Entries LeaderCommitIndex]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iexists es
    iframe

end proof

end Perennial
