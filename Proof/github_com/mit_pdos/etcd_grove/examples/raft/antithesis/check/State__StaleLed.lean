/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the proof of `State.StaleLed` (B 709).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__StaleLed
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Over
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem State.StaleLed.wp_proof
    (wp_Over : State.Over.spec (GF := GF) (hG := hG)) :
    State.StaleLed.spec (GF := GF) (hG := hG) := by
  intro p s
  wp_start as #Hs
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  ihave #Hb := HLedLog
  iunfold termLogsRO at Hb
  icases Hb with ⟨%gs, #Hgs, #Hb⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
  iapply wp_fupd
  wp_auto
  ihave #Hnil := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := w64) (GF := GF)
  ihave IH : iprop(∃ (k : w64) (y : G.TermLog) (osl : GoSlice) (L : List w64),
      "i" ∷ i_ptr ↦ k ∗ "p" ∷ p_ptr ↦ y ∗ "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* L ∗
      "Hcap" ∷ ownSliceCap w64 osl (DFrac.own 1) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z g.LedLog'.len ∧
        L.map sint.Z = ((s.ledLog.take (sint.nat k)).filter (fun p => s.over p.1)).map Prod.fst⌝) $$ [i p out Hcap0]
  · iexists _, _, slice.nil, []
    iframe
    isplitr
    · iexact Hnil
    isplitr
    · iexact Hcap0
    ipureintro
    exact ⟨Int.le_refl _, Hlen.2, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hk0, hk1, hkL⟩ := Hk
  wp_if_destruct
  · have Hlt : sint.nat k < s.ledLog.length := by rw [← Hl, Hlen.1]; word
    ihave ⟨%y0, %Hy, %HT, #HL0⟩ := bigSepL2_at _ gs s.ledLog (sint.nat k) Hlt $$ Hb
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z g.LedLog'.len from ⟨hk0, Hif⟩))]
    wp_apply wp_load_slice_index g.LedLog' (sint.Z k) gs DFrac.discard y0 hk0 $$ [Hgs] as -
    · isplitr
      · iexact Hgs
      ipureintro; exact Hy
    try wp_auto
    obtain ⟨p0, Hp0⟩ : ∃ p, s.ledLog[sint.nat k]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hfp : s.ledLog[sint.nat k]! = p0 := by simp [Hp0]
    have HT' : sint.Z y0.T' = p0.1 := by rw [HT, Hfp]
    have htake : s.ledLog.take (sint.nat (k + W64 1)) = s.ledLog.take (sint.nat k) ++ [p0] := by
      rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.take_add_one, Hp0]; simp
    have Hnext : 0 ≤ sint.Z (k + W64 1) ∧ sint.Z (k + W64 1) ≤ sint.Z g.LedLog'.len := by
      constructor <;> word
    wp_apply wp_Over p s y0.T' $$ [Hs]
    · iexact Hs
    rw [HT']
    cases hy : s.over p0.1
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨Hnext.1, Hnext.2, ?_⟩
      rw [htake, List.filter_append]
      simp [hy, hkL]
    · try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [Hout Hcap Hsl1] as %s1 ⟨Hs1, Hcap1, -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨Hnext.1, Hnext.2, ?_⟩
      rw [htake, List.filter_append]
      simp [hy, hkL, HT']
  · have hkx : sint.nat k = s.ledLog.length := by rw [← Hl, Hlen.1]; word
    rw [hkx, List.take_length] at hkL
    try wp_auto
    imod ownSlice_persist $$ Hout with #Hout
    imodintro
    iapply HΦ
    iunfold intsRO
    iexists L
    iframe Hout
    ipureintro; exact hkL

end proof

end AntCheck
end EtcdGrove
end Perennial
