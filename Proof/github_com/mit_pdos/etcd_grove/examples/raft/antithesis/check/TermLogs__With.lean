/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `TermLogs.With`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__With
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

section pure
omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx

/-- `TermFn.with` below every point: appended. -/
theorem TermLogsWith_below {α : Type} (l : TermFn α) (t : Int) (v : α) (h : ∀ p ∈ l, p.1 < t) :
    l.with t v = l ++ [(t, v)] := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    have hp := h p (List.mem_cons_self ..)
    simp only [TermFn.with, show ¬ t ≤ p.1 by omega, ite_false, List.cons_append]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- The first point at or above `t`. -/
theorem TermLogsWith_at {α : Type} (l : TermFn α) (q : Int × α) (t : Int) (v : α) (h : ∀ p ∈ l, p.1 < t)
    (hq : t ≤ q.1) : (l ++ [q]).with t v = l ++ (t, v) :: (if q.1 = t then [] else [q]) := by
  induction l with
  | nil => simp [TermFn.with, hq]
  | cons p ps ih =>
    have hp := h p (List.mem_cons_self ..)
    simp only [List.cons_append, TermFn.with, show ¬ t ≤ p.1 by omega, ite_false]
    rw [ih (fun r hr => h r (List.mem_cons_of_mem _ hr))]

/-- After the point at or above `t`: points appended as they are. -/
theorem TermLogsWith_after {α : Type} (l : TermFn α) (q : Int × α) (t : Int) (v : α) (h : ∃ p ∈ l, t ≤ p.1) :
    (l ++ [q]).with t v = l.with t v ++ [q] := by
  induction l with
  | nil => simp at h
  | cons p ps ih =>
    simp only [List.cons_append, TermFn.with]
    by_cases hp : t ≤ p.1
    · simp only [hp, ite_true]
      split <;> simp
    · simp only [hp, ite_false, List.cons_append]
      obtain ⟨r, hr, hrt⟩ := h
      rcases List.mem_cons.1 hr with rfl | hr'
      · exact absurd hrt hp
      · rw [ih ⟨r, hr', hrt⟩]

end pure

theorem TermLogs.With.wp_proof : TermLogs.With.spec (GF := GF) (hG := hG) := by
  intro sl f t vl v
  wp_start as ⟨#Hs, #Hv, %Hb⟩
  iunfold termLogsRO at Hs
  icases Hs with ⟨%gs, #Hgs, #Hb⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
  iapply wp_fupd
  wp_auto
  wp_apply (wp_slice_make3 (V := G.TermLog) (W64 0) (sl.len + W64 1) ⟨by word, by word⟩) as %o ⟨Ho, Hocap, -⟩
  try wp_auto
  ihave IH : iprop(∃ (n : w64) (y : G.TermLog) (d : Bool) (osl : GoSlice) (L : List G.TermLog) (O : TermFn (List Entry)),
      "i" ∷ i_ptr ↦ n ∗ "p" ∷ p_ptr ↦ y ∗ "done" ∷ done_ptr ↦ d ∗ "out" ∷ out_ptr ↦ osl ∗
      "Hout" ∷ osl ↦* L ∗ "Hcap" ∷ ownSliceCap G.TermLog osl (DFrac.own 1) ∗
      "#HL" ∷ ([∗list] g;p ∈ L;O, ⌜sint.Z g.T' = p.1⌝ ∗ logRO g.L' p.2) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        ((d = false ∧ O = f.take (sint.nat n) ∧ ∀ q ∈ f.take (sint.nat n), q.1 < sint.Z t) ∨
         (d = true ∧ (∃ q ∈ f.take (sint.nat n), sint.Z t ≤ q.1) ∧ O = TermFn.with (f.take (sint.nat n)) (sint.Z t) v))⌝)
      $$ [i p done out Ho Hocap]
  · iexists _, _, _, _, _, []
    iframe
    isplitr
    · simp only [List.replicate_zero]
      iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
    ipureintro
    refine ⟨?_, ?_, ?_⟩
    · word
    · word
    · left; rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IH
  obtain ⟨hn0, hn1, Hd⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < f.length := by rw [← Hl, Hlen.1]; word
    ihave ⟨%y0, %Hy, %HT, #HL0⟩ := bigSepL2_at _ gs f (sint.nat n) Hlt $$ Hb
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) gs DFrac.discard y0 hn0 $$ [Hgs] as -
    · isplitr
      · iexact Hgs
      ipureintro; exact Hy
    try wp_auto
    obtain ⟨p0, Hp0⟩ : ∃ p, f[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hfp : f[sint.nat n]! = p0 := by simp [Hp0]
    have HT' : sint.Z y0.T' = p0.1 := by rw [HT, Hfp]
    have htake : f.take (sint.nat (n + W64 1)) = f.take (sint.nat n) ++ [p0] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hp0]; simp
    have Hnext : 0 ≤ sint.Z (n + W64 1) ∧ sint.Z (n + W64 1) ≤ sint.Z sl.len := by
      constructor <;> word
    rcases Hd with ⟨rfl, rfl, hbelow⟩ | ⟨rfl, hex, rfl⟩
    · try wp_auto
      wp_if_destruct
      · -- `t <= p.T`: the new point
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl1 ⟨Hsl1, -⟩
        wp_apply wp_slice_append $$ [Hout Hcap Hsl1] as %s1 ⟨Hs1, Hcap1, -⟩
        · iframe
        try wp_auto
        have hex : ∃ q ∈ f.take (sint.nat (n + W64 1)), sint.Z t ≤ q.1 :=
          ⟨p0, by rw [htake]; exact List.mem_append_right _ (List.mem_singleton_self _), HT' ▸ Hif⟩
        have hwith := TermLogsWith_at (f.take (sint.nat n)) p0 (sint.Z t) v hbelow (HT' ▸ Hif)
        rw [← htake] at hwith
        wp_if_destruct
        · -- `p.T == t`: continue
          wp_for_post
          iframe
          iexists _, _, _, _, _, (List.take (sint.nat n) f ++ [(sint.Z y0.T', v)])
          iframe
          isplitr
          · iapply BigSepL2.bigSepL2_snoc.2
            iframe HL
            isplitr
            · ipureintro; rfl
            iexact Hv
          ipureintro
          refine ⟨?_, ?_, ?_⟩
          · exact Hnext.1
          · exact Hnext.2
          · right
            refine ⟨rfl, hex, ?_⟩
            rw [hwith, ite_eq_left_of_eq_true _ _ (eq_true HT'.symm)]
        · wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          wp_apply wp_slice_append $$ [Hs1 Hcap1 Hsl2] as %s2 ⟨Hs2, Hcap2, -⟩
          · iframe
          try wp_auto
          wp_for_post
          iframe
          iexists _, _, _, _, _, (List.take (sint.nat n) f ++ [(sint.Z t, v)] ++ [p0])
          iframe
          isplitr
          · iapply BigSepL2.bigSepL2_snoc.2
            isplitl
            · iapply BigSepL2.bigSepL2_snoc.2
              iframe HL
              isplitr
              · ipureintro; rfl
              iexact Hv
            isplitr
            · ipureintro; exact HT'
            rw [← Hfp]; iexact HL0
          ipureintro
          refine ⟨?_, ?_, ?_⟩
          · exact Hnext.1
          · exact Hnext.2
          · right
            refine ⟨rfl, hex, ?_⟩
            have hne : ¬ p0.1 = sint.Z t := by
              intro h; apply Hif; rw [← HT'] at h; exact BitVec.toInt_inj.mp h
            rw [hwith]; simp [hne]
      · -- `p.T < t`
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl1 ⟨Hsl1, -⟩
        wp_apply wp_slice_append $$ [Hout Hcap Hsl1] as %s1 ⟨Hs1, Hcap1, -⟩
        · iframe
        try wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _, _, _
        iframe
        isplitr
        · iapply BigSepL2.bigSepL2_snoc.2
          iframe HL
          isplitr
          · ipureintro; exact HT'
          rw [← Hfp]; iexact HL0
        ipureintro
        refine ⟨?_, ?_, ?_⟩
        · exact Hnext.1
        · exact Hnext.2
        · left
          refine ⟨rfl, htake.symm, ?_⟩
          rw [htake]; intro q hq
          rcases List.mem_append.1 hq with hq | hq
          · exact hbelow q hq
          · rw [List.mem_singleton.1 hq, ← HT']; omega
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
      iexists _, _, _, _, _, _
      iframe
      isplitr
      · iapply BigSepL2.bigSepL2_snoc.2
        iframe HL
        isplitr
        · ipureintro; exact HT'
        rw [← Hfp]; iexact HL0
      ipureintro
      refine ⟨?_, ?_, ?_⟩
      · exact Hnext.1
      · exact Hnext.2
      · right
        refine ⟨rfl, ?_, ?_⟩
        · obtain ⟨q, hq, hqt⟩ := hex
          exact ⟨q, by rw [htake]; exact List.mem_append_left _ hq, hqt⟩
        · rw [htake, TermLogsWith_after _ _ _ _ hex]
  · try wp_auto
    have hnx : sint.nat n = f.length := by rw [← Hl, Hlen.1]; word
    rw [hnx, List.take_length] at Hd
    rcases Hd with ⟨rfl, hO, hbelow⟩ | ⟨rfl, -, hO⟩
    · try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [Hout Hcap Hsl1] as %s1 ⟨Hs1, Hcap1, -⟩
      · iframe
      try wp_auto
      imod ownSlice_persist $$ Hs1 with #Hs1
      imodintro
      iapply HΦ
      iunfold termLogsRO
      iexists _
      iframe Hs1
      rw [TermLogsWith_below f _ v hbelow, ← hO]
      iapply BigSepL2.bigSepL2_snoc.2
      iframe HL
      isplitr
      · ipureintro; rfl
      iexact Hv
    · try wp_auto
      imod ownSlice_persist $$ Hout with #Hout
      imodintro
      iapply HΦ
      iunfold termLogsRO
      iexists _
      rw [← hO]
      iframe Hout HL

end proof

end AntCheck
end EtcdGrove
end Perennial
