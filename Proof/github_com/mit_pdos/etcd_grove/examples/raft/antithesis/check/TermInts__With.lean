/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `TermInts.With`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts__With
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
theorem TermIntsWith_below {α : Type} (l : TermFn α) (t : Int) (v : α) (h : ∀ p ∈ l, p.1 < t) :
    l.with t v = l ++ [(t, v)] := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    have hp := h p (List.mem_cons_self ..)
    simp only [TermFn.with, show ¬ t ≤ p.1 by omega, ite_false, List.cons_append]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- The first point at or above `t`. -/
theorem TermIntsWith_at {α : Type} (l : TermFn α) (q : Int × α) (t : Int) (v : α) (h : ∀ p ∈ l, p.1 < t)
    (hq : t ≤ q.1) : (l ++ [q]).with t v = l ++ (t, v) :: (if q.1 = t then [] else [q]) := by
  induction l with
  | nil => simp [TermFn.with, hq]
  | cons p ps ih =>
    have hp := h p (List.mem_cons_self ..)
    simp only [List.cons_append, TermFn.with, show ¬ t ≤ p.1 by omega, ite_false]
    rw [ih (fun r hr => h r (List.mem_cons_of_mem _ hr))]

/-- After the point at or above `t`: points appended as they are. -/
theorem TermIntsWith_after {α : Type} (l : TermFn α) (q : Int × α) (t : Int) (v : α) (h : ∃ p ∈ l, t ≤ p.1) :
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

omit [GooseSemantics] [GooseInterp] go_gctx in
/-- The relation of `termIntsRO`. -/
abbrev TermIntsWith_R (g : G.TermInt) (p : Int × Int) : Prop := sint.Z g.T' = p.1 ∧ sint.Z g.V' = p.2

theorem TermInts.With.wp_proof : TermInts.With.spec (GF := GF) (hG := hG) := by
  intro sl f t vw
  wp_start as ⟨#Hs, %Hb⟩
  iunfold termIntsRO at Hs
  icases Hs with ⟨%gs, #Hgs, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  have Hl := Hrel.length_eq
  iapply wp_fupd
  wp_auto
  wp_apply (wp_slice_make3 (V := G.TermInt) (W64 0) (sl.len + W64 1) ⟨by word, by word⟩) as %o ⟨Ho, Hocap, -⟩
  try wp_auto
  ihave IH : iprop(∃ (n : w64) (y : G.TermInt) (d : Bool) (osl : GoSlice) (L : List G.TermInt) (O : TermFn Int),
      "i" ∷ i_ptr ↦ n ∗ "p" ∷ p_ptr ↦ y ∗ "done" ∷ done_ptr ↦ d ∗ "out" ∷ out_ptr ↦ osl ∗
      "Hout" ∷ osl ↦* L ∗ "Hcap" ∷ ownSliceCap G.TermInt osl (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ List.Forall₂ TermIntsWith_R L O ∧
        ((d = false ∧ O = f.take (sint.nat n) ∧ ∀ q ∈ f.take (sint.nat n), q.1 < sint.Z t) ∨
         (d = true ∧ (∃ q ∈ f.take (sint.nat n), sint.Z t ≤ q.1) ∧
           O = TermFn.with (f.take (sint.nat n)) (sint.Z t) (sint.Z vw)))⌝)
      $$ [i p done out Ho Hocap]
  · iexists _, _, _, _, _, []
    iframe
    ipureintro
    refine ⟨?_, ?_, ?_, ?_⟩
    · word
    · word
    · exact List.Forall₂.nil
    · left; rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IH
  obtain ⟨hn0, hn1, HL, Hd⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < f.length := by rw [← Hl, Hlen.1]; word
    obtain ⟨y0, Hy⟩ : ∃ y, gs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem (Hl ▸ Hlt)⟩
    obtain ⟨p0, Hp0⟩ : ∃ p, f[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have HTV := forall₂_getElem Hrel (sint.nat n) (Hl ▸ Hlt) Hlt
    rw [Option.some.inj ((List.getElem?_eq_getElem (Hl ▸ Hlt)).symm.trans Hy),
      Option.some.inj ((List.getElem?_eq_getElem Hlt).symm.trans Hp0)] at HTV
    have HT' : sint.Z y0.T' = p0.1 := HTV.1
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) gs DFrac.discard y0 hn0 $$ [Hgs] as -
    · isplitr
      · iexact Hgs
      ipureintro; exact Hy
    try wp_auto
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
        have hwith := TermIntsWith_at (f.take (sint.nat n)) p0 (sint.Z t) (sint.Z vw) hbelow (HT' ▸ Hif)
        rw [← htake] at hwith
        wp_if_destruct
        · -- `p.T == t`: continue
          wp_for_post
          iframe
          iexists _, _, _, _, _, (List.take (sint.nat n) f ++ [(sint.Z y0.T', sint.Z vw)])
          iframe
          ipureintro
          refine ⟨Hnext.1, Hnext.2, List.Forall₂.append HL (List.Forall₂.cons ⟨rfl, rfl⟩ List.Forall₂.nil), ?_⟩
          right
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
          iexists _, _, _, _, _, (List.take (sint.nat n) f ++ [(sint.Z t, sint.Z vw)] ++ [p0])
          iframe
          ipureintro
          refine ⟨Hnext.1, Hnext.2, List.Forall₂.append
            (List.Forall₂.append HL (List.Forall₂.cons ⟨rfl, rfl⟩ List.Forall₂.nil))
            (List.Forall₂.cons HTV List.Forall₂.nil), ?_⟩
          right
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
        ipureintro
        refine ⟨Hnext.1, Hnext.2, List.Forall₂.append HL (List.Forall₂.cons HTV List.Forall₂.nil), ?_⟩
        left
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
      ipureintro
      refine ⟨Hnext.1, Hnext.2, List.Forall₂.append HL (List.Forall₂.cons HTV List.Forall₂.nil), ?_⟩
      right
      refine ⟨rfl, ?_, ?_⟩
      · obtain ⟨q, hq, hqt⟩ := hex
        exact ⟨q, by rw [htake]; exact List.mem_append_left _ hq, hqt⟩
      · rw [htake, TermIntsWith_after _ _ _ _ hex]
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
      iunfold termIntsRO
      iexists _
      iframe Hs1
      ipureintro
      rw [TermIntsWith_below f _ _ hbelow, ← hO]
      exact List.Forall₂.append HL (List.Forall₂.cons ⟨rfl, rfl⟩ List.Forall₂.nil)
    · try wp_auto
      imod ownSlice_persist $$ Hout with #Hout
      imodintro
      iapply HΦ
      iunfold termIntsRO
      iexists _
      iframe Hout
      ipureintro
      rw [← hO]
      exact HL

end proof

end AntCheck
end EtcdGrove
end Perennial
