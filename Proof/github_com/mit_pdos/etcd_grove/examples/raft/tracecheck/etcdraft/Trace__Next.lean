/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__Next`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__Next
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__nonReceive
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__receive

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Trace.Next.wp_proof
    (wp_nonReceive : Trace.nonReceive.spec (GF := GF) (hG := hG))
    (wp_receive : Trace.receive.spec (GF := GF) (hG := hG)) :
    Trace.Next.spec (GF := GF) (hG := hG) := by
  intro t tr g ts tss
  wp_start as ⟨#Ht, #Hts, %Hok, %Hnx⟩
  obtain ⟨Hl1, Hsv, Hact, Hmsgs, Hsc⟩ := Hok
  open_ts
  open_trace
  have hlenb := Hv.len_lt
  have hbl := Hv.bootstrap_length
  wp_auto
  ihave %Hbl := ownSlice_len $$ Hboot
  by_cases hgt : tr.len < ts.l
  · rw [decide_eq_true (show sint.Z gt.lines'.len < sint.Z g.L' by rw [Hg.1, ← hlenZ]; exact_mod_cast hgt)]
    wp_auto
    have : tss = [] := by
      simp [Trace.next, hgt, Pure.pure, Except.pure] at Hnx; exact Hnx
    subst this
    iapply HΦ
    iunfold tstatesOut
    iexists []
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
  rw [decide_eq_false (show ¬ sint.Z gt.lines'.len < sint.Z g.L' by rw [Hg.1, ← hlenZ]; exact_mod_cast hgt)]
  have hle : ts.l ≤ tr.len := by omega
  have hlz : sint.Z (g.L' + W64 1) = (ts.l : Int) + 1 := by
    have : (ts.l : Int) + 1 < 2 ^ 63 := by unfold numBound at hlenb; omega
    rw [← Hg.1] at this ⊢; word
  have hl1z : sint.Z (g.L' - W64 1) = (ts.l : Int) - 1 := by
    have : (ts.l : Int) + 1 < 2 ^ 63 := by unfold numBound at hlenb; omega
    rw [← Hg.1] at this ⊢; word
  have hbi : 0 ≤ sint.Z (g.L' - W64 1) ∧ sint.Z (g.L' - W64 1) < sint.Z gt.bootstrap'.len := by
    rw [hl1z]
    have : (tr.bootstrap.length : Int) = sint.Z gt.bootstrap'.len := by rw [Hbl.1]; word
    rw [← this, hbl]; omega
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true hbi)]
  obtain ⟨bv, hbv⟩ : ∃ bv, tr.bootstrap[(sint.Z (g.L' - W64 1)).toNat]? = some bv :=
    ⟨_, List.getElem?_eq_getElem (by rw [hbl, hl1z]; omega)⟩
  wp_apply wp_load_slice_index _ (sint.Z (g.L' - W64 1)) tr.bootstrap DFrac.discard bv hbi.1 $$ [Hboot] as -
  · isplitr
    · iexact Hboot
    ipureintro; exact hbv
  have hbv' : tr.bootstrap.getD (ts.l - 1) false = bv := by
    rw [List.getD_eq_getElem?_getD, show ts.l - 1 = (sint.Z (g.L' - W64 1)).toNat by omega, hbv]; rfl
  try wp_auto
  have hl0 : ¬ (ts.l == 0) = true := by simp; omega
  have hbv2 : (tr.bootstrap[ts.l - 1]?).getD false = bv := by rw [← List.getD_eq_getElem?_getD]; exact hbv'
  cases bv
  · obtain ⟨nr, hnr, rv, hrv, htss⟩ : ∃ nr, tr.nonReceive ts = .ok nr ∧ ∃ rv, tr.receive ts = .ok rv ∧
        tss = nr.map (fun s2 => ({ s := s2, l := ts.l + 1, pl := ts.l } : TState)) ++ rv := by
      unfold Trace.next at Hnx
      simp only [hbv', show ¬ (tr.len < ts.l) from hgt] at Hnx
      cases hnr : tr.nonReceive ts with
      | error e => simp [hnr, hl0, Bind.bind, Except.bind] at Hnx
      | ok nr =>
        cases hrv : tr.receive ts with
        | error e => simp [hnr, hrv, hl0, Bind.bind, Except.bind] at Hnx
        | ok rv =>
          simp [hnr, hrv, hl0, Bind.bind, Except.bind, Pure.pure, Except.pure] at Hnx
          exact ⟨nr, rfl, rv, rfl, Hnx.symm⟩
    have hsc := Hsc hle hbv'
    try wp_auto
    wp_apply wp_nonReceive t tr g ts nr $$ [Ht Hts] as %nsl Hn
    · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle, Hsv, Hact, hsc, hnr⟩
    iunfold statesOut at Hn
    icases Hn with ⟨%nqs, Hnq, Hncap, #Hnl⟩
    ihave %Hnql := ownSlice_len $$ Hnq
    ihave %Hnll := BigSepL2.bigSepL2_length $$ Hnl
    try wp_auto
    ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List G.TState) $$ []
    · iapply ownSlice_nil
    ihave Hcap0 : ownSliceCap G.TState (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    ihave IH : iprop(∃ (n : w64) (x : Loc) (osl : GoSlice) (gsl : List G.TState),
        "i" ∷ i_ptr ↦ n ∗ "s2" ∷ s2_ptr ↦ x ∗ "out" ∷ out_ptr ↦ osl ∗ "Hnq" ∷ nsl ↦* nqs ∗
        "Hout" ∷ osl ↦* gsl ∗ "Hcap" ∷ ownSliceCap G.TState osl (DFrac.own 1) ∗
        "Hacc" ∷ ([∗list] g';a ∈ gsl;(nr.take (sint.nat n)).map
          (fun s2 => ({ s := s2, l := ts.l + 1, pl := ts.l } : TState)), tstateRO (GF := GF) g' a) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z nsl.len⌝) $$ [i s2 out Hnq Hnil Hcap0]
    · iexists _, _, _, []
      iframe
      isplitr
      · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil]
        iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
      ipureintro; constructor <;> word
    wp_for IH
    obtain ⟨hn0, hn1⟩ := Hn
    wp_if_destruct
    · have Hlt : sint.nat n < nqs.length := by rw [Hnql.1]; word
      obtain ⟨q2, Hq2⟩ : ∃ q2, nqs[sint.nat n]? = some q2 := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨s2v, Hs2v⟩ : ∃ s2v, nr[sint.nat n]? = some s2v :=
        ⟨_, List.getElem?_eq_getElem (Hnll ▸ Hlt)⟩
      ihave #Hq2s := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => stateRO (GF := GF) a b) Hq2 Hs2v $$ Hnl
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z nsl.len from ⟨hn0, Hif⟩))]
      wp_apply wp_load_slice_index _ (sint.Z n) nqs (DFrac.own 1) q2 hn0 $$ [Hnq] as Hnq
      · iframe Hnq; ipureintro; exact Hq2
      try wp_auto
      wp_apply wp_slice_literal [({ S' := q2, L' := g.L' + W64 1, PL' := g.L' } : G.TState)]
      isplitr
      · ipureintro; rfl
      iintro %sl0 ⟨Hsl0, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [Hout Hcap Hsl0] as %s3 ⟨Hs3, Hcap3, -⟩
      · iframe
      try wp_auto
      have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      ihave Hacc' : ([∗list] g';a ∈ gsl ++ [({ S' := q2, L' := g.L' + W64 1, PL' := g.L' } : G.TState)];
          (nr.take (sint.nat (n + W64 1))).map (fun s2 => ({ s := s2, l := ts.l + 1, pl := ts.l } : TState)),
          tstateRO (GF := GF) g' a) $$ [Hacc]
      · rw [hn1', List.take_add_one, Hs2v, Option.toList_some, List.map_append, List.map_cons, List.map_nil]
        iapply BigSepL2.bigSepL2_snoc.2
        isplitl [Hacc]
        · iexact Hacc
        iunfold tstateRO
        isplitr
        · iexact Hq2s
        ipureintro; exact ⟨hlz, Hg.1⟩
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro; constructor <;> word
    · try wp_auto
      have hnx : sint.nat n = nr.length := by rw [← Hnll, Hnql.1]; word
      rw [hnx, List.take_length]
      wp_apply wp_receive t tr g ts $$ [Ht Hts] as %rsl Hr
      · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle, Hact.2.2.1, Hmsgs.1, Hmsgs.2⟩
      rw [hrv]
      iunfold tstatesOut at Hr
      icases Hr with ⟨%rgs, Hrg, -, Hrl⟩
      ihave %Hal := BigSepL2.bigSepL2_length $$ Hacc
      wp_apply wp_slice_append $$ [Hout Hcap Hrg] as %s3 ⟨Hs3, Hcap3, -⟩
      · iframe
      try wp_auto
      iapply HΦ
      rw [htss]
      iunfold tstatesOut
      iexists gsl ++ rgs
      iframe
  · have : tss = [{ s := ts.s, l := ts.l + 1, pl := ts.l }] := by
      unfold Trace.next at Hnx
      simp [hbv2, hgt, hl0, Pure.pure, Except.pure] at Hnx; exact Hnx.symm
    subst this
    try wp_auto
    wp_apply wp_slice_literal [({ S' := g.S', L' := g.L' + W64 1, PL' := g.L' } : G.TState)]
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, Hcap0⟩
    try wp_auto
    iapply HΦ
    iunfold tstatesOut
    iexists [({ S' := g.S', L' := g.L' + W64 1, PL' := g.L' } : G.TState)]
    iframe
    iapply BigSepL2.bigSepL2_cons.2
    isplitr
    · iunfold tstateRO
      isplitr
      · iexact Hst
      ipureintro; exact ⟨hlz, Hg.1⟩
    iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
