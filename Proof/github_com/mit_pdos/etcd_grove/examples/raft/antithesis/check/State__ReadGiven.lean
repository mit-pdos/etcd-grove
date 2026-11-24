/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the proof of `State.ReadGiven` (B 663-667).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__ReadGiven
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__ctx
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__index
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setReads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.violAdd
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ActionLaws

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

theorem State.ReadGiven.wp_proof
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_ctx : Event.ctx.spec (GF := GF) (hG := hG))
    (wp_index : Event.index.spec (GF := GF) (hG := hG))
    (wp_setReads : setReads.spec (GF := GF) (hG := hG))
    (wp_violAdd : violAdd.spec (GF := GF) (hG := hG)) :
    State.ReadGiven.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp

  obtain ⟨bb, EE, HW, HNO, -, hbb, -⟩ := HBd
  unfold numBound Event.weight at hbb
  unfold State.readGiven at Ho
  obtain ⟨kept, hkept, Ho⟩ := bind_ok Ho
  obtain ⟨stale, hstale, Ho⟩ := bind_ok Ho
  icases readsRO_at g.Reads' s.reads n ⟨Hn, by rw [HWf.len_reads]; exact Hlt⟩ $$ HReads with ⟨%rv, #Hra, #Hr⟩
  ihave #Hr' := Hr
  iunfold readRecsRO at Hr'
  icases Hr' with ⟨%items, #Hitems, %Hrel⟩
  ihave %Hil := ownSlice_len $$ Hitems
  have Hl := Hrel.length_eq
  -- the report's `ctx`, where the Lean evaluates it (a node with reads)
  obtain ⟨cx, hctx, hkept'⟩ : ∃ cx, (s.reads[sint.nat n]! ≠ [] → need ev.ctx = .ok cx) ∧
      kept = (s.reads[sint.nat n]!).filter (fun r => r.ctx != cx) := by
    cases hc : need ev.ctx with
    | ok cx =>
      refine ⟨cx, fun _ => rfl, ?_⟩
      have : (fun r : ReadRec => (do Pure.pure (r.ctx != (← need ev.ctx)) : EvalM Bool)) = (fun r : ReadRec => (Pure.pure (r.ctx != cx) : EvalM Bool)) := by
        funext r; simp [hc]
      rw [this, filterM_pure] at hkept
      cases hkept; rfl
    | error e =>
      cases hrs : s.reads[sint.nat n]! with
      | nil => rw [hrs] at hkept; cases hkept; exact ⟨[], fun h => absurd rfl h, rfl⟩
      | cons x xs =>
        rw [hrs] at hkept
        obtain ⟨e', he'⟩ := filterM_error x xs (fun r : ReadRec => (do Pure.pure (r.ctx != (← need ev.ctx)) : EvalM Bool)) e (fun y => by simp [hc])
        rw [he'] at hkept; cases hkept
  subst hkept'
  wp_auto
  wp_apply wp_load_at _ _ rv Hn $$ [Hra]
  · iexact Hra
  try wp_auto
  have hrvl : sint.nat rv.len = items.length := by rw [Hil.1]
  ihave #Hnil := ownSlice_nil (V := G.ReadRec) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := G.ReadRec) (GF := GF)
  ihave IH : iprop(∃ (k : w64) (rr : G.ReadRec) (osl : GoSlice) (L : List G.ReadRec),
      "i" ∷ i_ptr ↦ k ∗ "r" ∷ r_ptr ↦ rr ∗ "kept" ∷ kept_ptr ↦ osl ∗ "Hout" ∷ osl ↦* L ∗
      "Hcap" ∷ ownSliceCap G.ReadRec osl (DFrac.own 1) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z rv.len ∧
        L = (items.take (sint.nat k)).filter (fun g => g.Ctx' != cx)⌝) $$ [i r kept Hcap0]
  · iexists _, _, slice.nil, []
    iframe
    isplitr
    · iexact Hnil
    isplitr
    · iexact Hcap0
    ipureintro
    exact ⟨Int.le_refl _, Hil.2, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hk0, hk1, hkL⟩ := Hk
  wp_if_destruct
  · have Hlt' : sint.nat k < items.length := by rw [← hrvl]; have := sint_nat_cast hk0; have := sint_nat_cast Hil.2; omega
    obtain ⟨z, Hz⟩ : ∃ z, items[sint.nat k]? = some z := ⟨_, List.getElem?_eq_getElem Hlt'⟩
    have hrs : s.reads[sint.nat n]! ≠ [] := by
      intro h; rw [h, List.length_nil] at Hl; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rv.len from ⟨hk0, Hif⟩))]
    wp_apply wp_load_slice_index rv (sint.Z k) items DFrac.discard z hk0 $$ [Hitems] as -
    · isplitr
      · iexact Hitems
      ipureintro; rw [show (sint.Z k).toNat = sint.nat k by rfl]; exact Hz
    try wp_auto
    wp_apply wp_ctx e ev cx $$ [He]
    · iframe He; ipureintro; exact hctx hrs
    try wp_auto
    have hk1' : sint.nat (k + W64 1) = sint.nat k + 1 := by
      have := sint_add_one_lt Hif; have := sint_nat_cast hk0
      have := sint_nat_cast (k := k + W64 1) (by omega); omega
    have htake : items.take (sint.nat (k + W64 1)) = items.take (sint.nat k) ++ [z] := by
      rw [hk1', List.take_add_one, Hz]; simp
    have hk' := sint_add_one_lt Hif
    by_cases hz : z.Ctx' = cx
    · rw [decide_eq_true hz]
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨by omega, by omega, ?_⟩
      rw [htake, List.filter_append, hkL]
      simp [hz]
    · rw [decide_eq_false hz]
      try wp_auto
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
      refine ⟨by omega, by omega, ?_⟩
      rw [htake, List.filter_append, hkL]
      simp [hz]
  have hkn : sint.nat k = items.length := by rw [← hrvl]; have := sint_nat_cast hk0; have := sint_nat_cast Hil.2; omega
  rw [hkn, List.take_length] at hkL
  subst hkL
  imod ownSlice_persist $$ Hout with #Hout
  ihave #Hkept : readRecsRO osl ((s.reads[sint.nat n]!).filter (fun r => r.ctx != cx)) $$ [Hout]
  · iunfold readRecsRO; iexists _; iframe Hout; ipureintro; exact readRel_filter cx Hrel
  try wp_auto
  wp_apply wp_load_at _ _ rv Hn $$ [Hra]
  · iexact Hra
  try wp_auto
  ihave IH2 : iprop(∃ (k : w64) (rr : G.ReadRec),
      "i" ∷ i_ptr ↦ k ∗ "r" ∷ r_ptr ↦ rr ∗ "stale" ∷ stale_ptr ↦ false ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z rv.len ∧
        anyM ((s.reads[sint.nat n]!).drop (sint.nat k)) (fun r : ReadRec =>
          andM (do Pure.pure (r.ctx == (← need ev.ctx))) (do Pure.pure (decide ((← need ev.index) < r.floor))))
          = .ok stale⌝) $$ [i r stale]
  · iexists _, _
    iframe
    ipureintro
    exact ⟨Int.le_refl _, Hil.2, by rw [show sint.nat (W64 0) = 0 from rfl]; simpa using hstale⟩
  wp_for IH2
  obtain ⟨hk0, hk1, hkS⟩ := Hk
  wp_if_destruct
  · have Hlt' : sint.nat k < items.length := by rw [← hrvl]; have := sint_nat_cast hk0; have := sint_nat_cast Hil.2; omega
    have Hltr : sint.nat k < (s.reads[sint.nat n]!).length := by omega
    obtain ⟨z, Hz⟩ : ∃ z, items[sint.nat k]? = some z := ⟨_, List.getElem?_eq_getElem Hlt'⟩
    have hrz : readRel z (s.reads[sint.nat n]!)[sint.nat k] := by
      have := forall₂_getElem Hrel (sint.nat k) Hlt' Hltr
      rw [List.getElem?_eq_getElem Hlt'] at Hz; cases Hz; exact this
    have hrs : s.reads[sint.nat n]! ≠ [] := by
      intro h; rw [h, List.length_nil] at Hl; omega
    have hcx := hctx hrs
    rw [List.drop_eq_getElem_cons Hltr, anyM_cons] at hkS
    obtain ⟨c, hc, hkS⟩ := bind_ok hkS
    simp only [hcx, ok_bind, pure_ok] at hc
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rv.len from ⟨hk0, Hif⟩))]
    wp_apply wp_load_slice_index rv (sint.Z k) items DFrac.discard z hk0 $$ [Hitems] as -
    · isplitr
      · iexact Hitems
      ipureintro; rw [show (sint.Z k).toNat = sint.nat k by rfl]; exact Hz
    try wp_auto
    wp_apply wp_ctx e ev cx $$ [He]
    · iframe He; ipureintro; exact hcx
    try wp_auto
    have hk1' : sint.nat (k + W64 1) = sint.nat k + 1 := by
      have := sint_add_one_lt Hif; have := sint_nat_cast hk0
      have := sint_nat_cast (k := k + W64 1) (by omega); omega
    have hk' := sint_add_one_lt Hif
    rw [hrz.1]
    by_cases hz : (s.reads[sint.nat n]!)[sint.nat k].ctx = cx
    · rw [decide_eq_true hz]
      rw [beq_of_eq' hz, andM_ok_true] at hc
      obtain ⟨idx, hidx, hc⟩ := bind_ok hc
      simp only [pure_ok, Except.ok.injEq] at hc
      subst hc
      try wp_auto
      wp_apply wp_index e ev idx $$ [He] as %ui %Hui
      · iframe He; ipureintro; exact hidx
      try wp_auto
      rw [Hui, hrz.2]
      by_cases hlt : idx < (s.reads[sint.nat n]!)[sint.nat k].floor
      · rw [decide_eq_true hlt]
        rw [decide_eq_true hlt] at hkS
        simp only [ite_true, pure_ok, Except.ok.injEq] at hkS
        subst hkS
        try wp_auto
        wp_for_post
        try wp_auto
        wp_apply wp_clone p s $$ [Hs] as %q Hq
        · iexact Hs
        try wp_auto
        wp_apply wp_setReads g.Reads' s.reads n _ _ $$ [HReads Hkept] as %out #Hout
        · iframe HReads Hkept; ipureintro; exact ⟨Hn, by rw [HWf.len_reads]; exact Hlt⟩
        try wp_auto
        wp_apply wp_set_reads q s out (s.reads.set (sint.nat n) ((s.reads[sint.nat n]!).filter (fun r => r.ctx != cx))) (by rw [List.length_set, HWf.len_reads]) $$ [Hq Hout] as Hq
        · iframe Hq Hout
        try wp_auto
        have hvl : (s.viol.length : Int) + 1 < 2 ^ 63 := by
          have := HW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
        wp_apply wp_violAdd g.Viol' s.viol go!"ReadIndexStale" $$ [HViol] as %vsl #Hvsl
        · iframe HViol; ipureintro; exact hvl
        try wp_auto
        wp_apply wp_set_viol q _ vsl _ $$ [Hq Hvsl] as Hq
        · iframe Hq Hvsl
        try wp_auto
        simp only [ite_true, pure_ok, Except.ok.injEq] at Ho
        subst Ho
        iapply HΦ
        iunfold succOwn
        isplitr
        · ipureintro; rfl
        iexact Hq
      · rw [decide_eq_false hlt]
        rw [decide_eq_false hlt] at hkS
        simp only [Bool.false_eq_true, ite_false] at hkS
        try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by omega, by omega, ?_⟩
        rw [hk1']; exact hkS
    · rw [decide_eq_false hz]
      rw [beq_of_ne' hz, andM_ok_false] at hc
      cases hc
      simp only [Bool.false_eq_true, ite_false] at hkS
      try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by omega, by omega, ?_⟩
      rw [hk1']; exact hkS
  · have hkn : sint.nat k = (s.reads[sint.nat n]!).length := by
      rw [← Hl, ← hrvl]; have := sint_nat_cast hk0; have := sint_nat_cast Hil.2; omega
    rw [hkn, List.drop_length] at hkS
    cases hkS
    try wp_auto
    wp_apply wp_clone p s $$ [Hs] as %q Hq
    · iexact Hs
    try wp_auto
    wp_apply wp_setReads g.Reads' s.reads n _ _ $$ [HReads Hkept] as %out #Hout
    · iframe HReads Hkept; ipureintro; exact ⟨Hn, by rw [HWf.len_reads]; exact Hlt⟩
    try wp_auto
    wp_apply wp_set_reads q s out (s.reads.set (sint.nat n) ((s.reads[sint.nat n]!).filter (fun r => r.ctx != cx))) (by rw [List.length_set, HWf.len_reads]) $$ [Hq Hout] as Hq
    · iframe Hq Hout
    try wp_auto
    simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    iapply HΦ
    iunfold succOwn
    isplitr
    · ipureintro; rfl
    iexact Hq

end proof

end AntCheck
end EtcdGrove
end Perennial
