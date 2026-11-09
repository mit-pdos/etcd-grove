/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__isBecomeFollowerInUpdateTermOrReturnToFollower`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__isBecomeFollowerInUpdateTermOrReturnToFollower
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline

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

-- The second condition (`ReturnToFollower`'s line), the first having failed (hygiene off).
set_option hygiene false in
local macro "bf_c2" "[" xs:ident,* "]" : tactic => `(tactic| (
  rw [decide_strRel Hkf.1 (show strRel go!"ReceiveAppendEntriesRequest" "ReceiveAppendEntriesRequest" by strRel_lit)]
  by_cases c1 : (tr.line K).ev.name = "ReceiveAppendEntriesRequest"
  rotate_left
  · rw [decide_eq_false c1]
    try wp_auto
    iapply HΦ'; ipureintro; rw [hres]; simp [c1, $[$xs:ident],*]
  rw [decide_eq_true c1]
  try wp_auto
  rw [decide_eq_false Hpmnn]
  try wp_auto
  rw [sint_decide Hkf.2.2.1 Hpm.2.1]
  by_cases c2 : (tr.line K).ev.state.term = pm.term
  rotate_left
  · rw [decide_eq_false c2]
    try wp_auto
    iapply HΦ'; ipureintro; rw [hres]; simp [c1, c2, $[$xs:ident],*]
  rw [decide_eq_true c2]
  try wp_auto
  rw [sint_decide Hpm.2.1 Hef.2.2.1]
  by_cases c3 : pm.term = (tr.line ts.l).ev.state.term
  rotate_left
  · rw [decide_eq_false c3]
    try wp_auto
    iapply HΦ'; ipureintro; rw [hres]; simp [c1, c2, c3, $[$xs:ident],*]
  rw [decide_eq_true c3]
  simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Candidate,
    github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.PreCandidate]
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Role.TypeAssumptions.String_unfold.method_unfold]
  try wp_auto
  rw [decide_strRel Hkf.2.2.2.2.2.1 strRel_candidate]
  by_cases c4 : (tr.line K).ev.role = candidate
  · rw [decide_eq_true c4]
    try wp_auto
    iapply HΦ'; ipureintro; rw [hres]; simp [c1, c2, c3, c4, $[$xs:ident],*]
  rw [decide_eq_false c4]
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Role.TypeAssumptions.String_unfold.method_unfold]
  try wp_auto
  rw [decide_strRel Hkf.2.2.2.2.2.1 strRel_preCandidate]
  iapply HΦ'; ipureintro; rw [hres]
  by_cases c5 : (tr.line K).ev.role = preCandidate <;> simp [c1, c2, c3, c4, c5, $[$xs:ident],*]))

theorem Trace.isBecomeFollowerInUpdateTermOrReturnToFollower.wp_proof
    (wp_loglineIsEvent : Trace.loglineIsEvent.spec (GF := GF) (hG := hG))
    (wp_logline : Trace.logline.spec (GF := GF) (hG := hG)) :
    Trace.isBecomeFollowerInUpdateTermOrReturnToFollower.spec (GF := GF) (hG := hG) := by
  intro t tr g ts
  wp_start as ⟨#Ht, #Hts, %Hl1⟩
  ihave HΦ' : (∀ b : Bool, ⌜b = tr.isBecomeFollowerInUpdateTermOrReturnToFollower ts⌝ -∗ Φ #b) $$ [HΦ]
  · iintro %b %hb; rw [hb]; iapply HΦ; ipureintro; trivial
  open_ts
  wp_auto
  wp_apply wp_loglineIsEvent t tr g ts go!"BecomeFollower" "BecomeFollower" $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hev : tr.isEvent ts "BecomeFollower"
  · simp only [Bool.not_false]
    wp_auto
    iapply HΦ'; ipureintro; simp [Trace.isBecomeFollowerInUpdateTermOrReturnToFollower, hev]
  have hle : ts.l ≤ tr.len := Trace.isEvent_le hev
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
  open_trace
  open_lineP
  obtain ⟨F, hF⟩ : ∃ F : Nat → Nat → Nat, F = fun (acc : Nat) n =>
      if (tr.line (n + 1)).ev.nid == (tr.line ts.l).ev.nid then n + 1 else acc := ⟨_, rfl⟩
  have hk : ∀ m, (List.range m).foldl F 0 ≤ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range m).foldl F 0 = a at ih ⊢
      rw [hF]; dsimp only; split
      · exact Nat.le_refl _
      · exact Nat.le_succ_of_le ih
  have hlz : sint.Z (g.L' - W64 1) = (ts.l : Int) - 1 := by
    have : (1 : Int) ≤ sint.Z g.L' := by rw [Hg.1]; exact_mod_cast Hl1
    rw [← Hg.1]; word
  ihave IH : iprop(∃ (n k : w64),
      "n" ∷ n_ptr ↦ n ∗ "k" ∷ k_ptr ↦ k ∗
      "%Hn" ∷ ⌜1 ≤ sint.Z n ∧ sint.Z n ≤ (ts.l : Int) ∧
        sint.Z k = (((List.range (sint.nat n - 1)).foldl F 0 : Nat) : Int)⌝) $$ [n k]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by decide, by rw [show sint.Z (W64 1) = 1 from rfl]; exact_mod_cast Hl1, by
      rw [show sint.nat (W64 1) = 1 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnk⟩ := Hn
  wp_if_destruct
  · have hnz : sint.Z (n - W64 1) = sint.Z n - 1 := by clear hnk; word
    have hlenl : (tr.len : Int) = (tr.lines.length : Int) := rfl
    have hidx : 0 ≤ sint.Z (n - W64 1) ∧ sint.Z (n - W64 1) < sint.Z gt.lines'.len := by
      rw [hnz, ← hlenZ]; rw [hlz] at Hif; constructor <;> omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hidx)]
    have hnn : (sint.Z (n - W64 1)).toNat = sint.nat n - 1 := by rw [hnz]; clear hnk; word
    have hn1' : 1 ≤ sint.nat n := by clear hnk; word
    have hn2' : sint.nat n ≤ tr.len := by rw [hlz] at Hif; clear hnk; word
    have hx := Trace.line_eq tr (sint.nat n) hn1' hn2'
    obtain ⟨y, Hy⟩ : ∃ y, lns[(sint.Z (n - W64 1)).toNat]? = some y :=
      ⟨_, List.getElem?_eq_getElem (by rw [hnn, Hll]; unfold Trace.len at hn2'; omega)⟩
    rw [hnn] at Hy
    ihave #Hyx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => lineRO (GF := GF) a b) Hy hx $$ Hl
    rw [← hnn] at Hy
    icases ownSlice_elem_acc _ y _ _ lns hidx.1 Hy $$ Hlns with ⟨#Hye, -⟩
    icases typedPointsto_split _ _ _ $$ Hye with Hyf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hyf with ⟨#Y1, -⟩
    iunfold lineRO at Hyx
    icases Hyx with ⟨⟨%gey, #Hgey, #Hgeyr⟩, -⟩
    iunfold eventRO at Hgeyr
    icases Hgeyr with ⟨%Hyef, -⟩
    icases typedPointsto_split _ _ _ $$ Hgey with Hgeyf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hgeyf with ⟨-, #YN, -⟩
    wp_auto
    rw [decide_strRel Hyef.2.1 Hef.2.1]
    have hstep : (List.range (sint.nat (n + W64 1) - 1)).foldl F 0 =
        F ((List.range (sint.nat n - 1)).foldl F 0) (sint.nat n - 1) := by
      rw [show sint.nat (n + W64 1) - 1 = sint.nat n - 1 + 1 by clear hnk; word, List.range_succ,
        List.foldl_append]
      rfl
    have hsn : sint.nat n - 1 + 1 = sint.nat n := by omega
    by_cases hc : (tr.line (sint.nat n)).ev.nid = (tr.line ts.l).ev.nid
    · rw [decide_eq_true hc]
      wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by clear hnk; word, by rw [hlz] at Hif; clear hnk; word, ?_⟩
      rw [hstep, hF]
      dsimp only
      rw [hsn, ite_eq_left_iff.2 (fun h => absurd (by simp [hc]) h)]
      clear hnk; word
    · rw [decide_eq_false hc]
      wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by clear hnk; word, by rw [hlz] at Hif; clear hnk; word, ?_⟩
      rw [hstep, hF]
      dsimp only
      rw [hsn, ite_eq_right_iff.2 (fun h => absurd (by simpa using h) hc)]
      rw [← hF]; exact hnk
  · have hnl : sint.nat n - 1 = ts.l - 1 := by rw [hlz] at Hif; clear hnk; word
    rw [hnl] at hnk
    try wp_auto
    rw [sint_decide_nat hnk (show sint.Z (W64 0) = ((0 : Nat) : Int) from rfl)]
    have hkdef : (List.range (ts.l - 1)).foldl
        (fun (acc : Nat) n => if (tr.line (n + 1)).ev.nid == (tr.line ts.l).ev.nid then n + 1 else acc) 0 =
        (List.range (ts.l - 1)).foldl F 0 := by rw [hF]
    by_cases hk0 : (List.range (ts.l - 1)).foldl F 0 = 0
    · rw [decide_eq_true hk0]
      wp_auto
      iapply HΦ'; ipureintro
      unfold Trace.isBecomeFollowerInUpdateTermOrReturnToFollower
      simp only [hev, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hkdef, hk0]; rfl
    rw [decide_eq_false hk0]
    obtain ⟨K, hKd⟩ : ∃ K, K = (List.range (ts.l - 1)).foldl F 0 := ⟨_, rfl⟩
    rw [← hKd] at hk0 hnk hkdef
    have hKl : K ≤ ts.l - 1 := by rw [hKd]; exact hk _
    have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.2 hk0
    have hK2 : K ≤ tr.len := by omega
    have hkz : sint.Z (k - W64 1) = (K : Int) - 1 := by
      have : (1 : Int) ≤ sint.Z k := by rw [hnk]; exact_mod_cast hK1
      rw [← hnk]; word
    have hidx : 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z gt.lines'.len := by
      rw [hkz, ← hlenZ]; constructor <;> omega
    have hkn : (sint.Z (k - W64 1)).toNat = K - 1 := by rw [hkz]; omega
    have hx := Trace.line_eq tr K hK1 hK2
    obtain ⟨y, Hy⟩ : ∃ y, lns[(sint.Z (k - W64 1)).toNat]? = some y :=
      ⟨_, List.getElem?_eq_getElem (by rw [hkn, Hll]; unfold Trace.len at hK2; omega)⟩
    rw [hkn] at Hy
    ihave #Hyx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => lineRO (GF := GF) a b) Hy hx $$ Hl
    rw [← hkn] at Hy
    icases ownSlice_elem_acc _ y _ _ lns hidx.1 Hy $$ Hlns with ⟨#Hye, -⟩
    icases typedPointsto_split _ _ _ $$ Hye with Hyf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hyf with ⟨#Z1, -⟩
    iunfold lineRO at Hyx
    icases Hyx with ⟨⟨%gek, #Hgek, #Hgekr⟩, -⟩
    iunfold eventRO at Hgekr
    icases Hgekr with ⟨%Hkf, -, #Hkmsg, -⟩
    icases typedPointsto_split _ _ _ $$ Hgek with Hgekf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hgekf with ⟨#K1, -, #K3, #K4, -, -, #K7, -⟩
    icases typedPointsto_split _ _ _ $$ K3 with Hk3
    simp only [TypedPointsto.typedPointstoDef]
    icases Hk3 with ⟨#KS1, -⟩
    icases typedPointsto_split _ _ _ $$ State with Hls
    simp only [TypedPointsto.typedPointstoDef]
    icases Hls with ⟨#LS1, -⟩
    ihave #Hpi := etcdraftInit_get $$ Hpkg
    icases Hpi with ⟨-, -, ⟨%mr, #Hmr, #Hrnm⟩⟩
    have hres : tr.isBecomeFollowerInUpdateTermOrReturnToFollower ts =
        (match (tr.line K).ev.msg with
         | none => false
         | some pm =>
           ((isReceiveName (tr.line K).ev.name && decide ((tr.line K).ev.state.term < pm.term) &&
              (pm.term == (tr.line ts.l).ev.state.term)) ||
           (((tr.line K).ev.name == "ReceiveAppendEntriesRequest") && ((tr.line K).ev.state.term == pm.term) &&
              (pm.term == (tr.line ts.l).ev.state.term) &&
              (((tr.line K).ev.role == candidate) || ((tr.line K).ev.role == preCandidate))))) := by
      unfold Trace.isBecomeFollowerInUpdateTermOrReturnToFollower
      simp only [hev, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hkdef]
      simp only [beq_iff_eq, hk0, ite_false]
      cases (tr.line K).ev.msg <;> simp
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true hidx)]
    wp_auto
    wp_apply wp_map_lookup1 $$ [Hrnm] as -
    · iexact Hrnm
    rw [show (zero_val Bool) = false from rfl, receiveNamesMap_lookup Hkf.1]
    cases hm : (tr.line K).ev.msg with
    | none =>
      icases Hkmsg with %Hnull
      rw [Hnull]
      cases hrn : isReceiveName (tr.line K).ev.name
      · wp_auto
        rw [decide_strRel Hkf.1 (show strRel go!"ReceiveAppendEntriesRequest" "ReceiveAppendEntriesRequest" by strRel_lit)]
        by_cases c1 : (tr.line K).ev.name = "ReceiveAppendEntriesRequest"
        · rw [decide_eq_true c1]
          wp_auto
          iapply HΦ'; ipureintro; rw [hres, hm]
        · rw [decide_eq_false c1]
          wp_auto
          iapply HΦ'; ipureintro; rw [hres, hm]
      · wp_auto
        rw [decide_strRel Hkf.1 (show strRel go!"ReceiveAppendEntriesRequest" "ReceiveAppendEntriesRequest" by strRel_lit)]
        by_cases c1 : (tr.line K).ev.name = "ReceiveAppendEntriesRequest"
        · rw [decide_eq_true c1]
          wp_auto
          iapply HΦ'; ipureintro; rw [hres, hm]
        · rw [decide_eq_false c1]
          wp_auto
          iapply HΦ'; ipureintro; rw [hres, hm]
    | some pm =>
    icases Hkmsg with ⟨%gpm, #Hgpm, %Hpm⟩
    ihave %Hpmnn := typedPointsto_not_null _ _ _ $$ Hgpm
    icases typedPointsto_split _ _ _ $$ Hgpm with Hgpmf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hgpmf with ⟨-, #PM2, -⟩
    cases hrn : isReceiveName (tr.line K).ev.name
    · wp_auto
      have hrn' : (tr.line K).ev.name ≠ "ReceiveAppendEntriesRequest" := by
        intro h; rw [h] at hrn; exact absurd hrn (by decide)
      rw [decide_strRel Hkf.1 (show strRel go!"ReceiveAppendEntriesRequest" "ReceiveAppendEntriesRequest" by strRel_lit)]
      rw [decide_eq_false hrn']
      wp_auto
      iapply HΦ'; ipureintro; rw [hres]; simp [hm, hrn, hrn']
    wp_auto
    rw [decide_eq_false Hpmnn]
    wp_auto
    rw [show decide (sint.Z gek.State'.Term' < sint.Z gpm.Term') = decide ((tr.line K).ev.state.term < pm.term) by
      rw [Hkf.2.2.1, Hpm.2.1]]
    by_cases d1 : (tr.line K).ev.state.term < pm.term
    rotate_left
    · rw [decide_eq_false d1]
      wp_auto
      bf_c2 [hm, hrn, d1]
    rw [decide_eq_true d1]
    wp_auto
    rw [sint_decide Hpm.2.1 Hef.2.2.1]
    by_cases d2 : pm.term = (tr.line ts.l).ev.state.term
    · rw [decide_eq_true d2]
      wp_auto
      have d1' : (tr.line K).ev.state.term < (tr.line ts.l).ev.state.term := d2 ▸ d1
      iapply HΦ'; ipureintro; rw [hres]; simp [hm, hrn, d1', d2]
    rw [decide_eq_false d2]
    wp_auto
    bf_c2 [hm, hrn, d1, d2]

end proof

end Etcdraft
end EtcdGrove
end Perennial
