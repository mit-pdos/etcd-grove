/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/util/GetTargetNodeName.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.util.GetTargetNodeName
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.util.Defs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.util.Assumptions]

set_option hygiene false in
/-- An error return (`fmt.Errorf` of the pod's namespace and name, for `htn : targetNode .. = none`):
leaves the goal `podAt p dq d`. -/
macro "tnn_err" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_Errorf $$ [Hsl] as %e ⟨-, #HeS⟩
  · iframe; fmt_args_ok
  iapply HΦ
  rw [htn]
  isplitr [HeS]
  rotate_left
  · iexists e; iframe #; ipureintro; rfl))

set_option hygiene false in
/-- The pod back from its fields and the affinity's ownership `Ha`. -/
macro "tnn_pod" : tactic => `(tactic| (
  ihave Hl := Hl $$ [Fn Fa Fns Fnm]
  · iframe
  ihave Hs := Hs $$ Ha
  ihave Hd := Hd $$ Hs
  iunfold podAt; iexists v; iframe))

set_option hygiene false in
/-- The affinity's ownership `Ha` back from its node affinity field and ownership. -/
macro "tnn_aff" : tactic => `(tactic| (
  ihave Hax := Hax $$ Fna
  ihave Haown := Haown $$ Hna
  ihave Ha : ownPtrD kd.core.Affinity.own v.Spec'.Affinity' dq (some da) $$ [Hax Haown]
  · iunfold ownPtrD; iexists ax; iframe))

set_option hygiene false in
/-- The node affinity's ownership `Hna` back. -/
macro "tnn_na" : tactic => `(tactic| (
  ihave Hnx := Hnx $$ Fre
  ihave Hnown := Hnown $$ Hre
  ihave Hna : ownPtrD kd.core.NodeAffinity.own ax.NodeAffinity' dq (some dna) $$ [Hnx Hnown]
  · iunfold ownPtrD; iexists nx; iframe))

set_option hygiene false in
/-- The required selector's ownership `Hre` back. -/
macro "tnn_ns" : tactic => `(tactic| (
  ihave Hsx := Hsx $$ Fts
  ihave Hre : ownPtrD kd.core.NodeSelector.own nx.RequiredDuringSchedulingIgnoredDuringExecution' dq (some dsel) $$ [Hsx Hts]
  · iunfold ownPtrD; iexists sx; iframe; iapply (ns_own_terms _ _ _).2; iexact Hts))

set_option hygiene false in
/-- The next requirement (for `hpf : reqP keyName opIn re = false`). -/
macro "tnn_cont" : tactic => `(tactic| (
  wp_for_post
  ihave Hre : kd.core.NodeSelectorRequirement.own rv dq re $$ [Hvals]
  · iapply (req_own _ _ _).2; iframe; ipureintro; exact Hreq
  ihave Hml := Hml $$ Hre
  iframe
  iexists j + W64 1, rv
  iframe
  ipureintro
  refine ⟨by word, by word, ?_⟩
  intro k hk r hr
  by_cases hkj : k < sint.nat j
  · exact Hj.2.2 k hkj r hr
  · have : k = sint.nat j := by word
    subst this
    rw [hre] at hr; cases hr; exact hpf))

set_option hygiene false in
/-- The terms' ownership `Hts` back from inside the loops. -/
macro "tnn_inner" : tactic => `(tactic| (
  ihave Hre : kd.core.NodeSelectorRequirement.own rv dq re $$ [Hvals]
  · iapply (req_own _ _ _).2; iframe; ipureintro; exact Hreq
  ihave Hml := Hml $$ Hre
  ihave Hte := Hte $$ [Hms Hml]
  · iunfold ownSliceD; iexists rvs; iframe
  ihave Htl := Htl $$ Hte
  ihave Hts : ownSliceD kd.core.NodeSelectorTerm.own sx.NodeSelectorTerms' dq dsel.NodeSelectorTerms' $$ [Hts Htl]
  · iunfold ownSliceD; iexists tvs; iframe))

theorem GetTargetNodeName.wp_proof
    (wp_Errorf : EtcdGrove.fmt.Errorf.spec (GF := GF) (hG := hG)) :
    GetTargetNodeName.spec (GF := GF) (hG := hG) := by
  intro p dq d
  wp_start as Hp
  iunfold podAt at Hp
  icases Hp with ⟨%v, Hl, Hd⟩
  icases pod_meta _ _ _ $$ Hd with ⟨Hd, %Hm⟩
  icases pod_spec_acc _ _ _ $$ Hd with ⟨Hs, Hd⟩
  icases podSpec_aff_acc _ _ _ $$ Hs with ⟨%Hn, Ha, Hs⟩
  icases pod_tnn_acc _ _ _ $$ Hl with ⟨Fn, Fa, Fns, Fnm, Hl⟩
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
  wp_if_destruct
  rotate_left
  · -- a node name
    have hne : d.Spec'.NodeName' ≠ go!"" := by
      intro h; apply Hif; rw [Hn, h]; rfl
    iapply HΦ
    ihave Hl := Hl $$ [$Fn $Fa $Fns $Fnm]
    ihave Hs := Hs $$ Ha
    ihave Hd := Hd $$ Hs
    isplitl [Hl Hd]
    · iunfold podAt; iexists v; iframe
    simp only [targetNode, hne, ne_eq, not_false_eq_true, ↓reduceIte]
    ipureintro; exact ⟨Hn, trivial⟩
  have hnn : d.Spec'.NodeName' = go!"" := by
    rw [← Hn]; apply List.eq_nil_of_length_eq_zero; word
  icases ptrD_null _ _ _ _ $$ Ha with ⟨Ha, %Han⟩
  wp_if_destruct
  · -- no affinity
    have htn : targetNode keyName opIn d = none := by
      simp [targetNode, reqTerms, hnn, Han.mp Hif]
    tnn_err
    tnn_pod
  obtain ⟨da, hda⟩ : ∃ da, d.Spec'.Affinity' = some da := by
    cases h : d.Spec'.Affinity' with
    | none => exact absurd (Han.mpr h) Hif
    | some a => exact ⟨a, rfl⟩
  rw [hda]
  iunfold ownPtrD at Ha
  icases Ha with ⟨%ax, Hax, Haown⟩
  icases aff_na_acc _ _ _ $$ Hax with ⟨Fna, Hax⟩
  icases aff_own_na _ _ _ $$ Haown with ⟨Hna, Haown⟩
  icases ptrD_null _ _ _ _ $$ Hna with ⟨Hna, %Hnan⟩
  wp_auto
  wp_if_destruct
  · -- no node affinity
    have htn : targetNode keyName opIn d = none := by
      simp [targetNode, reqTerms, hnn, hda, Hnan.mp Hif]
    tnn_err
    tnn_aff
    tnn_pod
  obtain ⟨dna, hdna⟩ : ∃ dna, da.NodeAffinity' = some dna := by
    cases h : da.NodeAffinity' with
    | none => exact absurd (Hnan.mpr h) Hif
    | some a => exact ⟨a, rfl⟩
  rw [hdna]
  iunfold ownPtrD at Hna
  icases Hna with ⟨%nx, Hnx, Hnown⟩
  icases na_req_acc _ _ _ $$ Hnx with ⟨Fre, Hnx⟩
  icases na_own_req _ _ _ $$ Hnown with ⟨Hre, Hnown⟩
  icases ptrD_null _ _ _ _ $$ Hre with ⟨Hre, %Hren⟩
  wp_auto
  wp_if_destruct
  · -- no required node affinity
    have htn : targetNode keyName opIn d = none := by
      simp [targetNode, reqTerms, hnn, hda, hdna, Hren.mp Hif]
    tnn_err
    tnn_na
    tnn_aff
    tnn_pod
  obtain ⟨dsel, hdsel⟩ : ∃ dsel, dna.RequiredDuringSchedulingIgnoredDuringExecution' = some dsel := by
    cases h : dna.RequiredDuringSchedulingIgnoredDuringExecution' with
    | none => exact absurd (Hren.mpr h) Hif
    | some a => exact ⟨a, rfl⟩
  have hrt : reqTerms d = some dsel.NodeSelectorTerms' := by
    simp [reqTerms, hda, hdna, hdsel]
  rw [hdsel]
  iunfold ownPtrD at Hre
  icases Hre with ⟨%sx, Hsx, Hts⟩
  icases ns_terms_acc _ _ _ $$ Hsx with ⟨Fts, Hsx⟩
  icases (ns_own_terms _ _ _).1 $$ Hts with Hts
  iunfold ownSliceD at Hts
  icases Hts with ⟨%tvs, Hts, Htl⟩
  ihave %Htsl := ownSlice_len _ _ _ $$ Hts
  ihave %Htll := (BigSepL2.bigSepL2_length (PROP := IProp GF)) $$ Htl
  wp_auto
  wp_if_destruct
  · -- no terms
    have hnil : dsel.NodeSelectorTerms' = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [← Htll, Htsl.1]; word
    have htn : targetNode keyName opIn d = none := by
      simp [targetNode, hnn, hrt, hnil, nameReq]
    tnn_err
    ihave Hts : ownSliceD kd.core.NodeSelectorTerm.own sx.NodeSelectorTerms' dq dsel.NodeSelectorTerms' $$ [Hts Htl]
    · iunfold ownSliceD; iexists tvs; iframe
    tnn_ns
    tnn_na
    tnn_aff
    tnn_pod
  -- the loop over the terms: none of the first `i` has a matching requirement
  ihave HI : (∃ (i : w64) (tv : k8s_io.api.core.v1.NodeSelectorTerm),
      "i" ∷ i_ptr ↦ i ∗ "term" ∷ term_ptr ↦ tv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sx.NodeSelectorTerms'.len ∧
        ∀ k < sint.nat i, ∀ t, dsel.NodeSelectorTerms'[k]? = some t →
          t.MatchFields'.find? (reqP keyName opIn) = none⌝ : IProp GF) $$ [i term]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    intro k hk; exfalso; have : sint.nat (W64 0) = 0 := rfl; omega
  wp_for HI
  wp_if_destruct
  · -- an iteration
    have hilt : sint.nat i < dsel.NodeSelectorTerms'.length := by rw [← Htll, Htsl.1]; word
    obtain ⟨tv', htv⟩ : ∃ x, tvs[sint.nat i]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [Htll]; exact hilt)⟩
    obtain ⟨te, hte⟩ : ∃ e, dsel.NodeSelectorTerms'[sint.nat i]? = some e :=
      ⟨_, List.getElem?_eq_getElem hilt⟩
    simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sx.NodeSelectorTerms'.len from ⟨Hi.1, Hif⟩,
      _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index sx.NodeSelectorTerms' (sint.Z i) tvs _ tv' Hi.1) $$ [Hts] as Hts
    · iframe; ipureintro; exact htv
    icases (BigSepL2.bigSepL2_lookup_acc (PROP := IProp GF) htv hte) $$ Htl with ⟨Hte, Htl⟩
    icases term_own_fields _ _ _ $$ Hte with ⟨Hmf, Hte⟩
    iunfold ownSliceD at Hmf
    icases Hmf with ⟨%rvs, Hms, Hml⟩
    ihave %Hmsl := ownSlice_len _ _ _ $$ Hms
    ihave %Hmll := (BigSepL2.bigSepL2_length (PROP := IProp GF)) $$ Hml
    -- the loop over the term's field requirements: none of the first `j` matches
    ihave HJ : (∃ (j : w64) (ev : k8s_io.api.core.v1.NodeSelectorRequirement),
        "j" ∷ i_ptr ↦ j ∗ "exp" ∷ exp_ptr ↦ ev ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z tv'.MatchFields'.len ∧
          ∀ k < sint.nat j, ∀ r, te.MatchFields'[k]? = some r → reqP keyName opIn r = false⌝ : IProp GF)
        $$ [i exp]
    · iexists W64 0, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro k hk; exfalso; have : sint.nat (W64 0) = 0 := rfl; omega
    wp_for HJ
    wp_if_destruct
    · -- an inner iteration
      have hjlt : sint.nat j < te.MatchFields'.length := by rw [← Hmll, Hmsl.1]; word
      obtain ⟨rv, hrv⟩ : ∃ x, rvs[sint.nat j]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [Hmll]; exact hjlt)⟩
      obtain ⟨re, hre⟩ : ∃ e, te.MatchFields'[sint.nat j]? = some e :=
        ⟨_, List.getElem?_eq_getElem hjlt⟩
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z tv'.MatchFields'.len from ⟨Hj.1, Hif⟩,
        _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index tv'.MatchFields' (sint.Z j) rvs _ rv Hj.1) $$ [Hms] as Hms
      · iframe; ipureintro; exact hrv
      icases (BigSepL2.bigSepL2_lookup_acc (PROP := IProp GF) hrv hre) $$ Hml with ⟨Hre, Hml⟩
      icases (req_own _ _ _).1 $$ Hre with ⟨%Hreq, Hvals⟩
      ihave %Hvl := ownSlice_len _ _ _ $$ Hvals
      wp_if_destruct
      · have hkey := Hif
        wp_if_destruct
        · -- the matching requirement
          have hpt : reqP keyName opIn re = true := by
            simp [reqP, keyName, opIn, ← Hreq.1, ← Hreq.2, hkey, Hif]
          have hnr : nameReq keyName opIn dsel.NodeSelectorTerms' = some re :=
            nameReq_of_prefix _ _ _ (sint.nat i) te re Hi.2.2 hte
              (find?_of_prefix _ _ (sint.nat j) re Hj.2.2 hre hpt)
          wp_if_destruct
          · -- exactly one value: the node name
            have h1 : re.Values'.length = 1 := by rw [Hvl.1, Hif]; rfl
            obtain ⟨x, hx⟩ : ∃ x, re.Values' = [x] := by
              rcases hv : re.Values' with _ | ⟨x, _ | ⟨y, t⟩⟩
              · rw [hv] at h1; cases h1
              · exact ⟨x, rfl⟩
              · rw [hv] at h1; simp at h1
            have h01 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rv.Values'.len := by
              rw [Hif]; word
            have h0 : (0 : Int) ≤ sint.Z (W64 0) := h01.1
            simp only [h01, _root_.and_self, ↓reduceIte]
            wp_apply (wp_load_slice_index rv.Values' (sint.Z (W64 0)) re.Values' _ x h0)
              $$ [Hvals] as Hvals
            · iframe; ipureintro; rw [hx]; rfl
            have htn : targetNode keyName opIn d = some x := by
              simp only [targetNode, hnn, hrt, hnr, hx, ne_eq, not_true_eq_false, ↓reduceIte]
            wp_for_post
            wp_for_post
            iapply HΦ
            rw [htn]
            isplitl
            · tnn_inner
              tnn_ns
              tnn_na
              tnn_aff
              tnn_pod
            ipureintro; exact ⟨rfl, rfl⟩
          · -- not exactly one value: an error
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %sl ⟨Hsl, -⟩
            wp_apply wp_Errorf $$ [Hsl] as %e ⟨-, #HeS⟩
            · iframe
              try simp only [k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectNameField]
              rw [show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl, show sint.nat (W64 (0 + 1)) = 1 by rfl]
              simp only [List.set_cons_succ, List.set_cons_zero]
              fmt_args_ok
            have hv1 : re.Values'.length ≠ 1 := by
              intro h; apply Hif; have := Hvl.1; rw [h] at this; word
            have htn : targetNode keyName opIn d = none := by
              simp only [targetNode, hnn, hrt, hnr, ne_eq, not_true_eq_false, ↓reduceIte]
              split
              · rename_i x hx; rw [hx] at hv1; simp at hv1
              · rfl
            wp_for_post
            wp_for_post
            iapply HΦ
            rw [htn]
            isplitr [HeS]
            rotate_left
            · iexists e; iframe #; ipureintro; rfl
            tnn_inner
            tnn_ns
            tnn_na
            tnn_aff
            tnn_pod
        · have hpf : reqP keyName opIn re = false := by
            simp [reqP, opIn, ← Hreq.2]; intro _; exact Hif
          tnn_cont
      · have hpf : reqP keyName opIn re = false := by
          simp [reqP, keyName, ← Hreq.1]; intro h; exact absurd h Hif
        tnn_cont
    · -- no requirement of this term matches: the next term
      have hfind : te.MatchFields'.find? (reqP keyName opIn) = none := by
        apply find?_none_of_all
        intro k hk r hr
        exact Hj.2.2 k (by rw [← Hmll, Hmsl.1] at hk; word) r hr
      wp_for_post
      ihave Hte := Hte $$ [Hms Hml]
      · iunfold ownSliceD; iexists rvs; iframe
      ihave Htl := Htl $$ Hte
      iframe
      iexists i + W64 1, tv'
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro k hk t ht
      by_cases hki : k < sint.nat i
      · exact Hi.2.2 k hki t ht
      · have : k = sint.nat i := by word
        subst this
        rw [hte] at ht; cases ht; exact hfind
  · -- all terms seen: no matching requirement
    have hnr : nameReq keyName opIn dsel.NodeSelectorTerms' = none := by
      apply nameReq_none_of_all
      intro k hk t ht
      exact Hi.2.2 k (by rw [← Htll, Htsl.1] at hk; word) t ht
    have htn : targetNode keyName opIn d = none := by
      simp [targetNode, hnn, hrt, hnr]
    tnn_err
    ihave Hts : ownSliceD kd.core.NodeSelectorTerm.own sx.NodeSelectorTerms' dq dsel.NodeSelectorTerms' $$ [Hts Htl]
    · iunfold ownSliceD; iexists tvs; iframe
    tnn_ns
    tnn_na
    tnn_aff
    tnn_pod

end proof

end dsctl
end EtcdGrove
end Perennial
