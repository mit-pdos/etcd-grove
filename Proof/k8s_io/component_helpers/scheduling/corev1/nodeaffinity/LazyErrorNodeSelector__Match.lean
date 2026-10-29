/-
Proof of `Spec/k8s_io/component_helpers/scheduling/corev1/nodeaffinity/LazyErrorNodeSelector__Match.lean`,
over gap D2's body hypothesis. Lean-first.
-/
module

public import Spec.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.LazyErrorNodeSelector__Match
public import Spec.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.LazyErrorNodeSelector__Match_body
public import Spec.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.extractNodeFields
public import Spec.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.nodeSelectorTerm__match
public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate
public import Spec.k8s_io.apimachinery.pkg.util.errors.Flatten

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel k8s_io.component_helpers.scheduling.corev1.nodeaffinity

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.component_helpers.scheduling.corev1.nodeaffinity.Assumptions]

theorem LazyErrorNodeSelector.Match.wp_proof
    (h_body : LazyErrorNodeSelector.Match_body.spec (sem := sem))
    (wp_extractNodeFields : extractNodeFields.spec (GF := GF) (hG := hG))
    (wp_match : nodeSelectorTerm.match.spec (GF := GF) (hG := hG))
    (wp_NewAggregate : utilerrors.NewAggregate.spec (GF := GF) (hG := hG))
    (wp_Flatten : utilerrors.Flatten.spec (GF := GF) (hG := hG)) :
    LazyErrorNodeSelector.Match.spec (GF := GF) (hG := hG) := by
  haveI := h_body
  intro ns node dq d
  wp_start as ⟨#Hns, Hn⟩
  iunfold lesOk at Hns
  icases Hns with ⟨%s, %ts, #Hns, #Hs, #Hts⟩
  iunfold nodeAt at Hn
  icases Hn with ⟨%v, Hl, Hd⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  icases node_labelsField node dq v $$ Hl with ⟨HL, Hlback⟩
  wp_auto
  ihave Hl := Hlback $$ HL
  wp_apply (wp_extractNodeFields node dq v d) $$ [$Hl $Hd] as %fm ⟨Hl, Hd, Hfm⟩
  icases node_labels_acc v dq d $$ Hd with ⟨Hlab, Hdback⟩
  ihave %Hslen := ownSlice_len _ _ _ $$ Hs
  ihave #Hns' := Hns
  iStructNamed Hns'
  wp_auto
  ihave HI : (∃ (j : w64) (es : GoSlice) (L : List GoInterface),
      "i" ∷ i_ptr ↦ j ∗ "errs" ∷ errs_ptr ↦ es ∗ "Hes" ∷ es ↦* L ∗
      "Hcap" ∷ ownSliceCap GoInterface es (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ ∗
      "Hlab" ∷ ownMapD (K := GoString) (V := GoString) v.ObjectMeta'.Labels' dq
        d.ObjectMeta'.Labels' ∗
      "Hfm" ∷ fm ↦$ nodeFieldsM d.ObjectMeta'.Name' ∗
      "nodeLabels" ∷ nodeLabels_ptr ↦ v.ObjectMeta'.Labels' ∗
      "nodeFields" ∷ nodeFields_ptr ↦ fm : IProp GF)
    $$ [i errs Hlab Hfm nodeLabels nodeFields]
  · iexists W64 0, slice.nil, []
    iframe
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; exact ⟨by word, by word⟩
  wp_for HI
  by_cases hlt : sint.Z j < sint.Z s.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    obtain ⟨tv, htv⟩ : ∃ tv, ts[sint.nat j]? = some tv :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index s (sint.Z j) ts _ tv Hj.1) $$ [] as -
    · iframe #; ipureintro; simpa [sint.nat] using htv
    ihave #Htv := BigSepL.bigSepL_lookup (Φ := fun _ t => termOk (GF := GF) t) htv $$ Hts
    wp_apply (wp_match term_ptr tv v.ObjectMeta'.Labels' dq d.ObjectMeta'.Labels' fm (DFrac.own 1)
        (some (nodeFieldsM d.ObjectMeta'.Name'))) $$ [$term $Htv $Hlab Hfm]
      as %b %tes ⟨term, Hlab, Hfm, %Hb⟩
    · unfold ownMapD; iexact Hfm
    iunfold ownMapD at Hfm
    iunfold termOk at Htv
    icases Htv with ⟨-, -, %pes, #Hpes⟩
    by_cases hpe : tv.parseErrs' = slice.nil
    · have htes : tes = slice.nil := Hb.2 hpe
      subst htes
      wp_auto
      cases b
      · -- no match: the next term
        wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, es, L
        iframe
        ipureintro; exact ⟨by word, by word⟩
      · -- a match: `true`
        wp_auto
        wp_for_post
        iapply HΦ
        iunfold nodeAt
        iexists v
        iframe
        iapply Hdback $$ Hlab
    · obtain ⟨hbf, htes⟩ := Hb.1 hpe
      subst hbf htes
      ihave %Hplen := ownSlice_len _ _ _ $$ Hpes
      wp_if_destruct
      · -- parse errors: appended, the next term
        wp_apply (wp_slice_append (V := GoInterface) es L tv.parseErrs' pes DFrac.discard)
          $$ [$Hes $Hcap $Hpes] as %es' ⟨Hes, Hcap, -⟩
        wp_for_post
        iframe
        iexists j + W64 1, es', L ++ pes
        iframe
        ipureintro; exact ⟨by word, by word⟩
      · wp_for_post
        iframe
        iexists j + W64 1, es, L
        iframe
        ipureintro; exact ⟨by word, by word⟩
  · -- every term tried: `false` and the aggregated parse errors
    simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply (wp_NewAggregate es (DFrac.own 1) L) $$ [$Hes] as %a Hes
    wp_apply (wp_Flatten a) as %a' -
    iapply HΦ
    iunfold nodeAt
    iexists v
    iframe
    iapply Hdback $$ Hlab

end proof

end dsctl
end EtcdGrove
end Perennial
