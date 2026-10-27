/-
Proof of `Spec/k8s_io/client_go/listers/apps/v1/daemonSetLister__GetPodDaemonSets.lean`.
Lean-first.

The loop over the listed DaemonSets keeps the picked ones so far (`flagged`, with the flags of the
DaemonSets visited, each the `selPicks` of its namespace and selector).
-/
module

public import Spec.k8s_io.client_go.listers.apps.v1.daemonSetLister__GetPodDaemonSets
public import Spec.k8s_io.client_go.listers.apps.v1.daemonSetLister__DaemonSets
public import Spec.k8s_io.apimachinery.pkg.labels.Everything
public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.LabelSelectorAsSelector
public import Proof.k8s_io.client_go.listers.apps.v1.ErrorfLabels

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appslisters

open Iris Iris.BI Iris.ProofMode cache listers labels k8s_io.client_go.listers.apps.v1

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.apps.v1.Assumptions]
variable [package_sem' : k8s_io.client_go.listers.Assumptions]

open Classical in
theorem daemonSetLister.GetPodDaemonSets.wp_proof
    (wp_DaemonSets : daemonSetLister.DaemonSets.spec (GF := GF) (hG := hG))
    (wp_List : daemonSetNamespaceLister.List.spec (GF := GF) (hG := hG))
    (wp_Everything : labels.Everything.spec (GF := GF) (hG := hG))
    (wp_LSAS : labels.LabelSelectorAsSelector.spec (GF := GF) (hG := hG)) :
    daemonSetLister.GetPodDaemonSets.spec (GF := GF) (hG := hG) := by
  intro s dq ca ts γ OK Fam kf res ns0 pod pns pname L F
  iintro %Φ ⟨#Hpkg, Hri, #Hca, Hrd, #Htyped, #Hq, #Hdss, #Hpod⟩ HAU
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  unfold metaView
  icases Hpod with ⟨#Hpns, #Hpname, %lm, #Hlm, #HL⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply (wp_map_len_lt lm L DFrac.discard) $$ [$HL] as ⟨-, %Hsz⟩
  by_cases hz : GMap.size L = 0
  · -- no labels: an error (committed at the state as it is)
    rw [show W64 (GMap.size L) = W64 0 by rw [hz]; rfl]
    iapply fupd_wp
    rw [Iris.Std.LawfulSet.diff_empty]
    imod HAU with ⟨%σ, ⟨Hst, %hσ⟩, Hcl⟩
    imod Hcl $$ [Hst] with HK
    · iframe; ipureintro; exact hσ
    imodintro
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    have hargs : ∀ a ∈ [interface.mkOk go.string #pname],
        (∃ x : GoString, a = interface.mkOk go.string #x) ∨
          ∃ m : Loc, a = interface.mkOk (go.GoType.MapType go.string go.string) #m := by
      intro a ha; rw [List.mem_singleton] at ha; subst ha; left; exact ⟨_, rfl⟩
    wp_apply (wp_Errorf_labelArgs _ _ _ hargs) $$ [$Hfmt $Hasl] as %err -
    iapply HK
    iframe
    iunfold podDSPost
    ileft; ipureintro; exact ⟨hz, by simp⟩
  have hnz : W64 (GMap.size L) ≠ W64 0 := by intro h; apply hz; word
  simp only [hnz, decide_false]
  wp_auto
  wp_apply wp_Everything as %sel #Hsel
  icases Hsel with ⟨%si, %hsi, #Hsn, #Hse⟩
  ihave #Hev : everySel sel $$ []
  · iunfold everySel; iexists si; iframe #; ipureintro; exact hsi
  wp_apply (wp_DaemonSets s dq (riVal ca res ns0) pns) $$ [$Hri] as Hri
  rw [show (⟨⟨interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #ca, res,
    pns⟩⟩ : daemonSetNamespaceLister) = dsnlVal ca res pns from rfl]
  wp_bind (App (Val #(methods daemonSetNamespaceLister.ty go!"List" #(dsnlVal ca res pns)))
    (Val #sel))
  iapply (wp_List ca ts γ OK Fam kf res pns sel F) $$ [$Hpkg $Hca $Hrd $Htyped $Hev $Hq]
  inext
  imod HAU with ⟨%σ, ⟨Hst, %hσ⟩, Hcl⟩
  imodintro
  iexists σ
  iframe Hst
  isplitr
  · ipureintro; exact hσ
  iintro ⟨Hst, -⟩
  imod Hcl $$ [Hst] with HK
  · iframe; ipureintro; exact hσ
  imodintro
  iintro %sl %err ⟨%herr, %q, %ks, %ls, #Hns, %Hls, Hqm, Hsl, #Hoks, Hrd⟩
  subst herr
  wp_auto
  rename_i ip2
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  -- the loop over the listed DaemonSets: the flags of those visited, the picked ones kept
  ihave HI : (∃ (j : w64) (bs : List Bool) (dsl : GoSlice) (x : w64) (d0 : Loc)
      (sel0 err0 : GoInterface),
      "i" ∷ i_ptr ↦ j ∗ "i2" ∷ ip2 ↦ x ∗ "daemonSet" ∷ daemonSet_ptr ↦ d0 ∗
      "selector" ∷ selector_ptr ↦ sel0 ∗ "err" ∷ err_ptr ↦ err0 ∗
      "daemonSets" ∷ daemonSets_ptr ↦ dsl ∗
      "Hdsl" ∷ dsl ↦* flagged ls bs ∗
      "Hcap" ∷ ownSliceCap Loc dsl (DFrac.own 1) ∗
      "%Hj" ∷ ⌜sint.nat j = bs.length ∧ bs.length ≤ ls.length ∧ 0 ≤ sint.Z j⌝ ∗
      "#Hbs" ∷ □ ([∗list] k ↦ d ∈ ls.take bs.length, ∃ (dns : GoString) (S : Option SelV),
        dsView d dns S ∗ ⌜bs[k]? = some (decide (selPicks (some pns) L S dns))⌝) ∗
      "Hsl" ∷ sl ↦* ls ∗ "list" ∷ list_ptr ↦ sl ∗ "pod" ∷ pod_ptr ↦ pod : IProp GF)
    $$ [-HK Hri Hrd Hqm]
  · iexists W64 0, [], slice.nil, _, _, _, _
    iframe
    simp only [flagged_nil]
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · ipureintro; simp
    · imodintro; simp only [List.length_nil, List.take_zero]; iapply BigSepL.bigSepL_nil.2; itrivial
  wp_for HI
  by_cases hlt : sint.Z j < sint.Z sl.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    have hjl : bs.length < ls.length := by
      have := Hlen.1; rw [← Hj.1]; word
    obtain ⟨d, hd⟩ : ∃ d, ls[sint.nat j]? = some d :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hj.1]; exact hjl)⟩
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.2.2, hlt⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply (wp_load_slice_index sl (sint.Z j) ls _ d Hj.2.2) $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hd
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.2.2, hlt⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply (wp_load_slice_index sl (sint.Z j) ls _ d Hj.2.2) $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hd
    -- the DaemonSet's namespace and selector
    ihave #Hokd := (BigSepL.bigSepL_lookup (Φ := fun _ l => iprop(OK (ptrObj
      k8s_io.api.apps.v1.DaemonSet.ty l))) hd) $$ Hoks
    iunfold dsSel at Hdss
    ihave ⟨%dns, %S, #Hdv⟩ := Hdss $$ %d Hokd
    iunfold dsView at Hdv
    icases Hdv with ⟨#Hdns, %ls0, #Hls0, #Hlso⟩
    (try wp_auto)
    by_cases hns : dns = pns
    · rw [show decide (dns = pns) = true from decide_eq_true hns]
      wp_auto
      wp_apply (wp_LSAS ls0 S) $$ [$Hlso] as %sel1 %err1 Hr
      icases Hr with (%Herr | ⟨%Herr, #Hsel1⟩)
      · -- an invalid selector: skipped
        obtain ⟨hne, hval⟩ := Herr
        cases err1 with
        | nil => exact absurd rfl hne
        | ok ei =>
        wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, bs ++ [false], dsl, _, d, _, _
        rw [flagged_snoc ls bs false d (by rw [← Hj.1]; exact hd)]
        simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
        iframe
        isplitr
        · ipureintro
          refine ⟨by simp; word, by simp; omega, by word⟩
        iapply (visited_snoc ls bs d (by rw [← Hj.1]; exact hd) (some pns) L dns S false ?_) $$ [$Hbs]
        · simp [selPicks, hval]
        · iunfold dsView
          isplitr
          · iexact Hdns
          · iexists ls0; iframe #
      · obtain ⟨rfl, hval⟩ := Herr
        iunfold selOk at Hsel1
        icases Hsel1 with ⟨%i1, %hi1, #Hemp, #Hmat⟩
        subst hi1
        wp_auto
        wp_bind (App (Val #(methods i1.ty go!"Empty" i1.v)) (Val #()))
        iapply Hemp
        · itrivial
        inext
        iintro -
        cases hE : selEmpty S
        · wp_auto
          ihave #Hm1 := Hmat $$ %lm %L
          wp_bind (App (Val #(methods i1.ty go!"Matches" i1.v)) _)
          iapply Hm1
          · iexact HL
          inext
          iintro -
          by_cases hm : selMatch S L
          · -- picked: appended
            simp only [hm, _root_.decide_true]
            wp_auto
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, -⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hdsl $Hcap $Hl1] as %dsl' ⟨Hdsl, Hcap, -⟩
            (try wp_auto)
            wp_for_post
            iframe
            iexists j + W64 1, bs ++ [true], dsl', _, d, _, _
            rw [flagged_snoc ls bs true d (by rw [← Hj.1]; exact hd)]
            simp only [↓reduceIte]
            iframe
            isplitr
            · ipureintro
              refine ⟨by simp; word, by simp; omega, by word⟩
            iapply (visited_snoc ls bs d (by rw [← Hj.1]; exact hd) (some pns) L dns S true ?_) $$ [$Hbs]
            · simp [selPicks, hns, hval, hE, hm]
            · iunfold dsView
              isplitr
              · iexact Hdns
              · iexists ls0; iframe #
          · simp only [hm, decide_false]
            wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, bs ++ [false], dsl, _, d, _, _
            rw [flagged_snoc ls bs false d (by rw [← Hj.1]; exact hd)]
            simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
            iframe
            isplitr
            · ipureintro
              refine ⟨by simp; word, by simp; omega, by word⟩
            iapply (visited_snoc ls bs d (by rw [← Hj.1]; exact hd) (some pns) L dns S false ?_) $$ [$Hbs]
            · simp [selPicks, hm]
            · iunfold dsView
              isplitr
              · iexact Hdns
              · iexists ls0; iframe #
        · wp_auto
          wp_for_post
          iframe
          iexists j + W64 1, bs ++ [false], dsl, _, d, _, _
          rw [flagged_snoc ls bs false d (by rw [← Hj.1]; exact hd)]
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
          iframe
          isplitr
          · ipureintro
            refine ⟨by simp; word, by simp; omega, by word⟩
          iapply (visited_snoc ls bs d (by rw [← Hj.1]; exact hd) (some pns) L dns S false ?_) $$ [$Hbs]
          · simp [selPicks, hE]
          · iunfold dsView
            isplitr
            · iexact Hdns
            · iexists ls0; iframe #
    · simp only [hns, decide_false, Bool.not_false]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, bs ++ [false], dsl, _, d, _, _
      rw [flagged_snoc ls bs false d (by rw [← Hj.1]; exact hd)]
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
      iframe
      isplitr
      · ipureintro
        refine ⟨by simp; word, by simp; omega, by word⟩
      iapply (visited_snoc ls bs d (by rw [← Hj.1]; exact hd) (some pns) L dns S false ?_) $$ [$Hbs]
      · simp [selPicks, hns]
      · iunfold dsView
        isplitr
        · iexact Hdns
        · iexists ls0; iframe #
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hjeq : bs.length = ls.length := by
      have := Hlen.1; rw [← Hj.1]; word
    ihave %Hdl := ownSlice_len _ _ _ $$ Hdsl
    rw [hjeq, List.take_length]
    wp_auto
    by_cases hf : flagged ls bs = []
    · have h0 : dsl.len = W64 0 := by rw [hf] at Hdl; simp at Hdl; word
      rw [h0]
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      simp only [go.arrayLiteralSize, List.foldl]
      simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl,
        List.set_cons_succ, List.set_cons_zero]
      have hargs : ∀ a ∈ [interface.mkOk go.string #pname, interface.mkOk go.string #pns,
          interface.mkOk (go.GoType.MapType go.string go.string) #lm],
          (∃ x : GoString, a = interface.mkOk go.string #x) ∨
            ∃ m : Loc, a = interface.mkOk (go.GoType.MapType go.string go.string) #m := by
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
        rcases ha with rfl | rfl | rfl
        · left; exact ⟨_, rfl⟩
        · left; exact ⟨_, rfl⟩
        · right; exact ⟨_, rfl⟩
      wp_apply (wp_Errorf_labelArgs _ _ _ hargs) $$ [$Hfmt $Hasl] as %err -
      iapply HK
      iframe
      iunfold podDSPost
      iright
      iexists q, ks, ls, bs
      iframe #
      isplitr
      · ipureintro; exact hz
      isplitr
      · ipureintro; exact ⟨Hls, hjeq⟩
      rw [hf]
      simp only [↓reduceIte]
      ipureintro; simp
    · have h0 : dsl.len ≠ W64 0 := by
        intro h; apply hf; rw [h] at Hdl
        cases hfl : flagged ls bs with
        | nil => rfl
        | cons _ _ => rw [hfl] at Hdl; simp at Hdl; word
      simp only [h0, decide_false]
      wp_auto
      iapply HK
      iframe
      iunfold podDSPost
      iright
      iexists q, ks, ls, bs
      iframe #
      isplitr
      · ipureintro; exact hz
      isplitr
      · ipureintro; exact ⟨Hls, hjeq⟩
      simp only [hf, ↓reduceIte]
      iframe

end proof

end appslisters
end EtcdGrove
end Perennial
