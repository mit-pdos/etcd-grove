/-
Lean-first (no Rocq counterpart).

The proof of `WatchValidator.compareEvents` on the accepting run: both reference slices are fresh and
not `nil` (`toEventReference`), with equal contents, so `cmp.Diff` is `""`; then each pair of objects
is a pair of equal read-only driver's objects, which `reflect.DeepEqual` finds equal.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__compareEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__toEventReference
public import Spec.github_com.google.go_cmp.cmp.Diff
public import Spec.reflect.DeepEqualK8s

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem mapM_evRefL_length {rs : List REv} {refs : List (GoString × GoString × w64)}
    (h : rs.mapM evRefL = some refs) : refs.length = rs.length := by
  induction rs generalizing refs with
  | nil => simp at h; subst h; rfl
  | cons r rs ih =>
    rw [List.mapM_cons] at h
    cases hr : evRefL r with
    | none => rw [hr] at h; cases h
    | some e =>
      cases hrs : rs.mapM evRefL with
      | none => rw [hr, hrs] at h; cases h
      | some es =>
        rw [hr, hrs] at h
        simp at h
        subst h
        simp [ih hrs]

/-- An event with a reference holds a driver's object. -/
theorem mapM_evRefL_obj {rs : List REv} {refs : List (GoString × GoString × w64)}
    (h : rs.mapM evRefL = some refs) {i : Nat} {r : REv} (hr : rs[i]? = some r) :
    ∃ o, r.o = .obj o := by
  induction rs generalizing refs i with
  | nil => simp at hr
  | cons r' rs ih =>
    rw [List.mapM_cons] at h
    cases hr' : evRefL r' with
    | none => rw [hr'] at h; cases h
    | some e =>
      cases hrs : rs.mapM evRefL with
      | none => rw [hr', hrs] at h; cases h
      | some es =>
        cases i with
        | zero =>
          simp at hr; subst hr
          unfold evRefL at hr'
          cases ho : r'.o with
          | obj o => exact ⟨o, rfl⟩
          | status s => rw [ho] at hr'; simp [keyOfL] at hr'
          | other => rw [ho] at hr'; simp [keyOfL] at hr'
        | succ i => exact ih hrs (by simpa using hr)

theorem WatchValidator.compareEvents.wp_proof
    (wp_toEventReference : WatchValidator.toEventReference.spec (GF := GF) (hG := hG))
    (wp_Diff : cmp.Diff.spec_eventRefs (GF := GF) (hG := hG))
    (wp_DE : reflect.DeepEqual.spec_k8s (GF := GF) (hG := hG)) :
    WatchValidator.compareEvents.spec (GF := GF) (hG := hG) := by
  intro rp R esl gsl es gs hok
  unfold compareEventsL at hok
  cases her : es.mapM evRefL with
  | none => rw [her] at hok; cases hok
  | some er =>
  cases hgr : gs.mapM evRefL with
  | none => rw [her, hgr] at hok; cases hok
  | some gr =>
  rw [her, hgr] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨heq, hobj⟩ := hok
  subst heq
  wp_start as ⟨#HR, #He, #Hg⟩
  ihave #Hcmp : isPkgInit (PROP := IProp GF) pkg_id.github_com.google.go_cmp.cmp $$ []
  · iPkgInit
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty) (m := go!"toEventReference")]
  wp_call
  (try wp_auto)
  wp_apply (wp_toEventReference rp R esl es er her) $$ [] as %s1 %e1 ⟨⟨%he1, %hs1⟩, Hs1⟩
  · iframe #
  subst he1
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty) (m := go!"toEventReference")]
  wp_call
  (try wp_auto)
  wp_apply (wp_toEventReference rp R gsl gs er hgr) $$ [] as %s2 %e2 ⟨⟨%he2, %hs2⟩, Hs2⟩
  · iframe #
  subst he2
  wp_auto
  wp_apply (wp_Diff s1 s2 _ _ (DFrac.own 1) (DFrac.own 1)) $$ [$Hs1 $Hs2] as %d ⟨%hd, Hs1, Hs2⟩
  have hd' : d = go!"" := hd.2 ⟨⟨fun h => absurd h hs1, fun h => absurd h hs2⟩, rfl⟩
  subst hd'
  wp_auto
  have hlen : es.length = gs.length := by
    rw [← mapM_evRefL_length her, ← mapM_evRefL_length hgr]
  iunfold evsRO at He
  icases He with ⟨%evs, #Hesl, #Hevs⟩
  iunfold evsRO at Hg
  icases Hg with ⟨%gvs, #Hgsl, #Hgvs⟩
  ihave %Hel := ownSlice_len $$ Hesl
  ihave %Hgl := ownSlice_len $$ Hgsl
  ihave %Hel2 := BigSepL2.bigSepL2_length $$ Hevs
  ihave %Hgl2 := BigSepL2.bigSepL2_length $$ Hgvs
  rename_i iv_ptr
  irename : (iv_ptr ↦ (zero_val w64) : IProp GF) => i0
  ihave HL : (∃ (j : w64) (iv : w64),
      "i" ∷ i_ptr ↦ j ∗ "i0" ∷ iv_ptr ↦ iv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z gsl.len⌝ : IProp GF) $$ [i i0]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by word⟩
  wp_for HL
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z gsl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    have hje : sint.Z j < sint.Z esl.len := by
      have : esl.len = gsl.len := by
        have h1 : sint.nat esl.len = sint.nat gsl.len := by rw [← Hel.1, ← Hgl.1, Hel2, Hgl2, hlen]
        word
      rw [this]; exact Hif
    list_elem evs (sint.nat j) as ve
    list_elem gvs (sint.nat j) as vg
    obtain ⟨re, hre⟩ : ∃ r, es[sint.nat j]? = some r := by
      have : sint.nat j < es.length := by rw [← Hel2]; word
      exact ⟨_, List.getElem?_eq_getElem this⟩
    obtain ⟨rg, hrg⟩ : ∃ r, gs[sint.nat j]? = some r := by
      have : sint.nat j < gs.length := by rw [← Hgl2]; word
      exact ⟨_, List.getElem?_eq_getElem this⟩
    have hoeq : re.o = rg.o := by
      have h1 : (es.map REv.o)[sint.nat j]? = (gs.map REv.o)[sint.nat j]? := by rw [hobj]
      simp only [List.getElem?_map, hre, hrg, Option.map_some, Option.some.injEq] at h1
      exact h1
    obtain ⟨o, ho⟩ := mapM_evRefL_obj her hre
    ihave #Hve := BigSepL2.bigSepL2_lookup (Φ := fun _ v r => evRep (GF := GF) v r)
      Hve_lookup hre $$ Hevs
    ihave #Hvg := BigSepL2.bigSepL2_lookup (Φ := fun _ v r => evRep (GF := GF) v r)
      Hvg_lookup hrg $$ Hgvs
    iunfold evRep at Hve
    iunfold evRep at Hvg
    icases Hve with ⟨%-, #Hoe⟩
    icases Hvg with ⟨%-, #Hog⟩
    isimp only [ho] at Hoe
    isimp only [← hoeq, ho] at Hog
    iunfold evObjRep at Hoe
    iunfold evObjRep at Hog
    icases ownSlice_elem_acc (sint.Z j) ve esl DFrac.discard evs Hj.1 Hve_lookup $$ Hesl
      with ⟨#Hpe, -⟩
    icases ownSlice_elem_acc (sint.Z j) vg gsl DFrac.discard gvs Hj.1 Hvg_lookup $$ Hgsl
      with ⟨#Hpg, -⟩
    iStructNamedSuffix Hpe "_e"
    iStructNamedSuffix Hpg "_g"
    have hbe : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z esl.len := ⟨Hj.1, hje⟩
    (try wp_auto)
    iterate 2
      (try simp only [hbe, Hb', _root_.and_self, ↓reduceIte])
      (try wp_auto)
    wp_apply (wp_DE.1 ve.Object' vg.Object' (.obj o) (.obj o) DFrac.discard DFrac.discard) $$ [Hoe Hog]
      as %b ⟨%hb, -, -⟩
    · iframe #
    have hbt : b = true := hb.2 rfl
    subst hbt
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, j
    iframe
    ipureintro; refine ⟨by word, by word⟩
  · (try wp_auto)
    iapply HΦ; ipureintro; rfl

end proof

end k8s_correctness
end EtcdGrove
end Perennial
