/-
Lean-first (no Rocq counterpart).

The proof of `WatchValidator.checkWatch` on a watch it accepts (`wInPre`): the key is one `PrepareKey`
takes (`checkKey`), the resource version parses, the driver's selectors are not nil, no limit nor
continue token, the driver's predicate has `GetAttrs`, no timestamps, the legacy initial events are
excluded (a watch without `SendInitialEvents` starts from a positive revision, not `""`; `"0"` does not
parse), and a watch-list asks for bookmarks.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__checkWatch
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.checkKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ParseResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__Empty
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchLemmas

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

theorem WatchValidator.checkWatch.wp_proof
    (wp_CK : checkKey.spec (GF := GF) (hG := hG))
    (wp_PRV : k8s_etcd3.versioner.ParseResourceVersion.spec (GF := GF) (hG := hG))
    (wp_SE : storage.SelectionPredicate.Empty.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG)) :
    WatchValidator.checkWatch.spec (GF := GF) (hG := hG) := by
  intro rp x req hpre
  obtain ⟨hpk, hlim, n, hn, hn63, hok, hbm, hsi⟩ := hpre
  wp_start as #Hreq
  unfold wreqRep
  icases Hreq with ⟨%p, %hreq, #Hsie⟩
  subst hreq
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave #Hl := labelSelOk_driver wp_LM wp_LE x $$ Hpkg2
  ihave #Hf := fieldSelOk_driver wp_FM wp_FE x $$ Hpkg2
  wp_auto
  wp_apply (wp_CK x.WKey' x.Recursive') as %cerr %hcerr
  have hce : cerr = GoInterface.nil := hcerr.2 hpk
  subst hce
  wp_auto
  wp_apply (wp_PRV x.MinRV') as %n' %perr Hpr
  rw [hn]
  icases Hpr with %Hpr
  obtain ⟨rfl, rfl⟩ := Hpr
  wp_auto
  simp only [hlim]
  wp_auto
  iStructNamed opts
  ihave #Hl' : k8s.labelSelOk (watchOptsV x p).Predicate'.Label' (labelSelL x).all' (lmL (labelSelL x)) $$ []
  · rw [show (watchOptsV x p).Predicate'.Label' = (predV x).Label' from rfl]; iexact Hl
  ihave #Hf' : k8s.fieldSelOk (watchOptsV x p).Predicate'.Field' (decide ((fieldSelForL x).n' = W64 0))
      (fmL (fieldSelForL x)) $$ []
  · rw [show (watchOptsV x p).Predicate'.Field' = (predV x).Field' from rfl]; iexact Hf
  wp_apply (wp_SE _ (DFrac.own 1) (watchOptsV x p).Predicate' _ _ _ _ rfl) $$ [$Predicate $Hl' $Hf']
    as Predicate
  cases hb : (decide (x.SelApp' = []) && decide ((fieldSelForL x).n' = W64 0))
  all_goals simp only [Bool.not_true, Bool.not_false]
  all_goals wp_auto
  all_goals (try (simp only [decide_eq_false getAttrs_func_ne_nil]; wp_auto))
  all_goals
    by_cases hp2 : x.SendInit' = W64 2
    · have hbt := hbm hp2
      have hsie : sieOfL x = some true := by simp [sieOfL, hp2]
      isimp only [hsie] at Hsie
      iunfold k8s.sendInitIs at Hsie
      ihave %hpn := typedPointsto_not_null _ _ _ $$ Hsie
      simp only [decide_eq_false hpn]
      wp_auto
      simp only [decide_eq_false hpn]
      wp_auto
      simp only [hbt, Bool.not_true]
      wp_auto
      iapply HΦ; ipureintro; rfl
    · by_cases hp1 : x.SendInit' = W64 1
      · have hsie : sieOfL x = some false := by simp [sieOfL, hp1]
        isimp only [hsie] at Hsie
        iunfold k8s.sendInitIs at Hsie
        ihave %hpn := typedPointsto_not_null _ _ _ $$ Hsie
        simp only [decide_eq_false hpn]
        wp_auto
        simp only [decide_eq_false hpn]
        wp_auto
        iapply HΦ; ipureintro; rfl
      · have hsie : sieOfL x = none := by
          unfold sieOfL
          split <;> (try split) <;> first | rfl | (exfalso; apply hp2; assumption)
        have hn0 : 0 < uint.nat n' := by
          rcases hsi hp2 with h | h
          · exact absurd h hp1
          · exact h
        isimp only [hsie] at Hsie
        iunfold k8s.sendInitIs at Hsie
        icases Hsie with %hpn
        subst hpn
        have he : x.MinRV' ≠ [] := by
          intro h; rw [h] at hn; simp [parseRVD] at hn; subst hn; simp at hn0
        have h0 : x.MinRV' ≠ go!"0" := by
          intro h; rw [h] at hn; simp [parseRVD] at hn
        simp only [_root_.decide_true]
        wp_auto
        simp only [decide_eq_false he]
        wp_auto
        simp only [decide_eq_false h0]
        wp_auto
        iapply HΦ; ipureintro; rfl

end proof

end k8s_correctness
end EtcdGrove
end Perennial
