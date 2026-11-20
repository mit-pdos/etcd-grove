/-
Lean-first (no Rocq counterpart).

The proof of `WatchValidator.validateInitialEvents` on the accepting run: the requested resource
version (other than `""` and `"0"`) parses and is not above the bookmark's, the replay has a state at
the bookmark's resource version (`Replay.InitialEvents`), and its events compare equal to the initial
events (`compareEvents`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__validateInitialEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay__InitialEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__compareEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ParseResourceVersion

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

set_option hygiene false in
/-- The common end: `InitialEvents`, `compareEvents`. -/
local macro "vie_tail" : tactic => `(tactic| (
    wp_apply (wp_IE rp R x _ brv hst) $$ [] as %esl %eerr ⟨%heerr, %evs, %hevs, #Hevs⟩
    · iframe #
    subst heerr
    rw [hie, Option.some.injEq] at hevs
    subst hevs
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty) (m := go!"compareEvents")]
    wp_call
    (try wp_auto)
    wp_apply (wp_CE rp R esl sl exp init h2) $$ [] as %cerr %hcerr
    · iframe #
    subst hcerr
    wp_auto
    iapply HΦ; ipureintro; rfl))

theorem WatchValidator.validateInitialEvents.wp_proof
    (wp_PRV : k8s_etcd3.versioner.ParseResourceVersion.spec (GF := GF) (hG := hG))
    (wp_IE : Replay.InitialEvents.spec (GF := GF) (hG := hG))
    (wp_CE : WatchValidator.compareEvents.spec (GF := GF) (hG := hG)) :
    WatchValidator.validateInitialEvents.spec (GF := GF) (hG := hG) := by
  intro rp R x req sl init brv hok
  unfold initialOkL at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨h1, h2⟩ := hok
  cases hie : initialEventsR R x brv with
  | none => rw [hie] at h2; cases h2
  | some exp =>
  rw [hie] at h2
  simp only at h2
  have hst : (R.states !! brv).isSome := by
    unfold initialEventsR at hie
    cases h : R.states !! brv with
    | none => rw [h] at hie; cases hie
    | some _ => rfl
  wp_start as ⟨#HR, #Hreq, #Hs⟩
  ihave #HR0 := HR
  iunfold replayAt at HR0
  icases HR0 with ⟨#Hd, -⟩
  ihave #Hreq0 := Hreq
  iunfold wreqRep at Hreq0
  icases Hreq0 with ⟨%p, %hreq, #Hsie⟩
  subst hreq
  wp_auto
  by_cases hc : x.MinRV' ≠ [] ∧ x.MinRV' ≠ go!"0"
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h1
    cases hp : parseRVD x.MinRV' with
    | none => rw [hp] at h1; cases h1
    | some req =>
    rw [hp] at h1
    simp only [decide_eq_true_eq] at h1
    simp only [decide_eq_false hc.1]
    wp_auto
    simp only [decide_eq_false hc.2]
    wp_auto
    wp_apply (wp_PRV x.MinRV') as %n %perr Hpr
    rw [hp]
    icases Hpr with %Hpr
    obtain ⟨rfl, rfl⟩ := Hpr
    wp_auto
    have hlt : ¬ uint.Z brv < uint.Z n := by word
    simp only [hlt, decide_false]
    wp_auto
    vie_tail
  · by_cases he : x.MinRV' = []
    · simp only [he, decide_true, Bool.not_true]
      wp_auto
      vie_tail
    · have h0 : x.MinRV' = go!"0" := Classical.byContradiction fun h0 => hc ⟨he, h0⟩
      simp only [decide_eq_false he]
      wp_auto
      simp only [h0, decide_true]
      wp_auto
      vie_tail

end proof

end k8s_correctness
end EtcdGrove
end Perennial
