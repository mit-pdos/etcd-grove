module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.updated
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.splitKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Obj)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option hygiene false in
/-- `updated` after the rejection test: the copy, updated unless `in.NoOp`. -/
local macro "upd_rest" : tactic => `(tactic| (
  ihave Hp : p ↦{dq} v $$ [Namespace Name pUID Value pNode pApp ResourceVersion Annotated]
  · iapply typedPointsto_combine p _ dq Hpn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  (try wp_auto)
  icases (typedPointsto_not_null_dup _ _ _) $$ c with ⟨c, %Hcn⟩
  iStructNamed c
  cases hno : inp.NoOp'
  · (try wp_auto)
    by_cases hnm : v.Name' = []
    · rw [decide_eq_true hnm]
      (try wp_auto)
      wp_apply wp_splitKey
      (try wp_auto)
      iapply HΦ
      simp only [hrf, Bool.false_eq_true, ↓reduceIte]
      iframe Hp
      isplitr
      · ipureintro; simp [Hcn]
      iapply typedPointsto_combine c_ptr _ _ Hcn
      simp only [TypedPointsto.typedPointstoDef, updGo, hno, hnm, Bool.false_eq_true, ↓reduceIte]
      iframe
    · rw [decide_eq_false hnm]
      (try wp_auto)
      iapply HΦ
      simp only [hrf, Bool.false_eq_true, ↓reduceIte]
      iframe Hp
      isplitr
      · ipureintro; simp [Hcn]
      iapply typedPointsto_combine c_ptr _ _ Hcn
      simp only [TypedPointsto.typedPointstoDef, updGo, hno, hnm, Bool.false_eq_true, ↓reduceIte]
      iframe
  · (try wp_auto)
    iapply HΦ
    simp only [hrf, Bool.false_eq_true, ↓reduceIte]
    iframe Hp
    isplitr
    · ipureintro; simp [Hcn]
    iapply typedPointsto_combine c_ptr _ _ Hcn
    simp only [TypedPointsto.typedPointstoDef, updGo, hno, ↓reduceIte]
    iframe))

theorem updated.wp_proof (wp_splitKey : splitKey.spec (GF := GF) (hG := hG)) :
    updated.spec (GF := GF) (hG := hG) := by
  intro inp p dq v
  wp_start as Hp
  icases (typedPointsto_not_null_dup _ _ _) $$ Hp with ⟨Hp, %Hpn⟩
  iStructNamed Hp
  irename UID => pUID
  irename Node => pNode
  irename App => pApp
  (try wp_auto)
  iStructNamed «in»
  irename UID => inUID
  irename Node => inNode
  irename App => inApp
  by_cases hrj : rejects inp.HasReject' inp.Reject' v.Node' = true
  · -- rejected
    have hh : inp.HasReject' = true := by simp [rejects] at hrj; exact hrj.1
    have hn : v.Node' = inp.Reject' := by simp [rejects] at hrj; exact hrj.2
    rw [hh]
    (try wp_auto)
    rw [decide_eq_true hn]
    ihave Hp : p ↦{dq} v $$ [Namespace Name pUID Value pNode pApp ResourceVersion Annotated]
    · iapply typedPointsto_combine p _ dq Hpn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hi with ⟨-, -, -, -, ⟨%eU, #HeU, -⟩⟩
    (try wp_auto)
    iapply HΦ
    simp only [rejects, hn, decide_true, Bool.and_self, ↓reduceIte]
    iframe Hp
    iexact HeU
  have hr : rejects inp.HasReject' inp.Reject' v.Node' = false := by simpa using hrj
  cases hh : inp.HasReject'
  · have hrf : rejects false inp.Reject' v.Node' = false := rfl
    (try wp_auto)
    upd_rest
  · have hn : ¬ v.Node' = inp.Reject' := by simpa [rejects, hh] using hr
    have hrf : rejects true inp.Reject' v.Node' = false := by simp [rejects, hn]
    (try wp_auto)
    rw [decide_eq_false hn]
    (try wp_auto)
    upd_rest

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
