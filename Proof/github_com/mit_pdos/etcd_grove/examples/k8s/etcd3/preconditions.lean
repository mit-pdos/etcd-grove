module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.preconditions

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem preconditions.wp_proof :
    preconditions.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start as -
  cases hu : x.HasPreUID' <;> cases hr : x.HasPreRV'
  all_goals iapply wp_fupd
  all_goals wp_auto
  all_goals (repeat (first | (simp only [hu, hr]; wp_auto) | wp_auto))
  · imodintro
    iapply HΦ
    iunfold k8s.preAt
    ileft
    ipureintro
    exact ⟨rfl, by simp [kpreOf, hu, hr]⟩
  all_goals (try ipersist «$r0»)
  all_goals (try ipersist u)
  all_goals (try ipersist r)
  all_goals imodintro
  all_goals iapply HΦ
  all_goals iunfold k8s.preAt
  all_goals iright
  all_goals simp only [kpreOf, hu, hr, Bool.false_eq_true, ↓reduceIte, k8s.optStrPtr]
  · iexists _, _
    iframe «$r0» r
    ipureintro; rfl
  · iexists _, _
    iframe «$r0» u
    ipureintro; rfl
  · iexists _, _
    iframe «$r0» u r

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
