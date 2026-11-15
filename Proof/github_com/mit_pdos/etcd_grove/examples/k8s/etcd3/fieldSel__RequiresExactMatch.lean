module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.fieldSel__RequiresExactMatch

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem fieldSel.RequiresExactMatch.wp_proof :
    fieldSel.RequiresExactMatch.spec (GF := GF) (hG := hG) := by
  intro s f
  wp_start
  wp_auto
  by_cases h1 : 1 ≤ sint.Z s.n'
  · rw [show decide (sint.Z (W64 1) ≤ sint.Z s.n') = true by simpa using h1]
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      isimp [h1] at HΦ
      iapply HΦ; itrivial
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_if_destruct
        all_goals (try wp_auto)
        all_goals (simp only [show sint.Z (W64 2) = 2 from rfl] at *; isimp [*] at HΦ; iapply HΦ; itrivial)
      · (try wp_auto)
        (simp only [show sint.Z (W64 2) = 2 from rfl] at *; isimp [*] at HΦ; iapply HΦ; itrivial)
  · rw [show decide (sint.Z (W64 1) ≤ sint.Z s.n') = false by simpa using h1]
    (try wp_auto)
    have h2 : ¬ sint.Z (W64 2) ≤ sint.Z s.n' := by word
    rw [show decide (sint.Z (W64 2) ≤ sint.Z s.n') = false by simpa using h2]
    (try wp_auto)
    (simp only [show sint.Z (W64 2) = 2 from rfl] at *; isimp [*] at HΦ; iapply HΦ; itrivial)

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
