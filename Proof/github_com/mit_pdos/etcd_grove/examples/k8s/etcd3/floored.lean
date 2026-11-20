module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.floored

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

theorem floored.wp_proof : floored.spec (GF := GF) (hG := hG) := by
  intro r f
  wp_start as -
  wp_auto
  by_cases h0 : r = W64 0
  · subst h0
    have e : flooredL (W64 0) f = W64 0 := by unfold flooredL; simp
    rw [e]
    wp_auto
    iapply HΦ; itrivial
  · rw [decide_eq_false h0]
    wp_auto
    by_cases h1 : r < f
    · rw [decide_eq_true (show uint.Z r < uint.Z f by word)]
      have e : flooredL r f = f := by unfold flooredL; rw [if_pos ⟨h0, h1⟩]
      rw [e]
      wp_auto
      iapply HΦ; itrivial
    · rw [decide_eq_false (show ¬ uint.Z r < uint.Z f by word)]
      have e : flooredL r f = r := by unfold flooredL; rw [if_neg (fun h => h1 h.2)]
      rw [e]
      wp_auto
      iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
