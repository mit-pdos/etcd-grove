/-
Proof of `Spec/HardState__GetTerm.lean`. Lean-first (no Rocq counterpart).
-/
module

public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

theorem raftpb.HardState.GetTerm.wp_proof : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG) := by
  intro p hs
  wp_start as #Hp
  iunfold hardStateAt at Hp
  by_cases hn : p = null
  · rw [ite_eq_left hn]
    icases Hp with %Hhs
    subst hn Hhs
    simp only [HardStateModel.empty]
    wp_auto
    iapply HΦ
    itrivial
  rw [ite_eq_right hn]
  icases Hp with ⟨%pt, %pv, %pc, #Ht, #Hpt, #Hv, #Hpv, #Hc, #Hpc⟩
  have hd : decide (p = null) = false := decide_eq_false hn
  wp_auto
  simp only [hd, Bool.not_false]
  wp_auto
  iunfold optU64 at Hpt
  by_cases hp : pt = null
  · rw [ite_eq_left hp]
    icases Hpt with %Hz
    subst hp
    (try wp_auto)
    rw [← Hz]
    iapply HΦ
    itrivial
  · rw [ite_eq_right hp]
    (try wp_auto)
    have hd' : decide (pt = null) = false := decide_eq_false hp
    simp only [hd', Bool.not_false]
    wp_auto
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
