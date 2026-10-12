/-
Proof of `Spec/IsEmptyHardState.lean`. Lean-first (no Rocq counterpart).
-/
module

public import EtcdDeps.Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import EtcdDeps.Spec.go_etcd_io.raft.v3.isHardStateEqual

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
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem IsEmptyHardState.wp_proof
    (wp_isHardStateEqual : isHardStateEqual.spec (GF := GF) (hG := hG)) :
    IsEmptyHardState.spec (GF := GF) (hG := hG) := by
  intro st hs
  wp_start as #Hst
  ihave Hri : (raftInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold raftInit at Hri
  icases Hri with ⟨%e, #He, %Hen, #Ht, #Hv, #Hc⟩
  wp_auto
  wp_if_destruct
  · -- `st == nil`: the nil hard state reads as the empty one
    iunfold hardStateAt at Hst
    simp only [↓reduceIte]
    icases Hst with %Hhs
    iapply HΦ
    ipureintro
    simp [Hhs]
  · ihave #He' : hardStateAt (GF := GF) e HardStateModel.empty $$ []
    · iunfold hardStateAt
      rw [if_neg Hen]
      iexists null, null, null
      iframe Ht Hv Hc
      simp only [optU64, ↓reduceIte, HardStateModel.empty]
      isplit <;> try isplit
      all_goals itrivial
    wp_apply wp_isHardStateEqual st e hs HardStateModel.empty $$ [$Hpkg $Hst $He'] as %r Hr
    iapply HΦ
    iexact Hr

end proof

end EtcdGrove
end Perennial
