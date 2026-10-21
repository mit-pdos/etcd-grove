/-
Port of election_proof/proof_IsEmptyHardState.v.
-/
module

public import Proof.go_etcd_io.raft.v3.LemmasMiscR
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.isHardStateEqual

@[expose] public section

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
  ihave Hinit := isInitialized_access $$ Hpkg
  ihave ⟨%es, #Hg, #Hes⟩ := emptyState_hsRO $$ Hinit
  wp_auto
  wp_if_destruct
  · -- `st == nil`: the zero record
    iunfold hsOpt at Hst
    icases Hst with (⟨%Hp, %Hh⟩ | #Hst)
    · subst Hh
      ispecialize HΦ $$ []
      · itrivial
      iExactEq HΦ
      simp
    · iNamed Hst
      exact absurd rfl Hnn
  · wp_apply wp_isHardStateEqual st es hs (HardStateM.mk (W64 0) (W64 0) (W64 0)) $$ [$Hst]
    · iunfold hsOpt; iright; iexact Hes
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
