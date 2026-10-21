/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfState__GetAutoLeave.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetAutoLeave

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

theorem raftpb.ConfState.GetAutoLeave.wp_proof :
    raftpb.ConfState.GetAutoLeave.spec (GF := GF) (hG := hG) := by
  intro p dq c
  wp_start as Hc
  iunfold csOpt at Hc
  icases Hc with (⟨%Hp, %Hc⟩ | Hc)
  · subst Hp Hc
    wp_auto
    iapply HΦ
    iunfold csOpt
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · simp only [ownCSM]
    iunfold csPts at Hc
    iNamed Hc
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave (⟨%Hq, %Hv⟩ | ⟨#Hq, %Hqn⟩) := cellRO_cases $$ cA
    · subst Hq
      wp_auto
      rw [show false = c.AutoLeave' from Hv.symm]
      iapply HΦ
      iunfold csOpt
      iright
      simp only [ownCSM]
      iunfold csPts
      iexists sv, sl, so, sn, null, pw, pwo
      isplitr
      · ipureintro; exact Hnn
      iframe
      iframe cA cW cWO Hpb
      ipureintro; exact Hal
    · wp_if_destruct
      · exact absurd rfl Hqn
      · iapply HΦ
        iunfold csOpt
        iright
        simp only [ownCSM]
        iunfold csPts
        iexists sv, sl, so, sn, pa, pw, pwo
        isplitr
        · ipureintro; exact Hnn
        iframe
        iframe cA cW cWO Hpb
        ipureintro; exact Hal

end proof

end EtcdGrove
end Perennial
