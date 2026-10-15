/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__RemoveMember.lean`.
Lean-first (no Rocq counterpart), 2026-10-15 (stage N).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__RemoveMember
public import Spec.go_etcd_io.raft.v3.node__ProposeConfChange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem Register.RemoveMember.wp_proof
    (wp_node_ProposeConfChange : node.ProposeConfChange.spec (GF := GF) (hG := hG)) :
    Register.RemoveMember.spec (GF := GF) (hG := hG) := by
  intro γr γp r id Hok
  wp_start as #Hreg
  iunfold isRegister at Hreg
  icases Hreg with ⟨%id0, %n, %st, #Hrep⟩
  iunfold isReplica at Hrep
  iNamed Hrep
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  ihave Hcci : ownCCI (interface.mkOk raftpb.ConfChange.ty
      #({ Type' := W32 1, NodeId' := id, Context' := slice.nil, Id' := 0 } : raftpb.ConfChange))
      (DFrac.own 1) (some (.v1 (rmCC id))) $$ []
  · simp only [ownCCI, ownCCV1]
    iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    simp only [rmCC]
    iapply ownSlice_nil
  wp_apply wp_node_ProposeConfChange γp.node id0 n _ (.v1 (rmCC id)) (DFrac.own 1)
      (by rw [Hraft]; exact Hok) $$ [$Hraftinit $HisNode $Hcci] as %err -
  iapply HΦ
  itrivial

end proof

end register
end EtcdGrove
end Perennial
