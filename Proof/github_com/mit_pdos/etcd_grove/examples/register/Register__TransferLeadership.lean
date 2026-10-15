/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__TransferLeadership.lean`.
Lean-first (no Rocq counterpart), 2026-10-13.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__TransferLeadership
public import Spec.go_etcd_io.raft.v3.node__TransferLeadership

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

theorem Register.TransferLeadership.wp_proof
    (wp_node_TransferLeadership : node.TransferLeadership.spec (GF := GF) (hG := hG)) :
    Register.TransferLeadership.spec (GF := GF) (hG := hG) := by
  intro γr γp r to
  wp_start as #Hreg
  iunfold isRegister at Hreg
  icases Hreg with ⟨%id, %n, %st, #Hrep⟩
  iunfold isReplica at Hrep
  iNamed Hrep
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  wp_apply wp_node_TransferLeadership γp.node id n id to $$ [$Hraftinit $HisNode]
  iapply HΦ
  itrivial

end proof

end register
end EtcdGrove
end Perennial
