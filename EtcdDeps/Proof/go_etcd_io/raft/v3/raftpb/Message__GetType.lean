/-
Proof of `Spec/Message__GetType.lean`. Lean-first (no Rocq counterpart).
-/
module

public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType

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

theorem raftpb.Message.GetType.wp_proof : raftpb.Message.GetType.spec (GF := GF) (hG := hG) := by
  intro m to ty
  wp_start as #Hm
  iunfold msgAt at Hm
  icases Hm with ⟨%Hnn, %pto, %pty, #Hto, #Hpto, #Hty, #Hpty⟩
  have hd : decide (m = null) = false := decide_eq_false Hnn
  wp_auto
  simp only [hd, Bool.not_false]
  wp_auto
  iunfold optU32 at Hpty
  by_cases hp : pty = null
  · rw [ite_eq_left hp]
    icases Hpty with %Hz
    subst hp
    (try wp_auto)
    simp only [raftpb.MessageType_MsgHup]
    rw [← Hz]
    iapply HΦ
    itrivial
  · rw [ite_eq_right hp]
    (try wp_auto)
    have hd' : decide (pty = null) = false := decide_eq_false hp
    simp only [hd', Bool.not_false]
    wp_auto
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
