/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfChangeV2__LeaveJoint.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__LeaveJoint
public import Spec.github_com.gogo.protobuf.proto.Equal

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

theorem raftpb.ConfChangeV2.LeaveJoint.wp_proof
    (wp_gogoproto_Equal : gogoproto.Equal.spec (GF := GF) (hG := hG)) :
    raftpb.ConfChangeV2.LeaveJoint.spec (GF := GF) (hG := hG) := by
  intro c ccs dq
  wp_start as Hccs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hccs
  wp_auto
  wp_alloc q as Hq
  wp_auto
  wp_apply wp_gogoproto_Equal _ q
    ({ Transition' := c.Transition', Changes' := c.Changes', Context' := slice.nil } :
      raftpb.ConfChangeV2) _ _ rfl $$ [$c $Hq] as -
  have Hnil : c.Changes'.len = W64 0 ↔ ccs = [] := by
    constructor
    · intro h; apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, h]; rfl
    · intro h; subst h; simp only [List.length_nil] at Hlen; word
  simp only [Hnil]
  iapply HΦ $$ Hccs

end proof

end EtcdGrove
end Perennial
