/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/MarshalConfChange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.MarshalConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV1
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV1
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__Marshal
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__Marshal

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

theorem raftpb.MarshalConfChange.wp_proof
    (wp_ConfChange_AsV1 : raftpb.ConfChange.AsV1.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV1 : raftpb.ConfChangeV2.AsV1.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChange_Marshal : raftpb.ConfChange.Marshal.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_Marshal : raftpb.ConfChangeV2.Marshal.spec (GF := GF) (hG := hG)) :
    raftpb.MarshalConfChange.spec (GF := GF) (hG := hG) := by
  intro c o dq
  wp_start as Hc
  rcases o with _ | (m | m)
  · simp only [ownCCI, ccEntryType]
    icases Hc with %Hc
    subst Hc
    wp_auto
    simp only [raftpb.EntryConfChangeV2]
    wp_auto
    ihave Hnil : (slice.nil ↦* ([] : List w8)) $$ []
    · iapply ownSlice_nil
    iapply HΦ $$ %slice.nil %([] : List w8)
    iframe
    ipureintro; rfl
  · simp only [ownCCI, ccEntryType]
    icases Hc with ⟨%v, %Hc, Hown⟩
    subst Hc
    wp_auto
    wp_apply wp_ConfChange_AsV1
    simp only [raftpb.EntryConfChange]
    wp_auto
    wp_apply wp_ConfChange_Marshal _ v m (DFrac.own 1) dq $$ [$ccv1 $Hown]
      as %sl %bs ⟨-, Hown, Hsl, %Hdec⟩
    iapply HΦ $$ %sl %bs
    iframe
    ipureintro
    exact ⟨rfl, Hdec⟩
  · simp only [ownCCI, ccEntryType]
    icases Hc with ⟨%v, %Hc, Hown⟩
    subst Hc
    wp_auto
    wp_apply wp_ConfChangeV2_AsV1
    wp_apply wp_ConfChangeV2_AsV2
    simp only [raftpb.EntryConfChangeV2]
    wp_auto
    wp_apply wp_ConfChangeV2_Marshal _ v m (DFrac.own 1) dq $$ [$ccv2 $Hown]
      as %sl %bs ⟨-, Hown, Hsl, %Hdec⟩
    iapply HΦ $$ %sl %bs
    iframe
    ipureintro
    exact ⟨rfl, Hdec⟩

end proof

end EtcdGrove
end Perennial
