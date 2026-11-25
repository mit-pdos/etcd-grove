-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/appendBytes.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/appendBytes.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.appendBytes
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.appendVarint

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.appendBytes.wp_proof
    (wp_appendVarint : raftpb.appendVarint.spec (GF := GF) (hG := hG)) :
    raftpb.appendBytes.spec (GF := GF) (hG := hG) := by
  intro b B v dq vs
  wp_start as ⟨Hb, Hcap, Hv⟩
  ihave %Hlen := ownSlice_len $$ Hv
  wp_auto
  wp_apply wp_appendVarint $$ [$Hb $Hcap] as %s ⟨Hs, Hcap⟩
  wp_apply wp_slice_append $$ [$Hs $Hcap $Hv] as %s2 ⟨Hs2, Hcap, Hv⟩
  iapply HΦ
  iframe
  have hl : W64 (vs.length : Int) = v.len := by word
  unfold ccBytesEnc
  rw [hl, List.append_assoc]
  iframe

end proof

end EtcdGrove
end Perennial
