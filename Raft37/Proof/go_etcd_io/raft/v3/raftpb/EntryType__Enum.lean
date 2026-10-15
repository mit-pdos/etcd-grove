/-
Proof of `Raft37/Spec/go_etcd_io/raft/v3/raftpb/EntryType__Enum.lean`.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EntryType__Enum

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

theorem raftpb.EntryType.Enum.wp_proof :
    raftpb.EntryType.Enum.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
