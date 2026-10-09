/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.raft__softState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raft.softState.wp_proof : raft.softState.spec (GF := GF) (hG := hG) := by
  intro cfg r id s
  wp_start as Hphys
  wp_auto
  wp_apply raft.wp_load_lead $$ Hphys as Hphys
  wp_apply raft.wp_load_state $$ Hphys as Hphys
  rw [show ({ Lead' := s.lead, RaftState' := stateW64 s.role } : SoftState) =
    softstateVal (nodeSoftstate s) from rfl]
  iapply HΦ $$ Hphys

end proof

end EtcdGrove
end Perennial
