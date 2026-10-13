/-
`quorum.mapAckIndexer.AckedIndex`, Lean-first.
-/
module

public import Spec.go_etcd_io.raft.v3.quorum.mapAckIndexer__AckedIndex

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

/-- One `map.lookup2`. -/
theorem quorum.mapAckIndexer.AckedIndex.wp_proof :
    quorum.mapAckIndexer.AckedIndex.spec (GF := GF) (hG := hG) := by
  intro mref dq mm id
  wp_start as Hm
  wp_auto
  wp_apply wp_map_lookup2 $$ Hm as Hm
  simp only [Bool.decide_eq_true]
  rw [show (zero_val w64) = W64 0 from rfl]
  iapply HΦ
  iexact Hm

end proof

end EtcdGrove
end Perennial
