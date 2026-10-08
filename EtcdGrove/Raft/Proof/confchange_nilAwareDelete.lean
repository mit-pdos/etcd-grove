/-
Proof of `Spec/confchange_nilAwareDelete.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Raft.Spec.confchange_nilAwareDelete

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

theorem confchange.nilAwareDelete.wp_proof :
    confchange.nilAwareDelete.spec (GF := GF) (hG := hG) := by
  intro mp id dq
  wp_start as Hm
  wp_auto
  wp_end

end proof

end EtcdGrove
end Perennial
