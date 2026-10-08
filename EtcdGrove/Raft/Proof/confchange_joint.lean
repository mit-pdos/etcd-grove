/-
Proof of `Spec/confchange_joint.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Raft.Spec.confchange_joint
import EtcdGrove.Raft.Spec.confchange_outgoing

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

theorem confchange.joint.wp_proof
    (wp_confchange_outgoing : confchange.outgoing.spec (GF := GF) (hG := hG)) :
    confchange.joint.spec (GF := GF) (hG := hG) := by
  intro cfg v Harr
  wp_start as _
  wp_auto
  -- `len` of the nil map is `0`, a pure step, and `0 > 0` is `false`
  wp_apply wp_confchange_outgoing _ v map.nil Harr
  wp_end

end proof

end EtcdGrove
end Perennial
