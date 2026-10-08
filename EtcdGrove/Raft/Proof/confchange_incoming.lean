/-
Proof of `Spec/confchange_incoming.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Raft.Spec.confchange_incoming

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

theorem confchange.incoming.wp_proof : confchange.incoming.spec (GF := GF) (hG := hG) := by
  intro jc v0 v1 Harr
  wp_start as _
  wp_alloc voters_ptr as voters; wp_pures
  -- `voters[0]`: peel element 0 off the array cell
  icases array_acc _ (sint.Z (W64 0)) _ _ _ v0 (by decide) (by rw [Harr]; rfl)
    $$ voters with ⟨Hv0, -⟩
  wp_load; wp_pures
  wp_end

end proof

end EtcdGrove
end Perennial
