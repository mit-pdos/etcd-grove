/-
Proof of `Spec/confchange_outgoing.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.outgoing

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

theorem confchange.outgoing.wp_proof : confchange.outgoing.spec (GF := GF) (hG := hG) := by
  intro jc v0 v1 Harr
  wp_start as _
  wp_auto
  -- `voters[1]`: peel element 1 off the array cell
  icases array_acc _ (sint.Z (W64 1)) _ _ _ v1 (by decide) (by rw [Harr]; rfl)
    $$ voters with ⟨Hv1, -⟩
  wp_auto
  wp_end

end proof

end EtcdGrove
end Perennial
