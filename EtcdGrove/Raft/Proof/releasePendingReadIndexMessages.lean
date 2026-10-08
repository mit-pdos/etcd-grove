/-
Port of `election_proof/proof_releasePendingReadIndexMessages.v`.
-/
import EtcdGrove.Raft.Spec.releasePendingReadIndexMessages

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

/-- The length test reads `0` and the function returns. -/
theorem releasePendingReadIndexMessages.wp_proof :
    releasePendingReadIndexMessages.spec (GF := GF) (hG := hG) := by
  intro cfg r id s
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply raft.wp_load_pendingReadIndexMessages $$ Hphys as %sl ⟨Hphys, %Hsl⟩
  rw [Hsl]
  wp_auto
  wp_end

end proof

end EtcdGrove
end Perennial
