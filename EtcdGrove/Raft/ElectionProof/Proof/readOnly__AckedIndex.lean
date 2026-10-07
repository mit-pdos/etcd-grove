/-
Port of election_proof/proof_readOnly__AckedIndex.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.readOnly__AckedIndex

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
/-- One map lookup. -/
theorem readOnly.AckedIndex.wp_proof : readOnly.AckedIndex.spec (GF := GF) (hG := hG) := by
  intro ro r voterID
  wp_start as Hown
  iNamed Hown
  iunfold ownReadOnly at Hown
  icases Hown with ⟨%rov, %ptrs, Hown⟩
  iNamed Hown
  wp_auto
  wp_apply wp_map_lookup2 $$ Hacks as Hacks
  simp only [Bool.decide_eq_true, show zero_val w64 = W64 0 from rfl]
  iapply HΦ
  unfold ownReadOnly
  iexists rov, ptrs
  simp only [named]
  iframe
  ipureintro; exact ⟨Hro_safe, Hro_conf⟩

end proof

end EtcdGrove
end Perennial
