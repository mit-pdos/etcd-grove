/- Port of election_proof/proof_MakeProgressTracker.v. -/
import EtcdGrove.Raft.Spec.MakeProgressTracker

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

theorem tracker.MakeProgressTracker.wp_proof :
    tracker.MakeProgressTracker.spec (GF := GF) (hG := hG) := by
  intro mi mb
  wp_start as _
  wp_alloc maxBytes_ptr as maxBytes; wp_pures; wp_alloc maxInflight_ptr as maxInflight; wp_pures
  wp_load; wp_pures; wp_load; wp_pures; iclear maxBytes maxInflight
  wp_apply wp_map_make1 as %v0 Hv0
  wp_pures
  wp_apply wp_map_make1 as %vm Hvm
  wp_pures
  wp_apply wp_map_make1 as %pm Hpm
  wp_pures; wp_alloc p_ptr as p; wp_pures; wp_store; wp_pures; wp_load; wp_pures; iclear p
  iapply HΦ
  iframe
  ipureintro
  simp [sint.nat]

end proof

end EtcdGrove
end Perennial
