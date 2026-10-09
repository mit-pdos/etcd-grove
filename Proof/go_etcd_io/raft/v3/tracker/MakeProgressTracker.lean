/- Port of election_proof/proof_MakeProgressTracker.v. -/
module

public import Spec.go_etcd_io.raft.v3.tracker.MakeProgressTracker

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

theorem tracker.MakeProgressTracker.wp_proof :
    tracker.MakeProgressTracker.spec (GF := GF) (hG := hG) := by
  intro mi mb
  wp_start as _
  wp_auto
  wp_apply wp_map_make1 as %v0 Hv0
  wp_apply wp_map_make1 as %vm Hvm
  wp_apply wp_map_make1 as %pm Hpm
  iapply HΦ
  iframe
  ipureintro
  simp [sint.nat]

end proof

end EtcdGrove
end Perennial
