/- Port of election_proof/proof_MakeProgressTracker.v. -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.MakeProgressTracker

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

theorem tracker.MakeProgressTracker.wp_proof :
    tracker.MakeProgressTracker.spec (GF := GF) (hG := hG) := by
  intro mi mb
  wp_start as _
  -- the epoch is made read-only after the call (an update at the end)
  iapply wp_fupd
  wp_auto
  wp_apply wp_map_make1 as %v0 Hv0
  wp_apply wp_map_make1 as %vm Hvm
  wp_apply wp_map_make1 as %pm Hpm
  -- the epoch, read-only from now on, witness-free (2026-10-19)
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$v5» with #He
  imodintro
  iapply HΦ
  iframe
  isplitr
  · ipureintro
    simp [sint.nat]
  iunfold ownEpochNW
  iapply ownEpoch_bare_intro _ _ _ rfl rfl $$ He

end proof

end EtcdGrove
end Perennial
