/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/Epoch__HasWitness.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Epoch__HasWitness

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

theorem tracker.Epoch.HasWitness.wp_proof : tracker.Epoch.HasWitness.spec (GF := GF) (hG := hG) := by
  intro e
  wp_start as #He
  icases ownEpochNW_fields e $$ He with ⟨-, #Hw0, -, #Hw1, -⟩
  wp_auto
  iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
