/-
Port of election_proof/proof_raft__resetRandomizedElectionTimeout.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__resetRandomizedElectionTimeout
public import Spec.go_etcd_io.raft.v3.lockedRand__Intn

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

/-- The receiver of the `Intn` call is the global `globalRand`, loaded
through the read-only points-to that `isPkgInit raft` carries
(`isInitialized` in `Base.lean`); the same package predicate supplies
`isLockedRand` for it. The `+` wraps, and the spec is existential in
the sum, so nothing about the draw is needed beyond its existence. -/
theorem raft.resetRandomizedElectionTimeout.wp_proof
    (wp_lockedRand_Intn : lockedRand.Intn.spec (GF := GF) (hG := hG)) :
    raft.resetRandomizedElectionTimeout.spec (GF := GF) (hG := hG) := by
  intro cfg r id s
  wp_start as Hphys
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %e5, %gr, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  wp_auto
  -- `r.electionTimeout` is read twice, and `ownRaftPhys` does not track
  -- it, so the two reads are unrelated -- all `Intn` needs of its
  -- argument is the bound, which comes with each read
  wp_apply raft.wp_load_electionTimeout $$ Hphys as %et1 ⟨Hphys, %Het1⟩
  wp_apply raft.wp_load_electionTimeout $$ Hphys as %et2 ⟨Hphys, %Het2⟩
  wp_apply wp_lockedRand_Intn _ _ Het2 $$ [$HglobalRand] as %v %Hv
  wp_apply raft.wp_store_randomizedElectionTimeout $$ Hphys as Hphys
  iapply HΦ
  iexact Hphys

end proof

end EtcdGrove
end Perennial
