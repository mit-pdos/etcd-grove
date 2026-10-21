/-
`(*Epoch).ReplicateToWitness` (raft#168, `tracker/tracker.go`; 2026-10-19, witness support).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTracker

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `e.ReplicateToWitness()`: for each half, whether it has a witness and the witness is in
its replication set (`RSM.rep`). -/
abbrev tracker.Epoch.ReplicateToWitness.spec : Prop :=
  ∀ (e : Loc) (em : EpochM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownEpoch e em }}
    (App (Val (e @!! go.GoType.PointerType tracker.Epoch.ty @!! go!"ReplicateToWitness"))
      (Val #()))
  {{ RET (PairV #em.rs0.rep #em.rs1.rep); True }}

/-- Of a witness-free epoch, no half replicates to a witness (the statement this spec had until
the epoch model). -/
theorem tracker.Epoch.ReplicateToWitness.spec_nw
    (H : tracker.Epoch.ReplicateToWitness.spec (GF := GF) (hG := hG)) (e : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownEpochNW e }}
      (App (Val (e @!! go.GoType.PointerType tracker.Epoch.ty @!! go!"ReplicateToWitness"))
        (Val #()))
    {{ RET (PairV #false #false); True }} := by
  have h : (EpochM.bare (W64 0)).rs0.rep = false ∧ (EpochM.bare (W64 0)).rs1.rep = false := by
    simp [RSM.rep, EpochM.bare, RSM.bare]
  have Hs := H e (EpochM.bare (W64 0))
  rw [h.1, h.2] at Hs
  iintro %Φ ⟨#Hpkg, #He⟩ HΦ
  iapply Hs $$ [] HΦ
  iframe Hpkg
  iunfold ownEpochNW at He
  iexact He

end spec

end EtcdGrove
end Perennial
