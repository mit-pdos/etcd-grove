/-
`(*ReplicationSet).GetNonWitnessVoterSlice` (raft#168, `tracker/tracker.go`; 2026-10-20, witness
support).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvEpoch

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

/-- `r.GetNonWitnessVoterSlice()` of a replication set holding `m` (read-only, as an installed
epoch's): a fresh slice of the non-witness voters, in some order (the map's), each once -- what
the leader sends the witness as the replication set (`sendAppendToWitness`). -/
abbrev tracker.ReplicationSet.GetNonWitnessVoterSlice.spec : Prop :=
  ∀ (l : Loc) (rv : tracker.ReplicationSet) (m : RSM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ l ↦□ rv ∗ ownRS rv m }}
    (App (Val (l @!! go.GoType.PointerType tracker.ReplicationSet.ty
      @!! go!"GetNonWitnessVoterSlice")) (Val #()))
  {{ (sl : GoSlice) (xs : List w64), RET #sl;
      sl ↦* xs ∗ ownSliceCap w64 sl (DFrac.own 1) ∗ ⌜xs ≡ₚ GMap.elements m.nwv⌝ }}

end spec

end EtcdGrove
end Perennial
