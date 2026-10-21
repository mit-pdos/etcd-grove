/-
`(*Epoch).HasWitness` (raft#168, `tracker/tracker.go`; 2026-10-19, witness support).
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

/-- `e.HasWitness()`: whether a half of the epoch has a witness (`EpochM.hasWit`). -/
abbrev tracker.Epoch.HasWitness.spec : Prop :=
  ∀ (e : Loc) (em : EpochM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownEpoch e em }}
    (App (Val (e @!! go.GoType.PointerType tracker.Epoch.ty @!! go!"HasWitness")) (Val #()))
  {{ RET #em.hasWit; True }}

/-- Of a witness-free epoch, `false` (the statement this spec had until the epoch model). -/
theorem tracker.Epoch.HasWitness.spec_nw (H : tracker.Epoch.HasWitness.spec (GF := GF) (hG := hG))
    (e : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownEpochNW e }}
      (App (Val (e @!! go.GoType.PointerType tracker.Epoch.ty @!! go!"HasWitness")) (Val #()))
    {{ RET #false; True }} := by
  have h : (EpochM.bare (W64 0)).hasWit = false := by
    simp [EpochM.hasWit, EpochM.bare, RSM.bare]
  have Hs := H e (EpochM.bare (W64 0))
  rw [h] at Hs
  iintro %Φ ⟨#Hpkg, #He⟩ HΦ
  iapply Hs $$ [] HΦ
  iframe Hpkg
  iunfold ownEpochNW at He
  iexact He

end spec

end EtcdGrove
end Perennial
