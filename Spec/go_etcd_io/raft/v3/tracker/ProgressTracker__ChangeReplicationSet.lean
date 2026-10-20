/-
`(*ProgressTracker).ChangeReplicationSet` (raft#168, `tracker/tracker.go`; 2026-10-19, witness
support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTracker

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

/-- What `ChangeReplicationSet` reads past the epoch when the epoch has a witness: the progress
map (each half's excluded voter's `RecentActive` and `State`, and every peer's `RecentActive`),
whose peers include the halves' voters (`V0`, `V1`, of which the epoch is: `EpochWF`), none of
them `0`; and the tracker whole, to install the new epoch. -/
def chgRes (dq : DFrac) (tv : tracker.ProgressTracker) (V0 V1 : GSet w64) (w0 w1 : w64)
    (em : EpochM) (pvs : GMap w64 Progress) : IProp GF :=
  iprop(⌜dq = DFrac.own 1 ∧ EpochWF V0 V1 w0 w1 em ∧ W64 0 ∉ V0 ∧ W64 0 ∉ V1 ∧
      ∀ v, v ∈ V0 ∨ v ∈ V1 → (pvs !! v).isSome⌝ ∗
    ownProgressMap tv.Progress' pvs)

/-- `p.ChangeReplicationSet()`: `false`, nothing changed, with a witness-free epoch (the early
return, which reads nothing but the epoch); else, given what it reads (`chgRes`), `false` with
nothing changed, or `true` with a new epoch installed (`p.Epoch`), read-only, the next subterm's,
with the same witnesses and both halves well formed (`ChangeEpochOk`: which voter it excludes
depends on `RecentActive`, which the `Progress` model leaves out). -/
abbrev tracker.ProgressTracker.ChangeReplicationSet.spec : Prop :=
  ∀ (trk : Loc) (dq : DFrac) (tv : tracker.ProgressTracker) (em : EpochM) (V0 V1 : GSet w64)
    (w0 w1 : w64) (pvs : GMap w64 Progress),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦{dq} tv ∗
      ownEpoch tv.Epoch' em ∗
      (⌜em.hasWit = false⌝ ∨ chgRes dq tv V0 V1 w0 w1 em pvs) }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
      @!! go!"ChangeReplicationSet")) (Val #()))
  {{ (ch : Bool) (e : Loc), RET #ch; trk ↦{dq} { tv with Epoch' := e } ∗
      (⌜em.hasWit = false⌝ ∨ chgRes dq tv V0 V1 w0 w1 em pvs) ∗
      (⌜ch = false ∧ e = tv.Epoch'⌝ ∨
       ⌜ch = true ∧ em.hasWit = true⌝ ∗ ∃ em', ownEpoch e em' ∗
         ⌜ChangeEpochOk V0 V1 w0 w1 em em'⌝) }}

/-- With a witness-free epoch, `false` (the statement this spec had until the epoch model):
`stepLeader`'s check-quorum then starts no subterm. -/
theorem tracker.ProgressTracker.ChangeReplicationSet.spec_nw
    (H : tracker.ProgressTracker.ChangeReplicationSet.spec (GF := GF) (hG := hG))
    (trk : Loc) (dq : DFrac) (tv : tracker.ProgressTracker) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦{dq} tv ∗
        ownEpochNW tv.Epoch' }}
      (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
        @!! go!"ChangeReplicationSet")) (Val #()))
    {{ RET #false; trk ↦{dq} tv }} := by
  iintro %Φ ⟨#Hpkg, Htrk, #He⟩ HΦ
  iunfold ownEpochNW at He
  iapply H trk dq tv (EpochM.bare (W64 0)) ∅ ∅ (W64 0) (W64 0) ∅ $$ [Htrk]
  · iframe Hpkg Htrk He
    ileft; ipureintro; simp [EpochM.hasWit, EpochM.bare, RSM.bare]
  inext
  iintro %ch %e ⟨Htrk, -, (%Hch | ⟨%Hch, -⟩)⟩
  · obtain ⟨rfl, rfl⟩ := Hch
    iapply HΦ $$ Htrk
  · exfalso
    simp [EpochM.hasWit, EpochM.bare, RSM.bare] at Hch

end spec

end EtcdGrove
end Perennial
