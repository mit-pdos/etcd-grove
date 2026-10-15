/-
Port of `election_proof/spec_ProgressTracker__VoterNodes.v` (feb5c73d4).

Lean notes: Rocq leaves the type of `tv` implicit; it is written out
(`tracker.ProgressTracker`, as in `ownTracker`). Rocq's `trk.t` record is `Trk`. `elements cfg` is
`GMap.elements cfg`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvTrackerC
public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `p.VoterNodes()` is the voter ids, sorted. As for `MajorityConfig.Slice`, only the
permutation is stated. `newRaft` uses it only to build a log line.

At any configuration since 2026-10-13 (reconfiguration stage A1; `ownTrackerC`): the voters
of both halves (`CfgM.voters`, what `JointConfig.IDs` returns). The statement at a simple
configuration (`ownTracker cfg`, the voters `cfg`) is
`tracker.ProgressTracker.VoterNodes.spec_simple`. -/
abbrev tracker.ProgressTracker.VoterNodes.spec : Prop :=
  ∀ (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTrackerC c tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"VoterNodes"))
      (Val #()))
  {{ (sl : GoSlice) (xs : List w64), RET #sl;
      trk ↦ tv ∗ ownTrackerC c tv t ∗
      sl ↦* xs ∗ ⌜xs ≡ₚ GMap.elements c.voters⌝ }}

open Iris.ProofMode in
/-- The statement until 2026-10-13, at a simple configuration (`ownTracker`). -/
theorem tracker.ProgressTracker.VoterNodes.spec_simple
    (H : tracker.ProgressTracker.VoterNodes.spec (GF := GF) (hG := hG))
    (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"VoterNodes"))
      (Val #()))
  {{ (sl : GoSlice) (xs : List w64), RET #sl;
      trk ↦ tv ∗ ownTracker cfg tv t ∗
      sl ↦* xs ∗ ⌜xs ≡ₚ GMap.elements cfg⌝ }} := by
  iintro %Φ ⟨#Hpkg, Htrk, Hown⟩ HΦ
  ihave Hown := ownTracker_toC _ _ _ $$ Hown
  iapply H _ trk tv t $$ [$Hpkg $Htrk $Hown]
  inext
  iintro %sl %xs ⟨Htrk, Hown, Hsl, %Hxs⟩
  icases ownTrackerC_toTracker _ _ _ _ $$ Hown with ⟨Hown, -⟩
  iapply HΦ
  iframe Htrk Hown Hsl
  ipureintro
  rw [CfgM.voters_simple] at Hxs
  exact Hxs

end spec

end EtcdGrove
end Perennial
