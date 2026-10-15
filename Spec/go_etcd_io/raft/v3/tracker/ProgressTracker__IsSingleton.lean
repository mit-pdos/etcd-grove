/-
`tracker.ProgressTracker.IsSingleton`, Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTracker
public import Proof.go_etcd_io.raft.v3.InvTrackerC

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

/-- `p.IsSingleton()` (`tracker.ProgressTracker.IsSingleton.impl`,
`Code/go_etcd_io/raft/v3/tracker.lean`; tracker.go:160):

    return len(p.Voters[0]) == 1 && len(p.Voters[1]) == 0

For a general (possibly joint) configuration: the two halves of the voter config are id
sets that are `nil` or maps (`ownIdsetQ`), each read at its own fraction, and the
tracker struct is read at a fraction. The answer is about the sets (`len` of a `nil`
map is `0`); `&&` short-circuits, which the result does not see. No panic. -/
abbrev tracker.ProgressTracker.IsSingleton.spec : Prop :=
  ∀ (trk : Loc) (dq : DFrac) (tv : tracker.ProgressTracker) (v0 v1 : Loc) (dq0 dq1 : DFrac)
    (s0 s1 : GMap w64 Unit),
  tv.Config'.Voters'.arr = [v0, v1] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦{dq} tv ∗
      ownIdsetQ v0 dq0 s0 ∗ ownIdsetQ v1 dq1 s1 }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"IsSingleton"))
      (Val #()))
  {{ RET #(decide (GMap.size s0 = 1 ∧ GMap.size s1 = 0));
      trk ↦{dq} tv ∗ ownIdsetQ v0 dq0 s0 ∗ ownIdsetQ v1 dq1 s1 }}

open Iris.ProofMode in
/-- The tracker form at any configuration (2026-10-13, reconfiguration stage A1): with
`ownTrackerC c` sealed, the answer is whether the incoming voters are one id and the outgoing
none. -/
theorem tracker.ProgressTracker.IsSingleton.spec_trackerC
    (H : tracker.ProgressTracker.IsSingleton.spec (GF := GF) (hG := hG))
    (c : CfgM) (trk : Loc) (dq : DFrac) (tv : tracker.ProgressTracker) (t : Trk) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦{dq} tv ∗
      ownTrackerC c tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"IsSingleton"))
      (Val #()))
  {{ RET #(decide (GMap.size c.incoming = 1 ∧ GMap.size c.outgoing = 0));
      trk ↦{dq} tv ∗ ownTrackerC c tv t }} := by
  obtain ⟨votes, prs, pvs⟩ := t
  iintro %Φ ⟨#Hpkg, Htrk, Hown⟩ HΦ
  iunfold ownTrackerC at Hown
  iNamed Hown
  icases ownCfgCC_voters _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hv0, Hv1, Hcback⟩
  iapply H trk dq tv vin vout (DFrac.own 1) (DFrac.own 1) c.incoming c.outgoing Harr
    $$ [$Hpkg $Htrk $Hv0 $Hv1]
  inext
  iintro ⟨Htrk, Hv0, Hv1⟩
  ihave Hcfg := Hcback $$ Hv0 Hv1
  iapply HΦ
  iframe Htrk
  iapply ownTrackerC_intro c tv votes prs pvs Hinv Hdom Hflags Hsize HmaxInfl
    $$ Hvotes Hprs Hprogs Hcfg

end spec

end EtcdGrove
end Perennial
