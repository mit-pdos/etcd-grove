/-
Lemmas of the role step functions (`stepFollower`, `stepCandidate`, `stepLeader`) for the raft
v3.7 retarget (stage R4, phase 3, group G3).
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- The two voter halves of the tracker at `c` (2026-10-14, reconfiguration stage A3), as the
`quorum`/`readOnly` methods take them (`ownIdsetQ`), with their size bounds; given back
unchanged. -/
theorem ownTrackerC_halves (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTrackerC (GF := GF) c tv t -∗
      ∃ (vin vout : Loc), ⌜tv.Config'.Voters'.arr = [vin, vout]⌝ ∗
        ⌜(GMap.size c.incoming : Int) ≤ 2 ^ 62 ∧ (GMap.size c.outgoing : Int) ≤ 2 ^ 62⌝ ∗
        ownIdsetQ vin (DFrac.own 1) c.incoming ∗ ownIdsetQ vout (DFrac.own 1) c.outgoing ∗
        (ownIdsetQ vin (DFrac.own 1) c.incoming -∗ ownIdsetQ vout (DFrac.own 1) c.outgoing -∗
           ownTrackerC c tv t) := by
  obtain ⟨votes, prs, pvs⟩ := t
  iintro Hown
  icases ownTrackerC_voters_size c tv _ $$ Hown with ⟨%Hsz, Hown⟩
  iunfold ownTrackerC at Hown
  iNamed Hown
  icases ownCfgCC_voters _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hv0, Hv1, Hcback⟩
  iexists vin, vout
  isplitr
  · ipureintro; exact Harr
  isplitr
  · ipureintro; exact ⟨Hsz.2.1, Hsz.2.2⟩
  iframe Hv0 Hv1
  iintro Hv0 Hv1
  ihave Hcfg := Hcback $$ Hv0 Hv1
  iapply ownTrackerC_intro c tv votes prs pvs Hinv Hdom Hflags Hsize HmaxInfl
    $$ Hvotes Hprs Hprogs Hcfg

end proof

end EtcdGrove
end Perennial
