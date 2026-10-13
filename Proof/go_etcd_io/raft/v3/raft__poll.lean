/-
Port of election_proof/proof_raft__poll.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__poll
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__RecordVote
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__TallyVotes

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

/-- `poll` logs the vote, records it in the tracker, and returns the tally.
The only model-visible effect is `recordVote`; the leading `if v`
picks a format string and is otherwise immaterial, so both arms run the
same tail.

`RecordVote` and `TallyVotes` are methods of the embedded tracker, so
they take `&r.trk` and the tracker's own predicate:
`ownRaftPhys_tracker` hands out exactly that, and takes it back at
the new tally. -/
theorem raft.poll.wp_proof
    (wp_ProgressTracker_RecordVote :
      tracker.ProgressTracker.RecordVote.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_TallyVotes :
      tracker.ProgressTracker.TallyVotes.spec (GF := GF) (hG := hG)) :
    raft.poll.spec (GF := GF) (hG := hG) := by
  intro cfg r id s src t v Hcfg_ne
  wp_start as Hphys
  wp_auto
  cases v <;> wp_auto
  all_goals
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_raft_log
    icases ownRaftPhys_tracker cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
    wp_apply wp_ProgressTracker_RecordVote $$ [$Htrkf $Htrk] as ⟨Htrkf, Htrk⟩
    wp_apply (tracker.ProgressTracker.TallyVotes.spec_simple wp_ProgressTracker_TallyVotes) _ _ _ _ Hcfg_ne $$ [$Htrkf $Htrk]
      as %g %rj %res ⟨Htrkf, Htrk, %Hres, %Hwon, %Hlost⟩
    ihave Hphys := Hback $$ %tv %(recordVote s.votes src _) Htrkf Htrk
    iapply HΦ
    dsimp only
    iframe Hphys
    ipureintro
    exact ⟨Hres, Hwon, Hlost⟩

end proof

end EtcdGrove
end Perennial
