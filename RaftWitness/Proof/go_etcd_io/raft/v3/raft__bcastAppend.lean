/- Port of election_proof/proof_raft__bcastAppend.v.

Lean notes: the Rocq helper `wp_bcast` is inlined in the theorem (it was the whole
proof). The Rocq `Local Lemma send_msgs_app` is not needed (the state equations are
closed by `cases s; simp [sendMsgs]`). `ownTrackerC_cast` is a local helper. 
raft v3.7 (stage R4): compiles as ported (imports only).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__bcastAppend
public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Visit
public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__sendAppend

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

/-- `bcastAppend`

The body (`raft.bcastAppend.impl`) is

    r.trk.Visit(func(id uint64, _ *Progress) {
      if id == r.id { return }
      r.sendAppend(id)
    })

so the whole proof is the choice of `Visit`'s caller invariant `I` and the closure
obligation.

**`I` is a wand, and that is the point.** `Visit` takes the tracker object -- the `trk`
field and `ownTracker` -- and lends it to the closure; but `r.sendAppend(id)` is
specified on `ownRaftPhys`, which includes that object. So `I` carries exactly "the raft
struct with a tracker-shaped hole", the wand of `ownRaftPhysC_tracker_prvals`:

    ∃ ms, r_ptr ↦ r ∗ ⌜ReplSends id s ms⌝ ∗ ⌜prvalsMatch pvsx = prvalsMatch s.prvals⌝ ∗
          (∀ tvx pvsx, r.[trk] ↦ tvx -∗
                  ownTrackerC c tvx ⟨s.votes, s.progress, pvsx, s.ep⟩ -∗
                  ownRaftPhysCV c c.voters r id { sendMsgs s ms with prvals := pvsx })

quantified over the `Progress` values because `sendAppend` changes them
(`NState.prvals`), and over the field value because `ownRaftPhys` hides it: after
`sendAppend` the tracker is split off again at whatever value the struct now holds.
That is also why `visitClosureC`'s postcondition is existential in the tracker value; see
`InvTracker.lean`. What it does pin is the progress map, `NState.progress`, which is the
index of the wand's `ownTracker`. The closure fills the hole with what it was handed,
reads `r.id`, calls `sendAppend` on the whole struct, and splits the tracker off again
for `Visit`.

`ms` accumulates. Each iteration either sends nothing (the peer is the leader itself,
or `maybeSendAppend` declined) or adds messages `ReplSends` allows, which is closed
under concatenation; no `Match` moves. That is the whole content of the postcondition.
One `App` per peer would be false; see `Spec/raft__bcastAppend.lean`. -/
theorem raft.bcastAppend.wp_proof
    (wp_ProgressTracker_Visit : tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG))
    (wp_raft_sendAppend : raft.sendAppend.spec (GF := GF) (hG := hG)) :
    raft.bcastAppend.spec (GF := GF) (hG := hG) := by
  intro c r id s Hlead
  wp_start as Hphys
  wp_auto
  -- (stage R8a) the leader's progress bound, carried through the `Visit`
  icases ownRaftPhysC_prvals_ok c r id s $$ Hphys with ⟨%Hok0, -, Hphys⟩
  icases ownRaftPhysC_tracker_prvals $$ Hphys with ⟨%tv, Htrkf, Htrk, Hrest⟩
  wp_apply wp_ProgressTracker_Visit c _ tv ⟨s.votes, s.progress, s.prvals, s.ep⟩ _
      (fun _ pvsx => iprop(∃ (ms : List Msg),
        "rp" ∷ r_ptr ↦ r ∗
        "%Hms" ∷ ⌜ReplSends id s ms⌝ ∗
        "%Hmm" ∷ ⌜prvalsMatch pvsx = prvalsMatch s.prvals⌝ ∗
        "%Hok" ∷ ⌜PrvalsOk { sendMsgs s ms with prvals := pvsx }⌝ ∗
        "Hrest" ∷ (∀ tvx pvsx', r.[raft, go!"trk"] ↦ tvx -∗
            ownTrackerC c tvx ⟨s.votes, s.progress, pvsx', s.ep⟩ -∗
            ⌜PrvalsOk { sendMsgs s ms with prvals := pvsx' }⌝ -∗
            ownRaftPhysCV c c.voters r id { sendMsgs s ms with prvals := pvsx' })))
    $$ [$Htrkf $Htrk r Hrest]
  · isplitl [r Hrest]
    · iexists []
      simp only [named]
      iframe r
      isplitr
      · ipureintro; intro m Hm; simp at Hm
      isplitr
      · ipureintro; trivial
      isplitr
      · ipureintro; exact Hok0.of_fields rfl rfl rfl
      iintro %tvx %pvsx Hf Ht %Hok'
      ihave Hphys := Hrest $$ %tvx %pvsx Hf Ht %(Hok'.of_fields rfl rfl rfl)
      iapply ownRaftPhysC_eq c r id _ _ (by cases s; simp [sendMsgs]) $$ Hphys
    -- the closure
    imodintro
    unfold visitClosureC
    iintro %i %pr %tv0 %pvs0 %p %D
    wp_start as ⟨%Hicfg, %Hpri, %Hpvi, %HmaxI, Htrkf, Hpr, Hback, HI⟩
    iNamed HI
    ihave Htrk := Hback $$ %p Hpr %(And.intro rfl rfl)
    ihave Hphys := Hrest $$ Htrkf Htrk %(by rw [GMap.insert_id _ _ _ Hpvi]; exact Hok)
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    by_cases Hii : i = id
    · -- the leader itself: nothing is sent
      rw [decide_eq_true Hii]
      wp_auto
      icases ownRaftPhysC_tracker_prvals $$ Hphys with ⟨%tv1, Htrkf, Htrk, Hrest⟩
      ihave Htrk := ownTrackerC_cast c tv1 _ ⟨s.votes, s.progress, <[i := p]> pvs0, s.ep⟩ ?_ $$ Htrk
      · rfl
      iapply HΦ
      iexists tv1, _
      iframe Htrkf Htrk
      iexists ms
      simp only [named]
      iframe rp
      isplitr
      · ipureintro; exact Hms
      isplitr
      · ipureintro; rw [GMap.insert_id _ _ _ Hpvi]; exact Hmm
      isplitr
      · ipureintro; rw [GMap.insert_id _ _ _ Hpvi]; exact Hok
      iintro %tvx %pvsx Hf Ht %Hok'
      ihave Hphys := Hrest $$ %tvx %pvsx Hf [Ht] %Hok'
      · iapply ownTrackerC_cast c tvx ⟨s.votes, s.progress, pvsx, s.ep⟩ _ ?_ $$ Ht
        rfl
      iapply ownRaftPhysC_eq c r id _ _ (by cases s; rfl) $$ Hphys
    · -- a peer: `sendAppend` may add `App`s and change `Progress`es
      rw [decide_eq_false Hii]
      wp_auto
      wp_apply wp_raft_sendAppend _ _ _ _ i Hii (by exact Hicfg) (by exact Hlead) $$ [$Hphys]
        as %ms' %pvs' ⟨Hphys, %Hms', %Hmm'⟩
      try wp_auto
      icases ownRaftPhysC_prvals_ok c r id _ $$ Hphys with ⟨%Hok', -, Hphys⟩
      icases ownRaftPhysC_tracker_prvals $$ Hphys with ⟨%tv1, Htrkf, Htrk, Hrest⟩
      ihave Htrk := ownTrackerC_cast c tv1 _ ⟨s.votes, s.progress, pvs', s.ep⟩ ?_ $$ Htrk
      · rfl
      iapply HΦ
      iexists tv1, _
      iframe Htrkf Htrk
      iexists ms ++ ms'
      simp only [named]
      iframe rp
      isplitr
      · ipureintro
        exact replSends_app id s ms ms' Hms ((replSends_send_prvals id s ms _ ms').1 Hms')
      isplitr
      · ipureintro; simp only at Hmm'; rw [Hmm', GMap.insert_id _ _ _ Hpvi]; exact Hmm
      isplitr
      · ipureintro; exact Hok'.of_fields rfl rfl rfl
      iintro %tvx %pvsx Hf Ht %Hok''
      ihave Hphys := Hrest $$ %tvx %pvsx Hf [Ht] %(Hok''.of_fields rfl rfl rfl)
      · iapply ownTrackerC_cast c tvx ⟨s.votes, s.progress, pvsx, s.ep⟩ _ ?_ $$ Ht
        rfl
      iapply ownRaftPhysC_eq c r id _ _ (by cases s; simp [sendMsgs, List.append_assoc]) $$ Hphys
  iintro ⟨%tvfin, %pvsfin, Htrkf, Htrk, HI⟩
  iNamed HI
  ihave Hphys := Hrest $$ %tvfin %pvsfin Htrkf Htrk %Hok
  wp_auto
  iapply HΦ $$ %ms %pvsfin
  iframe Hphys
  ipureintro
  exact ⟨Hms, Hmm⟩

end proof

end EtcdGrove
end Perennial
