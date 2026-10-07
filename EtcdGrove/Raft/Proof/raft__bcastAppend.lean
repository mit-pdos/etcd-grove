/- Port of election_proof/proof_raft__bcastAppend.v.

Lean notes: the Rocq helper `wp_bcast` is inlined in the theorem (it was the whole
proof). The Rocq `Local Lemma send_msgs_app` is not needed (the state equations are
closed by `cases s; simp [sendMsgs]`). `ownTracker_cast` is a local helper. -/
import EtcdGrove.Raft.Spec.raft__bcastAppend
import EtcdGrove.Raft.Spec.ProgressTracker__Visit
import EtcdGrove.Raft.Spec.raft__sendAppend

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ownTracker` at two indices that are equal (by computation: a state reached by
record updates). -/
private theorem ownTracker_cast (cfg : GSet w64) (tv : tracker.ProgressTracker) (t t' : Trk)
    (h : t = t') : ownTracker (GF := GF) cfg tv t ⊢ ownTracker cfg tv t' := h ▸ .rfl

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
struct with a tracker-shaped hole", the wand of `ownRaftPhys_tracker_prvals`:

    ∃ ms, r_ptr ↦ r ∗ ⌜ReplSends id s ms⌝ ∗ ⌜prvalsMatch pvsx = prvalsMatch s.prvals⌝ ∗
          (∀ tvx pvsx, r.[trk] ↦ tvx -∗
                  ownTracker cfg tvx ⟨s.votes, s.progress, pvsx⟩ -∗
                  ownRaftPhys cfg r id { sendMsgs s ms with prvals := pvsx })

quantified over the `Progress` values because `sendAppend` changes them
(`NState.prvals`), and over the field value because `ownRaftPhys` hides it: after
`sendAppend` the tracker is split off again at whatever value the struct now holds.
That is also why `visitClosure`'s postcondition is existential in the tracker value; see
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
  intro cfg r id s
  wp_start as Hphys
  wp_auto
  icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv, Htrkf, Htrk, Hrest⟩
  wp_apply wp_ProgressTracker_Visit cfg _ tv ⟨s.votes, s.progress, s.prvals⟩ _
      (fun _ pvsx => iprop(∃ (ms : List Msg),
        "rp" ∷ r_ptr ↦ r ∗
        "%Hms" ∷ ⌜ReplSends id s ms⌝ ∗
        "%Hmm" ∷ ⌜prvalsMatch pvsx = prvalsMatch s.prvals⌝ ∗
        "Hrest" ∷ (∀ tvx pvsx', r.[raft, go!"trk"] ↦ tvx -∗
            ownTracker cfg tvx ⟨s.votes, s.progress, pvsx'⟩ -∗
            ownRaftPhys cfg r id { sendMsgs s ms with prvals := pvsx' })))
    $$ [$Htrkf $Htrk r Hrest]
  · isplitl [r Hrest]
    · iexists []
      simp only [named]
      iframe r
      isplitr
      · ipureintro; intro m Hm; simp at Hm
      isplitr
      · ipureintro; trivial
      iintro %tvx %pvsx Hf Ht
      ihave Hphys := Hrest $$ %tvx %pvsx Hf Ht
      iapply ownRaftPhys_eq cfg r id _ _ (by cases s; simp [sendMsgs]) $$ Hphys
    -- the closure
    imodintro
    unfold visitClosure
    iintro %i %pr %tv0 %pvs0 %p %D
    wp_start as ⟨%Hicfg, %Hpri, %Hpvi, %HmaxI, Htrkf, Hpr, Hback, HI⟩
    iNamed HI
    ihave Htrk := Hback $$ Hpr
    ihave Hphys := Hrest $$ Htrkf Htrk
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    by_cases Hii : i = id
    · -- the leader itself: nothing is sent
      rw [decide_eq_true Hii]
      wp_auto
      icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv1, Htrkf, Htrk, Hrest⟩
      ihave Htrk := ownTracker_cast cfg tv1 _ ⟨s.votes, s.progress, <[i := p]> pvs0⟩ ?_ $$ Htrk
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
      iintro %tvx %pvsx Hf Ht
      ihave Hphys := Hrest $$ %tvx %pvsx Hf [Ht]
      · iapply ownTracker_cast cfg tvx ⟨s.votes, s.progress, pvsx⟩ _ ?_ $$ Ht
        rfl
      iapply ownRaftPhys_eq cfg r id _ _ (by cases s; rfl) $$ Hphys
    · -- a peer: `sendAppend` may add `App`s and change `Progress`es
      rw [decide_eq_false Hii]
      wp_auto
      wp_apply wp_raft_sendAppend _ _ _ _ i Hii Hicfg $$ [$Hphys]
        as %ms' %pvs' ⟨Hphys, %Hms', %Hmm'⟩
      try wp_auto
      icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv1, Htrkf, Htrk, Hrest⟩
      ihave Htrk := ownTracker_cast cfg tv1 _ ⟨s.votes, s.progress, pvs'⟩ ?_ $$ Htrk
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
      iintro %tvx %pvsx Hf Ht
      ihave Hphys := Hrest $$ %tvx %pvsx Hf [Ht]
      · iapply ownTracker_cast cfg tvx ⟨s.votes, s.progress, pvsx⟩ _ ?_ $$ Ht
        rfl
      iapply ownRaftPhys_eq cfg r id _ _ (by cases s; simp [sendMsgs, List.append_assoc]) $$ Hphys
  iintro ⟨%tvfin, %pvsfin, Htrkf, Htrk, HI⟩
  iNamed HI
  ihave Hphys := Hrest $$ %tvfin %pvsfin Htrkf Htrk
  wp_auto
  iapply HΦ $$ %ms %pvsfin
  iframe Hphys
  ipureintro
  exact ⟨Hms, Hmm⟩

end proof

end EtcdGrove
end Perennial
