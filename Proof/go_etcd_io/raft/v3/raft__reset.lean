/-
Port of election_proof/proof_raft__reset.v.

Lean notes: the Rocq section-local `reset_inv` and its three lemmas are the private
`ResetInv`, `resetInv_empty`, `resetInv_step`, `resetInv_done`; `log_last_unsigned` is
`logLast_unsigned`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__reset
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ResetVotes
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Visit
public import Spec.go_etcd_io.raft.v3.tracker.NewInflights
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.newReadOnly
public import Spec.go_etcd_io.raft.v3.raft__resetRandomizedElectionTimeout
public import Spec.go_etcd_io.raft.v3.raft__abortLeaderTransfer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section helpers
variable [FfiSyntax]

/-- What `reset`'s `Visit` has done after visiting the ids in `D`: the `Progress`
values range over the same peers as before, and every visited peer's `Match` is
`reset`'s. -/
private def ResetInv (id li : w64) (P0 pvs : GMap w64 Progress) (D : GSet w64) : Prop :=
  domSet pvs = domSet P0 ∧
  ∀ k p, k ∈ D → pvs !! k = some p → p.matched = (if k = id then li else W64 0)

/-- `lastIndex()`'s result, as `logLast`. -/
private theorem logLast_unsigned (ls : LogState) (i : w64)
    (H : uint.Z i = uint.Z ls.prev.index' + (ls.sents.length : Int)
                    + (ls.uents.length : Int)) :
    i = logLast ls := by
  unfold logLast
  apply uint_Z_inj.1
  rw [← H]
  word

private theorem resetInv_empty (id li : w64) (P0 : GMap w64 Progress) :
    ResetInv id li P0 P0 ∅ :=
  ⟨rfl, fun k _ Hk _ => absurd Hk (GMap.not_elem_of_empty k)⟩

private theorem resetInv_step (id li : w64) (P0 pvs : GMap w64 Progress) (D : GSet w64)
    (i : w64) (v p0 : Progress) (H : ResetInv id li P0 pvs D) (Hi : pvs !! i = some p0)
    (Hv : v.matched = (if i = id then li else W64 0)) :
    ResetInv id li P0 (<[i := v]> pvs) ({[i]} ∪ D) := by
  obtain ⟨Hdom, Hm⟩ := H
  refine ⟨by rw [GMap.dom_insert_lookup _ _ _ _ Hi, Hdom], ?_⟩
  intro k p Hk Hp
  by_cases Hki : k = i
  · subst Hki
    rw [GMap.lookup_insert_eq] at Hp
    cases Hp
    exact Hv
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hki)] at Hp
    rw [GMap.elem_of_union, GMap.elem_of_singleton] at Hk
    exact Hm k p (Hk.resolve_left Hki) Hp

private theorem resetInv_done (id li : w64) (P0 pvs : GMap w64 Progress)
    (H : ResetInv id li P0 pvs (domSet P0)) :
    prvalsMatch pvs = resetMatched id li P0 := by
  obtain ⟨Hdom, Hm⟩ := H
  apply GMap.map_eq
  intro k
  rw [prvalsMatch, GMap.lookup_fmap', resetMatched, GMap.lookup_imap]
  cases Hk : pvs !! k with
  | some p =>
    cases HP : P0 !! k with
    | some q =>
      simp only [Option.map_some, Option.bind_some]
      rw [Hm k p ((GMap.elem_of_dom _ _).2 ⟨q, HP⟩) Hk]
    | none =>
      exfalso
      have : k ∈ domSet pvs := (GMap.elem_of_dom _ _).2 ⟨p, Hk⟩
      rw [Hdom] at this
      exact (GMap.not_elem_of_dom _ _).2 HP this
  | none =>
    cases HP : P0 !! k with
    | some q =>
      exfalso
      have : k ∈ domSet P0 := (GMap.elem_of_dom _ _).2 ⟨q, HP⟩
      rw [← Hdom] at this
      exact (GMap.not_elem_of_dom _ _).2 Hk this
    | none => rfl

end helpers

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]


/-- `ownTracker` at two indices that are equal (by computation: a state reached by
record updates). -/
private theorem ownTracker_cast (cfg : GSet w64) (tv : tracker.ProgressTracker) (t t' : Trk)
    (h : t = t') : ownTracker (GF := GF) cfg tv t ⊢ ownTracker cfg tv t' := h ▸ .rfl

/-- `reset term` clears the vote iff the term changes, clears `lead` and the vote tally,
and re-initialises everything the model does not see: the two tick counters, the
randomised election timeout, the leader-transfer target, every peer's `Progress`, the
pending-config index, the uncommitted size and the read-only queue.

The structure follows the code:

- The `if r.Term != term` is joined (`wp_join`) at `ownRaftPhys` of `s0`, the state with
  the term and vote updated; after the join the rest of the body is proved once.
- `trk.ResetVotes()` runs on the tracker `ownRaftPhys_tracker` hands out, which goes
  back at the empty tally.
- `trk.Visit f` needs the tracker field, and lends it to the closure with one
  `Progress`; the closure reads `r.raftLog`, `r.id` (the whole struct) and
  `r.trk.MaxInflight`, `r.trk.MaxInflightBytes` (the tracker field), and writes `*pr`.
  So `I` is the wand of `ownRaftPhys_tracker_prvals` -- the struct with a
  tracker-shaped hole, taking it back at any `Progress` values -- as in `bcastAppend`,
  plus (since 2026-10-01) `ResetInv`: the `Match` of every peer visited so far is
  `reset`'s. `Visit` ends at the full voter set, which is the progress map's domain,
  so every peer's `Match` is known (`resetInv_done`). `I` also has to carry the frame
  slot of the pointer variable (`r_ptr ↦ r`). -/
theorem raft.reset.wp_proof
    (wp_ProgressTracker_ResetVotes : tracker.ProgressTracker.ResetVotes.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_Visit : tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG))
    (wp_tracker_NewInflights : tracker.NewInflights.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_newReadOnly : newReadOnly.spec (GF := GF) (hG := hG))
    (wp_raft_resetRandomizedElectionTimeout :
      raft.resetRandomizedElectionTimeout.spec (GF := GF) (hG := hG))
    (wp_raft_abortLeaderTransfer : raft.abortLeaderTransfer.spec (GF := GF) (hG := hG)) :
    raft.reset.spec (GF := GF) (hG := hG) := by
  intro cfg r id s term Hle
  wp_start as Hphys
  -- `lastIndex()` does not wrap: the closure's `pr.Match = lastIndex()` is then `logLast`
  icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlb⟩
  icases ownRaftLog_nowrap $$ Hlog with ⟨%Hnw, Hlog⟩
  ihave Hphys := Hlb $$ Hlog
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  -- Two arms: `r.Term != term` writes `Term` and `Vote`; otherwise nothing is written
  -- and the vote survives.
  wp_join iprop(r_ptr ↦ r ∗ term_ptr ↦ term ∗ ownRaftPhys cfg r id
      { s with term := term, vote := if term = s.term then s.vote else W64 0 })
    with [r term Hphys] as ⟨r, term, Hphys⟩
  · wp_apply raft.wp_store_Term (Hle := Hle) $$ Hphys as Hphys
    wp_apply raft.wp_store_Vote $$ Hphys as Hphys
    isplitr
    · ipureintro; exact rfl
    iframe r term
    iapply ownRaftPhys_eq cfg r id _ _ ?_ $$ Hphys
    rw [if_neg (Ne.symm Hif)]
  -- `lead := None`, `electionElapsed := 0`, `heartbeatElapsed := 0`
  wp_apply raft.wp_store_lead $$ Hphys as Hphys
  wp_apply raft.wp_store_electionElapsed $$ Hphys as Hphys
  wp_apply raft.wp_store_heartbeatElapsed $$ Hphys as Hphys
  wp_apply wp_raft_resetRandomizedElectionTimeout $$ [$Hphys] as Hphys
  wp_apply wp_raft_abortLeaderTransfer $$ [$Hphys] as Hphys
  -- `r.trk.ResetVotes()`, on the tracker the accessor hands out; put back at the empty
  -- tally
  icases ownRaftPhys_tracker $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_apply wp_ProgressTracker_ResetVotes $$ [$Htrkf $Htrk] as %votesRef ⟨Htrkf, Htrk⟩
  ihave Hphys := Hback $$ Htrkf Htrk
  ihave Hphys := ownRaftPhys_eq cfg r id _ (resetTo0 s term) (by cases s; rfl) $$ Hphys
  try wp_auto
  -- `Visit` owns the tracker field and lends it to the closure together with one
  -- `Progress`. The caller invariant is the rest of the struct -- the wand of
  -- `ownRaftPhys_tracker_prvals` -- and `ResetInv`.
  icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv1, Htrkf, Htrk, HI⟩
  icases ownTracker_prvals_dom $$ Htrk with ⟨%Hpdom, Htrk⟩
  icases ownTracker_progress_map $$ Htrk with ⟨-, %Hprdom, Htrk⟩
  have Hdomcfg : domSet s.prvals = cfg := by rw [← Hprdom, ← Hpdom]; rfl
  wp_apply wp_ProgressTracker_Visit cfg _ tv1
      ⟨(resetTo0 s term).votes, (resetTo0 s term).progress, (resetTo0 s term).prvals⟩ _
      (fun D pvsx => iprop(r_ptr ↦ r ∗
        ⌜ResetInv id (logLast s.logst) s.prvals pvsx D⌝ ∗
        (∀ tvx pvsx', r.[raft, go!"trk"] ↦ tvx -∗
          ownTracker cfg tvx ⟨(resetTo0 s term).votes, (resetTo0 s term).progress, pvsx'⟩ -∗
          ownRaftPhys cfg r id { resetTo0 s term with prvals := pvsx' })))
    $$ [$Htrkf $Htrk $r $HI]
    as ⟨%tvfin, %pvsfin, Htrkf, Htrk, r, %Hinv, HI⟩
  · isplitr
    · ipureintro; exact resetInv_empty _ _ _
    -- the `Visit` closure: re-initialise one `Progress` wholesale. The `Progress` goes
    -- back into the tracker, and the tracker into the struct, whenever the next step
    -- needs the struct whole (`r.raftLog.lastIndex()`, `r.id`); it is borrowed again,
    -- at the value `NState.prvals` records, for the steps that need it
    -- (`pr.IsLearner`, the store to `*pr`, `pr.Match`).
    imodintro
    unfold visitClosure
    iintro %i %pr %tv0 %pvs0 %p %D
    wp_start as ⟨%Hicfg, %Hpri, %Hpvi, %HmaxI, Htrkf, Hpr, Hprback, r, %Hinv0, HI⟩
    dsimp only
    have Hpri' : (resetTo0 s term).progress !! i = some pr := Hpri
    ihave Htrk := Hprback $$ Hpr
    ihave Hphys := HI $$ Htrkf Htrk
    wp_auto
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hphys⟩
    wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli0⟩
    ihave Hphys := Hphys $$ Hlog
    -- `r.trk.MaxInflight`, `r.trk.MaxInflightBytes` through the tracker field, then
    -- `pr.IsLearner` and the store through `pr`
    icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv2, Htrkf, Htrk, HI⟩
    ihave Htrk := ownTracker_cast cfg tv2 _
      ⟨(resetTo0 s term).votes, (resetTo0 s term).progress, <[i := p]> pvs0⟩ ?_ $$ Htrk
    · rfl
    icases ownTracker_maxinflight $$ Htrk with ⟨%HmaxI2, Htrk⟩
    icases ownTracker_lookup cfg tv2
      ⟨(resetTo0 s term).votes, (resetTo0 s term).progress, <[i := p]> pvs0⟩ i pr Hpri $$ Htrk
      with ⟨%p1, %Hpv1, Hpr, Hprback⟩
    -- Keep `Hnolearner`: `ownProgress`'s `progressAbs` says `pv.IsLearner' = false`,
    -- and the closure has to hand it back.
    iunfold ownProgress at Hpr
    icases Hpr with ⟨%pv1, Hpr⟩
    iNamed Hpr
    iclear Hinfl
    have Hnolearner := ((progressAbs_Some _ _ _).1 Habs).1
    wp_auto
    wp_apply wp_tracker_NewInflights _ _ HmaxI2 as %ifl Hifl
    -- the `Progress` literal has no `State` field, so `State` is the zero value
    -- `StateProbe`; `IsLearner` is copied across
    ihave Htrk := Hprback $$ [Hpv Hifl]
    · iapply ownProgress_of pr
        { Match' := W64 0, Next' := li + W64 1, sentCommit' := 0, State' := 0,
          PendingSnapshot' := 0, RecentActive' := false, MsgAppFlowPaused' := false,
          Inflights' := ifl, IsLearner' := pv1.IsLearner' } .probe _ Hnolearner rfl $$ Hpv Hifl
    ihave Hphys := HI $$ Htrkf [Htrk]
    · iapply ownTracker_cast _ _ _ _ ?_ $$ Htrk
      rfl
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    -- Both arms end the same way: hand the field and the tracker back to `Visit`, and
    -- the wand back to `I`.
    by_cases Hii : i = id
    · rw [decide_eq_true Hii]
      wp_auto
      wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
      icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hphys⟩
      wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li2 ⟨Hlog, %Hli1⟩
      ihave Hphys := Hphys $$ Hlog
      -- `pr.Match = lastIndex()`: borrow `pr` once more
      icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv3, Htrkf, Htrk, HI⟩
      ihave Htrk := ownTracker_cast cfg tv3 _
        ⟨(resetTo0 s term).votes, (resetTo0 s term).progress, _⟩ ?_ $$ Htrk
      · rfl
      icases ownTracker_lookup cfg tv3 ⟨(resetTo0 s term).votes, (resetTo0 s term).progress, _⟩ i pr
        Hpri' $$ Htrk with ⟨%p2, %Hpv2, Hpr, Hprback⟩
      iunfold ownProgress at Hpr
      icases Hpr with ⟨%pv2, Hpr⟩
      iNamed Hpr
      have Habs2 := (progressAbs_Some _ _ _).1 Habs
      wp_auto
      ihave Htrk := Hprback $$ [Hpv Hinfl]
      · iapply ownProgress_of pr { pv2 with Match' := li2 } p2.state _ Habs2.1 Habs2.2.1
          $$ Hpv Hinfl
      ihave Hphys := HI $$ Htrkf [Htrk]
      · iapply ownTracker_cast _ _ _ _ ?_ $$ Htrk
        rfl
      icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv3, Htrkf, Htrk, HI⟩
      ihave Htrk := ownTracker_cast cfg tv3 _
        ⟨(resetTo0 s term).votes, (resetTo0 s term).progress, _⟩ ?_ $$ Htrk
      · rfl
      iapply HΦ
      iexists tv3, _
      iframe Htrkf Htrk r
      isplitr
      · ipureintro
        simp only [GMap.insert_insert]
        refine resetInv_step _ _ _ _ _ _ _ _ Hinv0 Hpvi ?_
        simp only [progressOf, if_pos Hii]
        exact logLast_unsigned _ _ Hli1
      iintro %tvx %pvsx Hf Ht
      ihave Hphys := HI $$ %tvx %pvsx Hf [Ht]
      · iapply ownTracker_cast _ _ _ _ ?_ $$ Ht
        rfl
      iapply ownRaftPhys_eq cfg r id _ _ (by rfl) $$ Hphys
    · rw [decide_eq_false Hii]
      wp_auto
      icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv3, Htrkf, Htrk, HI⟩
      ihave Htrk := ownTracker_cast cfg tv3 _
        ⟨(resetTo0 s term).votes, (resetTo0 s term).progress, _⟩ ?_ $$ Htrk
      · rfl
      iapply HΦ
      iexists tv3, _
      iframe Htrkf Htrk r
      isplitr
      · ipureintro
        simp only [GMap.insert_insert]
        refine resetInv_step _ _ _ _ _ _ _ _ Hinv0 Hpvi ?_
        simp only [progressOf, if_neg Hii]
      iintro %tvx %pvsx Hf Ht
      ihave Hphys := HI $$ %tvx %pvsx Hf [Ht]
      · iapply ownTracker_cast _ _ _ _ ?_ $$ Ht
        rfl
      iapply ownRaftPhys_eq cfg r id _ _ (by rfl) $$ Hphys
  -- `Visit` hands the field and the tracker back
  ihave Hphys := HI $$ %tvfin %pvsfin Htrkf [Htrk]
  · iapply ownTracker_cast _ _ _ _ ?_ $$ Htrk
    rfl
  -- `pendingConfIndex := 0`, `uncommittedSize := 0`
  try wp_auto
  wp_apply raft.wp_store_pendingConfIndex $$ Hphys as Hphys
  wp_apply raft.wp_store_uncommittedSize $$ Hphys as Hphys
  -- `r.readOnly = newReadOnly(r.readOnly.option)`
  icases ownRaftPhys_readOnly $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
  icases ownReadOnly_option $$ Hro with ⟨%o, %Hosafe, Hopt, Hroback⟩
  wp_auto
  ihave Hro := Hroback $$ Hopt
  wp_apply wp_newReadOnly _ Hosafe as %ro' Hro'
  ihave Hphys := Hback $$ %ro' %(ReadOnly.mk [] ∅ (W64 0)) Hrof Hro'
  iapply HΦ $$ %pvsfin
  isplitl
  · iapply ownRaftPhys_eq cfg r id _ _ (by rfl) $$ Hphys
  ipureintro
  apply resetInv_done
  rw [Hdomcfg]
  exact Hinv

end proof

end EtcdGrove
end Perennial
