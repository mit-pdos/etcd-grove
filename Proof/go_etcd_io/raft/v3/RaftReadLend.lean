/-
Lean-first (no Rocq counterpart). Trace-check, step 4 (`hCC`; 2026-11-12; `notes/trace-check-design.md`
§3.4, "Read-only lending"; slice 29n's finding 1): **what `traceEvent` reads of raft's state, and its
read-only lending**.

- `ownRaftCore r id s`: the struct's fields every hook's header reads, with the log behind `raftLog`
  (`id`, shared; `Term`, `Vote`, `state`, `raftLog`; `ownRaftLog`): what `raft.hardState` and
  `makeTracingState` read.
- `ownRaftReadT c r id s tv`: that, the `trk` field (holding `tv`) and `tv`'s configuration maps
  (`ownCfgCC tv.Config' 1 c`): what `traceEvent` reads (never a `Progress`).
- `RaftReadLend P c r id s`: `ownRaftReadT` lent out of `P`, persistently; `raftReadLend_of_lend`: a
  whole struct's lending gives it (`ownRaftPhysC_readT`), so every hook's caller is unchanged.
- `ownRaftPhysCV_reconfigCore`: `ownRaftPhysCV_reconfig` with the core out of the wand, so that a caller
  holding the struct open at its tracker (`switchToConfig`'s) can still lend the read view, the old
  configuration's maps given back by the `Changer` (`Config.Clone` only reads them).

Raft-internal (not on `etc/api/raft.txt`). The sealed struct's internals through `import all`.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedMsg
import all Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The struct's header fields and the log**, as the hooks and `hardState` read them. -/
def ownRaftCore (r : Loc) (id : w64) (s : NState) : IProp GF :=
  iprop(r.[raft, go!"id"] ↦□ id ∗ r.[raft, go!"Term"] ↦ s.term ∗ r.[raft, go!"Vote"] ↦ s.vote ∗
    r.[raft, go!"state"] ↦ stateW64 s.role ∗ r.[raft, go!"raftLog"] ↦ s.log ∗
    ownRaftLog s.log s.logst)

/-- The configuration's halves are small enough for `MajorityConfig.Slice` (`ownTrackerC`'s bound on
the progress map, which tracks them). -/
def CfgSizeOk (c : CfgM) : Prop :=
  (GMap.size c.incoming : Int) ≤ 2 ^ 62 ∧ (GMap.size c.outgoing : Int) ≤ 2 ^ 62

/-- **What `traceEvent` reads of raft's state**: the core, the `trk` field and its configuration's
maps. -/
def ownRaftReadT (c : CfgM) (r : Loc) (id : w64) (s : NState) (tv : tracker.ProgressTracker) :
    IProp GF :=
  iprop(ownRaftCore r id s ∗ r.[raft, go!"trk"] ↦ tv ∗ ownCfgCC tv.Config' (DFrac.own 1) c ∗
    ⌜CfgSizeOk c⌝)

/-- **Raft's state, lent read-only out of `P`** (persistently: a hook may read it more than once). -/
def RaftReadLend (P : IProp GF) (c : CfgM) (r : Loc) (id : w64) (s : NState) : IProp GF :=
  iprop(□ (P -∗ ∃ tv, ownRaftReadT c r id s tv ∗ (ownRaftReadT c r id s tv -∗ P)))

instance raftReadLend_persistent (P : IProp GF) (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    Persistent (RaftReadLend P c r id s) := by
  unfold RaftReadLend; infer_instance

end defs

/-! ## Some ghost names (for the untraced instances of the traced statements)

A traced statement (`raft.switchToConfig.spec`, `raft.applyConfChange.tracedSpec`) quantifies over the
cluster's ghost names `γ`, which its capability (`trCapB s.gh.tr γ …`, `emp` untraced) reads; an
untraced caller, which has none, passes this value. -/

/-- A `RaftNames` value: one voter, nothing allocated (never owned: only for untraced instances). -/
def raftNames0 [GooseExts] : RaftNames where
  reCfg := {[W64 1]}
  reVotes := ∅
  reTerms := ∅
  reAcks := ∅
  reCamp := ∅
  reVlogs := ∅
  reWins := ∅
  reEvs := ∅
  reCommit := default
  reProps := default
  reRLog := default
  reFresh := default
  reLcm := ∅
  reRdq := ∅
  reReads := default
  reRdFresh := default
  reRdCred := default
  reTbl := default
  reDyn := none
  reCCOk := fun _ _ => True
  reBootRaw := []
  reCfg_ne := fun h => by
    have hm : W64 1 ∈ ({[W64 1]} : GSet w64) := GMap.elem_of_singleton_2 _
    rw [h] at hm
    exact (GMap.elem_of_empty _).1 hm
  reTracked := none
  reTracked_ok := fun _ h => by cases h
  reNoSnap := false
  reNoSnap_ok := fun h => by cases h
  reNoXfer := false
  reNoXfer_ok := fun h => by cases h
  reSnapOkRaw := fun _ _ => True

/-! ## Out of the sealed struct -/

set_option hygiene false in
local macro "iNamed_physC' " H:ident : tactic =>
  `(tactic| (ihave $H:ident := ownRaftPhysCV_open _ _ _ _ _ $$ $H:ident;
             iunfold ownRaftPhysG at $H:ident;
             icases $H:ident with ⟨%rv, %msgs, %msgsAA, %lok, $H:ident⟩;
             iNamed $H:ident))

section physC
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `trk` field and the core's four owned fields at once. -/
private theorem raft_split_trk_core (l : Loc) (rv : raft) :
    ⊢ raftOwn (GF := GF) l rv -∗
      l.[raft, go!"trk"] ↦ rv.trk' ∗ l.[raft, go!"Term"] ↦ rv.Term' ∗ l.[raft, go!"Vote"] ↦ rv.Vote' ∗
      l.[raft, go!"state"] ↦ rv.state' ∗ l.[raft, go!"raftLog"] ↦ rv.raftLog' ∗
      (∀ x, l.[raft, go!"trk"] ↦ x -∗ l.[raft, go!"Term"] ↦ rv.Term' -∗
        l.[raft, go!"Vote"] ↦ rv.Vote' -∗ l.[raft, go!"state"] ↦ rv.state' -∗
        l.[raft, go!"raftLog"] ↦ rv.raftLog' -∗ raftOwn l { rv with trk' := x }) := by
  unfold raftOwn
  iintro Hf
  iNamed Hf
  iframe H_trk H_Term H_Vote H_state H_raftLog
  iintro %x H_trk H_Term H_Vote H_state H_raftLog
  simp only [named]
  iframe
  try iframe #

/-- **`ownRaftPhysCV_reconfig` with the core out of the wand**: the struct open at its tracker and at
its header fields and log, re-sealed at any configuration `c'` (and `Hvoter`'s set `V'`, holding of the
role), at the same tally, header and log. -/
theorem ownRaftPhysCV_reconfigCore (c c' : CfgM) (V V' : GSet w64) (r : Loc) (id : w64) (s : NState)
    (Hv : s.role ≠ .follower → s.role ≠ .leader → id ∈ V') :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTrackerC c tv ⟨s.votes, s.progress, s.prvals⟩ ∗ ownRaftCore r id s ∗
        (∀ tv' prs' pvs', ownRaftCore r id s -∗ r.[raft, go!"trk"] ↦ tv' -∗
           ownTrackerC c' tv' ⟨s.votes, prs', pvs'⟩ -∗
           ⌜PrvalsOk { s with progress := prs', prvals := pvs' }⌝ -∗
           ownRaftPhysCV c' V' r id { s with progress := prs', prvals := pvs' }) := by
  iintro H
  iNamed_physC' H
  ihave #Hfid := raftOwn_id _ _ $$ Hr
  icases raft_split_trk_core r rv $$ Hr with ⟨Hf, HfT, HfV, HfS, HfL, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  isplitl [HfT HfV HfS HfL Hlog]
  · unfold ownRaftCore
    rw [← Hid, ← Hterm, ← Hvote, ← Hstate, ← Hlogp]
    iframe HfT HfV HfS HfL Hlog Hfid
  iintro %tv' %prs' %pvs' Hcore Hf Htrk %Hok
  unfold ownRaftCore
  icases Hcore with ⟨-, HfT, HfV, HfS, HfL, Hlog⟩
  ihave HfT : r.[raft, go!"Term"] ↦ rv.Term' $$ [HfT]
  · rw [Hterm]; iexact HfT
  ihave HfV : r.[raft, go!"Vote"] ↦ rv.Vote' $$ [HfV]
  · rw [Hvote]; iexact HfV
  ihave HfS : r.[raft, go!"state"] ↦ rv.state' $$ [HfS]
  · rw [Hstate]; iexact HfS
  ihave HfL : r.[raft, go!"raftLog"] ↦ rv.raftLog' $$ [HfL]
  · rw [Hlogp]; iexact HfL
  ihave Hlog : ownRaftLog (GF := GF) rv.raftLog' s.logst $$ [Hlog]
  · rw [Hlogp]; iexact Hlog
  ihave Hr := Hback $$ %tv' Hf HfT HfV HfS HfL
  iapply ownRaftPhysCV_intro c' V' r id { s with progress := prs', prvals := pvs' }
      { rv with trk' := tv' } msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hsdr Hid_nz HelectionTimeout Hlok Htl Hlogp Htick HmsgsAA_ok Hout_term Hgh_out Hgh_unst Hv
    Hok Hnsl Hxf Hlq
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox Hnscap Hscert

/-- The trace logger, shared, with its contract at the node's mode (the nil logger untraced), in
either mode (`ownRaftPhysC_traceLogger` is the untraced case). -/
theorem ownRaftPhysC_traceLoggerG (c : CfgM) (V : GSet w64) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ∃ tl : GoInterface, r.[raft, go!"traceLogger"] ↦□ tl ∗ ⌜s.gh.tr = none → TraceLoggerOk tl⌝ ∗
        ownRaftPhysCV c V r id s := by
  iintro H
  iNamed_physC' H
  ihave #Hftl := raftOwn_traceLogger _ _ $$ Hr
  iexists rv.traceLogger'
  iframe Hftl
  isplitr
  · ipureintro; exact fun htr => Htl.untraced htr
  iapply ownRaftPhysCV_intro c V _ _ s _ msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hsdr Hid_nz HelectionTimeout Hlok Htl Hlogp Htick HmsgsAA_ok Hout_term Hgh_out
    Hgh_unst Hvoter Hprok Hnsl Hxf Hlq
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox Hnscap Hscert

/-- The configuration's maps out of the tracker, given back. -/
theorem ownTrackerC_cfg (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTrackerC (GF := GF) c tv t -∗
      ownCfgCC tv.Config' (DFrac.own 1) c ∗ (ownCfgCC tv.Config' (DFrac.own 1) c -∗ ownTrackerC c tv t) := by
  iintro Htrk
  iunfold ownTrackerC at Htrk
  iNamed Htrk
  iframe Hcfg
  iintro Hcfg
  iapply ownTrackerC_intro c tv t.votes t.prs t.peers Hinv Hdom Hflags Hsize HmaxInfl
    $$ Hvotes Hprs Hprogs Hcfg

/-- **The read view out of the whole struct**, given back. -/
theorem ownRaftPhysC_readT (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c c.voters r id s -∗
      ∃ tv, ownRaftReadT c r id s tv ∗ (ownRaftReadT c r id s tv -∗ ownRaftPhysCV c c.voters r id s) := by
  iintro H
  icases ownRaftPhysC_prvals_ok c r id s $$ H with ⟨%Hok, -, H⟩
  icases ownRaftPhysC_voter c r id s $$ H with ⟨%Hvt, H⟩
  icases ownRaftPhysCV_reconfigCore c c c.voters c.voters r id s Hvt $$ H
    with ⟨%tv, Hf, Htrk, Hcore, Hback⟩
  icases ownTrackerC_pure c _ _ $$ Htrk with ⟨%Hpure, Htrk⟩
  obtain ⟨-, Hdom, -, Hsize, -⟩ := Hpure
  have Hsz : CfgSizeOk c := by
    simp only at Hdom Hsize
    constructor
    · have := size_le_of_sub_dom c.incoming s.progress (by rw [Hdom]; exact incoming_sub_ids c)
      omega
    · have := size_le_of_sub_dom c.outgoing s.progress (by rw [Hdom]; exact outgoing_sub_ids c)
      omega
  icases ownTrackerC_cfg $$ Htrk with ⟨Hcfg, Htback⟩
  iexists tv
  isplitl [Hcore Hf Hcfg]
  · unfold ownRaftReadT; iframe; ipureintro; exact Hsz
  iintro Hrd
  unfold ownRaftReadT
  icases Hrd with ⟨Hcore, Hf, Hcfg, -⟩
  ihave Htrk := Htback $$ Hcfg
  ihave H := Hback $$ %tv %s.progress %s.prvals Hcore Hf Htrk %(by cases s; exact Hok)
  iapply ownRaftPhysC_eq (c := c) (V := c.voters) r id _ _ (by cases s; rfl) $$ H

/-- **The core out of the whole struct**, given back (`raft.hardState`'s callers). -/
theorem ownRaftPhysC_core (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c c.voters r id s -∗
      ownRaftCore r id s ∗ (ownRaftCore r id s -∗ ownRaftPhysCV c c.voters r id s) := by
  iintro H
  icases ownRaftPhysC_readT c r id s $$ H with ⟨%tv, Hrd, Hback⟩
  unfold ownRaftReadT
  icases Hrd with ⟨Hcore, Hf, Hcfg, %Hsz⟩
  iframe Hcore
  iintro Hcore
  iapply Hback
  iframe
  ipureintro; exact Hsz

/-- **A whole struct's lending gives the read-only one.** -/
theorem raftReadLend_of_lend (P : IProp GF) (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    RaftLend P c r id s ⊢ RaftReadLend P c r id s := by
  iintro #H
  unfold RaftReadLend
  imodintro
  iintro HP
  iunfold RaftLend at H
  icases H $$ HP with ⟨Hphys, Hb⟩
  icases ownRaftPhysC_readT c r id s $$ Hphys with ⟨%tv, Hrd, Hback⟩
  iexists tv
  iframe Hrd
  iintro Hrd
  iapply Hb
  iapply Hback $$ Hrd

/-- Raft's state alone, read-only. -/
theorem raftReadLend_self (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ RaftReadLend (ownRaftPhysCV (GF := GF) c c.voters r id s) c r id s := by
  iapply raftReadLend_of_lend
  iapply raftLend_self

/-- (2026-11-12, trace-check step 5) **The whole struct lends itself** under the trace gate (what a
caller of `traceNodeEvent` at the whole struct hands it). -/
theorem trOwn_physLend (tr : Option GName) (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    trOwn (GF := GF) tr (ownRaftPhysCV c c.voters r id s) ⊢
      trOwn tr iprop(ownRaftPhysCV c c.voters r id s ∗
        RaftReadLend (ownRaftPhysCV c c.voters r id s) c r id s) := by
  iintro H
  iapply trOwn_wand
  iframe H
  iintro Hp
  iframe Hp
  iapply raftReadLend_self

/-- The read view itself, as `P`. -/
theorem raftReadLend_readT (c : CfgM) (r : Loc) (id : w64) (s : NState) (tv : tracker.ProgressTracker) :
    ⊢ RaftReadLend (ownRaftReadT (GF := GF) c r id s tv) c r id s := by
  unfold RaftReadLend
  imodintro
  iintro HP
  iexists tv
  iframe HP
  iintro H
  iexact H

end physC

end EtcdGrove
end Perennial
