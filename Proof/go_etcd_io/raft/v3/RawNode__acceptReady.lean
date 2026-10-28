/- `RawNode.acceptReady`, Lean-first (2026-10-10): the second half of the proof of
`RawNode.Ready` (`RawNode__Ready.lean` until then, itself the port of
election_proof/proof_RawNode__Ready.v at 857d09190, finished in Lean), from the call of
`acceptReady` on, starting from `ownRawNodeReady`. The node after `Ready` is
`readyNstate`, the queue `readySteps`, both internal to this proof.

Lean notes: `ready_rnstate`, `ready_nstate` are `readySteps` (only the queue: the
previous `SoftState`/`HardState` are no longer in `RNState`), `readyNstate`; Rocq's
`pending.self <$> selfs` is `selfs.map Pending.self`. `needStorageAppendRespMsg`,
`newStorageAppendRespMsg` and `newStorageApplyRespMsg`, stepped through inline in Rocq,
got local specs (`wp_*_inline`) until 2026-10-16 (raft v3.7: specs of their own, so
`hasNextOrInProgressUnstableEnts`, `IsEmptySnap` and `lastEntryID` are no longer this
proof's callees); the Rocq `wp_if_join`s are `wp_join`s.
`to_pstate_ready`, `nstate_rel_ready`, `ready_ce_last`, `selfmsgs`, `selfmsgs_take_S`,
`self_pending`, `self_pending_own` are `toPState_ready`, `nstateRel_ready`,
`ready_ce_last`, `selfmsgs`, `selfmsgs_take_succ`, `self_pending`, `self_pending_own`
(Rocq's `selfabs`, the self-addressed messages' abstractions, went on 2026-10-10: the
queue records the messages' terms, `selfPending`).

Raft v3.7 (2026-10-16, stage R5, `notes/decisions.md` D8): `rd.HardState` is `nil` or a
read-only hard state, stored into `prevHardSt` when not empty (`hsRO_of_hsOpt`); each
`msgsAfterAppend` message's `GetTo` reads its ownership (the self-addressed ones owned in
`Hself`, a half of the others in `Hother`: the other halves were handed out); the
self-addressed ones move to `stepsOnAdvance` as `msgIn`s (`self_pending`, `LemmasReadyR`);
the acknowledgements are built by `newStorageAppendRespMsg`/`newStorageApplyRespMsg`, whose
specs replace the old inline ones, and own nothing beyond their `msgIn` (no `pendingOwn`: an
apply acknowledgement is not a `MsgApp`, so no capacity); the last committed entry's index
is read with `GetIndex` through its read-only pointer (`entsRO_lookup`).
-/
module

public import Proof.go_etcd_io.raft.v3.LemmasReadyR
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Spec.go_etcd_io.raft.v3.RawNode__acceptReady
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.needStorageApplyRespMsg
public import Spec.go_etcd_io.raft.v3.raftLog__acceptUnstable
public import Spec.go_etcd_io.raft.v3.entsSize
public import Spec.go_etcd_io.raft.v3.raftLog__acceptApplying
public import Spec.go_etcd_io.raft.v3.traceReady
public import Spec.go_etcd_io.raft.v3.needStorageAppendRespMsg
public import Spec.go_etcd_io.raft.v3.newStorageAppendRespMsg
public import Spec.go_etcd_io.raft.v3.newStorageApplyRespMsg
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section helpers
variable [GooseExts]

/-- (D22 S-d3a) The log a `Ready` accepts: with a snapshot, the storage lent (`ownRaftLog_lend`). -/
def rdyLs (L : Option SnapLoan) (ls : LogState) : LogState :=
  if L.isSome then { ls with lent := true, sat := false } else ls

theorem rdyLog_true (L : Option SnapLoan) (ls : LogState) :
    rdyLog true L.isSome ls = logHanded (rdyLs L ls) := by
  unfold rdyLog rdyLs; cases L <;> rfl

/-- (D22 S-d3a) The trip of a loan's snapshot (`NGhost.snp`). -/
def loanTrip (L : Option SnapLoan) : Option SnapTrip :=
  L.map (fun l => snapTrip l.snap l.snap.Metadata'.ConfState'.lists)

/-- The node after `Ready`: the outbox handed to the application, the unstable entries
in progress and the handed-out ones the application's to persist (`logAcceptUnstable`),
`applying` at the last committed entry handed out (`logAcceptApplying`; `sz` is
`entsSize` of them), and (2026-10-13) the `ReadState`s handed out (`r.readStates = nil`). -/
def readyNstate (s : NState) (L : Option SnapLoan) (ce : List EntryM) (sz : w64) : NState :=
  { s with outbox := [],
           logst := logAcceptApplying (logAcceptUnstable (rdyLs L s.logst)) ce sz,
           gh := { s.gh with outlb := 0, unst := false, slent := L.isSome, snp := loanTrip L },
           rd := { s.rd with states := [] } }

/-- (2026-10-25, T-M M2b) A `Ready` keeps what a pre-candidate's campaign guard reads: the log's
boundary, entries, commit index, `applied`, pending snapshot and the role (`PreGuardF`). -/
theorem readyNstate_guard {fp : List EntryM} {s : NState} {L : Option SnapLoan} {ce : List EntryM}
    {sz : w64} (h : PreGuardF fp s) : PreGuardF fp (readyNstate s L ce sz) := by
  have e : (readyNstate s L ce sz).logst.prev = s.logst.prev ∧
      (readyNstate s L ce sz).logst.sents = s.logst.sents ∧
      (readyNstate s L ce sz).logst.uents = s.logst.uents ∧
      (readyNstate s L ce sz).logst.committed = s.logst.committed ∧
      (readyNstate s L ce sz).logst.applied = s.logst.applied ∧
      (readyNstate s L ce sz).logst.snap = s.logst.snap := by
    unfold readyNstate logAcceptApplying logAcceptUnstable rdyLs
    split <;> split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := e
  intro hl hp
  rw [h1] at hl
  obtain ⟨hs, hn⟩ := h hl hp
  refine ⟨by rw [h6]; exact hs, ?_⟩
  rw [h2, h3, h4, h5]; exact hn

/-- (2026-10-28, stage U0) A `Ready` keeps the role and the pending snapshot (`SnapFol`). -/
theorem readyNstate_snapFol {s : NState} {L : Option SnapLoan} {ce : List EntryM}
    {sz : w64} (h : SnapFol s) : SnapFol (readyNstate s L ce sz) := by
  have e : (readyNstate s L ce sz).logst.snap = s.logst.snap := by
    unfold readyNstate logAcceptApplying logAcceptUnstable rdyLs
    split <;> split <;> rfl
  intro hs
  exact h (e ▸ hs)

/-- The local messages `acceptReady` queues for `Advance`: the self-addressed responses
from `msgsAfterAppend` (`selfs`, each `selfPending`), an acknowledgement of the log up to
its last entry if there were unstable entries, and an acknowledgement of the committed
entries handed out, if any. -/
def readySteps (s : NState) (L : Option SnapLoan) (selfs : List Pending) (ce : List EntryM) :
    List Pending :=
  selfs ++
  (if s.logst.uents = [] ∧ L = none then []
   else [Pending.appendAck s.term s.logst.prev
     (if s.logst.uents ≠ [] then some (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))
      else none) (L.map SnapLoan.snap)]) ++
  (if ce = [] then [] else [Pending.applyAck ce])

/-- `Ready` changes nothing the protocol sees but the outbox and (2026-10-13) the
`ReadState`s. -/
theorem toPState_ready (s : NState) (L : Option SnapLoan) (ce : List EntryM) (sz : w64) :
    toPState (readyNstate s L ce sz) =
      { toPState s with outbox := [], rd := { (toPState s).rd with states := [] } } := by
  unfold readyNstate logAcceptApplying logAcceptUnstable toPState rdyLs
  by_cases h : s.role = .leader <;> cases ce.getLast? <;> cases L <;> simp [h, rdNL]

/-- `StepsOk` of the acknowledgements `Ready` queues after the self-addressed
responses. -/
theorem ready_stepsOk (s' : NState) (t : w64) (b : entryID) (last : Option entryID)
    (sn : Option SnapshotM) (ce : List EntryM)
    (u : Prop) [Decidable u]
    (Ht : uint.Z t ≤ uint.Z s'.term)
    (Hl : ¬ u → ∀ x, last = some x → plogLast b s'.logst.stored = x ∧ 1 ≤ uint.Z t)
    (Hce : ∀ e, ce.getLast? = some e →
      uint.Z e.Index' ≤ uint.Z s'.logst.committed ∧ uint.Z e.Index' ≤ uint.Z s'.logst.applying) :
    StepsOk s' ((if u then [] else [Pending.appendAck t b last sn]) ++
                (if ce = [] then [] else [Pending.applyAck ce])) := by
  by_cases hu : u <;> by_cases hc : ce = [] <;>
    simp only [hu, hc, ↓reduceIte, List.nil_append, List.singleton_append]
  · trivial
  · intro p Hp
    rw [List.mem_singleton] at Hp
    subst Hp
    exact Hce
  · exact ⟨⟨Ht, Hl hu⟩, fun p Hp => by cases Hp⟩
  · refine ⟨⟨Ht, Hl hu⟩, fun p Hp => ?_⟩
    rw [List.mem_singleton] at Hp
    subst Hp
    exact Hce

/-- `StepsOk` of self-addressed responses in front of a `StepsOk` queue. -/
theorem stepsOk_selfs (s : NState) (selfs rest : List Pending)
    (Hs : ∀ p ∈ selfs, (∃ pv t, p = .self pv t) ∧ PendingOk s p) (Hr : StepsOk s rest) :
    StepsOk s (selfs ++ rest) := by
  induction selfs with
  | nil => exact Hr
  | cons p ps IH =>
    obtain ⟨⟨pv, t, rfl⟩, Hp⟩ := Hs p List.mem_cons_self
    exact ⟨Hp, IH (fun q Hq => Hs q (List.mem_cons_of_mem _ Hq))⟩

/-- (D22 S-d3a) What `acceptUnstable` and `acceptApplying` keep of the log. -/
theorem accept_fields (ls : LogState) (ce : List EntryM) (sz : w64) :
    (logAcceptApplying (logAcceptUnstable ls) ce sz).prev = ls.prev ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).snap = ls.snap ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).storage = ls.storage ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).committed = ls.committed ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).lent = ls.lent ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).ksn = ls.ksn ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).sat = false ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).sip = (ls.sip || ls.snap.isSome) ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).fl = ls.fl ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).applied = ls.applied ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).stored = ls.sents ++ ls.uents ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).unpersisted = nextUnstable ls ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).uents = ls.uents ∧
    (logAcceptApplying (logAcceptUnstable ls) ce sz).sents = ls.sents := by
  unfold logAcceptApplying logAcceptUnstable
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end helpers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem RawNode.acceptReady.wp_proof
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_needStorageApplyRespMsg : needStorageApplyRespMsg.spec (GF := GF) (hG := hG))
    (wp_raftLog_acceptUnstable : raftLog.acceptUnstable.spec (GF := GF) (hG := hG))
    (wp_entsSize : entsSize.spec (GF := GF) (hG := hG))
    (wp_raftLog_acceptApplying : raftLog.acceptApplying.spec (GF := GF) (hG := hG))
    (wp_traceReady : traceReady.spec (GF := GF) (hG := hG))
    (wp_needStorageAppendRespMsg : needStorageAppendRespMsg.spec (GF := GF) (hG := hG))
    (wp_newStorageAppendRespMsg : newStorageAppendRespMsg.spec (GF := GF) (hG := hG))
    (wp_newStorageApplyRespMsg : newStorageApplyRespMsg.spec (GF := GF) (hG := hG))
    (wp_Message_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hlc := HasLC.hasLC))
    (wp_Entry_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hlc := HasLC.hasLC)) :
    RawNode.acceptReady.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs rd ce es ms h L
  wp_start as H
  iNamed H
  iNamed Hrn
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  -- (D22 S-d3a) the log as the hand-out left it: with a snapshot, the storage lent
  generalize Hls0 : rdyLs L s.logst = ls0
  have Hls0f : ls0.prev = s.logst.prev ∧ ls0.sents = s.logst.sents ∧ ls0.uents = s.logst.uents ∧
      ls0.committed = s.logst.committed ∧ ls0.applying = s.logst.applying ∧
      ls0.applied = s.logst.applied ∧ ls0.snap = s.logst.snap ∧ ls0.fl = s.logst.fl ∧
      ls0.storage = s.logst.storage ∧ ls0.unpersisted = s.logst.unpersisted ∧
      ls0.inprogress = s.logst.inprogress ∧ ls0.ksn = s.logst.ksn ∧ ls0.sip = s.logst.sip ∧
      ls0.lent = L.isSome := by
    rw [← Hls0]; unfold rdyLs
    cases L with
    | none =>
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      show s.logst.lent = false
      have h1 := Hgh_unst.1.2.1
      have h2 := Hloan.1.1
      rw [Hloan.2] at h2
      rw [h1, h2]; rfl
    | some _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ihave Hlog : ownRaftLog s.log (logHanded ls0) $$ [Hlog]
  · iExactEq Hlog
    rw [rdyLog_true, Hls0]
  subst Hes
  -- ghost facts, read before anything moves; the ghost state is at the drained outbox
  -- (`ownRawNodeReady_handout`, 2026-10-13), the outbox's messages' facts in `Hout`
  simp only [↓reduceIte]
  iunfold ownStepGhost at Hghost
  icases Hghost with ⟨Hghost, Hrest⟩
  icases ghostRest_nsLink γ _ cf id _ $$ Hrest with ⟨%Hnl, Hrest⟩
  -- (D22 S-b′3) the queued messages' certificates, through the storage's link
  icases ghostRest_certLink γ _ cf id _ $$ Hrest with ⟨#Hlink, Hrest⟩
  imod qCerts_of_srcs γ _ (ms1 ++ ms2) ⊤ CoPset.subseteq_top $$ Hlink Hscert with #Hqc
  icases ownRaftGhost_storedRecs_keep _ _ _ $$ Hghost with ⟨Hghost, #Hlr⟩
  icases ownRaftGhost_terms_le _ _ _ $$ Hghost with ⟨%Htle, Hghost⟩
  icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hwf1, Hlog⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hwf2, Hlog⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hwf3, Hlog⟩
  icases ownRaftLog_wf _ _ $$ Hlog with ⟨%Hidx, Hlog⟩
  icases ownRaftLog_snap_facts _ _ $$ Hlog with ⟨%Hsfa, Hlog⟩
  simp only [logHanded] at Hwf1 Hwf2 Hwf3 Hidx
  obtain ⟨Hf_prev, Hf_sents, Hf_uents, Hf_cm, Hf_apg, Hf_ap, Hf_snap, Hf_fl, Hf_st, Hf_unp, Hf_ip,
    Hf_ksn, Hf_sip, Hf_lent⟩ := Hls0f
  rw [Hf_prev, Hf_sents, Hf_uents] at Hidx
  rw [Hf_prev, Hf_sents, Hf_uents, Hf_cm] at Hwf2
  -- (D22 S-d3b) with unstable entries, the term past `0`: the last entry's term, at most the
  -- term (`TermsLe`), is a record's (`storedRecs_last_term`)
  ihave %Hterm1 : ⌜s.logst.uents ≠ [] → 1 ≤ uint.Z s.term⌝ $$ []
  · by_cases hu : s.logst.uents = []
    · ipureintro; exact fun h => absurd hu h
    · have Hw := Hwf3
      rw [Hf_prev, Hf_sents, Hf_uents] at Hw
      icases storedRecs_last_term γ _ _ (by simp [toPState, hu])
          (by simp only [toPState, List.length_append]; push_cast; omega) $$ Hlr with %Hlt
      ipureintro
      intro _
      have h2 := Htle _ _ Hlt.2
      have h1 := Hlt.1
      simp only [toPState] at h2 h1 ⊢
      apply Int.not_lt.1
      intro hlt
      have h0 : uint.Z (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)).term' = 0 := by
        have := uint_Z_nonneg (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)).term'
        omega
      exact h1 (uint_Z_inj.mp (by rw [h0]; rfl))
  icases Hrdrs with ⟨%sts, #Hrdsts, %Hsts⟩
  ihave %Hstl := readStatesPts_len _ _ $$ Hrdsts
  icases Hrdhard with ⟨%hrd, #Hrdhard, #Hrdw⟩
  -- (D22l) the caller's hard state is the `Ready`'s
  ihave %Hhh := hsOpt_agree rd.HardState' hrd h $$ [Hrdhard Hh]
  · isplitl [] <;> iassumption
  subst Hhh
  -- (D22 S-d3a) the `Ready`'s snapshot: the loan's facts, the node's half of the snapshot
  icases rdSnapRel_facts γ rs rd ce L s $$ Hrdz with ⟨%Hrdp, Hrdz⟩
  have Hce0' : ∀ l, L = some l → ce = [] := fun l hl => (Hrdp.2 l hl).2.2.2.2.2.2.1
  -- the snapshot pointer as `needStorageAppendRespMsg` reads it: `nil`, or half of it
  ihave Hsno : iprop(snapOpt rd.Snapshot' (DFrac.own (1 : Qp).half) (L.map SnapLoan.snap) ∗
      loanCom γ L) $$ [Hrdz]
  · cases L with
    | none =>
      simp only [rdSnapRel, snapOpt, Option.map_none, loanCom]
      icases Hrdz with %Hz
      isplitr
      · ipureintro; exact Hz.1
      ipureintro; trivial
    | some l =>
      simp only [rdSnapRel, snapOpt, Option.map_some, loanCom]
      icases Hrdz with ⟨Hs, #Hc, %Hz⟩
      rw [← Hz.1]
      iframe Hs Hc
      ipureintro; exact Hz.2.2.2.2.2.2.2.2.2.2.2
  icases Hsno with ⟨Hsno, #Hloanc⟩
  have Hsnne : ∀ sv, L.map SnapLoan.snap = some sv → sv.Metadata'.Index' ≠ W64 0 := by
    intro sv hsv
    cases hl : L with
    | none => rw [hl] at hsv; cases hsv
    | some l =>
      rw [hl] at hsv; cases hsv
      have := (Hrdp.2 l hl).2.2.2.2.1
      intro h0; rw [h0] at this; simp at this
  wp_auto
  -- `if rd.SoftState != nil { rn.prevSoftSt = rd.SoftState }`: either way `prevSoftSt`
  -- points to a read-only `SoftState`
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ rd ∗
      ∃ (psp : Loc) (v : SoftState), rawNodeOwn rn { rnv with prevSoftSt' := psp } ∗ psp ↦□ v)
    with [Hrn rn rd] as ⟨rn, rd, %psp, %v, Hrn, #Hpsp⟩
  · iframe rn rd
    iexists rnv.prevSoftSt', sv
    iframe Hsoft
    iexact Hrn
  · icases Hrdsoft with (%Hn | ⟨%v, #Hv⟩)
    · exact absurd Hn Hif
    iframe rn rd
    iexists rd.SoftState', v
    iframe Hv
    iexact Hrn
  -- `if !IsEmptyHardState(rd.HardState) { rn.prevHardSt = rd.HardState }`: either way
  -- `prevHardSt` points to a read-only hard state
  wp_apply wp_IsEmptyHardState $$ [$Hrdhard]
  -- (D22l) its record moves to `phsNext rs.phs hrd`, its witness kept
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ rd ∗
      ∃ (ph : Loc) (hph : HardStateM),
        rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph } ∗
          prevHS γ ph hph (phsNext rs.phs hrd))
    with [Hrn rn rd] as ⟨rn, rd, %ph, %hph, Hrn, #Hph⟩
  · iframe rn rd
    iexists rnv.prevHardSt', hprev
    rw [phsNext_empty _ _ (by first | exact Hif | exact Classical.not_not.1 Hif | simpa using Hif)]
    iframe Hhard
    iexact Hrn
  · iframe rn rd
    iexists rd.HardState', hrd
    iframe Hrn
    rw [phsNext_ne _ _ Hif]
    ihave #Hro := hsRO_of_hsOpt _ _ Hif $$ Hrdhard
    iapply prevHS_intro $$ Hro Hrdw
  -- `if len(rd.ReadStates) != 0 { rn.raft.readStates = nil }`: either way the node has no
  -- `ReadState` left
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ rd ∗
      rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph } ∗
      ∃ rs', rnv.raft'.[raft, go!"readStates"] ↦ rs' ∗ readStatesPts rs' [] ∗
        ownSliceCap ReadState rs' (DFrac.own 1))
    with [rn rd Hrn Hf_readStates HreadStates_cap]
    as ⟨rn, rd, Hrn, %rs', Hf_readStates, #HreadStates', HreadStates_cap'⟩
  · first
      | (iframe rn rd Hrn
         iexists slice.nil
         iframe Hf_readStates
         isplitr
         · iapply readStatesPts_nil
         · iapply ownSliceCap_nil
         done)
      | (have He : s.rd.states = [] := by
           apply Hsts
           apply List.eq_nil_of_length_eq_zero
           rw [Hstl.1]
           have Hz : rd.ReadStates'.len = W64 0 := by
             first | exact Hif | (apply Classical.byContradiction; intro h; exact Hif h)
           rw [Hz]; rfl
         iframe rn rd Hrn
         iexists rss
         iframe Hf_readStates HreadStates_cap
         rw [← He]
         iexact HreadStates
         done)
  · first
      | (iframe rn rd Hrn
         iexists slice.nil
         iframe Hf_readStates
         isplitr
         · iapply readStatesPts_nil
         · iapply ownSliceCap_nil
         done)
      | (have He : s.rd.states = [] := by
           apply Hsts
           apply List.eq_nil_of_length_eq_zero
           rw [Hstl.1]
           have Hz : rd.ReadStates'.len = W64 0 := by
             first | exact Hif | (apply Classical.byContradiction; intro h; exact Hif h)
           rw [Hz]; rfl
         iframe rn rd Hrn
         iexists rss
         iframe Hf_readStates HreadStates_cap
         rw [← He]
         iexact HreadStates
         done)
  rw [Hasync]
  ihave %Hs0 := ownSlice_len _ _ _ $$ Hsteps
  have Hs0' : rnv.stepsOnAdvance'.len = W64 0 := by
    simp only [List.length_nil] at Hs0
    word
  wp_auto
  rw [Hs0']
  wp_auto
  -- `for _, m := range r.msgsAfterAppend { if m.GetTo() == r.id {
  -- rn.stepsOnAdvance = append(rn.stepsOnAdvance, m) } }`: each `GetTo` reads the message
  -- through what the node keeps of it (`Hself`: whole; `Hother`: a half)
  ihave IH : iprop(∃ (n : w64) (stl : GoSlice) (mv : Loc),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗
      "Hrn" ∷ rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl } ∗
      "Hsteps" ∷ stl ↦* (selfmsgs id (ms2.take (sint.nat n))).map QMsg.loc ∗
      "Hsteps_cap" ∷ ownSliceCap Loc stl (DFrac.own 1) ∗
      "HmsgsAA" ∷ sl2 ↦* ms2.map QMsg.loc ∗
      "Hself" ∷ ([∗list] q ∈ ms2, selfOwn id q) ∗
      "Hother" ∷ ([∗list] q ∈ ms2, otherHalf id q) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ms2.length : Int)⌝)
    $$ [i m Hrn Hsteps Hsteps_cap HmsgsAA Hself Hother]
  · iexists W64 0, rnv.stepsOnAdvance', null
    have H0 : sint.nat (W64 0) = 0 := rfl
    rw [H0, List.take_zero]
    simp only [selfmsgs, List.filter_nil, List.map_nil, named]
    iframe i m Hsteps Hsteps_cap HmsgsAA Hself Hother
    isplitl [Hrn]
    · rw [Hasync]
      iexact Hrn
    · ipureintro; word
  wp_for IH
  ihave %Hl3 := ownSlice_len _ _ _ $$ HmsgsAA
  simp only [List.length_map] at Hl3
  wp_if_destruct
  · have Hlt : sint.Z n < sint.Z sl2.len := by simpa using Hif
    list_elem ms2 (sint.nat n) as mm
    have Hmml : (ms2.map QMsg.loc)[sint.nat n]? = some mm.loc := by
      rw [List.getElem?_map, Hmm_lookup]; rfl
    rw [ite_pos' (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl2.len from ⟨Hn.1, Hlt⟩)]
    wp_apply wp_load_slice_index sl2 (sint.Z n) (ms2.map QMsg.loc) (DFrac.own 1) mm.loc Hn.1
      $$ [HmsgsAA] with HmsgsAA
    · iframe
      ipureintro
      exact Hmml
    have HnS : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    by_cases hs : mm.st.msg.To' = id
    · have hsq : isSelfQ id mm = true := decide_eq_true hs
      icases bigSepL_acc_same (fun q => selfOwn (GF := GF) id q) ms2 _ mm Hmm_lookup $$ Hself
        with ⟨Hmm, Hself⟩
      ihave Hmm : qOwn mm $$ [Hmm]
      · unfold selfOwn; simp only [hsq, ↓reduceIte]; iexact Hmm
      wp_apply (wp_Message_GetTo.1 mm.loc (DFrac.own 1) DFrac.discard false mm.st) $$ [$Hmm]
        as Hmm
      ihave Hself := Hself $$ [Hmm]
      · unfold selfOwn; simp only [hsq, ↓reduceIte]; iexact Hmm
      rw [hs]
      wp_auto
      -- to oneself: queued to step on `Advance`
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %stl1 ⟨Hsl1, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hsteps $Hsteps_cap $Hsl1] as %stl' ⟨Hsteps, Hsteps_cap, -⟩
      wp_for_post
      iframe
      iexists n + W64 1, stl', mm.loc
      rw [HnS, selfmsgs_take_succ _ _ _ _ Hmm_lookup, ite_pos' hs, List.map_append,
        List.map_cons, List.map_nil]
      iframe
      ipureintro; word
    · have hsq : isSelfQ id mm = false := decide_eq_false hs
      icases bigSepL_acc_same (fun q => otherHalf (GF := GF) id q) ms2 _ mm Hmm_lookup $$ Hother
        with ⟨Hmm, Hother⟩
      ihave Hmm : msgOwn mm.loc (DFrac.own (1 : Qp).half) mm.st $$ [Hmm]
      · unfold otherHalf; simp only [hsq, Bool.false_eq_true, ↓reduceIte]; iexact Hmm
      wp_apply (wp_Message_GetTo.1 mm.loc (DFrac.own (1 : Qp).half) DFrac.discard false mm.st)
        $$ [$Hmm] as Hmm
      ihave Hother := Hother $$ [Hmm]
      · unfold otherHalf; simp only [hsq, Bool.false_eq_true, ↓reduceIte]; iexact Hmm
      wp_if_destruct
      · exact absurd rfl hs
      wp_for_post
      iframe
      iexists n + W64 1, stl, mm.loc
      rw [HnS, selfmsgs_take_succ _ _ _ _ Hmm_lookup, ite_neg' hs, List.append_nil]
      iframe
      ipureintro; word
  have Hn2 : sint.nat n = ms2.length := by
    have : ¬ sint.Z n < sint.Z sl2.len := by simpa using Hif
    word
  rw [show ms2.take (sint.nat n) = ms2 from List.take_of_length_le (by omega)]
  -- `needStorageAppendRespMsg(r, rd)`: unstable entries, or (D22 S-d3a) a snapshot handed out
  wp_apply (wp_needStorageAppendRespMsg rnv.raft' s.log (logHanded ls0) rd _ (L.map SnapLoan.snap)
      Hsnne)
    $$ [$Hf_raftLog $Hlog $Hsno] as ⟨Hf_raftLog, Hlog, Hsno⟩
  have Hhu : (logHanded ls0).uents = s.logst.uents := Hf_uents
  have Hcbv : Bool.or (Bool.not (decide (ls0.uents = []))) (Option.map SnapLoan.snap L).isSome =
      decide (¬ (s.logst.uents = [] ∧ L = none)) := by
    rw [Hf_uents]; cases L <;> by_cases hu : s.logst.uents = [] <;> simp [hu]
  rw [Hcbv]
  have Hhp : (logHanded ls0).prev = s.logst.prev := Hf_prev
  have Hhs : (logHanded ls0).sents = s.logst.sents := Hf_sents
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ rd ∗
      ownRaftLog s.log (logHanded ls0) ∗ rnv.raft'.[raft, go!"raftLog"] ↦ s.log ∗
      rnv.raft'.[raft, go!"Term"] ↦ s.term ∗
      snapOpt rd.Snapshot' (DFrac.own (1 : Qp).half) (L.map SnapLoan.snap) ∗
      ∃ (stl' : GoSlice) (acks : List Loc),
        rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl' } ∗
        stl' ↦* ((selfmsgs id ms2).map QMsg.loc ++ acks) ∗
        ownSliceCap Loc stl' (DFrac.own 1) ∗
        (snapOpt rd.Snapshot' (DFrac.own 1) (L.map SnapLoan.snap) -∗
          pendList γ id acks (if s.logst.uents = [] ∧ L = none then []
            else [Pending.appendAck s.term s.logst.prev
              (if s.logst.uents ≠ [] then some (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))
               else none) (L.map SnapLoan.snap)])))
    with [rn rd Hlog Hf_raftLog Hf_Term Hrn Hsteps Hsteps_cap Hsno]
    as ⟨rn, rd, Hlog, Hf_raftLog, Hf_Term, Hsno, %stl3, %acks1, Hrn, Hsteps, Hsteps_cap, Hpa⟩
  · -- `newStorageAppendRespMsg(r, rd)`
    have Hc : ¬ (s.logst.uents = [] ∧ L = none) := by
      first | exact Hif | simpa using Hif
    wp_apply (wp_newStorageAppendRespMsg rnv.raft' id s.term s.log (logHanded ls0) rd _
        (L.map SnapLoan.snap) Hsnne)
      $$ [$Hf_id $Hf_Term $Hf_raftLog $Hlog $Hsno] as %ml ⟨Hml, Hsno, Hf_Term, Hf_raftLog, Hlog⟩
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %stl1 ⟨Hsl1, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hsteps $Hsteps_cap $Hsl1] as %stl' ⟨Hsteps, Hsteps_cap, -⟩
    isplitr
    · ipureintro; rfl
    iframe rn rd Hlog Hf_raftLog Hf_Term Hsno
    iexists stl', [ml]
    rw [ite_neg' Hc]
    iframe Hrn Hsteps Hsteps_cap
    iintro Hs1
    ihave Hml := Hml $$ Hs1
    iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
        pendingRel γ id st p))).2
    iexists _
    iframe Hml
    unfold pendingRel
    isplitr
    · ipureintro
      show _ = _
      rw [Hf_uents, Hf_prev, Hf_sents]
      by_cases hu : s.logst.uents = [] <;> simp [hu]
    · itrivial
  · -- nothing to acknowledge: no unstable entries, no snapshot
    have Hc : s.logst.uents = [] ∧ L = none := by
      first | exact Hif | exact Classical.not_not.1 Hif | simpa using Hif
    iframe rn rd Hlog Hf_raftLog Hf_Term Hsno
    iexists stl, []
    rw [ite_pos' Hc, List.append_nil]
    iframe Hrn Hsteps Hsteps_cap
    iintro -
    iapply pendList_nil
  -- `if needStorageApplyRespMsg(rd) { ... newStorageApplyRespMsg(r, rd.CommittedEntries) ... }`
  ihave %Hcel := entsPts_len _ _ _ $$ Hce
  wp_apply wp_needStorageApplyRespMsg
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ rd ∗
      ∃ (stl' : GoSlice) (acks : List Loc),
        rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl' } ∗
        stl' ↦* ((selfmsgs id ms2).map QMsg.loc ++ acks1 ++ acks) ∗
        ownSliceCap Loc stl' (DFrac.own 1) ∗
        pendList γ id acks (if ce = [] then [] else [Pending.applyAck ce]))
    with [rn rd Hrn Hsteps Hsteps_cap]
    as ⟨rn, rd, %stl4, %acks2, Hrn, Hsteps, Hsteps_cap, Hpc⟩
  · -- committed entries: `newStorageApplyRespMsg(r, rd.CommittedEntries)`
    have Hce0 : ce ≠ [] := by
      intro Hc; subst Hc; simp at Hcel; word
    wp_apply (wp_newStorageApplyRespMsg rnv.raft' id rd.CommittedEntries' ce) $$ [$Hf_id $Hce]
      as %ml Hml
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %stl1 ⟨Hsl1, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hsteps $Hsteps_cap $Hsl1] as %stl' ⟨Hsteps, Hsteps_cap, -⟩
    isplitr
    · ipureintro; rfl
    iframe rn rd
    iexists stl', [ml]
    rw [ite_neg' Hce0]
    iframe Hrn Hsteps Hsteps_cap
    iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
        pendingRel γ id st p))).2
    iexists _
    iframe Hml
    unfold pendingRel
    isplitr
    · ipureintro; rfl
    · itrivial
  · have Hce0 : ce = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    iframe rn rd
    iexists stl3, []
    rw [ite_pos' Hce0, List.append_nil]
    iframe Hrn Hsteps Hsteps_cap
    iapply pendList_nil
  wp_apply wp_raftLog_acceptUnstable _ ls0 (Hf_unp.trans Hunp) $$ [Hlog] as Hlog
  · iframe Hlog
  -- `if len(rd.CommittedEntries) > 0 { ... acceptApplying(ents[len(ents)-1].GetIndex(),
  -- entsSize(ents), applyUnstableEntries()) }`
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ rd ∗
      rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl4 } ∗
      rnv.raft'.[raft, go!"raftLog"] ↦ s.log ∗
      ∃ sz, ownRaftLog s.log (logAcceptApplying (logAcceptUnstable ls0) ce sz))
    with [rn rd Hrn Hf_raftLog Hlog] as ⟨rn, rd, Hrn, Hf_raftLog, %sz, Hlog⟩
  · -- the last committed entry handed out (no snapshot: `ls0` is the log)
    have Hce0 : ce ≠ [] := by
      intro Hc; subst Hc; simp at Hcel; word
    have HL : L = none := by
      cases hl : L with
      | none => rfl
      | some l => exact absurd (Hce0' l hl) Hce0
    have Hl0 : ls0 = s.logst := by rw [← Hls0, HL]; rfl
    subst Hl0
    obtain ⟨e, He⟩ : ∃ e, ce.getLast? = some e := by
      cases h : ce.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 h) Hce0
      | some e => exact ⟨e, rfl⟩
    obtain ⟨ce0, Hce0'⟩ := List.getLast?_eq_some_iff.1 He
    have Hlen0' : ce.length = ce0.length + 1 := by rw [Hce0']; simp
    have Hlk : ce[(sint.Z (rd.CommittedEntries'.len - W64 1)).toNat]? = some e := by
      have Hi : (sint.Z (rd.CommittedEntries'.len - W64 1)).toNat = ce0.length := by word
      rw [Hi, Hce0']; simp
    icases entsRO_lookup rd.CommittedEntries' ce _ e Hlk $$ Hce with ⟨%els, %le, #Hels, #Hle, %Hl⟩
    rw [ite_pos' (show 0 ≤ sint.Z (rd.CommittedEntries'.len - W64 1) ∧
      sint.Z (rd.CommittedEntries'.len - W64 1) < sint.Z rd.CommittedEntries'.len by word)]
    wp_apply wp_load_slice_index rd.CommittedEntries' (sint.Z (rd.CommittedEntries'.len - W64 1))
      els DFrac.discard le (by word) $$ [Hels] with -
    · iframe Hels; ipureintro; exact Hl.1
    wp_apply (wp_Entry_GetIndex.1 le DFrac.discard e) $$ [$Hle] as -
    wp_apply wp_entsSize rd.CommittedEntries' ce DFrac.discard $$ [$Hce] as %sz' -
    wp_method_call
    wp_call
    wp_auto
    rw [Hasync]
    have Hlast := Hceok e He
    icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcb2, Hlog⟩
    icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hnw2, Hlog⟩
    have Hend : uint.Z e.Index' < uint.Z (logEnd s.logst) := by
      have := (show LogNoWrap s.logst from Hnw2).logLast_Z
      unfold logEnd
      have := Hcb2.1.2.2
      simp only [logAcceptUnstable] at this Hnw2
      word
    wp_apply wp_raftLog_acceptApplying s.log (logAcceptUnstable s.logst) e.Index' sz' true
      ⟨by show uint.Z s.logst.applied ≤ _; omega, by show _ ≤ uint.Z s.logst.committed; omega,
        by show uint.Z s.logst.applying ≤ _; omega, Hend⟩
      (fun h => absurd (show s.logst.snap = none from (Hrdp.1 HL).2) h)
      $$ [Hlog] as Hlog
    · iframe Hlog
    isplitr
    · ipureintro; rfl
    iframe rn rd Hrn Hf_raftLog
    iexists sz'
    iExactEq Hlog
    unfold logAcceptApplying
    rw [He]
    rfl
  · have Hce0 : ce = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    subst Hce0
    iframe rn rd Hrn Hf_raftLog
    iexists W64 0
    have Hla : logAcceptApplying (logAcceptUnstable ls0) [] (W64 0) =
        logAcceptUnstable ls0 := rfl
    rw [Hla]
    iexact Hlog
  -- the ghost state: `Step.drain` was taken by `ownRawNodeReady_handout` (2026-10-13); now
  -- `Step.takeReads` (2026-10-13): the `ReadState`s were handed out, with their facts, by
  -- `readyWithoutAccept`
  imod rdCred_zero_upd (GF := GF) γ with Hcr0
  imod ownRaftGhost_step_takeReads (E := ⊤) γ id _ $$ [] [Hcr0] Hghost with Hghost
  · iapply (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) γ m)).2
    iempintro
  · rw [show rdCount ([] : List Msg) = 0 from rfl]; iexact Hcr0
  wp_apply wp_traceReady
  -- the self-addressed responses, as the queue's first pending steps (before the raft struct
  -- is closed: `Hself` is about `ms2`)
  have Hsub2 : ∀ q ∈ ms2, q ∈ ms1 ++ ms2 := fun q h => List.mem_append_right _ h
  ihave Hps := self_pending γ id s.term s.outbox ms1 ms2 Houtbox ms2 Hsub2 HmsgsAA_ok Hnsout
    (fun h => (Hxf.2.1 (Hnl.2.2.trans h)).2 (Hnl.2.1.trans h)) Hxf.2.2 $$ Hout Hqc Hself
  -- (D22 S-d3a) the log after the `Ready`: what it keeps of `ls0` and `s.logst`
  have Haf := accept_fields ls0 ce sz
  have Hsip00 : s.logst.sip = false := by
    cases h : s.logst.sip
    · rfl
    · exact absurd (Hloan.1.none_noack Hloan.2).1 (Hgh_unst.1.2.2.2.1 (.inl h))
  have HlL : logLast ls0 = logLast s.logst := by
    rw [← Hls0]; unfold rdyLs; split <;> rfl
  have Hnu0 : nextUnstable ls0 = nextUnstable s.logst := by
    unfold nextUnstable logOffset; rw [Hf_uents, Hf_ip, Hf_prev, Hf_sents]
  -- (D22 S-d3a) the snapshot handed out recorded (`NGhost.slent`, `snp`): `SnpOk` of the log after
  have HsnpN : SnpOk { s.gh with outlb := 0, unst := false, slent := L.isSome, snp := loanTrip L }
      (logAcceptApplying (logAcceptUnstable ls0) ce sz) := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -⟩ := Haf
    refine ⟨by rw [a5, Hf_lent], fun k hk => ?_, fun h => ?_, fun h => ?_, fun k hk hlt => ?_⟩
    rotate_right
    · -- (D22 S-d4 item 3) a snapshot handed out lends the storage
      exfalso
      cases hl : L with
      | none => rw [hl] at hk; cases hk
      | some l =>
        have : (logAcceptApplying (logAcceptUnstable ls0) ce sz).lent = true := by
          rw [a5, Hf_lent, hl]; rfl
        rw [this] at hlt; cases hlt
    · cases hl : L with
      | none => rw [hl] at hk; cases hk
      | some l =>
        rw [hl] at hk; simp only [loanTrip, Option.map_some, Option.some.injEq] at hk; subst hk
        obtain ⟨-, Hs1, -, Hk1, -⟩ := Hrdp.2 l hl
        refine ⟨fun _ => ⟨?_, .inl ?_⟩, ?_, ?_⟩
        · rw [a8, Hf_sip, Hf_snap, Hs1]; simp
        · rw [a5, Hf_lent, hl]; rfl
        · rw [a6, Hf_ksn]; exact Hk1
        · rw [a4, Hf_cm]
          have hp : ls0.prev = snapId l.snap :=
            (Hsfa.2.2.2 _ (show ls0.snap = _ by rw [Hf_snap]; exact Hs1)).1
          rw [Hf_prev] at hp
          have := Hwf2.1.1
          rw [hp] at this
          exact this
    · rcases h with h | h
      · rw [a8, Hf_sip, Hsip00, Bool.false_or, Hf_snap] at h
        cases hl : L with
        | none =>
          have := (Hrdp.1 hl).2
          rw [this] at h; simp at h
        | some l => simp [loanTrip]
      · rw [a7] at h; cases h
    · -- (D22 S-d3b) in progress only the snapshot handed out; nothing absorbed
      rcases h with h | h
      · rw [a8, Hf_sip, Hsip00, Bool.false_or, Hf_snap] at h
        cases hl : L with
        | none =>
          have := (Hrdp.1 hl).2
          rw [this] at h; simp at h
        | some l =>
          refine ⟨snapTrip l.snap l.snap.Metadata'.ConfState'.lists, by simp [loanTrip], ?_⟩
          rw [a2, Hf_snap]
          exact (Hrdp.2 l hl).2.1
      · rw [a7] at h; cases h
  -- the raft struct, closed with empty queues
  ihave Hphys := Hclose $$ %slice.nil %slice.nil %([] : List QMsg)
    %([] : List QMsg) %([] : List Msg)
    %(logAcceptApplying (logAcceptUnstable ls0) ce sz)
    %({ s.gh with outlb := 0, unst := false, slent := L.isSome, snp := loanTrip L } : NGhost)
    %rs' %({ s.rd with states := [] } : RdState)
    Hf_Term Hf_Vote Hf_readStates HreadStates' HreadStates_cap' %(And.intro rfl rfl)
    Hf_raftLog Hf_state Hf_lead Hf_msgs [] [] Hf_msgsAA [] []
    [] [] [] [] [] [] [] [] [] Hlog
  · rw [List.map_nil]; iapply ownSlice_nil
  · iapply ownSliceCap_nil
  · rw [List.map_nil]; iapply ownSlice_nil
  · iapply ownSliceCap_nil
  · iapply outboxRel_nil
  · ipureintro; intro _ h; cases h
  · ipureintro; intro _ h; cases h
  · ipureintro; exact Nat.zero_le _
  · ipureintro; exact ⟨(fun h => by cases h), HsnpN⟩
  · ipureintro
    obtain ⟨a1, a2, a3, a4, -⟩ := Haf
    exact ⟨rfl, fun _ => ⟨by rw [a1, Hf_prev], by rw [a2, Hf_snap], by rw [a3, Hf_st],
      by rw [a4, Hf_cm]; exact Int.le_refl _⟩, fun _ h => by cases h⟩
  · ipureintro; intro _; rw [logLast_acceptApplying, logLast_acceptUnstable, HlL]; exact Int.le_refl _
  · ipureintro
    exact XfOk.nil (fun h => (Hxf.1 h).1) (fun h => (Hxf.2.1 h).1)
  · rw [List.append_nil]; iapply qSrcs_nil
  -- the node after `Ready`
  have Hlogst : (readyNstate s L ce sz).logst = logAcceptApplying (logAcceptUnstable ls0) ce sz := by
    rw [← Hls0]; rfl
  obtain ⟨Haf1, Haf2, Haf3, Haf4, Haf5, Haf6, Haf7, Haf8, Haf9, Haf10, Haf11, Haf12, Haf13, Haf14⟩ :=
    Haf
  -- (D22 S-d3b) all of the log in progress after the `Ready`
  have Hip_last : plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) <
      uint.Z (readyNstate s L ce sz).logst.inprogress := by
    rw [Hlogst]
    have Hip : (logAcceptApplying (logAcceptUnstable ls0) ce sz).inprogress = logEnd ls0 := by
      unfold logAcceptApplying logAcceptUnstable; split <;> rfl
    rw [Hip]
    have Hw := Hwf3
    unfold logEnd logLast plogLastIndexZ
    rw [Hf_prev, Hf_sents, Hf_uents] at *
    simp only [List.length_append]
    word
  have Hce_ok : ∀ e, ce.getLast? = some e →
      uint.Z e.Index' ≤ uint.Z (readyNstate s L ce sz).logst.committed ∧
      uint.Z e.Index' ≤ uint.Z (readyNstate s L ce sz).logst.applying ∧
      (readyNstate s L ce sz).logst.applying = e.Index' ∧
      uint.Z e.Index' = uint.Z s.logst.applying + (ce.length : Int) := by
    intro e He
    have Hlast := Hceok e He
    have Ha := logAcceptApplying_applying (logAcceptUnstable ls0) ce sz e He
    rw [Hlogst, Haf4, Ha, Hf_cm]
    exact ⟨Hlast.2.1, Int.le_refl _, rfl, Hlast.2.2⟩
  have Hap0 : ce = [] → (readyNstate s L ce sz).logst.applying = s.logst.applying := by
    intro h; subst h; rw [Hlogst]; show ls0.applying = _; exact Hf_apg
  have Hdlen' : (rs.delivered ++ ce).length =
      (uint.Z (readyNstate s L ce sz).logst.applying).toNat := by
    cases He : ce.getLast? with
    | none =>
      have He' := List.getLast?_eq_none_iff.1 He
      rw [Hap0 He', He', List.append_nil, Hdlen]
    | some e =>
      obtain ⟨-, -, Ha, Hi⟩ := Hce_ok e He
      rw [Ha, List.length_append, Hdlen]
      word
  have Hstok' : StepsOk (readyNstate s L ce sz)
      (readySteps s L ((selfmsgs id ms2).map (fun q => selfPending q.st.msg)) ce) := by
    unfold readySteps
    rw [List.append_assoc]
    refine stepsOk_selfs _ _ _ (fun p Hp => ?_) ?_
    · -- each self-addressed response's term, as `ownRaftPhys` bounds it (`AAMsgOk`)
      obtain ⟨m, Hm, rfl⟩ := List.mem_map.1 Hp
      have Hm' := List.mem_filter.1 Hm
      obtain ⟨-, -, Hself⟩ := HmsgsAA_ok m Hm'.1
      have Hb := (Hself (of_decide_eq_true Hm'.2)).2.2.2.2
      refine ⟨⟨_, _, rfl⟩, ?_⟩
      simp only [PendingOk, selfPending, decide_eq_true_eq]
      refine ⟨Hb, fun _ => ?_⟩
      -- (2026-10-17) a pre-vote response within the ceiling (`OutTermOk`, `RNPv`)
      show _ ≤ uint.Z s.gh.tc
      have := Hpvoff.2.2.1
      rcases Hout_term m (List.mem_append_right _ Hm'.1) with h | h <;> omega
    apply ready_stepsOk _ _ _ _ _ ce _ (Int.le_refl _)
    · -- the acknowledgement is of the last entry of the log, which the storage holds
      -- once the entries handed out are appended (`logAcceptUnstable`); (D22 S-d3b) after the
      -- `Ready`'s boundary, at a term past `0` (`Hterm1`)
      intro _ x hx
      rw [Hlogst, Haf11, Hf_sents, Hf_uents]
      by_cases hu : s.logst.uents = []
      · simp [hu] at hx
      · simp only [hu, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hx
        exact ⟨hx, Hterm1 hu⟩
    · intro e He
      obtain ⟨H1, H2, -, -⟩ := Hce_ok e He
      exact ⟨H1, H2⟩
  ihave Hphys : ownRaftPhysCV cf cf.voters rnv.raft' id (readyNstate s L ce sz) $$ [Hphys]
  · unfold readyNstate
    rw [Hls0]
    iexact Hphys
  have Hrapp : (readyNstate s L ce sz).logst.applied = s.logst.applied := by
    rw [Hlogst, Haf10, Hf_ap]
  ihave Hrest := ghostRest_keep γ _ cf id (s := { s with outbox := [] })
    (s' := readyNstate s L ce sz) (by rw [toPState_ready]; rfl) (by rw [toPState_ready]; rfl)
    (by rw [toPState_ready]; rfl) (by rw [toPState_ready]; rfl) (by rw [toPState_ready]; rfl)
    Hrapp (by rw [Hlogst, Haf2, Hf_snap]) rfl
    (hst := by rw [Hlogst, Haf3, Hf_st]) $$ Hrest
  ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) cf id
      (readyNstate s L ce sz) $$ [Hghost Hrest]
  · iunfold ownStepGhost
    iframe Hrest
    rw [show toPState (readyNstate s L ce sz) = { toPState { s with outbox := [] } with
        rd := { (toPState { s with outbox := [] }).rd with states := [] } } by
      rw [toPState_ready]; rfl]
    iexact Hghost
  ihave #Hstrecs0 := storedRecs_eq γ _ s.logst.prev _
    (readyNstate s L ce sz).logst.stored (by rfl)
    (by rw [Hlogst, Haf11, Hf_sents, Hf_uents]; rfl) $$ Hlr
  -- the queue: the self-addressed responses, then the acknowledgements; (D22 S-d3a) with a
  -- snapshot, its acknowledgement whole once the application gives its half back (`lentPend`)
  ihave Hpend : lentPend L (pendList γ id ((selfmsgs id ms2).map QMsg.loc ++ acks1 ++ acks2)
      (readySteps s L ((selfmsgs id ms2).map (fun q => selfPending q.st.msg)) ce))
    $$ [Hps Hpa Hpc Hsno]
  · unfold readySteps
    cases hl : L with
    | none =>
      simp only [lentPend, snapOpt, Option.map_none, _root_.and_true]
      icases Hsno with %Hn
      ihave Hpa := Hpa $$ %Hn
      iapply (BigSepL2.bigSepL2_app_wand (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
          pendingRel γ id st p))) $$ [Hps Hpa] [Hpc]
      · iapply (BigSepL2.bigSepL2_app_wand (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
          pendingRel γ id st p))) $$ Hps Hpa
      · iexact Hpc
    | some l =>
      simp only [lentPend, snapOpt, Option.map_some]
      have Hpt := (Hrdp.2 l hl).1
      rw [← Hpt]
      iframe Hsno
      iintro Hs1
      ihave Hpa := Hpa $$ Hs1
      iapply (BigSepL2.bigSepL2_app_wand (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
          pendingRel γ id st p))) $$ [Hps Hpa] [Hpc]
      · iapply (BigSepL2.bigSepL2_app_wand (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
          pendingRel γ id st p))) $$ Hps Hpa
      · iexact Hpc
  -- (D19i part 1) the floor and `applied` unmoved; `applying` moved to the last committed entry
  -- handed out, whose acknowledgement is queued
  let rsN : RNState :=
    { rs with delivered := rs.delivered ++ ce, unpersisted := nextUnstable s.logst,
              steps := readySteps s L ((selfmsgs id ms2).map (fun q => selfPending q.st.msg)) ce,
              outlb := 0, unst := false, phs := phsNext rs.phs hrd, psnap := false, slent := L }
  have HrnflN : RNFl rsN (readyNstate s L ce sz) := by
    have Hfl0 : (readyNstate s L ce sz).logst.fl = s.logst.fl := by
      rw [Hlogst, Haf9, Hf_fl]
    refine ⟨fun hw => by rw [Hfl0, Hrapp]; exact Hrnfl.1 hw, fun hlt => ?_⟩
    cases hce : ce.getLast? with
    | none =>
      exfalso
      have hap := Hap0 (List.getLast?_eq_none_iff.1 hce)
      rw [hap, Hrapp] at hlt
      exact absurd Hrnfl.2 (Int.not_le.2 hlt)
    | some e =>
      obtain ⟨-, -, hap, -⟩ := Hce_ok e hce
      have Hne : ce ≠ [] := by intro h; subst h; simp at hce
      refine ⟨ce, e, ?_, hce, by rw [hap]; exact Int.le_refl _⟩
      show Pending.applyAck ce ∈ readySteps s L _ ce
      simp only [readySteps, if_neg Hne, List.mem_append, List.mem_singleton, _root_.or_true]
  -- (D22 S-d3a) the loan, as the node keeps it (`LoanOk`)
  have HloanN : LoanOk rsN (readyNstate s L ce sz) := by
    refine ⟨rfl, fun hl => ⟨?_, ?_⟩, fun l hl => ?_⟩
    · have hl' : L = none := hl
      show loanTrip L = none
      rw [hl']; rfl
    · intro t b e sv hm
      have hl' : L = none := hl
      subst hl'
      simp only [rsN, readySteps, Option.map_none, List.mem_append, List.mem_map] at hm
      rcases hm with (⟨q, -, hq⟩ | hm) | hm
      · simp [selfPending] at hq
      · split at hm <;> simp at hm
      · split at hm <;> simp at hm
    · have hl' : L = some l := hl
      subst hl'
      obtain ⟨Hs1, -, -, -, Hfl1, Hce1, Hdp1, Hdl1, Hap1, Hnx1, -⟩ := (Hrdp.2 l rfl).2
      subst Hce1
      have Hpl : s.logst.prev = snapId l.snap := by
        have hp : ls0.prev = snapId l.snap :=
          (Hsfa.2.2.2 _ (show ls0.snap = _ by rw [Hf_snap]; exact Hs1)).1
        rw [Hf_prev] at hp; exact hp
      refine ⟨rfl, .inl ?_, ?_, ?_, ?_, ?_, ?_, Hdl1, ?_⟩
      · rw [Hlogst, Haf2, Hf_snap, Hs1]
      · -- the snapshot, the log's boundary, at most the commit index
        rw [Hlogst, Haf4, Hf_cm]
        have := Hwf2.1.1
        rw [Hpl] at this
        exact this
      · rw [Hlogst, Haf9, Hf_fl, Hfl1]
      · rw [Hlogst, Haf11, Haf12, Hnu0, Hnx1, Hf_sents, Hf_uents]
      · rw [Hap0 rfl]; exact Int.le_of_lt Hap1
      · show rs.delivered ++ [] <+: l.dlv; rw [List.append_nil]; exact Hdp1
      · refine ⟨(selfmsgs id ms2).map (fun q => selfPending q.st.msg), s.term,
          if s.logst.uents ≠ [] then some (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))
          else none, ?_, ?_⟩
        · show readySteps s (some l) _ [] = _
          simp [readySteps, Hpl]
        · intro p hp
          obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
          exact ⟨_, _, rfl⟩
  -- (D22 S-d3b) the acknowledgement's facts (`ackInv`): the records of what the storage will hold,
  -- after the log's boundary; no restore since, nothing cut (all of it in progress)
  ihave #Hstrecs' : ackInv γ rsN (readyNstate s L ce sz) $$ []
  · unfold ackInv
    iintro %t %b %e %sn %hm
    have Hm2 : t = s.term ∧ b = s.logst.prev ∧ sn = L.map SnapLoan.snap := by
      simp only [rsN, readySteps, List.mem_append, List.mem_map] at hm
      rcases hm with (⟨q, -, hq⟩ | hm) | hm
      · simp [selfPending] at hq
      · split at hm
        · simp at hm
        · simp only [List.mem_singleton, Pending.appendAck.injEq] at hm
          exact ⟨hm.1, hm.2.1, hm.2.2.2⟩
      · split at hm <;> simp at hm
    obtain ⟨rfl, rfl, rfl⟩ := Hm2
    iframe Hstrecs0
    unfold ackArm
    ileft
    isplitr
    · ipureintro
      refine ⟨by rw [Hlogst, Haf1, Hf_prev], ?_⟩
      rw [Hlogst, Haf2, Hf_snap]
      cases hl : L with
      | none => exact (Hrdp.1 hl).2
      | some l => exact (Hrdp.2 l hl).2.1
    iintro %_
    unfold ackLostW
    ileft
    ipureintro
    rw [show (readyNstate s L ce sz).logst.stored = s.logst.sents ++ s.logst.uents by
      rw [Hlogst, Haf11, Hf_sents, Hf_uents]]
    exact Hip_last
  iapply HΦ $$ %(readySteps s L ((selfmsgs id ms2).map (fun q => selfPending q.st.msg)) ce)
  simp only [named]
  ihave #Hsloc' := snapLocOk_keep γ id (o' := (readyNstate s L ce sz).logst.snap)
    (.inl (by rw [Hlogst, Haf2, Hf_snap])) $$ Hsloc
  iapply ownRawNode_intro γ rn id rsN
    (readyNstate s L ce sz) cf fp
    { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl4 }
    v hph _
    Hwf Hin Hal Hasync Hdlen'
    (by show nextUnstable s.logst = _; rw [Hlogst, Haf12, Hnu0])
    (fun h => by
      rw [Hlogst, Haf2, Hf_snap]
      rcases h with ⟨-, h⟩ | h
      · exact (Hrdp.1 h).2
      · exact Hsnap (.inr h))
    Hstok' Htrm
    (by rw [Hlogst, Haf3, Hf_st]; exact Hstor)
    ⟨fun h => readyNstate_guard (Hpvoff.1 h), Hpvoff.2.1, Hpvoff.2.2.1, Hpvoff.2.2.2.1,
      readyNstate_snapFol Hpvoff.2.2.2.2⟩ rfl rfl
    (by rw [Hlogst, Haf4, Hf_cm]; exact Hrs_clb) HrnflN HloanN
    $$ Hrn Hphys Hghost Hsdrf Hpsp Hph Hsteps Hsteps_cap Hpend Hcommitted Hstrecs' Hloanc Hsloc'

end proof

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.readyNstate
