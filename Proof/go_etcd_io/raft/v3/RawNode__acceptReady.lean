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
variable [FfiSyntax]

/-- The node after `Ready`: the outbox handed to the application, the unstable entries
in progress and the handed-out ones the application's to persist (`logAcceptUnstable`),
`applying` at the last committed entry handed out (`logAcceptApplying`; `sz` is
`entsSize` of them), and (2026-10-13) the `ReadState`s handed out (`r.readStates = nil`). -/
def readyNstate (s : NState) (ce : List EntryM) (sz : w64) : NState :=
  { s with outbox := [],
           logst := logAcceptApplying (logAcceptUnstable s.logst) ce sz,
           gh := { tc := s.gh.tc, ns := s.gh.ns, xf := s.gh.xf, bt := s.gh.bt },
           rd := { s.rd with states := [] } }

/-- The local messages `acceptReady` queues for `Advance`: the self-addressed responses
from `msgsAfterAppend` (`selfs`, each `selfPending`), an acknowledgement of the log up to
its last entry if there were unstable entries, and an acknowledgement of the committed
entries handed out, if any. -/
def readySteps (s : NState) (selfs : List Pending) (ce : List EntryM) :
    List Pending :=
  selfs ++
  (if s.logst.uents = [] then []
   else [Pending.appendAck s.term (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))]) ++
  (if ce = [] then [] else [Pending.applyAck ce])

/-- `Ready` changes nothing the protocol sees but the outbox and (2026-10-13) the
`ReadState`s. -/
theorem toPState_ready (s : NState) (ce : List EntryM) (sz : w64) :
    toPState (readyNstate s ce sz) =
      { toPState s with outbox := [], rd := { (toPState s).rd with states := [] } } := by
  unfold readyNstate logAcceptApplying logAcceptUnstable toPState
  by_cases h : s.role = .leader <;> cases ce.getLast? <;> simp [h, rdNL]

omit [FfiSyntax] in
private theorem prefix_getElem? {α : Type _} {l1 l2 : List α} {i : Nat} {x : α}
    (h : l1 <+: l2) (hx : l1[i]? = some x) : l2[i]? = some x := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]
  exact hx

/-- The last committed entry handed out is the one at `applying + len`, within
`(applying, committed]`: what `acceptApplying` needs. -/
theorem ready_ce_last (es ce : List EntryM) (prev : entryID) (cm apg : w64)
    (e : EntryM)
    (Hidx : LogIndicesOk prev es)
    (Hle : uint.Z prev.index' ≤ uint.Z apg ∧ uint.Z apg ≤ uint.Z cm)
    (Hnw : uint.Z cm + 1 < 2 ^ 64)
    (Hce : ce <+: (plogFrom prev es (apg + W64 1)).take (uint.Z cm - uint.Z apg).toNat)
    (Hl : ce.getLast? = some e) :
    uint.Z apg < uint.Z e.Index' ∧ uint.Z e.Index' ≤ uint.Z cm ∧
    uint.Z e.Index' = uint.Z apg + (ce.length : Int) := by
  unfold plogFrom at Hce
  have Hk : (uint.Z (apg + W64 1) - uint.Z prev.index' - 1).toNat
      = (uint.Z apg - uint.Z prev.index').toNat := by word
  rw [Hk] at Hce
  obtain ⟨ce0, rfl⟩ := List.getLast?_eq_some_iff.1 Hl
  have Hlen := Hce.length_le
  simp only [List.length_append, List.length_singleton, List.length_take] at Hlen
  have Hlk : (ce0 ++ [e])[ce0.length]? = some e := by simp
  have H1 := prefix_getElem? Hce Hlk
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at H1
  have H2 := Hidx _ _ H1
  push_cast at H2
  simp only [List.length_append, List.length_singleton]
  omega

/-- `StepsOk` of the acknowledgements `Ready` queues after the self-addressed
responses. -/
theorem ready_stepsOk (s' : NState) (t : w64) (last : entryID) (ce : List EntryM)
    (u : Prop) [Decidable u]
    (Ht : uint.Z t ≤ uint.Z s'.term)
    (Hl : ¬ u → plogLast s'.logst.prev s'.logst.stored = last)
    (Hce : ∀ e, ce.getLast? = some e →
      uint.Z e.Index' ≤ uint.Z s'.logst.committed ∧ uint.Z e.Index' ≤ uint.Z s'.logst.applying) :
    StepsOk s' ((if u then [] else [Pending.appendAck t last]) ++
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

end helpers

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem nstateRel_ready (s : NState) (ps : PState) (ce : List EntryM) (sz : w64) :
    NStateRel s ps → NStateRel (readyNstate s ce sz)
      { ps with outbox := [], rd := { ps.rd with states := [] } } := by
  intro ⟨Hps, Hwf⟩
  subst Hps
  exact ⟨toPState_ready s ce sz, Hwf⟩


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
  intro γ rn id rs rd ce es ms h
  wp_start as H
  iNamed H
  iNamed Hrn
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  ihave Hlog : ownRaftLog s.log (logHanded s.logst) $$ [Hlog]
  · iExactEq Hlog
    rfl
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
  icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hwf1, Hlog⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hwf2, Hlog⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hwf3, Hlog⟩
  icases ownRaftLog_wf _ _ $$ Hlog with ⟨%Hidx, Hlog⟩
  simp only [logHanded] at Hwf1 Hwf2 Hwf3 Hidx
  icases Hrdrs with ⟨%sts, #Hrdsts, %Hsts⟩
  ihave %Hstl := readStatesPts_len _ _ $$ Hrdsts
  icases Hrdhard with ⟨%hrd, #Hrdhard, #Hrdw⟩
  -- (D22l) the caller's hard state is the `Ready`'s
  ihave %Hhh := hsOpt_agree rd.HardState' hrd h $$ [Hrdhard Hh]
  · isplitl [] <;> iassumption
  subst Hhh
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
  -- `needStorageAppendRespMsg(r, rd)`: the snapshot is `nil`
  wp_apply (wp_needStorageAppendRespMsg rnv.raft' s.log (logHanded s.logst) rd Hrdz)
    $$ [$Hf_raftLog $Hlog] as ⟨Hf_raftLog, Hlog⟩
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ rd ∗
      ownRaftLog s.log (logHanded s.logst) ∗ rnv.raft'.[raft, go!"raftLog"] ↦ s.log ∗
      rnv.raft'.[raft, go!"Term"] ↦ s.term ∗
      ∃ (stl' : GoSlice) (acks : List Loc),
        rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl' } ∗
        stl' ↦* ((selfmsgs id ms2).map QMsg.loc ++ acks) ∗
        ownSliceCap Loc stl' (DFrac.own 1) ∗
        pendList γ id acks (if s.logst.uents = [] then []
           else [Pending.appendAck s.term (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))]))
    with [rn rd Hlog Hf_raftLog Hf_Term Hrn Hsteps Hsteps_cap]
    as ⟨rn, rd, Hlog, Hf_raftLog, Hf_Term, %stl3, %acks1, Hrn, Hsteps, Hsteps_cap, Hpa⟩
  · -- no unstable entries: nothing to acknowledge
    have Hu : s.logst.uents = [] := by first | exact Hif | simpa using Hif
    iframe rn rd Hlog Hf_raftLog Hf_Term
    iexists stl, []
    rw [ite_pos' Hu, List.append_nil]
    iframe Hrn Hsteps Hsteps_cap
    iapply pendList_nil
  · -- `newStorageAppendRespMsg(r, rd)`
    have Hu : s.logst.uents ≠ [] := by first | exact Hif | exact of_decide_eq_true Hif | simpa using Hif
    wp_apply (wp_newStorageAppendRespMsg rnv.raft' id s.term s.log (logHanded s.logst) rd Hrdz)
      $$ [$Hf_id $Hf_Term $Hf_raftLog $Hlog] as %ml ⟨Hml, Hf_Term, Hf_raftLog, Hlog⟩
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %stl1 ⟨Hsl1, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hsteps $Hsteps_cap $Hsl1] as %stl' ⟨Hsteps, Hsteps_cap, -⟩
    isplitr
    · ipureintro; rfl
    iframe rn rd Hlog Hf_raftLog Hf_Term
    iexists stl', [ml]
    rw [ite_neg' Hu]
    iframe Hrn Hsteps Hsteps_cap
    iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
        pendingRel γ id st p))).2
    iexists _
    iframe Hml
    unfold pendingRel
    isplitr
    · ipureintro
      show _ = _
      simp only [Hu, not_false_eq_true, ↓reduceIte]
    · itrivial
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
  wp_apply wp_raftLog_acceptUnstable _ _ Hunp Hsnap $$ [Hlog] as Hlog
  · iframe Hlog
  -- `if len(rd.CommittedEntries) > 0 { ... acceptApplying(ents[len(ents)-1].GetIndex(),
  -- entsSize(ents), applyUnstableEntries()) }`
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ rd ∗
      rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl4 } ∗
      rnv.raft'.[raft, go!"raftLog"] ↦ s.log ∗
      ∃ sz, ownRaftLog s.log (logAcceptApplying (logAcceptUnstable s.logst) ce sz))
    with [rn rd Hrn Hf_raftLog Hlog] as ⟨rn, rd, Hrn, Hf_raftLog, %sz, Hlog⟩
  · -- the last committed entry handed out
    have Hce0 : ce ≠ [] := by
      intro Hc; subst Hc; simp at Hcel; word
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
        by show uint.Z s.logst.applying ≤ _; omega, fun _ => Hend⟩
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
    have Hla : logAcceptApplying (logAcceptUnstable s.logst) [] (W64 0) =
        logAcceptUnstable s.logst := rfl
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
    (fun h => (Hxf.2 (Hnl.2.2.trans h)).2 (Hnl.2.1.trans h)) $$ Hout Hqc Hself
  -- the raft struct, closed with empty queues
  ihave Hphys := Hclose $$ %slice.nil %slice.nil %([] : List QMsg)
    %([] : List QMsg) %([] : List Msg)
    %(logAcceptApplying (logAcceptUnstable s.logst) ce sz) %({ tc := s.gh.tc, ns := s.gh.ns, xf := s.gh.xf, bt := s.gh.bt } : NGhost)
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
  · ipureintro; intro h; cases h
  · ipureintro
    refine ⟨rfl, fun _ => ?_, fun _ h => by cases h⟩
    unfold logAcceptApplying logAcceptUnstable
    split <;> exact ⟨rfl, rfl, rfl, Int.le_refl _⟩
  · ipureintro; intro _; rw [logLast_acceptApplying, logLast_acceptUnstable]; exact Int.le_refl _
  · ipureintro
    exact XfOk.nil (fun h => (Hxf.1 h).1) (fun h => (Hxf.2 h).1)
  · rw [List.append_nil]; iapply qSrcs_nil
  -- the node after `Ready`
  have Hlf := logAcceptApplying_fields (logAcceptUnstable s.logst) ce sz
  have Hlogst : (readyNstate s ce sz).logst = logAcceptApplying (logAcceptUnstable s.logst) ce sz :=
    rfl
  have Hce_ok : ∀ e, ce.getLast? = some e →
      uint.Z e.Index' ≤ uint.Z (readyNstate s ce sz).logst.committed ∧
      uint.Z e.Index' ≤ uint.Z (readyNstate s ce sz).logst.applying ∧
      (readyNstate s ce sz).logst.applying = e.Index' ∧
      uint.Z e.Index' = uint.Z s.logst.applying + (ce.length : Int) := by
    intro e He
    have Hlast := Hceok e He
    have Ha := logAcceptApplying_applying (logAcceptUnstable s.logst) ce sz e He
    rw [Hlogst, Hlf.1, Ha]
    exact ⟨Hlast.2.1, Int.le_refl _, rfl, Hlast.2.2⟩
  have Hdlen' : (rs.delivered ++ ce).length =
      (uint.Z (readyNstate s ce sz).logst.applying).toNat := by
    cases He : ce.getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at He
      subst He
      rw [List.append_nil, Hdlen]
      rfl
    | some e =>
      obtain ⟨-, -, Ha, Hi⟩ := Hce_ok e He
      rw [Ha, List.length_append, Hdlen]
      word
  have Hstok' : StepsOk (readyNstate s ce sz)
      (readySteps s ((selfmsgs id ms2).map (fun q => selfPending q.st.msg)) ce) := by
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
    apply ready_stepsOk _ _ _ ce _ (Int.le_refl _)
    · -- the acknowledgement is of the last entry of the log, which the storage holds
      -- once the entries handed out are appended (`logAcceptUnstable`)
      intro _
      rw [Hlogst, Hlf.2.2.2.2.1, Hlf.2.2.2.2.2]
      rfl
    · intro e He
      obtain ⟨H1, H2, -, -⟩ := Hce_ok e He
      exact ⟨H1, H2⟩
  ihave Hphys : ownRaftPhysCV cf cf.voters rnv.raft' id (readyNstate s ce sz) $$ [Hphys]
  · unfold readyNstate
    iexact Hphys
  have Hrapp : (readyNstate s ce sz).logst.applied = s.logst.applied := by
    simp only [readyNstate, logAcceptApplying, logAcceptUnstable]
    split <;> rfl
  ihave Hrest := ghostRest_keep γ _ cf id (s := { s with outbox := [] })
    (s' := readyNstate s ce sz) (by rw [toPState_ready]; rfl) (by rw [toPState_ready]; rfl)
    (by rw [toPState_ready]; rfl) (by rw [toPState_ready]; rfl) (by rw [toPState_ready]; rfl)
    Hrapp (by rw [Hlogst, Hlf.2.2.2.1]; rfl) rfl
    (hst := by simp only [readyNstate, logAcceptApplying, logAcceptUnstable]; split <;> rfl) $$ Hrest
  ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) cf id
      (readyNstate s ce sz) $$ [Hghost Hrest]
  · iunfold ownStepGhost
    iframe Hrest
    rw [show toPState (readyNstate s ce sz) = { toPState { s with outbox := [] } with
        rd := { (toPState { s with outbox := [] }).rd with states := [] } } by
      rw [toPState_ready]; rfl]
    iexact Hghost
  ihave #Hstrecs' := storedRecs_eq γ _ (readyNstate s ce sz).logst.prev _
    (readyNstate s ce sz).logst.stored (by rw [Hlogst, Hlf.2.2.2.2.1]; rfl)
    (by rw [Hlogst, Hlf.2.2.2.2.2]; rfl) $$ Hlr
  ihave #Hstrecs' := storedRecsP_intro γ rs.psnap _ _ $$ Hstrecs'
  -- the queue: the self-addressed responses, then the acknowledgements
  ihave Hpend : pendList γ id ((selfmsgs id ms2).map QMsg.loc ++ acks1 ++ acks2)
      (readySteps s ((selfmsgs id ms2).map (fun q => selfPending q.st.msg)) ce)
    $$ [Hps Hpa Hpc]
  · unfold readySteps
    iapply (BigSepL2.bigSepL2_app_wand (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
        pendingRel γ id st p))) $$ [Hps Hpa] [Hpc]
    · iapply (BigSepL2.bigSepL2_app_wand (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
        pendingRel γ id st p))) $$ Hps Hpa
    · iexact Hpc
  -- (D19i part 1) the floor and `applied` unmoved; `applying` moved to the last committed entry
  -- handed out, whose acknowledgement is queued
  have HrnflN : RNFl
      { rs with delivered := rs.delivered ++ ce, unpersisted := nextUnstable s.logst,
                steps := readySteps s ((selfmsgs id ms2).map (fun q => selfPending q.st.msg)) ce,
                outlb := 0, unst := false, phs := phsNext rs.phs hrd }
      (readyNstate s ce sz) := by
    have Hfl0 : (readyNstate s ce sz).logst.fl = s.logst.fl := by
      simp only [readyNstate, logAcceptApplying, logAcceptUnstable]
      split <;> rfl
    refine ⟨fun hw => by rw [Hfl0, Hrapp]; exact Hrnfl.1 hw, fun hlt => ?_⟩
    cases hce : ce.getLast? with
    | none =>
      exfalso
      have hap : (readyNstate s ce sz).logst.applying = s.logst.applying := by
        simp only [readyNstate, logAcceptApplying, logAcceptUnstable, hce]
      rw [hap, Hrapp] at hlt
      exact absurd Hrnfl.2 (Int.not_le.2 hlt)
    | some e =>
      have hap : (readyNstate s ce sz).logst.applying = e.Index' := by
        simp only [readyNstate, logAcceptApplying, logAcceptUnstable, hce]
      have Hne : ce ≠ [] := by intro h; subst h; simp at hce
      refine ⟨ce, e, ?_, hce, by rw [hap]; exact Int.le_refl _⟩
      simp only [readySteps, if_neg Hne, List.mem_append, List.mem_singleton, _root_.or_true]
  iapply HΦ $$ %(readySteps s ((selfmsgs id ms2).map (fun q => selfPending q.st.msg)) ce)
  simp only [named]
  iapply ownRawNode_intro γ rn id
    { rs with delivered := rs.delivered ++ ce, unpersisted := nextUnstable s.logst,
              steps := readySteps s ((selfmsgs id ms2).map (fun q => selfPending q.st.msg)) ce,
              outlb := 0, unst := false, phs := phsNext rs.phs hrd }
    (readyNstate s ce sz) cf fp
    { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl4 }
    v hph _
    Hwf Hin Hal Hasync Hdlen'
    (by rw [Hlogst, Hlf.2.2.1]; rfl) (fun _ => by rw [Hlogst, Hlf.2.2.2.1]; exact Hsnap) Hstok' Htrm
    (by rw [Hlogst, logAcceptApplying_storage]; exact Hstor) Hpvoff rfl rfl
    (by rw [Hlogst, Hlf.1]; exact Hrs_clb) HrnflN
    $$ Hrn Hphys Hghost Hsdrf Hpsp Hph Hsteps Hsteps_cap Hpend Hcommitted Hstrecs'

end proof

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.readyNstate
