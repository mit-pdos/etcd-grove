/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgStorageAppendResp.v
(857d09190).

`Step`'s `MsgStorageAppendResp` branch (2026-10-05), in its own file. Proof structure,
not specification: no `Module Type`, no `Parameter`; only `Proof/raft__Step.lean` may
import this module.

Lean notes: the branch lemma takes the callee specs (Rocq's functor argument
`P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
section variable `c` as its second.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base
public import Proof.go_etcd_io.raft.v3.raft__Step.ReplLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

set_option maxHeartbeats 1000000 in
/-- The local acknowledgement `RawNode.Advance` steps after the application persisted a
`Ready`'s entries (`newStorageAppendRespMsg`: `Term` the term at `acceptReady`,
`Index`/`LogTerm` the last entry then, no snapshot). By the term:

- `Term = 0` or `Term = r.Term`: the type switch's case runs
  `if m.Index != 0 { r.raftLog.stableTo(entryID{m.LogTerm, m.Index}) }` and finds
  `m.Snapshot` `nil`;
- `Term < r.Term` (the node moved on since the `Ready`): the preamble's stale-message
  arm, which for this type only logs (and would apply a snapshot, `nil` here);
- `Term > r.Term` would make the node step down to a term no message brought --
  excluded by the premise.

The log is re-split (`logStableTo`) and the protocol sees nothing: `StepC.refl`. -/
theorem wp_Step_MsgStorageAppendResp_none (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (ents : List EntryM) :
    m.Type' = MsgStorageAppendResp →
    sn = none →
    uint.Z m.Term' ≤ uint.Z s.term →
    (m.Term' = W64 0 ∨ m.Term' = s.term →
     m.Index' ≠ W64 0 →
     StableOk s.logst (entryID.mk m.LogTerm' m.Index')) →
    s.gh.unst = false →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hframe" ∷ ⌜LocalFrame s s' ∧ s'.logst.applying = s.logst.applying⌝ ∗
        "%Hrefines" ∷ ⌜StepCD c id B m s [] s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hsn Hle Hstok Hghoff Hwf
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  by_cases Hstale : m.Term' ≠ W64 0 ∧ uint.Z m.Term' < uint.Z s.term
  · -- stale: logged and dropped
    obtain ⟨Hnz, Hlt⟩ := Hstale
    rw [decide_eq_false Hnz]
    wp_auto
    wp_drive _Q
    rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
    wp_auto
    wp_drive _Q
    rw [decide_eq_true Hlt]
    wp_auto
    wp_drive _Q
    -- not `MsgHeartbeat`/`MsgApp`, not `MsgPreVote`: the `MsgStorageAppendResp` arm
    wp_drive _Q
    cq_split _Q
    all_goals
      by_cases Hi0 : m.Index' = W64 0
      all_goals first
        | (rw [decide_eq_true Hi0]
           wp_auto)
        | (rw [decide_eq_false Hi0]
           wp_auto
           -- the log line
           wp_drive _Q
           wp_raft_logC)
    -- no snapshot
    all_goals
      wp_apply wp_GetSnapshot_none _Q _ _ _ _ _ Hsn $$ [$Hm] as Hm
      try wp_auto
      iapply HΦ $$ %interface.nil %s
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩,
        StepCD.frame (.refl _) (RFrame.refl _), rfl⟩
  -- `Term = 0` or `Term = r.Term`: the switch's case
  have Hmt : m.Term' = W64 0 ∨ m.Term' = s.term := by
    by_cases Hz : m.Term' = W64 0
    · exact .inl Hz
    · right
      have : ¬ uint.Z m.Term' < uint.Z s.term := fun h => Hstale ⟨Hz, h⟩
      word
  by_cases Hz : m.Term' = W64 0
  all_goals first
    | (rw [decide_eq_true Hz]
       wp_auto)
    | (rw [decide_eq_false Hz]
       wp_auto
       have Heq : m.Term' = s.term := Hmt.resolve_left Hz
       wp_drive _Q
       rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Heq]; omega)]
       wp_auto
       wp_drive _Q
       rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Heq]; omega)]
       wp_auto)
  -- the type switch: `MsgStorageAppendResp`
  all_goals
    wp_drive _Q
    by_cases Hi0 : m.Index' = W64 0
    · rw [decide_eq_true Hi0]
      wp_auto
      wp_apply wp_GetSnapshot_none _Q _ _ _ _ _ Hsn $$ [$Hm] as Hm
      try wp_auto
      iapply HΦ $$ %interface.nil %s
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩,
        StepCD.frame (.refl _) (RFrame.refl _), rfl⟩
    · rw [decide_eq_false Hi0]
      wp_auto
      -- `r.raftLog.stableTo(entryID{m.LogTerm, m.Index})`
      wp_drive _Q
      wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
      icases ownRaftPhysC_log_at c r id s $$ Hphys with ⟨Hlog, -, Hback⟩
      -- (D22 S-d1b) `stableTo` admits the acknowledgement's window (`ownRaftLogW`)
      icases ownRaftLog_quiet _ _ $$ Hlog with ⟨%Hq0, Hlog⟩
      ihave Hlog := ownRaftLog_toW _ _ $$ Hlog
      wp_apply _P.stableTo _ _ _ (Hstok Hmt Hi0) $$ [$Hlog] as Hlog
      ihave Hlog := ownRaftLogW_quietW _ _ $$ Hlog %(⟨by unfold logStableTo; split <;> exact Hq0.1,
        by unfold logStableTo; split <;> exact Hq0.2⟩)
      have Hkp : LogNsKeep s (logStableTo s.logst ⟨m.LogTerm', m.Index'⟩) := fun _ =>
        ⟨(logStableTo_fields _ _).2.2.2.2.1, (logStableTo_fields _ _).2.2.1,
          logStableTo_storage _ _, by unfold logStableTo; split <;> exact Int.le_refl _⟩
      ihave Hphys := Hback $$ %_ Hlog %(LogGhOk.of_off Hghoff Hkp (logStableTo_storage _ _))
        %(fun _ => by rw [logLast_stableTo]; exact Int.le_refl _)
      wp_apply wp_GetSnapshot_none _Q _ _ _ _ _ Hsn $$ [$Hm] as Hm
      try wp_auto
      iapply HΦ $$ %interface.nil %_
      iframe Hphys
      ipureintro
      obtain ⟨Hap, Hun, Hsn', Hip, Hpv, Hst⟩ :=
        logStableTo_fields s.logst (entryID.mk m.LogTerm' m.Index')
      refine ⟨Hwf, ⟨⟨rfl, Hip, Hun, Hsn', Hpv, Hst, logStableTo_storage _ _, rfl, rfl, rfl,
        by unfold logStableTo; split <;> rfl,
        by rw [show (logStableTo s.logst (entryID.mk m.LogTerm' m.Index')).applied = s.logst.applied
          by unfold logStableTo; split <;> rfl]; exact Int.le_refl _⟩, Hap⟩, ?_, rfl⟩
      refine StepCD.frame ?_ ⟨by unfold logStableTo; split <;> rfl, Hsn', fun h => ⟨h, rfl⟩⟩
      rw [toPState_logStableTo]
      exact .refl _


/-! ### A snapshot's acknowledgement (D22 S-d2, 2026-10-21) -/

/-- `m.GetSnapshot()` of a message holding the snapshot `sv`: a pointer to it, the message
given back with it. -/
theorem wp_GetSnapshot_some (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) (sv : SnapshotM) (h : ms.snap = some sv) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ msgPtsC l dq dqe cap ms }}
      (App (Val (l @!! go.GoType.PointerType raftpb.Message.ty @!! go!"GetSnapshot")) (Val #()))
    {{ (ps : Loc), RET #ps; ⌜ps ≠ null⌝ ∗ ownSnapM ps dq sv ∗
        (ownSnapM ps dq sv -∗ msgPtsC l dq dqe cap ms) }} := by
  iintro %Φ ⟨#Hi, Hm⟩ HΦ
  iapply Q.GetSnapshot.1 l dq dqe cap ms $$ [$Hi $Hm]
  inext
  iintro %ps ⟨Hs, Hback⟩
  ihave Hs' : ownSnapM (GF := GF) ps dq sv $$ [Hs]
  · rw [h] at *; simp only [snapOpt]; iexact Hs
  ihave %Hnn : ⌜ps ≠ null⌝ $$ [Hs']
  · iunfold ownSnapM at Hs'; iNamed Hs'; ipureintro; exact Hnn
  iapply HΦ
  iframe Hs'
  isplitr
  · ipureintro; exact Hnn
  iintro Hs
  iapply Hback
  rw [h]; simp only [snapOpt]; iexact Hs

theorem ackLog_fields (ls : LogState) (sv : SnapshotM) :
    (ackLog ls (some sv)).prev = ls.prev ∧ (ackLog ls (some sv)).sents = ls.sents ∧
    (ackLog ls (some sv)).uents = ls.uents ∧ (ackLog ls (some sv)).committed = ls.committed ∧
    (ackLog ls (some sv)).snap = ls.snap ∧ (ackLog ls (some sv)).storage = ls.storage ∧
    (ackLog ls (some sv)).inprogress = ls.inprogress ∧ (ackLog ls (some sv)).aps = ls.aps ∧
    (ackLog ls (some sv)).applying = ls.applying := by
  unfold ackLog
  by_cases h : ls.sat = true
  · rw [if_pos h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [if_neg h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ackLog_sapp (ls : LogState) (sv : SnapshotM) (h : ls.sapp = false) :
    (ackLog ls (some sv)).sapp = ls.sat := by
  unfold ackLog; cases hs : ls.sat <;> simp [h]

theorem ackSnapLog_none (ls : LogState) (m : MessageM) (t : w64) (sv : SnapshotM)
    (h : ackStableId m t = none) :
    ackSnapLog ls m t sv =
      logAppliedTo (logStableSnap (ackLog ls (some sv)) sv.Metadata'.Index') sv.Metadata'.Index'
        (W64 0) := by
  unfold ackSnapLog; rw [h]

theorem ackSnapLog_some (ls : LogState) (m : MessageM) (t : w64) (sv : SnapshotM) (id : entryID)
    (h : ackStableId m t = some id) :
    ackSnapLog ls m t sv =
      logAppliedTo (logStableSnap (logStableTo (ackLog ls (some sv)) id) sv.Metadata'.Index')
        sv.Metadata'.Index' (W64 0) := by
  unfold ackSnapLog; rw [h]

/-- What the acknowledgement keeps: the protocol log and the commit index. -/
theorem ackSnapLog_proto (ls : LogState) (m : MessageM) (t : w64) (sv : SnapshotM) :
    (ackSnapLog ls m t sv).prev = ls.prev ∧
    (ackSnapLog ls m t sv).sents ++ (ackSnapLog ls m t sv).uents = ls.sents ++ ls.uents ∧
    (ackSnapLog ls m t sv).committed = ls.committed ∧
    (ackSnapLog ls m t sv).storage = ls.storage ∧
    uint.Z ls.inprogress ≤ uint.Z (ackSnapLog ls m t sv).inprogress := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7, -, -⟩ := ackLog_fields ls sv
  have Hk : ∀ L : LogState, L.prev = ls.prev → L.sents ++ L.uents = ls.sents ++ ls.uents →
      L.committed = ls.committed → L.storage = ls.storage →
      uint.Z ls.inprogress ≤ uint.Z L.inprogress →
      (logAppliedTo (logStableSnap L sv.Metadata'.Index') sv.Metadata'.Index' (W64 0)).prev = ls.prev ∧
      (logAppliedTo (logStableSnap L sv.Metadata'.Index') sv.Metadata'.Index' (W64 0)).sents ++
        (logAppliedTo (logStableSnap L sv.Metadata'.Index') sv.Metadata'.Index' (W64 0)).uents
        = ls.sents ++ ls.uents ∧
      (logAppliedTo (logStableSnap L sv.Metadata'.Index') sv.Metadata'.Index' (W64 0)).committed
        = ls.committed ∧
      (logAppliedTo (logStableSnap L sv.Metadata'.Index') sv.Metadata'.Index' (W64 0)).storage
        = ls.storage ∧
      uint.Z ls.inprogress ≤
        uint.Z (logAppliedTo (logStableSnap L sv.Metadata'.Index') sv.Metadata'.Index' (W64 0)).inprogress := by
    intro L a b c d e
    obtain ⟨f1, f2, f3, f4, -, -, f7, -, -, f10, -⟩ := logStableSnap_fields L sv.Metadata'.Index'
    simp only [logAppliedTo]
    rw [f1, f2, f3, f4, f7, f10]
    exact ⟨a, b, c, d, e⟩
  unfold ackSnapLog
  split
  · rename_i id _
    obtain ⟨-, -, -, g4, g5, -⟩ := logStableTo_fields (ackLog ls (some sv)) id
    apply Hk
    · rw [g5, h1]
    · unfold logStableTo; split
      · simp only [List.append_assoc, List.take_append_drop]; rw [h2, h3]
      · rw [h2, h3]
    · unfold logStableTo; split <;> first | exact h4 | (simp only; exact h4)
    · rw [logStableTo_storage, h6]
    · rw [h7] at g4; exact g4
  · exact Hk _ h1 (by rw [h2, h3]) h4 h6 (by rw [h7]; exact Int.le_refl _)

/-- The acknowledgement's arm opens the windows on the raft struct (a ghost step): the log in
the `sapp` window when the storage is at the pending snapshot (`ownRaftLog_sapp`). -/
theorem ackOpen (c : CfgM) (r : Loc) (id : w64) (s : NState) (sv : SnapshotM)
    (Hghoff : s.gh.unst = false) :
    ownRaftPhysCV (GF := GF) c c.voters r id s ⊢
      ownRaftPhysCVW c c.voters r id { s with logst := ackLog s.logst (some sv) } := by
  iintro Hphys
  icases ownRaftPhysC_log_atW c r id s $$ Hphys with ⟨Hlog, %Hgh0, Hback⟩
  ihave Hlog : ownRaftLogW s.log (ackLog s.logst (some sv)) $$ [Hlog]
  · cases Hsat : s.logst.sat
    · have : ackLog s.logst (some sv) = s.logst := by simp [ackLog, Hsat]
      rw [this]; iapply ownRaftLog_toW; iexact Hlog
    · have : ackLog s.logst (some sv) = { s.logst with sapp := true } := by simp [ackLog, Hsat]
      rw [this]; iapply ownRaftLog_sapp _ _ Hsat; iexact Hlog
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, -⟩ := ackLog_fields s.logst sv
  have Hkeep0 : LogNsKeep s (ackLog s.logst (some sv)) :=
    fun _ => ⟨h1, h5, h6, by rw [h4]; exact Int.le_refl _⟩
  iapply Hback $$ %_ Hlog %(LogGhOk.of_off Hghoff Hkeep0 h6)
    %(fun _ => logLast_le_of_fields (by rw [h1]) (by rw [h2]) (by rw [h3]))

set_option maxHeartbeats 1000000 in
/-- `Step` on the acknowledgement of a `Ready` that handed out a snapshot `sv`, its receipt
absorbed (`sat` when it is the pending snapshot). By the term, as without a snapshot:

- `Term = 0` or `Term = r.Term`: the type switch's case runs `stableTo` when `Index ≠ 0` (in the
  `sapp` window the arm opens first, `ownRaftLog_sapp`: the entries after the snapshot move stable
  with the snapshot still pending), then `appliedSnap`;
- `Term < r.Term`: the stale arm, which logs and runs `appliedSnap` alone.

The log is `ackSnapLog`'s, the rest of the state kept; the protocol sees nothing. -/
theorem wp_Step_MsgStorageAppendResp_snap (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sv : SnapshotM) (ctx : List w8) (rs : List Loc) (ents : List EntryM) :
    m.Type' = MsgStorageAppendResp →
    snapHit s.logst.snap sv.Metadata'.Index' = s.logst.sat →
    uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.prev.index' →
    (c.autoLeave = true → s.role ≠ .leader) →
    uint.Z m.Term' ≤ uint.Z s.term →
    (m.Term' = W64 0 ∨ m.Term' = s.term →
     m.Index' ≠ W64 0 →
     StableOk (ackLog s.logst (some sv)) (entryID.mk m.LogTerm' m.Index')) →
    s.gh.unst = false →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, some sv, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id { s with logst := ackSnapLog s.logst m s.term sv } ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hhit Hle Hal Hlt Hstok Hghoff Hwf
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  -- what the windows need of the struct: the log quiet, no snapshot in the no-snapshot mode
  icases ownRaftPhysC_ns c r id s $$ Hphys with ⟨%Hnsl, -, Hphys⟩
  have Hns : s.gh.ns = true → s.logst.snap = none := fun h => (Hnsl h).1
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_quiet _ _ $$ Hlog with ⟨%Hq0, Hlog⟩
  ihave Hphys := Hback $$ Hlog
  obtain ⟨h1, -, -, -, h5, -, -, h8, -⟩ := ackLog_fields s.logst sv
  -- `appliedSnap`'s premises, at the log the arm leaves for it (`stableTo` keeps them)
  have Hsa0 : (ackLog s.logst (some sv)).sapp = s.logst.sat := ackLog_sapp _ _ Hq0.1
  have Hpre : ∀ L : LogState, L.snap = s.logst.snap → L.sapp = s.logst.sat → L.aps = false →
      L.prev = s.logst.prev →
      (snapHit L.snap sv.Metadata'.Index' = true ↔ L.sapp = true) ∧ L.aps = false ∧
      uint.Z sv.Metadata'.Index' ≤ uint.Z L.prev.index' := by
    intro L a b c d
    rw [a, b, d, Hhit]
    exact ⟨Iff.rfl, c, Hle⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  by_cases Hstale : m.Term' ≠ W64 0 ∧ uint.Z m.Term' < uint.Z s.term
  · -- stale: logged; `appliedSnap` alone
    obtain ⟨Hnz, Hlt'⟩ := Hstale
    have Hnone : ackStableId m s.term = none := by
      unfold ackStableId
      rw [if_neg]
      rintro ⟨h | h, -⟩
      · exact Hnz h
      · rw [h] at Hlt'; omega
    rw [decide_eq_false Hnz]
    wp_auto
    wp_drive _Q
    rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
    wp_auto
    wp_drive _Q
    rw [decide_eq_true Hlt']
    wp_auto
    wp_drive _Q
    -- not `MsgHeartbeat`/`MsgApp`, not `MsgPreVote`: the `MsgStorageAppendResp` arm
    wp_drive _Q
    cq_split _Q
    all_goals
      by_cases Hi0 : m.Index' = W64 0
      all_goals first
        | (rw [decide_eq_true Hi0]
           wp_auto)
        | (rw [decide_eq_false Hi0]
           wp_auto
           -- the log line
           wp_drive _Q
           wp_raft_logC)
    all_goals
      ihave Hphys := ackOpen c r id s sv Hghoff $$ Hphys
      wp_apply wp_GetSnapshot_some _Q _ _ _ _ _ sv rfl $$ [$Hm] as %ps ⟨%Hps, Hsv, Hmb⟩
      rw [decide_eq_false Hps]
      try wp_auto
      ihave Hm := Hmb $$ Hsv
      wp_apply wp_GetSnapshot_some _Q _ _ _ _ _ sv rfl $$ [$Hm] as %ps' ⟨%Hps', Hsv, Hmb⟩
      obtain ⟨Hiff, Haps, Hle1⟩ := Hpre _ h5 Hsa0 (by rw [h8]; exact Hq0.2) h1
      wp_apply _P.appliedSnap c r id { s with logst := ackLog s.logst (some sv) } _ _ sv Hiff Haps
        Hle1 Hal Hghoff (fun h => by simp only [h5]; exact Hns h) $$ [$Hphys $Hsv] as ⟨Hsv, Hphys⟩
      try wp_auto
      iapply HΦ $$ %interface.nil
      isplitl [Hphys]
      · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
        rw [ackSnapLog_none _ _ _ _ Hnone]
        try (first | rfl | (simp only [Hcq, Hpv]; done) | (simp only [Hcq]; done) | (simp only [Hpv]; done))
      ipureintro; rfl
  -- `Term = 0` or `Term = r.Term`: the switch's case
  have Hmt : m.Term' = W64 0 ∨ m.Term' = s.term := by
    by_cases Hz : m.Term' = W64 0
    · exact .inl Hz
    · right
      have : ¬ uint.Z m.Term' < uint.Z s.term := fun h => Hstale ⟨Hz, h⟩
      word
  by_cases Hz : m.Term' = W64 0
  all_goals first
    | (rw [decide_eq_true Hz]
       wp_auto)
    | (rw [decide_eq_false Hz]
       wp_auto
       have Heq : m.Term' = s.term := Hmt.resolve_left Hz
       wp_drive _Q
       rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Heq]; omega)]
       wp_auto
       wp_drive _Q
       rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Heq]; omega)]
       wp_auto)
  -- the type switch: `MsgStorageAppendResp`
  all_goals
    wp_drive _Q
    by_cases Hi0 : m.Index' = W64 0
    · have Hnone : ackStableId m s.term = none := by
        unfold ackStableId; rw [if_neg]; rintro ⟨-, h⟩; exact h Hi0
      rw [decide_eq_true Hi0]
      wp_auto
      ihave Hphys := ackOpen c r id s sv Hghoff $$ Hphys
      wp_apply wp_GetSnapshot_some _Q _ _ _ _ _ sv rfl $$ [$Hm] as %ps ⟨%Hps, Hsv, Hmb⟩
      rw [decide_eq_false Hps]
      try wp_auto
      ihave Hm := Hmb $$ Hsv
      wp_apply wp_GetSnapshot_some _Q _ _ _ _ _ sv rfl $$ [$Hm] as %ps' ⟨%Hps', Hsv, Hmb⟩
      obtain ⟨Hiff, Haps, Hle1⟩ := Hpre _ h5 Hsa0 (by rw [h8]; exact Hq0.2) h1
      wp_apply _P.appliedSnap c r id { s with logst := ackLog s.logst (some sv) } _ _ sv Hiff Haps
        Hle1 Hal Hghoff (fun h => by simp only [h5]; exact Hns h) $$ [$Hphys $Hsv] as ⟨Hsv, Hphys⟩
      try wp_auto
      iapply HΦ $$ %interface.nil
      isplitl [Hphys]
      · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
        rw [ackSnapLog_none _ _ _ _ Hnone]
        try (first | rfl | (simp only [Hcq, Hpv]; done) | (simp only [Hcq]; done) | (simp only [Hpv]; done))
      ipureintro; rfl
    · have Hsome : ackStableId m s.term = some ⟨m.LogTerm', m.Index'⟩ := by
        unfold ackStableId; rw [if_pos ⟨Hmt, Hi0⟩]
      rw [decide_eq_false Hi0]
      wp_auto
      -- `r.raftLog.stableTo(entryID{m.LogTerm, m.Index})`, in the window
      wp_drive _Q
      ihave Hphys := ackOpen c r id s sv Hghoff $$ Hphys
      wp_apply raft.wp_load_raftLogCW $$ Hphys as Hphys
      icases ownRaftPhysCVW_log_at c r id _ $$ Hphys with ⟨Hlog, -, Hback⟩
      wp_apply _P.stableTo _ _ _ (Hstok Hmt Hi0) $$ [$Hlog] as Hlog
      obtain ⟨-, -, g3, g4, g5, -⟩ :=
        logStableTo_fields (ackLog s.logst (some sv)) ⟨m.LogTerm', m.Index'⟩
      have Hkeep1 : LogNsKeep { s with logst := ackLog s.logst (some sv) }
          (logStableTo (ackLog s.logst (some sv)) ⟨m.LogTerm', m.Index'⟩) :=
        fun _ => ⟨g5, g3, logStableTo_storage _ _, by
          unfold logStableTo; split <;> exact Int.le_refl _⟩
      ihave Hphys := Hback $$ %_ Hlog %(LogGhOk.of_off Hghoff Hkeep1 (logStableTo_storage _ _))
        %(fun _ => by rw [logLast_stableTo]; exact Int.le_refl _)
      wp_apply wp_GetSnapshot_some _Q _ _ _ _ _ sv rfl $$ [$Hm] as %ps ⟨%Hps, Hsv, Hmb⟩
      rw [decide_eq_false Hps]
      try wp_auto
      ihave Hm := Hmb $$ Hsv
      wp_apply wp_GetSnapshot_some _Q _ _ _ _ _ sv rfl $$ [$Hm] as %ps' ⟨%Hps', Hsv, Hmb⟩
      have Hsapp1 : (logStableTo (ackLog s.logst (some sv)) ⟨m.LogTerm', m.Index'⟩).sapp =
          s.logst.sat := by
        unfold logStableTo; split <;> exact Hsa0
      have Haps1 : (logStableTo (ackLog s.logst (some sv)) ⟨m.LogTerm', m.Index'⟩).aps = false := by
        unfold logStableTo; split <;> (rw [h8]; exact Hq0.2)
      obtain ⟨Hiff, Haps, Hle1⟩ := Hpre _ (g3.trans h5) Hsapp1 Haps1 (g5.trans h1)
      ihave Hphys := ownRaftPhysCVW_eq c r id _
        { s with logst := logStableTo (ackLog s.logst (some sv)) ⟨m.LogTerm', m.Index'⟩ } rfl $$ Hphys
      wp_apply _P.appliedSnap c r id
          { s with logst := logStableTo (ackLog s.logst (some sv)) ⟨m.LogTerm', m.Index'⟩ } _ _ sv
          Hiff Haps Hle1 Hal Hghoff (fun h => by simp only [g3, h5]; exact Hns h)
        $$ [$Hphys $Hsv] as ⟨Hsv, Hphys⟩
      try wp_auto
      iapply HΦ $$ %interface.nil
      isplitl [Hphys]
      · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
        rw [ackSnapLog_some _ _ _ _ _ Hsome]
        try (first | rfl | (simp only [Hcq, Hpv]; done) | (simp only [Hcq]; done) | (simp only [Hpv]; done))
      ipureintro; rfl

end StepProof

end branches

end EtcdGrove
end Perennial
