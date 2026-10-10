/- `RawNode.acceptReady`, Lean-first (2026-10-10): the second half of the proof of
`RawNode.Ready` (`RawNode__Ready.lean` until then, itself the port of
election_proof/proof_RawNode__Ready.v at 857d09190, finished in Lean), from the call of
`acceptReady` on, starting from `ownRawNodeReady`. The node after `Ready` is
`readyNstate`, the queue `readySteps`, both internal to this proof.

Lean notes: `ready_rnstate`, `ready_nstate` are `readySteps` (only the queue: the
previous `SoftState`/`HardState` are no longer in `RNState`), `readyNstate`; Rocq's
`pending.self <$> selfs` is `selfs.map Pending.self`. `needStorageAppendRespMsg`,
`newStorageAppendRespMsg` and `newStorageApplyRespMsg`, stepped through inline in Rocq,
get local specs (`wp_*_inline`); the Rocq `wp_if_join`s are `wp_join`s.
`to_pstate_ready`, `nstate_rel_ready`, `ready_ce_last`, `selfmsgs`, `selfmsgs_take_S`,
`self_pending`, `self_pending_own` are `toPState_ready`, `nstateRel_ready`,
`ready_ce_last`, `selfmsgs`, `selfmsgs_take_succ`, `self_pending`, `self_pending_own`
(Rocq's `selfabs`, the self-addressed messages' abstractions, went on 2026-10-10: the
queue records the messages' terms, `selfPending`).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Spec.go_etcd_io.raft.v3.RawNode__acceptReady
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextOrInProgressUnstableEnts
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.raftLog__lastEntryID
public import Spec.go_etcd_io.raft.v3.needStorageApplyRespMsg
public import Spec.go_etcd_io.raft.v3.raftLog__acceptUnstable
public import Spec.go_etcd_io.raft.v3.entsSize
public import Spec.go_etcd_io.raft.v3.raftLog__acceptApplying
public import Spec.go_etcd_io.raft.v3.traceReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

/-- `if_pos`/`if_neg` (deprecated in core under those names). -/
private theorem ite_pos' {α : Sort _} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := ite_eq_left_of_eq_true _ _ (eq_true h)

private theorem ite_neg' {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := ite_eq_right_of_eq_false _ _ (eq_false h)

section helpers
variable [FfiSyntax]

/-- The node after `Ready`: the outbox handed to the application, the unstable entries
in progress and the handed-out ones the application's to persist (`logAcceptUnstable`),
`applying` at the last committed entry handed out (`logAcceptApplying`; `sz` is
`entsSize` of them). -/
def readyNstate (s : NState) (ce : List raftpb.Entry) (sz : w64) : NState :=
  { s with outbox := [],
           logst := logAcceptApplying (logAcceptUnstable s.logst) ce sz, gh := {} }

/-- The local messages `acceptReady` queues for `Advance`: the self-addressed responses
from `msgsAfterAppend` (`selfs`, each `selfPending`), an acknowledgement of the log up to
its last entry if there were unstable entries, and an acknowledgement of the committed
entries handed out, if any. -/
def readySteps (s : NState) (selfs : List Pending) (ce : List raftpb.Entry) :
    List Pending :=
  selfs ++
  (if s.logst.uents = [] then []
   else [Pending.appendAck s.term (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))]) ++
  (if ce = [] then [] else [Pending.applyAck ce])

/-- `Ready` changes nothing the protocol sees but the outbox. -/
theorem toPState_ready (s : NState) (ce : List raftpb.Entry) (sz : w64) :
    toPState (readyNstate s ce sz) = { toPState s with outbox := [] } := by
  unfold readyNstate logAcceptApplying logAcceptUnstable
  cases ce.getLast? <;> rfl

omit [FfiSyntax] in
private theorem prefix_getElem? {α : Type _} {l1 l2 : List α} {i : Nat} {x : α}
    (h : l1 <+: l2) (hx : l1[i]? = some x) : l2[i]? = some x := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]
  exact hx

/-- The last committed entry handed out is the one at `applying + len`, within
`(applying, committed]`: what `acceptApplying` needs. -/
theorem ready_ce_last (es ce : List raftpb.Entry) (prev : entryID) (cm apg : w64)
    (e : raftpb.Entry)
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
theorem ready_stepsOk (s' : NState) (t : w64) (last : entryID) (ce : List raftpb.Entry)
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

/-- The messages of `msgsAfterAppend` that `acceptReady` keeps to step (`To = id`;
`readyWithoutAccept` hands out the others, `nonself`). -/
def selfmsgs (id : w64) (ms : List raftpb.Message) : List raftpb.Message :=
  ms.filter (fun m => decide (m.To' = id))

theorem selfmsgs_take_succ (id : w64) (ms : List raftpb.Message) (n : Nat)
    (mm : raftpb.Message) (Hl : ms[n]? = some mm) :
    selfmsgs id (ms.take (n + 1)) =
      selfmsgs id (ms.take n) ++ (if mm.To' = id then [mm] else []) := by
  unfold selfmsgs
  rw [List.take_add_one, Hl]
  by_cases h : mm.To' = id <;> simp [List.filter_append, h]

theorem selfmsgs_cons (id : w64) (m : raftpb.Message) (ms : List raftpb.Message) :
    selfmsgs id (m :: ms) = if m.To' = id then m :: selfmsgs id ms else selfmsgs id ms := by
  by_cases h : m.To' = id <;> simp [selfmsgs, h]

end helpers

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

theorem nstateRel_ready (s : NState) (ps : PState) (ce : List raftpb.Entry) (sz : w64) :
    NStateRel s ps → NStateRel (readyNstate s ce sz) { ps with outbox := [] } := by
  intro ⟨Hps, Hwf⟩
  subst Hps
  exact ⟨toPState_ready s ce sz, Hwf⟩

/-- A response type is not a snapshot's. -/
theorem mtypeOf_resp_ne_snap (m : raftpb.Message)
    (H : m.Type' = MsgAppResp ∨ m.Type' = MsgVoteResp ∨ m.Type' = MsgPreVoteResp) :
    mtypeOf m.Type' ≠ some .snap := by
  rcases H with H | H | H <;> rw [H] <;> decide

/-- The self-addressed messages `acceptReady` queues, as pending steps (2026-10-10): each
is `AAMsgOk` (`ownRaftPhys`'s `msgsAfterAppend`), and its abstraction, at its entries
-- none: `Entries` is `nil` -- was in the outbox, whose messages are all `isMessage`
(`ownRaftGhost_outbox`). -/
theorem self_pending (γ : RaftNames) (id t : w64) (o : List Msg) (ms : List raftpb.Message)
    (as_ : List (Option Msg)) (HP : ∀ a ∈ as_, ∀ x, a = some x → x ∈ o)
    (Hok : ∀ m ∈ ms, AAMsgOk id t m) :
    ⊢ ([∗list] x ∈ o, isMessage (GF := GF) γ x) -∗
      ([∗list] _k ↦ m;a ∈ ms;as_, msgAbs (GF := GF) m a) -∗
      [∗list] _k ↦ m;p ∈ selfmsgs id ms;(selfmsgs id ms).map selfPending,
        pendingRel (GF := GF) γ id m p := by
  induction ms generalizing as_ with
  | nil =>
    iintro _ _
    simp only [selfmsgs, List.filter_nil, List.map_nil]
    iempintro
  | cons m ms IH =>
    iintro #Ho H
    icases (BigSepL2.bigSepL2_cons_inv_left).1 $$ H with ⟨%a, %as', %Has, #Hm, H⟩
    subst Has
    rw [selfmsgs_cons]
    have HP' : ∀ b ∈ as', ∀ x, b = some x → x ∈ o :=
      fun b Hb => HP b (List.mem_cons_of_mem _ Hb)
    have Hok' : ∀ m' ∈ ms, AAMsgOk id t m' := fun m' Hm' => Hok m' (List.mem_cons_of_mem _ Hm')
    by_cases h : m.To' = id
    · simp only [h, ↓reduceIte, List.map_cons]
      obtain ⟨Hty, Hfr, Hself⟩ := Hok m List.mem_cons_self
      obtain ⟨Hnz, Hen, Hcn, Hrj, -⟩ := Hself h
      isplitr
      · simp only [pendingRel, selfPending]
        isplitr
        · ipureintro
          refine ⟨⟨Hty, Hfr, h, Hnz, Hen, Hcn, Hrj⟩, ?_⟩
          simp
        imodintro
        iintro %ty %Hty'
        unfold msgAbs
        icases Hm with (%Hn | ⟨%ty0, %ents, %Hs, #Hents⟩ | ⟨%sv, %voters, %Hs, -, -⟩)
        · rw [Hn.1] at Hty'; cases Hty'
        · obtain ⟨Hty0, -, rfl⟩ := Hs
          rw [Hty0] at Hty'
          cases Hty'
          ihave %Hl := ownSlice_len _ _ _ $$ Hents
          have He : ents = [] := by
            rw [Hen] at Hl
            exact List.eq_nil_of_length_eq_zero Hl.1
          subst He
          iapply BigSepL.bigSepL_mem (Φ := fun x => isMessage (GF := GF) γ x)
            (HP _ List.mem_cons_self _ rfl) $$ Ho
        · exact absurd Hs.1 (mtypeOf_resp_ne_snap m Hty)
      · iapply IH as' HP' Hok' $$ Ho H
    · simp only [h, ↓reduceIte]
      iapply IH as' HP' Hok' $$ Ho H

theorem self_pending_own (id : w64) (ms : List raftpb.Message) :
    ⊢ [∗list] _k ↦ m;p ∈ selfmsgs id ms;(selfmsgs id ms).map selfPending,
        pendingOwn (GF := GF) m p := by
  induction ms with
  | nil => simp only [selfmsgs, List.filter_nil, List.map_nil]; iempintro
  | cons m ms IH =>
    rw [selfmsgs_cons]
    by_cases h : m.To' = id
    · simp only [h, ↓reduceIte, List.map_cons]
      isplitr
      · simp only [pendingOwn, selfPending]
        itrivial
      · iapply IH
    · simp only [h, ↓reduceIte]
      iapply IH

/-- `needStorageAppendRespMsg(r, rd)` is `hasNextOrInProgressUnstableEnts() ||
!IsEmptySnap(rd.Snapshot)`, and the snapshot is empty (Rocq: stepped through inline
under a `wp_wand`). -/
private theorem wp_needStorageAppendRespMsg_inline
    (wp_raftLog_hasNextOrInProgressUnstableEnts :
      raftLog.hasNextOrInProgressUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (r : Loc) (l : Loc) (ls : LogState) (rd : Ready)
    (Hsn : rd.Snapshot' = zero_val raftpb.Snapshot) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        r.[raft, go!"raftLog"] ↦ l ∗ ownRaftLog l ls }}
      (App (App (Val #(functions needStorageAppendRespMsg [])) (Val #r)) (Val #rd))
    {{ RET #(decide (ls.uents ≠ [])); r.[raft, go!"raftLog"] ↦ l ∗ ownRaftLog l ls }} := by
  wp_start as ⟨Hf, Hlog⟩
  wp_auto
  wp_apply wp_raftLog_hasNextOrInProgressUnstableEnts $$ [Hlog] as %bu ⟨Hlog, %Hbu⟩
  · iframe Hlog
  subst Hbu
  by_cases hu : ls.uents ≠ []
  · rw [decide_eq_true hu]
    wp_auto
    iapply HΦ
    iframe Hf Hlog
  · rw [decide_eq_false hu]
    wp_auto
    wp_apply wp_IsEmptySnap as %be %Hbe
    subst Hbe
    rw [Hsn]
    have H0 : (zero_val raftpb.Snapshot).Metadata'.Index' = W64 0 := rfl
    rw [decide_eq_true H0, Bool.not_true]
    iapply HΦ
    iframe Hf Hlog

/-- `newStorageAppendRespMsg(r, rd)` with unstable entries and no snapshot:
`appendAckMsg` at the log's last entry (Rocq: stepped through inline). -/
private theorem wp_newStorageAppendRespMsg_inline
    (wp_raftLog_hasNextOrInProgressUnstableEnts :
      raftLog.hasNextOrInProgressUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (r : Loc) (id t : w64) (l : Loc) (ls : LogState) (rd : Ready)
    (Hu : ls.uents ≠ []) (Hsn : rd.Snapshot' = zero_val raftpb.Snapshot) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        r.[raft, go!"id"] ↦□ id ∗ r.[raft, go!"Term"] ↦ t ∗
        r.[raft, go!"raftLog"] ↦ l ∗ ownRaftLog l ls }}
      (App (App (Val #(functions newStorageAppendRespMsg [])) (Val #r)) (Val #rd))
    {{ RET #(appendAckMsg id t (plogLast ls.prev (ls.sents ++ ls.uents)));
        r.[raft, go!"id"] ↦□ id ∗ r.[raft, go!"Term"] ↦ t ∗
        r.[raft, go!"raftLog"] ↦ l ∗ ownRaftLog l ls }} := by
  wp_start as ⟨Hid, Hterm, Hf, Hlog⟩
  wp_auto
  wp_apply wp_raftLog_hasNextOrInProgressUnstableEnts $$ [Hlog] as %bu ⟨Hlog, %Hbu⟩
  · iframe Hlog
  subst Hbu
  rw [decide_eq_true Hu]
  wp_auto
  wp_apply wp_raftLog_lastEntryID $$ [Hlog] as %e ⟨Hlog, %He⟩
  · iframe Hlog
  wp_apply wp_IsEmptySnap as %be %Hbe
  subst Hbe
  rw [Hsn]
  have H0 : (zero_val raftpb.Snapshot).Metadata'.Index' = W64 0 := rfl
  rw [decide_eq_true H0]
  wp_auto
  subst He
  ispecialize HΦ $$ [Hid Hterm Hf Hlog]
  · iframe
  iExactEq HΦ
  rfl

/-- `newStorageApplyRespMsg(r, ents)` (Rocq: stepped through inline). -/
private theorem wp_newStorageApplyRespMsg_inline (r : Loc) (id : w64) (sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"id"] ↦□ id }}
      (App (App (Val #(functions newStorageApplyRespMsg [])) (Val #r)) (Val #sl))
    {{ RET #(applyAckMsg id sl); r.[raft, go!"id"] ↦□ id }} := by
  wp_start as Hid
  wp_auto
  ispecialize HΦ $$ Hid
  iExactEq HΦ
  rfl

theorem RawNode.acceptReady.wp_proof
    (wp_raftLog_hasNextOrInProgressUnstableEnts :
      raftLog.hasNextOrInProgressUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (wp_needStorageApplyRespMsg : needStorageApplyRespMsg.spec (GF := GF) (hG := hG))
    (wp_raftLog_acceptUnstable : raftLog.acceptUnstable.spec (GF := GF) (hG := hG))
    (wp_entsSize : entsSize.spec (GF := GF) (hG := hG))
    (wp_raftLog_acceptApplying : raftLog.acceptApplying.spec (GF := GF) (hG := hG))
    (wp_traceReady : traceReady.spec (GF := GF) (hG := hG)) :
    RawNode.acceptReady.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs rd ce es ms
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
  -- ghost facts, read before anything moves
  ihave #Hout := ownRaftGhost_outbox _ _ _ $$ Hghost
  icases ownRaftGhost_storedRecs_keep _ _ _ $$ Hghost with ⟨Hghost, #Hlr⟩
  icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hwf1, Hlog⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hwf2, Hlog⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hwf3, Hlog⟩
  icases ownRaftLog_wf _ _ $$ Hlog with ⟨%Hidx, Hlog⟩
  simp only [logHanded] at Hwf1 Hwf2 Hwf3 Hidx
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
  -- `if !IsEmptyHardState(rd.HardState) { rn.prevHardSt = rd.HardState }`: no spec
  -- constrains `prevHardSt`
  wp_apply wp_IsEmptyHardState
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ rd ∗
      ∃ ph, rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph })
    with [Hrn rn rd] as ⟨rn, rd, %ph, Hrn⟩
  rw [Hrdz.2, Hasync]
  ihave %Hs0 := ownSlice_len _ _ _ $$ Hsteps
  have Hs0' : rnv.stepsOnAdvance'.len = W64 0 := by
    simp only [List.length_nil] at Hs0
    word
  wp_auto
  rw [Hs0']
  wp_auto
  -- `for _, m := range r.msgsAfterAppend { if m.To == r.id {
  -- rn.stepsOnAdvance = append(rn.stepsOnAdvance, m) } }`
  ihave IH : iprop(∃ (n : w64) (stl : GoSlice) (mv : raftpb.Message),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗
      "Hrn" ∷ rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl } ∗
      "Hsteps" ∷ stl ↦* selfmsgs id (ms2.take (sint.nat n)) ∗
      "Hsteps_cap" ∷ ownSliceCap raftpb.Message stl (DFrac.own 1) ∗
      "HmsgsAA" ∷ sl2 ↦* ms2 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ms2.length : Int)⌝)
    $$ [i m Hrn Hsteps Hsteps_cap HmsgsAA]
  · iexists W64 0, rnv.stepsOnAdvance', zero_val raftpb.Message
    have H0 : sint.nat (W64 0) = 0 := rfl
    rw [H0, List.take_zero]
    simp only [selfmsgs, List.filter_nil, named]
    iframe i m Hsteps Hsteps_cap HmsgsAA
    isplitl [Hrn]
    · rw [Hasync]
      iexact Hrn
    · ipureintro; word
  wp_for IH
  ihave %Hl3 := ownSlice_len _ _ _ $$ HmsgsAA
  wp_if_destruct
  · list_elem ms2 (sint.nat n) as mm
    rw [ite_pos' (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl2.len from ⟨Hn.1, Hif⟩)]
    wp_apply wp_load_slice_index sl2 (sint.Z n) ms2 (DFrac.own 1) mm Hn.1 $$ [HmsgsAA]
      with HmsgsAA
    · iframe
      ipureintro
      exact Hmm_lookup
    have HnS : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    wp_if_destruct
    · -- to oneself: queued to step on `Advance`
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %stl1 ⟨Hsl1, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hsteps $Hsteps_cap $Hsl1] as %stl' ⟨Hsteps, Hsteps_cap, -⟩
      wp_for_post
      iframe
      iexists n + W64 1, stl', mm
      -- (`wp_if_destruct` substituted `id := mm.To'`)
      rw [HnS, selfmsgs_take_succ _ _ _ _ Hmm_lookup, ite_pos' rfl]
      iframe
      ipureintro; word
    · wp_for_post
      iframe
      iexists n + W64 1, stl, mm
      rw [HnS, selfmsgs_take_succ _ _ _ _ Hmm_lookup, ite_neg' Hif, List.append_nil]
      iframe
      ipureintro; word
  rw [List.take_of_length_le (l := ms2) (i := sint.nat n) (by word)]
  -- `needStorageAppendRespMsg(r, rd)`: the snapshot is empty
  wp_apply wp_needStorageAppendRespMsg_inline wp_raftLog_hasNextOrInProgressUnstableEnts
    wp_IsEmptySnap rnv.raft' s.log (logHanded s.logst) _ Hrdz.1 $$ [$Hf_raftLog $Hlog] as ⟨Hf_raftLog, Hlog⟩
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ rd ∗
      ownRaftLog s.log (logHanded s.logst) ∗ rnv.raft'.[raft, go!"raftLog"] ↦ s.log ∗
      rnv.raft'.[raft, go!"id"] ↦□ id ∗ rnv.raft'.[raft, go!"Term"] ↦ s.term ∗
      ∃ stl', rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl' } ∗
        stl' ↦* (selfmsgs id ms2 ++
          (if s.logst.uents = [] then []
           else [appendAckMsg id s.term (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))])) ∗
        ownSliceCap raftpb.Message stl' (DFrac.own 1))
    with [rn rd Hlog Hf_raftLog Hf_id Hf_Term Hrn Hsteps Hsteps_cap]
    as ⟨rn, rd, Hlog, Hf_raftLog, Hf_id, Hf_Term, %stl3, Hrn, Hsteps, Hsteps_cap⟩
  · -- no unstable entries: nothing to acknowledge
    iframe rn rd Hlog Hf_raftLog Hf_id Hf_Term
    iexists stl
    rw [ite_pos' Hif, List.append_nil]
    iframe Hrn Hsteps Hsteps_cap
  · -- `newStorageAppendRespMsg(r, rd)`
    wp_apply wp_newStorageAppendRespMsg_inline wp_raftLog_hasNextOrInProgressUnstableEnts
      wp_IsEmptySnap wp_raftLog_lastEntryID rnv.raft' id s.term s.log (logHanded s.logst) _ Hif Hrdz.1
      $$ [$Hf_id $Hf_Term $Hf_raftLog $Hlog] as ⟨Hf_id, Hf_Term, Hf_raftLog, Hlog⟩
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %stl1 ⟨Hsl1, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hsteps $Hsteps_cap $Hsl1] as %stl' ⟨Hsteps, Hsteps_cap, -⟩
    isplitr
    · ipureintro; rfl
    iframe rn rd Hlog Hf_raftLog Hf_id Hf_Term
    iexists stl'
    rw [ite_neg' Hif]
    iframe Hrn Hsteps Hsteps_cap
  -- `if needStorageApplyRespMsg(rd) { ... newStorageApplyRespMsg(r, rd.CommittedEntries) ... }`
  ihave %Hcel := ownSlice_len _ _ _ $$ Hce
  wp_apply wp_needStorageApplyRespMsg
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ rd ∗
      rnv.raft'.[raft, go!"id"] ↦□ id ∗
      ∃ stl', rawNodeOwn rn { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl' } ∗
        stl' ↦* (selfmsgs id ms2 ++
          (if s.logst.uents = [] then []
           else [appendAckMsg id s.term (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))]) ++
          (if ce = [] then [] else [applyAckMsg id rd.CommittedEntries'])) ∗
        ownSliceCap raftpb.Message stl' (DFrac.own 1) ∗
        (if ce = [] then iprop(True)
         else ownSliceCap raftpb.Entry rd.CommittedEntries' (DFrac.own 1)))
    with [rn rd Hf_id Hrn Hsteps Hsteps_cap Hce_cap]
    as ⟨rn, rd, Hf_id, %stl4, Hrn, Hsteps, Hsteps_cap, Hcecap⟩
  · -- committed entries: `newStorageApplyRespMsg(r, rd.CommittedEntries)`
    have Hce0 : ce ≠ [] := by
      intro Hc; subst Hc; simp at Hcel; word
    wp_apply wp_newStorageApplyRespMsg_inline rnv.raft' id rd.CommittedEntries' $$ [$Hf_id]
      as Hf_id
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %stl1 ⟨Hsl1, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hsteps $Hsteps_cap $Hsl1] as %stl' ⟨Hsteps, Hsteps_cap, -⟩
    isplitr
    · ipureintro; rfl
    iframe rn rd Hf_id
    iexists stl'
    rw [ite_neg' Hce0, ite_neg' Hce0, List.append_assoc]
    iframe Hrn Hsteps Hsteps_cap Hce_cap
  · have Hce0 : ce = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    iframe rn rd Hf_id
    iexists stl3
    rw [ite_pos' Hce0, ite_pos' Hce0, List.append_nil]
    iframe Hrn Hsteps Hsteps_cap
  wp_apply wp_raftLog_acceptUnstable _ _ Hunp Hsnap $$ [Hlog] as Hlog
  · iframe Hlog
  -- `if len(rd.CommittedEntries) > 0 { ... acceptApplying(index, entsSize(ents),
  -- applyUnstableEntries()) }`
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
    rw [ite_pos' (show 0 ≤ sint.Z (rd.CommittedEntries'.len - W64 1) ∧
      sint.Z (rd.CommittedEntries'.len - W64 1) < sint.Z rd.CommittedEntries'.len by word)]
    have Hlk : ce[(sint.Z (rd.CommittedEntries'.len - W64 1)).toNat]? = some e := by
      have Hi : (sint.Z (rd.CommittedEntries'.len - W64 1)).toNat = ce0.length := by word
      rw [Hi, Hce0']; simp
    icases ownSlice_elem_acc (sint.Z (rd.CommittedEntries'.len - W64 1)) e rd.CommittedEntries'
      DFrac.discard ce (by word) Hlk $$ Hce with ⟨He', -⟩
    -- the `Index` field load goes through the read-only element: split it into fields
    iStructNamed He'
    wp_auto
    wp_apply wp_entsSize rd.CommittedEntries' ce DFrac.discard $$ [$Hce] as %sz' -
    wp_method_call
    wp_call
    wp_auto
    rw [Hasync]
    have Hlast := Hceok e He
    wp_apply wp_raftLog_acceptApplying s.log (logAcceptUnstable s.logst) e.Index' sz' true
      ⟨by show uint.Z s.logst.applied ≤ _; omega, by show _ ≤ uint.Z s.logst.committed; omega⟩
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
  -- the ghost state: `Step.drain`
  have Hdrain : Step γ.reCfg id ps [] { ps with outbox := [] } :=
    Step.drain ps [] List.nil_subperm
  imod ownRaftGhost_step_0 _ _ _ _ Hdrain $$ Hghost with Hghost
  wp_apply wp_traceReady
  -- the raft struct, closed with empty queues
  ihave Hphys := Hclose $$ %slice.nil %slice.nil %([] : List raftpb.Message)
    %([] : List raftpb.Message) %([] : List Msg)
    %(logAcceptApplying (logAcceptUnstable s.logst) ce sz) %({} : NGhost)
    Hf_Term Hf_Vote Hf_readStates Hf_raftLog Hf_state Hf_lead Hf_msgs [] [] Hf_msgsAA [] []
    [] [] [] [] [] Hlog
  · iapply ownSlice_nil
  · iapply ownSliceCap_nil
  · iapply ownSlice_nil
  · iapply ownSliceCap_nil
  · iapply outboxRel_nil
  · ipureintro; intro _ h; cases h
  · ipureintro; intro _ h; cases h
  · ipureintro; exact Nat.zero_le _
  · ipureintro; intro h; cases h
  iunfold outboxRel at Houtbox
  icases Houtbox with ⟨%as1, %as2, %Hperm, #Hb1, #Hb2⟩
  obtain ⟨Hps, Hwfs⟩ := Hrel
  subst Hps
  have Hin_out : ∀ a ∈ as1 ++ as2, ∀ x, a = some x → x ∈ s.outbox := by
    intro a Ha x Hx
    subst Hx
    apply Hperm.mem_iff.2
    simp only [absList, ← List.filterMap_append]
    exact List.mem_filterMap.2 ⟨some x, Ha, rfl⟩
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
  have Hstok' :
      StepsOk (readyNstate s ce sz) (readySteps s ((selfmsgs id ms2).map selfPending) ce) := by
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
      refine ⟨Hb, fun Hpf => ?_⟩
      have Hnp := (Hout_term m (List.mem_append_right _ Hm'.1) Hpf).2
      simp only [decide_eq_false_iff_not]
      exact Hnp
    apply ready_stepsOk _ _ _ ce _ (Int.le_refl _)
    · -- the acknowledgement is of the last entry of the log, which the storage holds
      -- once the entries handed out are appended (`logAcceptUnstable`)
      intro _
      rw [Hlogst, Hlf.2.2.2.2.1, Hlf.2.2.2.2.2]
      rfl
    · intro e He
      obtain ⟨H1, H2, -, -⟩ := Hce_ok e He
      exact ⟨H1, H2⟩
  ihave Hphys : ownRaftPhys γ.reCfg rnv.raft' id (readyNstate s ce sz) $$ [Hphys]
  · unfold readyNstate
    iexact Hphys
  ihave #Hstrecs' := storedRecs_eq γ _ (readyNstate s ce sz).logst.prev _
    (readyNstate s ce sz).logst.stored (by rw [Hlogst, Hlf.2.2.2.2.1]; rfl)
    (by rw [Hlogst, Hlf.2.2.2.2.2]; rfl) $$ Hlr
  iapply HΦ $$ %(readySteps s ((selfmsgs id ms2).map selfPending) ce)
  simp only [named]
  iapply ownRawNode_intro γ rn id
    { rs with delivered := rs.delivered ++ ce, unpersisted := nextUnstable s.logst,
              steps := readySteps s ((selfmsgs id ms2).map selfPending) ce,
              outlb := 0, unst := false }
    (readyNstate s ce sz) { toPState s with outbox := [] }
    { rnv with prevSoftSt' := psp, prevHardSt' := ph, stepsOnAdvance' := stl4 }
    v _
    (nstateRel_ready s _ ce sz ⟨rfl, Hwfs⟩) Hin Hasync Hdlen'
    (by rw [Hlogst, Hlf.2.2.1]; rfl) (by rw [Hlogst, Hlf.2.2.2.1]; exact Hsnap) Hstok' Htrm
    (by rw [Hlogst, logAcceptApplying_storage]; exact Hstor) Hpvoff rfl rfl
    (by rw [Hlogst, Hlf.1]; exact Hrs_clb)
    $$ Hrn Hphys Hghost Hpsp Hsteps Hsteps_cap [] [Hcecap] Hcommitted Hstrecs'
  · -- the pending steps' messages
    simp only [readySteps]
    iapply BigSepL2.bigSepL2_app_wand $$ [] []
    · iapply BigSepL2.bigSepL2_app_wand $$ [] []
      · iapply self_pending γ id s.term (toPState s).outbox ms2 as2
          (fun a Ha => Hin_out a (List.mem_append_right _ Ha)) HmsgsAA_ok $$ Hout Hb2
      · by_cases hu : s.logst.uents = []
        · rw [ite_pos' hu, ite_pos' hu]; iempintro
        · rw [ite_neg' hu, ite_neg' hu]
          iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ m p => pendingRel (GF := GF) γ id m p)).2
          simp only [pendingRel]
          ipureintro; trivial
    · by_cases hc : ce = []
      · rw [ite_pos' hc, ite_pos' hc]; iempintro
      · rw [ite_neg' hc, ite_neg' hc]
        iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ m p => pendingRel (GF := GF) γ id m p)).2
        simp only [pendingRel]
        iexists rd.CommittedEntries'
        isplitr
        · ipureintro; rfl
        · iexact Hce
  · -- what they own: the committed entries' capacity
    simp only [readySteps]
    iapply BigSepL2.bigSepL2_app_wand $$ [] [Hcecap]
    · iapply BigSepL2.bigSepL2_app_wand $$ [] []
      · iapply self_pending_own id ms2
      · by_cases hu : s.logst.uents = []
        · rw [ite_pos' hu, ite_pos' hu]; iempintro
        · rw [ite_neg' hu, ite_neg' hu]
          iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ m p => pendingOwn (GF := GF) m p)).2
          simp only [pendingOwn]
          itrivial
    · by_cases hc : ce = []
      · simp only [hc, ↓reduceIte]; iempintro
      · simp only [hc, ↓reduceIte]
        iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ m p => pendingOwn (GF := GF) m p)).2
        simp only [pendingOwn, applyAckMsg]
        iexact Hcecap

end proof

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.readyNstate
