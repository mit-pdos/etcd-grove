/- Port of election_proof/proof_RawNode__Ready.v (857d09190).

The Rocq main proof is `Admitted` after its WIP script (it ends in `Show.` once the raft
struct is closed with empty queues). Here the script is ported and then finished:
`RawNode.Ready.wp_proof` has no `sorry` (the tail after the Rocq's `Show.` -- the
postcondition: refolding `ownRawNode` at `readyNstate`/`readyRnstate`, `Hcommitted`,
`Hmsgs_abs`, `Hselfs`, `MustSync` -- is new, built from the Rocq's own helper lemmas).

Lean notes: `readyWithoutAccept`'s `rd` is tracked as `readyVal` (one field per
argument); `needStorageAppendRespMsg`, `newStorageAppendRespMsg` and
`newStorageApplyRespMsg`, stepped through inline in Rocq, get local specs
(`wp_*_inline`); the Rocq `wp_if_join`s are `wp_join`s. `to_pstate_ready`, `nstate_rel_ready`, `ready_committed_prefix`,
`ready_ce_last`, `nonself`, `selfmsgs`, `nonself_take_S`, `selfmsgs_take_S`, `selfabs`,
`self_pending`, `self_pending_own`, `selfabs_in`, `msgs_abs_list`, `nonself_sepL` are
`toPState_ready`, `nstateRel_ready`, `ready_committed_prefix`, `ready_ce_last`,
`nonself`, `selfmsgs`, `nonself_take_succ`, `selfmsgs_take_succ`, `selfabs`,
`self_pending`, `self_pending_own`, `selfabs_in`, `msgs_abs_list`, `nonself_sepL`.
-/
import EtcdGrove.Raft.Spec.RawNode__Ready
import EtcdGrove.Raft.Spec.raftLog__nextUnstableEnts
import EtcdGrove.Raft.Spec.raftLog__nextCommittedEnts
import EtcdGrove.Raft.Spec.SoftState__equal
import EtcdGrove.Raft.Spec.isHardStateEqual
import EtcdGrove.Raft.Spec.raftLog__hasNextUnstableSnapshot
import EtcdGrove.Raft.Spec.MustSync
import EtcdGrove.Raft.Spec.raftLog__hasNextOrInProgressUnstableEnts
import EtcdGrove.Raft.Spec.IsEmptyHardState
import EtcdGrove.Raft.Spec.IsEmptySnap
import EtcdGrove.Raft.Spec.raftLog__lastEntryID
import EtcdGrove.Raft.Spec.needStorageApplyRespMsg
import EtcdGrove.Raft.Spec.raftLog__acceptUnstable
import EtcdGrove.Raft.Spec.entsSize
import EtcdGrove.Raft.Spec.raftLog__acceptApplying
import EtcdGrove.Raft.Spec.traceReady

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- `if_pos`/`if_neg` (deprecated in core under those names). -/
private theorem ite_pos' {α : Sort _} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := ite_eq_left_of_eq_true _ _ (eq_true h)

private theorem ite_neg' {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := ite_eq_right_of_eq_false _ _ (eq_false h)

section helpers
variable [FfiSyntax]

/-- `Ready` changes nothing the protocol sees but the outbox. -/
theorem toPState_ready (s : NState) (ce : List raftpb.Entry) (sz : w64) :
    toPState (readyNstate s ce sz) = { toPState s with outbox := [] } := by
  unfold readyNstate logAcceptApplying logAcceptUnstable
  cases ce.getLast? <;> rfl

/-- The committed entries handed out sit in the global log right after its first
`applying` entries: `fp` is the log below the boundary `prev` (`FullOk`), `es` the log
after it. -/
theorem ready_committed_prefix (fp es ce : List raftpb.Entry) (prev : entryID) (cm apg : w64)
    (Hfp : (fp.length : Int) = uint.Z prev.index')
    (Hle : uint.Z prev.index' ≤ uint.Z apg ∧ uint.Z apg ≤ uint.Z cm)
    (Hcm : uint.Z cm ≤ uint.Z prev.index' + (es.length : Int))
    (Hnw : uint.Z cm + 1 < 2 ^ 64)
    (Hce : ce <+: (plogFrom prev es (apg + W64 1)).take (uint.Z cm - uint.Z apg).toNat) :
    (fp ++ es).take (uint.Z apg).toNat ++ ce <+: (fp ++ es).take (uint.Z cm).toNat ∧
    ((fp ++ es).take (uint.Z apg).toNat).length = (uint.Z apg).toNat := by
  unfold plogFrom at Hce
  have Hk : (uint.Z (apg + W64 1) - uint.Z prev.index' - 1).toNat
      = (uint.Z apg).toNat - fp.length := by word
  rw [Hk] at Hce
  rw [List.take_append, List.take_append,
    List.take_of_length_le (l := fp) (by omega), List.take_of_length_le (l := fp) (by omega)]
  refine ⟨?_, by simp only [List.length_append, List.length_take]; word⟩
  rw [List.append_assoc, List.prefix_append_right_inj]
  have Hsplit : (uint.Z cm).toNat - fp.length
      = ((uint.Z apg).toNat - fp.length) + (uint.Z cm - uint.Z apg).toNat := by omega
  rw [Hsplit, List.take_add, List.prefix_append_right_inj]
  exact Hce

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
    uint.Z apg < uint.Z e.Index' ∧ uint.Z e.Index' ≤ uint.Z cm := by
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
  omega

/-- The messages of `msgsAfterAppend` that `readyWithoutAccept` hands out (`To ≠ id`)
and those `acceptReady` keeps to step (`To = id`). -/
def nonself (id : w64) (ms : List raftpb.Message) : List raftpb.Message :=
  ms.filter (fun m => decide (m.To' ≠ id))
def selfmsgs (id : w64) (ms : List raftpb.Message) : List raftpb.Message :=
  ms.filter (fun m => decide (m.To' = id))

theorem nonself_take_succ (id : w64) (ms : List raftpb.Message) (n : Nat)
    (mm : raftpb.Message) (Hl : ms[n]? = some mm) :
    nonself id (ms.take (n + 1)) =
      nonself id (ms.take n) ++ (if mm.To' = id then [] else [mm]) := by
  unfold nonself
  rw [List.take_add_one, Hl]
  by_cases h : mm.To' = id <;> simp [List.filter_append, h]

theorem selfmsgs_take_succ (id : w64) (ms : List raftpb.Message) (n : Nat)
    (mm : raftpb.Message) (Hl : ms[n]? = some mm) :
    selfmsgs id (ms.take (n + 1)) =
      selfmsgs id (ms.take n) ++ (if mm.To' = id then [mm] else []) := by
  unfold selfmsgs
  rw [List.take_add_one, Hl]
  by_cases h : mm.To' = id <;> simp [List.filter_append, h]

def selfabs (id : w64) (ms : List raftpb.Message) (as_ : List (Option Msg)) :
    List (Option Msg) :=
  ((ms.zip as_).filter (fun p => decide (p.1.To' = id))).map Prod.snd

theorem selfabs_in (id : w64) (ms : List raftpb.Message) (as_ : List (Option Msg)) (x : Msg) :
    some x ∈ selfabs id ms as_ → some x ∈ as_ := by
  unfold selfabs
  intro Hx
  obtain ⟨⟨m, a⟩, Hp, rfl⟩ := List.mem_map.1 Hx
  exact List.of_mem_zip (List.mem_filter.1 Hp).1 |>.2

theorem selfmsgs_cons (id : w64) (m : raftpb.Message) (ms : List raftpb.Message) :
    selfmsgs id (m :: ms) = if m.To' = id then m :: selfmsgs id ms else selfmsgs id ms := by
  by_cases h : m.To' = id <;> simp [selfmsgs, h]

theorem nonself_cons (id : w64) (m : raftpb.Message) (ms : List raftpb.Message) :
    nonself id (m :: ms) = if m.To' = id then nonself id ms else m :: nonself id ms := by
  by_cases h : m.To' = id <;> simp [nonself, h]

theorem selfabs_cons (id : w64) (m : raftpb.Message) (ms : List raftpb.Message)
    (a : Option Msg) (as_ : List (Option Msg)) :
    selfabs id (m :: ms) (a :: as_) =
      if m.To' = id then a :: selfabs id ms as_ else selfabs id ms as_ := by
  by_cases h : m.To' = id <;> simp [selfabs, h]

/-- The `Ready` `readyWithoutAccept` builds, field by field (`Snapshot` stays zero and
`ReadStates` nil: no snapshot is pending, no read state is queued). -/
abbrev readyVal (sp : Loc) (hs : raftpb.HardState) (ents ce msgs : GoSlice) (ms : Bool) :
    Ready :=
  Ready.mk sp hs slice.nil ents (zero_val raftpb.Snapshot) ce msgs ms

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


/-- The self-addressed messages `acceptReady` queues, as pending steps. -/
theorem self_pending (id : w64) (ms : List raftpb.Message) (as_ : List (Option Msg)) :
    ⊢ ([∗list] _k ↦ m;a ∈ ms;as_, msgAbs (GF := GF) m a) -∗
      [∗list] _k ↦ m;p ∈ selfmsgs id ms;(selfabs id ms as_).map Pending.self,
        pendingRel (GF := GF) id m p := by
  induction ms generalizing as_ with
  | nil =>
    iintro H
    ihave %Has := BigSepL2.bigSepL2_nil_inv_left $$ H
    subst Has
    simp only [selfmsgs, selfabs, List.filter_nil, List.zip_nil_left, List.map_nil]
    iempintro
  | cons m ms IH =>
    iintro H
    icases (BigSepL2.bigSepL2_cons_inv_left).1 $$ H with ⟨%a, %as', %Has, #Hm, H⟩
    subst Has
    rw [selfmsgs_cons, selfabs_cons]
    by_cases h : m.To' = id
    · simp only [h, ↓reduceIte, List.map_cons]
      isplitr
      · simp only [pendingRel]
        isplitr
        · iexact Hm
        · ipureintro; exact h
      · iapply IH as' $$ H
    · simp only [h, ↓reduceIte]
      iapply IH as' $$ H

theorem self_pending_own (id : w64) (ms : List raftpb.Message) (as_ : List (Option Msg))
    (Hl : ms.length = as_.length) :
    ⊢ [∗list] _k ↦ m;p ∈ selfmsgs id ms;(selfabs id ms as_).map Pending.self,
        pendingOwn (GF := GF) m p := by
  induction ms generalizing as_ with
  | nil => simp only [selfmsgs, selfabs, List.filter_nil, List.zip_nil_left, List.map_nil]; iempintro
  | cons m ms IH =>
    cases as_ with
    | nil => cases Hl
    | cons a as' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at Hl
      rw [selfmsgs_cons, selfabs_cons]
      by_cases h : m.To' = id
      · simp only [h, ↓reduceIte, List.map_cons]
        isplitr
        · simp only [pendingOwn]
          itrivial
        · iapply IH as' Hl
      · simp only [h, ↓reduceIte]
        iapply IH as' Hl

theorem msgs_abs_list (P : Option Msg → Prop) (ms : List raftpb.Message)
    (as_ : List (Option Msg)) (HP : ∀ a ∈ as_, P a) :
    ⊢ ([∗list] _k ↦ m;a ∈ ms;as_, msgAbs (GF := GF) m a) -∗
      [∗list] m ∈ ms, ∃ a, msgAbs (GF := GF) m a ∗ ⌜P a⌝ := by
  induction ms generalizing as_ with
  | nil => iintro _; iempintro
  | cons m ms IH =>
    iintro H
    icases (BigSepL2.bigSepL2_cons_inv_left).1 $$ H with ⟨%a, %as', %Has, Hm, H⟩
    subst Has
    isplitl [Hm]
    · iexists a
      iframe Hm
      ipureintro
      exact HP a List.mem_cons_self
    · iapply IH as' (fun b Hb => HP b (List.mem_cons_of_mem _ Hb)) $$ H

theorem nonself_sepL (id : w64) (ms : List raftpb.Message) (Φ : raftpb.Message → IProp GF) :
    ⊢ ([∗list] m ∈ ms, Φ m) -∗ [∗list] m ∈ nonself id ms, Φ m := by
  induction ms with
  | nil => iintro _; simp only [nonself, List.filter_nil]; iempintro
  | cons m ms IH =>
    iintro ⟨Hm, H⟩
    rw [nonself_cons]
    by_cases h : m.To' = id
    · simp only [h, ↓reduceIte]
      iapply IH $$ H
    · simp only [h, ↓reduceIte]
      isplitl [Hm]
      · iexact Hm
      · iapply IH $$ H

/-- The `Ready`'s `SoftState`, made read-only (Rocq's inline `iAssert`). -/
private theorem soft_persist (c : Prop) [Decidable c] (sp : Loc) (v : SoftState) :
    ⊢ (if c then iprop(⌜sp = null⌝) else sp ↦ v) -∗
      |==> (if c then iprop(⌜sp = null⌝ : IProp GF) else sp ↦□ v) := by
  by_cases h : c
  · rw [ite_pos' h, ite_pos' h]
    iintro H; imodintro; iexact H
  · rw [ite_neg' h, ite_neg' h]
    iintro H
    ipersist H
    imodintro
    iexact H

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
        r.[raft, go!"id"] ↦ id ∗ r.[raft, go!"Term"] ↦ t ∗
        r.[raft, go!"raftLog"] ↦ l ∗ ownRaftLog l ls }}
      (App (App (Val #(functions newStorageAppendRespMsg [])) (Val #r)) (Val #rd))
    {{ RET #(appendAckMsg id t (plogLast ls.prev (ls.sents ++ ls.uents)));
        r.[raft, go!"id"] ↦ id ∗ r.[raft, go!"Term"] ↦ t ∗
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
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"id"] ↦ id }}
      (App (App (Val #(functions newStorageApplyRespMsg [])) (Val #r)) (Val #sl))
    {{ RET #(applyAckMsg id sl); r.[raft, go!"id"] ↦ id }} := by
  wp_start as Hid
  wp_auto
  ispecialize HΦ $$ Hid
  iExactEq HΦ
  rfl

theorem RawNode.Ready.wp_proof
    (wp_raftLog_nextUnstableEnts : raftLog.nextUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_raftLog_nextCommittedEnts : raftLog.nextCommittedEnts.spec (GF := GF) (hG := hG))
    (wp_SoftState_equal : SoftState.equal.spec (GF := GF) (hG := hG))
    (wp_isHardStateEqual : isHardStateEqual.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableSnapshot :
      raftLog.hasNextUnstableSnapshot.spec (GF := GF) (hG := hG))
    (wp_MustSync : MustSync.spec (GF := GF) (hG := hG))
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
    RawNode.Ready.spec (GF := GF) (hG := hG) := by
  intro cfg γ rn id s ps rs Hcfg Hrel Hsteps0 Hunp Hsnap
  wp_start as H
  iNamed H
  iNamed Hrn
  ihave %Hlen0 := BigSepL2.bigSepL2_length $$ Hpend
  rw [Hsteps0] at Hlen0
  cases steps with
  | cons _ _ => simp at Hlen0
  | nil =>
  -- ghost facts, read before anything moves
  ihave #Hout := ownRaftGhost_outbox _ _ _ $$ Hghost
  icases ownRaftGhost_committed _ _ _ $$ Hghost with ⟨%fp, %Hfp, #Hcm⟩
  icases ownRaftPhys_view cfg rnv.raft' id s $$ Hphys with ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hwf1, Hlog⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hwf2, Hlog⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hwf3, Hlog⟩
  icases ownRaftLog_wf _ _ $$ Hlog with ⟨%Hidx, Hlog⟩
  wp_auto
  -- `readyWithoutAccept`
  wp_method_call
  wp_call
  wp_auto
  -- the outer `rn` (of `Ready`) and the inner one (of `readyWithoutAccept`)
  rename_i rn0_ptr
  irename: (rn0_ptr ↦ (_ : Loc)) => rn0
  wp_apply wp_raftLog_nextUnstableEnts $$ [Hlog] as %sents ⟨Hlog, #Hents⟩
  · iframe Hlog
  -- `rn.applyUnstableEntries()` is `!asyncStorageWrites`
  wp_method_call
  wp_call
  wp_auto
  rw [Hasync]
  wp_apply wp_raftLog_nextCommittedEnts $$ [Hlog] as %sce %ce ⟨Hlog, #Hce, Hce_cap, %Hcepre, -⟩
  · iframe Hlog
  have Hsoft_iff : (s.lead = sv.Lead' ∧ stateW64 s.role = sv.RaftState') ↔
      nodeSoftstate s = rs.soft := by
    subst Hsoftv
    constructor
    · intro ⟨H1, H2⟩
      show SoftSt.mk _ _ = _
      rw [H1, H2]; rfl
    · intro H
      rw [← H]; exact ⟨rfl, rfl⟩
  have Hhs_iff : (s.term = (hardstateVal rs.hard).Term' ∧ s.vote = (hardstateVal rs.hard).Vote' ∧
      s.logst.committed = (hardstateVal rs.hard).Commit') ↔ nodeHardstate s = rs.hard := by
    constructor
    · intro ⟨H1, H2, H3⟩
      show HardSt.mk _ _ _ = _
      rw [H1, H2, H3]; rfl
    · intro H
      rw [← H]; exact ⟨rfl, rfl, rfl⟩
  -- `r.softState()`, compared with `prevSoftSt`; the two arms joined
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_SoftState_equal $$ [$softSt $Hsoft] as ⟨softSt, -⟩
  wp_join iprop(∃ sp, rd_ptr ↦ readyVal sp (zero_val raftpb.HardState) sents sce sl1 false ∗
      (if nodeSoftstate s = rs.soft then iprop(⌜sp = null⌝)
       else sp ↦ softstateVal (nodeSoftstate s)))
    with [rd softSt] as ⟨%sp, rd, Hsoftp⟩
  · iexists null
    iframe rd
    rw [ite_pos' (Hsoft_iff.1 Hif)]
    ipureintro; rfl
  · iexists escapingSoftSt_ptr
    iframe rd
    rw [ite_neg' (fun Hc => Hif (Hsoft_iff.2 Hc))]
    simp only [softstateVal, nodeSoftstate]
    iexact escapingSoftSt
  imod soft_persist _ _ _ $$ Hsoftp with #Hsoftp
  -- `r.hardState()`, compared with `prevHardSt`; the two arms joined
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_method_call
  wp_call
  wp_auto
  ihave Hlog := Hlb $$ Hl
  rw [Hlv.1]
  clear Hlv
  wp_apply wp_isHardStateEqual
  rw [Hhard]
  wp_join iprop(rd_ptr ↦ readyVal sp (if nodeHardstate s = rs.hard then zero_val raftpb.HardState
      else hardstateVal (nodeHardstate s)) sents sce sl1 false) with [rd hardSt] as rd
  · rw [ite_pos' (Hhs_iff.1 Hif)]
    iexact rd
  · rw [ite_neg' (fun Hc => Hif (Hhs_iff.2 Hc))]
    simp only [hardstateVal, nodeHardstate, readyVal]
    iexact rd
  wp_apply wp_raftLog_hasNextUnstableSnapshot $$ [Hlog] as %bsn ⟨Hlog, %Hbsn⟩
  · iframe Hlog
  rw [Hbsn Hsnap]
  wp_auto
  ihave %Hel := ownSlice_len _ _ _ $$ Hents
  rw [Hrs]
  wp_auto
  -- `MustSync(r.hardState(), rn.prevHardSt, len(rd.Entries))`
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv2, Hl, %Hlv, Hlb⟩
  wp_method_call
  wp_call
  wp_auto
  ihave Hlog := Hlb $$ Hl
  rw [Hlv.1, Hhard]
  clear Hlv
  wp_apply wp_MustSync
  rw [Hasync]
  wp_auto
  generalize HHS : (if nodeHardstate s = rs.hard then zero_val raftpb.HardState
      else hardstateVal (nodeHardstate s)) = HS
  generalize HMS : decide (¬sents.len = W64 0 ∨ ¬s.vote = rs.hard.vote ∨
      ¬s.term = rs.hard.term) = MS
  -- `for _, m := range r.msgsAfterAppend { if m.To != r.id { rd.Messages =
  -- append(rd.Messages, m) } }`: in place, into `r.msgs`' capacity
  ihave IH : iprop(∃ (n : w64) (msl : GoSlice) (mv : raftpb.Message),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗
      "rd" ∷ rd_ptr ↦ readyVal sp HS sents sce msl MS ∗
      "Hmsgs" ∷ msl ↦* (ms1 ++ nonself id (ms2.take (sint.nat n))) ∗
      "Hmsgs_cap" ∷ ownSliceCap raftpb.Message msl (DFrac.own 1) ∗
      "HmsgsAA" ∷ sl2 ↦* ms2 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ms2.length : Int)⌝)
    $$ [i m rd Hmsgs Hmsgs_cap HmsgsAA]
  · iexists W64 0, sl1, zero_val raftpb.Message
    have H0 : sint.nat (W64 0) = 0 := rfl
    rw [H0, List.take_zero]
    simp only [nonself, List.filter_nil, List.append_nil, named]
    iframe i m Hmsgs Hmsgs_cap HmsgsAA
    isplitl [rd]
    · iexact rd
    · ipureintro; word
  wp_for IH
  ihave %Hl2 := ownSlice_len _ _ _ $$ HmsgsAA
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
    · -- to oneself: kept for `acceptReady`
      wp_for_post
      iframe
      iexists n + W64 1, msl, mm
      -- (`wp_if_destruct` substituted `id := mm.To'`)
      rw [HnS, nonself_take_succ _ _ _ _ Hmm_lookup, ite_pos' rfl, List.append_nil]
      iframe
      ipureintro; word
    · -- to another node: handed out
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %msl1 ⟨Hsl1, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hmsgs $Hmsgs_cap $Hsl1] as %msl' ⟨Hmsgs, Hmsgs_cap, -⟩
      wp_for_post
      iframe
      iexists n + W64 1, msl', mm
      rw [HnS, nonself_take_succ _ _ _ _ Hmm_lookup, ite_neg' Hif, List.append_assoc]
      iframe
      ipureintro; word
  -- the loop is done: every message of `msgsAfterAppend` seen
  rw [List.take_of_length_le (l := ms2) (i := sint.nat n) (by word)]
  -- `acceptReady`
  wp_method_call
  wp_call
  wp_auto
  -- `if rd.SoftState != nil { rn.prevSoftSt = rd.SoftState }`: either way `prevSoftSt`
  -- points to the node's soft state
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ readyVal sp HS sents sce msl MS ∗
      ∃ psp, rn ↦ { rnv with prevSoftSt' := psp } ∗ psp ↦□ softstateVal (nodeSoftstate s))
    with [Hrn rn rd] as ⟨rn, rd, %psp, Hrn, #Hpsp⟩
  · -- `SoftState = nil`
    by_cases hc : nodeSoftstate s = rs.soft
    · iframe rn rd
      iexists rnv.prevSoftSt'
      rw [hc, ← Hsoftv]
      iframe Hsoft
      iexact Hrn
    · rw [ite_neg' hc]
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hsoftp
      exact absurd rfl Hnn
  · by_cases hc : nodeSoftstate s = rs.soft
    · rw [ite_pos' hc]
      icases Hsoftp with %Hsp
      exact absurd Hsp Hif
    · rw [ite_neg' hc]
      iframe rn rd
      iexists sp
      iframe Hsoftp
      iexact Hrn
  -- `if !IsEmptyHardState(rd.HardState) { rn.prevHardSt = rd.HardState }`
  wp_apply wp_IsEmptyHardState
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ readyVal sp HS sents sce msl MS ∗
      rn ↦ { rnv with prevSoftSt' := psp,
                      prevHardSt' := hardstateVal (if hsEmptyAbs (nodeHardstate s) then rs.hard
                                                   else nodeHardstate s) })
    with [Hrn rn rd] as ⟨rn, rd, Hrn⟩
  · -- empty: `prevHardSt` unchanged
    iframe rn rd
    have HPH : hardstateVal (if hsEmptyAbs (nodeHardstate s) then rs.hard else nodeHardstate s)
        = rnv.prevHardSt' := by
      rw [Hhard]
      subst HHS
      by_cases E : nodeHardstate s = rs.hard
      · rw [E]; split <;> rfl
      · rw [ite_neg' E] at Hif
        have : hsEmptyAbs (nodeHardstate s) = true := by
          simp only [hsEmptyAbs, decide_eq_true_eq]; exact Hif
        rw [this]; rfl
    rw [HPH]
    iexact Hrn
  · -- non-empty: `prevHardSt = rd.HardState`
    iframe rn rd
    have HPH : hardstateVal (if hsEmptyAbs (nodeHardstate s) then rs.hard else nodeHardstate s)
        = HS := by
      subst HHS
      by_cases E : nodeHardstate s = rs.hard
      · rw [ite_pos' E] at Hif
        exact absurd ⟨rfl, rfl, rfl⟩ Hif
      · rw [ite_neg' E] at Hif ⊢
        have : hsEmptyAbs (nodeHardstate s) = false := by
          simp only [hsEmptyAbs, decide_eq_false_iff_not]; exact Hif
        rw [this]; rfl
    rw [HPH]
    iexact Hrn
  rw [Hasync]
  ihave %Hs0 := ownSlice_len _ _ _ $$ Hsteps
  have Hs0' : rnv.stepsOnAdvance'.len = W64 0 := by
    simp only [List.length_nil] at Hs0
    word
  wp_auto
  rw [Hs0']
  wp_auto
  generalize HPH : hardstateVal (if hsEmptyAbs (nodeHardstate s) then rs.hard
      else nodeHardstate s) = PH
  -- `for _, m := range r.msgsAfterAppend { if m.To == r.id {
  -- rn.stepsOnAdvance = append(rn.stepsOnAdvance, m) } }`
  ihave IH : iprop(∃ (n : w64) (stl : GoSlice) (mv : raftpb.Message),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗
      "Hrn" ∷ rn ↦ { rnv with prevSoftSt' := psp, prevHardSt' := PH, stepsOnAdvance' := stl } ∗
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
    wp_IsEmptySnap rnv.raft' s.log s.logst _ rfl $$ [$Hf_raftLog $Hlog] as ⟨Hf_raftLog, Hlog⟩
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ readyVal sp HS sents sce msl MS ∗
      ownRaftLog s.log s.logst ∗ rnv.raft'.[raft, go!"raftLog"] ↦ s.log ∗
      rnv.raft'.[raft, go!"id"] ↦ id ∗ rnv.raft'.[raft, go!"Term"] ↦ s.term ∗
      ∃ stl', rn ↦ { rnv with prevSoftSt' := psp, prevHardSt' := PH, stepsOnAdvance' := stl' } ∗
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
      wp_IsEmptySnap wp_raftLog_lastEntryID rnv.raft' id s.term s.log s.logst _ Hif rfl
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
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ readyVal sp HS sents sce msl MS ∗
      rnv.raft'.[raft, go!"id"] ↦ id ∗
      ∃ stl', rn ↦ { rnv with prevSoftSt' := psp, prevHardSt' := PH, stepsOnAdvance' := stl' } ∗
        stl' ↦* (selfmsgs id ms2 ++
          (if s.logst.uents = [] then []
           else [appendAckMsg id s.term (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))]) ++
          (if ce = [] then [] else [applyAckMsg id sce])) ∗
        ownSliceCap raftpb.Message stl' (DFrac.own 1) ∗
        (if ce = [] then iprop(True) else ownSliceCap raftpb.Entry sce (DFrac.own 1)))
    with [rn rd Hf_id Hrn Hsteps Hsteps_cap Hce_cap]
    as ⟨rn, rd, Hf_id, %stl4, Hrn, Hsteps, Hsteps_cap, Hcecap⟩
  · -- committed entries: `newStorageApplyRespMsg(r, rd.CommittedEntries)`
    have Hce0 : ce ≠ [] := by
      intro Hc; subst Hc; simp at Hcel; word
    wp_apply wp_newStorageApplyRespMsg_inline rnv.raft' id sce $$ [$Hf_id] as Hf_id
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
  wp_apply wp_raftLog_acceptUnstable _ _ Hunp $$ [Hlog] as Hlog
  · iframe Hlog
  -- `if len(rd.CommittedEntries) > 0 { ... acceptApplying(index, entsSize(ents),
  -- applyUnstableEntries()) }`
  wp_join iprop(rn_ptr ↦ rn ∗ rd_ptr ↦ readyVal sp HS sents sce msl MS ∗
      rn ↦ { rnv with prevSoftSt' := psp, prevHardSt' := PH, stepsOnAdvance' := stl4 } ∗
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
    rw [ite_pos' (show 0 ≤ sint.Z (sce.len - W64 1) ∧ sint.Z (sce.len - W64 1) < sint.Z sce.len
      by word)]
    have Hlk : ce[(sint.Z (sce.len - W64 1)).toNat]? = some e := by
      have Hi : (sint.Z (sce.len - W64 1)).toNat = ce0.length := by word
      rw [Hi, Hce0']; simp
    icases ownSlice_elem_acc (sint.Z (sce.len - W64 1)) e sce DFrac.discard ce (by word) Hlk
      $$ Hce with ⟨He', -⟩
    -- the `Index` field load goes through the read-only element: split it into fields
    iStructNamed He'
    wp_auto
    wp_apply wp_entsSize sce ce DFrac.discard $$ [$Hce] as %sz' -
    wp_method_call
    wp_call
    wp_auto
    rw [Hasync]
    have Hlast := ready_ce_last _ ce _ s.logst.committed s.logst.applying e Hidx
      ⟨by have := Hwf2.2 Hsnap; omega, Hwf1.2.2⟩ (by omega) Hcepre He
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
    %(logAcceptApplying (logAcceptUnstable s.logst) ce sz)
    Hf_id Hf_Term Hf_Vote Hf_readStates Hf_raftLog Hf_state Hf_lead Hf_msgs [] [] Hf_msgsAA [] []
    [] Hlog
  · iapply ownSlice_nil
  · iapply ownSliceCap_nil
  · iapply ownSlice_nil
  · iapply ownSliceCap_nil
  · iapply outboxRel_nil
  -- Rocq stops here (`Show. Admitted.`); the rest is new in the Lean port.
  iunfold outboxRel at Houtbox
  icases Houtbox with ⟨%as1, %as2, %Hperm, #Hb1, #Hb2⟩
  ihave %Hla1 := BigSepL2.bigSepL2_length $$ Hb1
  ihave %Hla2 := BigSepL2.bigSepL2_length $$ Hb2
  obtain ⟨Hps, Hwfs⟩ := Hrel
  subst Hps
  have Hin_out : ∀ a ∈ as1 ++ as2, ∀ x, a = some x → x ∈ s.outbox := by
    intro a Ha x Hx
    subst Hx
    apply Hperm.mem_iff.2
    simp only [absList, ← List.filterMap_append]
    exact List.mem_filterMap.2 ⟨some x, Ha, rfl⟩
  ispecialize HΦ $$ %(readyVal sp HS sents sce msl MS) %ce %sz %(ms1 ++ nonself id ms2)
    %(selfabs id ms2 as2)
  iapply HΦ
  simp only [named]
  isplitl [Hrn Hphys Hsteps Hsteps_cap Hcecap]
  · unfold ownRawNode
    iexists { rnv with prevSoftSt' := psp, prevHardSt' := PH, stepsOnAdvance' := stl4 },
      softstateVal (nodeSoftstate s), _
    simp only [named]
    iframe Hrn Hsteps Hsteps_cap
    isplitl [Hphys]
    · unfold readyNstate
      iexact Hphys
    isplitr
    · ipureintro; exact Hasync
    isplitr
    · iexact Hpsp
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rw [← HPH]; rfl
    simp only [readyRnstate]
    isplitr
    · -- the pending steps' messages
      iapply BigSepL2.bigSepL2_app_wand $$ [] []
      · iapply BigSepL2.bigSepL2_app_wand $$ [] []
        · iapply self_pending id ms2 as2 $$ Hb2
        · by_cases hu : s.logst.uents = []
          · rw [ite_pos' hu, ite_pos' hu]; iempintro
          · rw [ite_neg' hu, ite_neg' hu]
            iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ m p => pendingRel (GF := GF) id m p)).2
            simp only [pendingRel]
            ipureintro; trivial
      · by_cases hc : ce = []
        · rw [ite_pos' hc, ite_pos' hc]; iempintro
        · rw [ite_neg' hc, ite_neg' hc]
          iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ m p => pendingRel (GF := GF) id m p)).2
          simp only [pendingRel]
          iexists sce
          isplitr
          · ipureintro; rfl
          · iexact Hce
    · -- what they own: the committed entries' capacity
      iapply BigSepL2.bigSepL2_app_wand $$ [] [Hcecap]
      · iapply BigSepL2.bigSepL2_app_wand $$ [] []
        · iapply self_pending_own id ms2 as2 Hla2
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
  isplitl [Hghost]
  · iexact Hghost
  isplitr
  · ipureintro
    refine ⟨nstateRel_ready s _ ce sz ⟨rfl, Hwfs⟩, ?_⟩
    rw [← Hcfg]; exact Hdrain
  isplitr
  · iexact Hents
  isplitr
  · iexact Hce
  isplitr
  · ipureintro; exact Hcepre
  isplitr
  · -- the committed entries handed out, in the global committed log
    have Hpre := ready_committed_prefix fp (s.logst.sents ++ s.logst.uents) ce s.logst.prev
      s.logst.committed s.logst.applying Hfp.1
      ⟨by have := Hwf2.2 Hsnap; omega, Hwf1.2.2⟩
      (by simp only [List.length_append]; push_cast; omega) (by omega) Hcepre
    iexists (fp ++ (s.logst.sents ++ s.logst.uents)).take (uint.Z s.logst.applying).toNat
    isplitl
    · rw [show (toPState s).commit = s.logst.committed from rfl,
        show (toPState s).log = s.logst.sents ++ s.logst.uents from rfl]
      iapply isCommitted_mono _ _ _ Hpre.1 $$ Hcm
    · ipureintro; exact Hpre.2
  isplitl [Hmsgs]
  · iexact Hmsgs
  isplitl [Hmsgs_cap]
  · iexact Hmsgs_cap
  isplitr
  · iapply (BigSepL.bigSepL_append (Φ := fun _ m => iprop(∃ a, msgAbs (GF := GF) m a ∗
        ⌜∀ (x : Msg), a = some x → x ∈ (toPState s).outbox⌝))).2
    isplitr
    · iapply msgs_abs_list (fun a => ∀ (x : Msg), a = some x → x ∈ (toPState s).outbox) ms1 as1
        (fun a Ha => Hin_out a (List.mem_append_left _ Ha)) $$ Hb1
    · iapply nonself_sepL id ms2 (fun m => iprop(∃ a, msgAbs (GF := GF) m a ∗
          ⌜∀ (x : Msg), a = some x → x ∈ (toPState s).outbox⌝))
      iapply msgs_abs_list (fun a => ∀ (x : Msg), a = some x → x ∈ (toPState s).outbox) ms2 as2
        (fun a Ha => Hin_out a (List.mem_append_right _ Ha)) $$ Hb2
  isplitr
  · ipureintro
    intro x Hx
    exact Hin_out _ (List.mem_append_right _ (selfabs_in id ms2 as2 x Hx)) x rfl
  isplitr
  · iexact Hout
  isplitr
  · ipureintro; trivial
  isplitr
  · iexact Hsoftp
  isplitr
  · ipureintro
    rw [← HMS]
    have Hne : (¬sents.len = W64 0) ↔ nextUnstable s.logst ≠ [] := by
      constructor
      · intro H Hc; apply H; rw [Hc] at Hel; simp at Hel; word
      · intro H Hc; apply H; apply List.eq_nil_of_length_eq_zero; rw [Hel.1, Hc]; rfl
    simp only [Hne]
  · ipureintro; trivial

end proof

end EtcdGrove
end Perennial
