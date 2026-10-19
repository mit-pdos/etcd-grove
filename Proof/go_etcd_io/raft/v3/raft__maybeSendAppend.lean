/-
Port of election_proof/proof_raft__maybeSendAppend.v.

Lean notes: Rocq's `msa_pkg` and its one `;`-chained script for the three arms are the
macros `msa_fetch`/`msa_tail`/`msa_send`, which work on hypotheses of fixed names
(`Hents : sl_e ↦*□ es_e`, `Hphys`, `Hwin`, `Hpkgin`, `Hpkgpre`). In the full-window
arm `wp_auto` already decides `len(ents) == 0` on the zero slice, so that arm splits on
`sendIfEmpty` itself and then calls `msa_send`. `msa_app_facts` is inlined
(`app_payload_from_log`). The `MsgApp` send is `wp_send_app`.

raft v3.7 (stage R4): `ents` is a `[]*pb.Entry` of read-only entries (`entsRO`, R3's
`raftLog.entries`; the full-window arm's zero slice by `entsPts_nil`). `wp_send_app` is gone: the
message `&pb.Message{To: new(to), Type: MsgApp.Enum(), Index: new(prevIndex), LogTerm:
new(prevTerm), Entries: ents, Commit: new(r.raftLog.committed)}` is built owned in `msa_send`
(`msgOwn_of_struct`, sharing `ents`' pointers) and handed to `send`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__maybeSendAppend
public import Spec.go_etcd_io.raft.v3.tracker.Progress__IsPaused
public import Spec.go_etcd_io.raft.v3.tracker.Progress__SentEntries
public import Spec.go_etcd_io.raft.v3.tracker.Progress__SentCommit
public import Spec.go_etcd_io.raft.v3.tracker.Inflights__Full
public import Spec.go_etcd_io.raft.v3.raftLog__term
public import Spec.go_etcd_io.raft.v3.raftLog__entries
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.raft__maybeSendSnapshot
public import Spec.go_etcd_io.raft.v3.payloadsSize
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasSendR

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

/- What the three arms of `pr.State != StateReplicate || !pr.Inflights.Full()` have in
common (Rocq's `msa_pkg`; here the hypotheses `msa_tail` expects).

The `if` has three outcomes -- not in `StateReplicate`; in it with room in the window;
in it with the window full -- and the first two run `r.raftLog.entries` while the third
leaves `ents` at the zero slice. Everything after the `if` is the same program, so the
three are brought to a common state and the rest of the proof is written once (the
`msa_tail` macro below).

The existentials are `ents`: the slice and its entries, read-only (`raftLog.entries`
hands them out for good), so the log in the struct is unchanged. The struct is whole
and at `s`: `pr` went back after the reads each arm makes, at the same value. `Hwin` is
`Progress.SentEntries`'s second premise in the only form all three arms can supply it:
entries are fetched only when the window has room, so a non-empty `ents` in
`StateReplicate` means the window was not full -- and nothing between the test and
`SentEntries` touches the window, which `NState.prvals` records. -/

set_option hygiene false in
/-- One arm's fetch of `ents := r.raftLog.entries(pr.Next, r.maxMsgSize)`, after giving
`pr` back. -/
local macro "msa_fetch" : tactic => `(tactic| (
  try rw [Hnx]
  ihave Hphys := Hpback $$ [Hpv Hinfl]
  · iapply ownProgress_intro $$ Hpv Hinfl
    ipureintro; exact Habs
  wp_apply raft.wp_load_maxMsgSizeC $$ Hphys as %mms Hphys
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  wp_apply wp_raftLog_entries _ s.logst _ _ Hlo $$ [Hlog]
    as %sl_e %es_e %err_e ⟨Hlog, Hentr⟩
  · iframe
  ihave Hphys := Hlogback $$ Hlog
  icases Hentr with (⟨%Herr_e, #Hents, %Hin, %Hpre⟩ | ⟨%Hsle, #Herr_e, #Hcut_e⟩)
  rotate_left
  · -- (D19i part 1) `ErrCompacted`: the application compacted past `pr.Next`; no entries, so
    -- `false` without `sendIfEmpty`, else a snapshot
    obtain ⟨rfl, -⟩ := Hsle
    ihave #Hinit := isInitialized_access $$ Hpkg
    iNamed Hinit
    icombine Herr_e ErrCompacted gives %Heq_e
    subst Heq_e
    obtain ⟨tyc, pc, Hec⟩ := HErrCompacted_new
    subst Hec
    try wp_auto
    cases sendIfEmpty
    · try wp_auto
      ihave Hphys := ownRaftPhysC_send_nil c r id s $$ Hphys
      iapply HΦ $$ %false %([] : List Msg) %s.prvals
      isplitl
      · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
        cases s; rfl
      ipureintro
      exact ⟨fun _ h => (nomatch h), rfl⟩
    · try wp_auto
      -- (D21 M3) not in the no-snapshot mode: there `Next ≥ 2` and the storage is never compacted
      -- past `1`
      cases Hns : s.gh.ns
      case true =>
        iexfalso
        have H2 := (Hpok0.2 Hns).1
        iunfold NsCap at Hnscap
        ihave #Hcap := Hnscap $$ %rfl
        icases storPast_cap _ _ _ $$ Hcut_e Hcap with %H
        ipureintro; omega
      ihave #Hcompact : (⌜uint.Z s.logst.prev.index' ≠ 0⌝ ∨
          storPast (GF := GF) s.logst.storage 1) $$ []
      · iright
        iapply storPast_mono _ (uint.Z p.next) 1 (by have := (word.unsigned_range s.logst.prev.index').1; omega)
        iexact Hcut_e
      wp_apply wp_raft_maybeSendSnapshot c r id s to pr Hto Hlk Hns $$ [Hphys]
        as %b %ms' %pvs' ⟨Hphys, %Hms', %Hmm'⟩
      · iframe
        try iexact Hcompact
      iapply HΦ
      iframe
      ipureintro
      exact ⟨Hms', Hmm'⟩
  subst Herr_e
  try wp_auto))

/-- The leader's progress bound after `SentEntries` (2026-10-16, stage R8a, D11): the entries sent
are a prefix of the log from `Next` on (`Hpre`), so `Next + |ents| ≤ lastIndex + 1`
(`plogFrom_prefix_bound`). -/
private theorem sentEntries_ok (s : NState) (p : Progress) (sl_e : GoSlice) (es_e : List EntryM)
    (psz : w64) (Hok : s.role = .leader → PrOkN s.gh.ns s.logst p) (Hnw : LogNoWrap s.logst)
    (Hlen : es_e.length = sint.nat sl_e.len ∧ 0 ≤ sint.Z sl_e.len)
    (Hlo : uint.Z s.logst.prev.index' + 1 ≤ uint.Z p.next)
    (Hpre : es_e <+: plogFrom (toPState s).base (toPState s).log p.next) :
    s.role = .leader → PrOkN s.gh.ns s.logst (progressSentEntries p sl_e.len psz) := by
  intro Hl
  have Hp := Hok Hl
  have Hlz := Hnw.logLast_Z
  have Hn2 := Hp.1.2.1
  have Hb := plogFrom_prefix_bound s.logst.prev (s.logst.sents ++ s.logst.uents) es_e p.next Hpre
    Hlo (by unfold plogLastIndexZ; rw [List.length_append]; push_cast; omega)
  unfold plogLastIndexZ at Hb
  rw [List.length_append] at Hb
  have He : (es_e.length : Int) = sint.Z sl_e.len := by
    rw [Hlen.1]; word
  push_cast at Hb
  refine Hp.sentEntries Hnw Hlen.2 ?_
  omega

set_option hygiene false in
/-- The message goes out: `r.send(MsgApp)`, `pr.SentEntries`, `pr.SentCommit`,
`return true`. -/
local macro "msa_send" : tactic => `(tactic| (
  -- the literal reads `r.raftLog.committed` through the log's record
  rw [show raftpb.MsgApp = #((W32 3 : raftpb.MessageType)) from rfl]
  wp_apply wp_MessageType_Enum (W32 3)
  iintro %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  imod cellRO_alloc $$ «$v0» with #cTo
  wp_auto
  imod cellRO_alloc $$ «$v2» with #cIx
  imod cellRO_alloc $$ «$v3» with #cLt
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lvc, Hl, %Hlvc, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hlogback $$ Hlog
  imod cellRO_alloc $$ «$v5» with #cCo
  ihave Hents2 : entsPts (GF := GF) sl_e DFrac.discard es_e $$ Hents
  iunfold entsPts at Hents2
  icases Hents2 with ⟨%els, #Hsl, #Hbig⟩
  ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnilb with #Hnilb
  ihave Hnilr : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod msgOwn_of_struct «$a0_ptr»
    { state' := zeroValDef, Type' := pty, To' := «$v0_ptr», From' := null, Term' := null,
      LogTerm' := «$v3_ptr», Index' := «$v2_ptr», Entries' := sl_e, Commit' := «$v5_ptr»,
      Vote' := null, Snapshot' := null, Reject' := null, RejectHint' := null,
      Context' := slice.nil, Responses' := slice.nil, unknownFields' := slice.nil, sizeCache' := 0 }
    els ⟨⟨W32 3, to, 0, 0, pterm, p.next - W64 1, lvc.committed', 0, false, 0⟩, es_e, none, [], []⟩
    ⊤ rfl $$ [«$a0» Hnilr] with Hm
  · iframe «$a0» cTy cTo cIx cLt cCo Hsl Hbig Hnilb Hnilr
    simp only [snapOpt]
    msg_nulls
    try itrivial
  wp_apply wp_raft_send c r id s «$a0_ptr»
      ⟨W32 3, to, 0, 0, pterm, p.next - W64 1, lvc.committed', 0, false, 0⟩ es_e none [] []
      [Msg.mk .app id to s.term false (p.next - W64 1) pterm lvc.committed' (W64 0) es_e]
      (Or.inl rfl) (Or.inr (Or.inl ⟨.app, Or.inl rfl, rfl, rfl, Hto, rfl⟩))
      (fun h => absurd h (by simp [MsgSnap])) $$ [Hphys Hm] as Hphys
  · iframe
  wp_apply wp_payloadsSize sl_e es_e DFrac.discard $$ [] as %psz ⟨-, -⟩
  · iframe # ∗
  -- `pr.SentEntries(...)`: `send` changed only the outbox, so `pr` is still at `p`
  icases ownRaftPhysC_pr_upd c r id _ to pr p $$ Hphys %Hlk %Hpvs with ⟨%Hok, %Hnw, Hpa, Hpback⟩
  have Hwin2 : p.state = .replicate → 0 < sint.Z sl_e.len → inflightsFull p.infl = false :=
    fun H1 H2 => Hwin H1 (fun Heq => by rw [Heq] at Hlen; obtain ⟨Hl1, -⟩ := Hlen; simp only [List.length_nil] at Hl1; word)
  wp_apply wp_Progress_SentEntries pr p _ _ Hnosnap Hwin2 $$ [Hpa] as Hpa
  · iframe
  ihave Hphys := Hpback $$ %_ Hpa %(progressSentEntries_learner _ _ _)
    %(sentEntries_ok s p sl_e es_e psz Hok Hnw Hlen Hlo Hpkgpre)
  -- `pr.SentCommit(r.raftLog.committed)`: the argument first, then `pr` once more, at
  -- the value `SentEntries` left
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lvc2, Hl, %Hlvc2, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hlogback $$ Hlog
  icases ownRaftPhysC_pr_upd c r id _ to pr (progressSentEntries p sl_e.len psz)
    $$ Hphys %Hlk %(GMap.lookup_insert_eq _ _ _) with ⟨%Hok2, -, Hpa, Hpback⟩
  wp_apply wp_Progress_SentCommit $$ [Hpa] as Hpa
  · iframe
  ihave Hphys := Hpback $$ %_ Hpa %rfl %(fun Hl => (Hok2 Hl).sentCommit _)
  iapply HΦ $$ %true
    %([Msg.mk MsgType.app id to s.term false (p.next - W64 1) pterm lvc.committed' (W64 0)
        es_e] : List Msg)
    %(<[to := progressSentCommit (progressSentEntries p sl_e.len psz) lvc2.committed']>
        (<[to := progressSentEntries p sl_e.len psz]> s.prvals))
  isplitl
  · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
    rfl
  ipureintro
  constructor
  · intro m Hm
    simp only [List.mem_singleton] at Hm
    subst Hm
    refine ⟨?_, fun _ => Hlvc.1, (fun h => nomatch h), (fun h => nomatch h)⟩
    left
    have Hn1 : p.next - W64 1 + W64 1 = p.next := by word
    refine ⟨rfl, rfl, rfl, Hto, Hterm_at, ?_, Hpkgin, by rw [Hn1]; exact Hpkgpre, ?_⟩
    · show uint.Z lvc.committed' ≤ uint.Z s.logst.committed
      rw [Hlvc.1]; exact Int.le_refl _
    · refine app_payload_from_log s.logst.prev (s.logst.sents ++ s.logst.uents) pterm
        (p.next - W64 1) es_e Hlwf (by simp only [List.length_append]; push_cast; omega)
        ⟨Herr1.1, by unfold plogLastIndexZ; simp only [List.length_append]; push_cast; omega⟩
        (by rw [Hn1]; exact Hpkgpre)
  · show prvalsMatch _ = _
    rw [GMap.insert_insert]
    refine prvalsMatch_insert_same _ _ p _ Hpvs ?_
    simp only [progressSentCommit, progressSentEntries]
    split <;> (try split) <;> rfl))

set_option hygiene false in
/-- Everything after the `||`'s three arms (Rocq's one `;`-chained script), from the
hypotheses `Hents : sl_e ↦*□ es_e`, `Hphys`, `Hwin`, `Hpkgin`, `Hpkgpre`. -/
local macro "msa_tail" : tactic => `(tactic| (
  ihave %Hlen := entsPts_len _ _ _ $$ Hents
  -- `if len(ents) == 0 && !sendIfEmpty { return false }`
  wp_if_destruct
  · cases sendIfEmpty
    · -- no entries, and the caller does not want an empty append
      wp_auto
      ihave Hphys := ownRaftPhysC_send_nil c r id s $$ Hphys
      iapply HΦ $$ %false %([] : List Msg) %s.prvals
      isplitl
      · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
        cases s; rfl
      ipureintro
      exact ⟨fun _ h => (nomatch h), rfl⟩
    · wp_auto
      msa_send
  · msa_send))

/-- `r.maybeSendAppend(to, sendIfEmpty)`.

**What is held across `r.send(...)`.** One voter's `Progress` -- `pr.SentEntries` needs
what this proof learned about it before the send (not `StateSnapshot`; a non-full window
in `StateReplicate`) -- and `ents`, which `raftLog.entries` hands out read-only and for
good (`payloadsSize` reads it after the send). Neither is lent: `pr` is borrowed out of
the struct for each stretch of the body that touches it (`ownRaftPhysC_pr` and its
variants) and given back before the next access to the struct, and what the proof knows
about it survives the calls in between because the state records its value
(`NState.prvals`, `s.prvals !! to = some p`) and `send` changes only the outbox. Each
`raftLog` call and each read of `r.raftLog.committed` takes the log out with
`ownRaftPhysC_log_same` and puts it back.

- `pr := r.trk.Progress[to]` hits because `to ∈ domSet s.progress` (a voter or, since
  2026-10-13, a learner).
- `pr.IsPaused()`: on `true`, return `false` having sent nothing; on `false`,
  `p.state ≠ .snapshot`, which is `SentEntries`'s first premise.
- `r.raftLog.term(pr.Next-1)`: on an error, `maybeSendSnapshot`; on `nil`, the iff gives
  `prev.index + 1 ≤ pr.Next`, `raftLog.entries`'s premise.
- the `||` and its three arms: see the comment above `wp_send_app`.
- `len(ents) == 0 && !sendIfEmpty` returns `false`; the second `err != nil` is dead.
- `r.send(MsgApp)` with `SendOk`'s second clause, then `SentEntries`, `SentCommit`,
  `return true`. -/
theorem raft.maybeSendAppend.wp_proof
    (wp_Progress_IsPaused : tracker.Progress.IsPaused.spec (GF := GF) (hG := hG))
    (wp_Progress_SentEntries : tracker.Progress.SentEntries.spec (GF := GF) (hG := hG))
    (wp_Progress_SentCommit : tracker.Progress.SentCommit.spec (GF := GF) (hG := hG))
    (wp_Inflights_Full : tracker.Inflights.Full.spec (GF := GF) (hG := hG))
    (wp_raftLog_term : raftLog.term.spec (GF := GF) (hG := hG))
    (wp_raftLog_entries : raftLog.entries.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_raft_maybeSendSnapshot : raft.maybeSendSnapshot.spec (GF := GF) (hG := hG))
    (wp_payloadsSize : payloadsSize.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.maybeSendAppend.spec (GF := GF) (hG := hG) := by
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  intro c r id s to sendIfEmpty Hto Hcfg Hlead
  wp_start as Hpre
  iNamed Hpre
  -- `r.trk.Progress` is read through the tracker field
  icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTrackerC_progress_map c _ _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  icases ownTrackerC_prvals_dom c _ _ $$ Htrk with ⟨%Hpdom, Htrk⟩
  dsimp only at Hdom Hpdom
  obtain ⟨pr, Hlk⟩ : ∃ pr, s.progress !! to = some pr := by
    rw [← GMap.elem_of_dom]; exact Hcfg
  obtain ⟨p, Hpvs⟩ : ∃ p, s.prvals !! to = some p := by
    rw [← GMap.elem_of_dom, Hpdom, GMap.elem_of_dom, Hlk]; exact ⟨_, rfl⟩
  wp_auto
  ihave Hphys := Hback $$ %tv Htrkf Htrk
  -- (D21 M3) the no-snapshot mode's facts and the peer's bound, for the two snapshot fallbacks
  icases ownRaftPhysC_ns c r id s $$ Hphys with ⟨%Hnsl, #Hnscap, Hphys⟩
  icases ownRaftPhysC_prvals_ok c r id s $$ Hphys with ⟨%Hok0, -, Hphys⟩
  have Hpok0 := Hok0.lookup Hlead Hpvs
  wp_apply wp_map_lookup1 $$ Hprs as -
  rw [Hlk]
  dsimp only [Option.getD_some]
  -- `pr.IsPaused()` and `prevIndex := pr.Next - 1`, on `pr` borrowed
  icases ownRaftPhysC_pr c r id s to pr p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  wp_apply wp_Progress_IsPaused $$ [$Hpa] as Hpa
  cases Hpaused : progressIsPaused p
  case true =>
    -- paused: nothing is sent, `false`
    wp_auto
    ihave Hphys := Hpback $$ Hpa
    ihave Hphys := ownRaftPhysC_send_nil c r id s $$ Hphys
    iapply HΦ $$ %false %([] : List Msg) %s.prvals
    isplitl
    · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
      cases s; rfl
    ipureintro

    exact ⟨fun _ h => (nomatch h), rfl⟩
  -- not paused, so not in `StateSnapshot` -- `SentEntries`' first premise
  have Hnosnap : p.state ≠ .snapshot := by
    intro Hc; simp [progressIsPaused, Hc] at Hpaused
  -- `pr.Next`, read off the value: the record's `next`
  iNamed Hpa
  obtain ⟨-, Hst, -, Hnx, -⟩ := (progressAbs_Some _ _ _).1 Habs
  wp_auto
  rw [Hnx]
  ihave Hphys := Hpback $$ [Hpv Hinfl]
  · iapply ownProgress_intro $$ Hpv Hinfl
    ipureintro; exact Habs
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  -- `r.raftLog.term(pr.Next - 1)`
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hnw, Hlog⟩
  icases ownRaftLog_wf _ _ $$ Hlog with ⟨%Hlwf, Hlog⟩
  wp_apply wp_raftLog_term _ s.logst _ $$ [$Hlog] as %pterm %err ⟨Hlog, %Herr, %Hterm_at, -, #Hcut⟩
  ihave Hphys := Hlogback $$ Hlog
  cases err with
  | ok eok =>
    -- the log no longer has `pr.Next - 1`: fall back to a snapshot. (Stage R8a, D11.) The
    -- failure is `ErrCompacted`, not `ErrUnavailable`: the leader's progress bound (`PrvalsOk`,
    -- `1 ≤ pr.Next ≤ lastIndex + 1`) puts `pr.Next - 1` at or below the last index, so `term`'s
    -- iff leaves `pr.Next - 1 < prev.index`, and the log is compacted (`prev.index ≥ 1`):
    -- `maybeSendSnapshot`'s premise, under which the storage's snapshot is non-empty.
    icases ownRaftPhysC_prvals_ok c r id s $$ Hphys with ⟨%Hok, -, Hphys⟩
    have Hpok := Hok.lookup Hlead Hpvs
    -- (D21 M3) not in the no-snapshot mode: there `Next ≥ 2`, the log's boundary is at most `1`
    -- and the storage is never compacted past `1`, so `term(Next - 1)` does not fail
    cases Hns : s.gh.ns
    case true =>
      iexfalso
      have H2 := (Hpok.2 Hns).1
      have Hp1 := (Hnsl Hns).2
      obtain ⟨h1, h2, -, -⟩ := Hpok.1
      have Hll := (show LogNoWrap s.logst from Hnw).logLast_Z
      icases Hcut with (%Hc | #Hc)
      · ipureintro
        rcases Hc with Hc | Hnot
        · cases Hc
        apply Hnot
        constructor <;> word
      · iunfold NsCap at Hnscap
        ihave #Hcap := Hnscap $$ %rfl
        icases storPast_cap _ _ _ $$ Hc Hcap with %H
        ipureintro; word
    -- (D19i part 1) or the application compacted past it (`storPast`)
    ihave #Hcompact : (⌜uint.Z s.logst.prev.index' ≠ 0⌝ ∨
        storPast (GF := GF) s.logst.storage 1) $$ []
    · icases Hcut with (%Hc | #Hc)
      · ileft
        ipureintro
        rcases Hc with Hc | Hnot
        · cases Hc
        obtain ⟨h1, h2, -, -⟩ := Hpok.1
        have Hll := (show LogNoWrap s.logst from Hnw).logLast_Z
        intro Hz
        apply Hnot
        constructor <;> word
      · iright
        iapply storPast_one
        iexact Hc
    wp_auto
    wp_apply wp_raft_maybeSendSnapshot c r id s to pr Hto Hlk Hns $$ [$Hphys $Hcompact]
      as %b %ms' %pvs' ⟨Hphys, %Hms', %Hmm'⟩
    iapply HΦ
    iframe
    ipureintro
    exact ⟨Hms', Hmm'⟩
  | nil =>
  -- `err = nil`: the iff gives `pr.Next` a lower bound against the log
  have Herr1 := Herr.1 rfl
  -- and the term it returned is the log's at `pr.Next - 1`: `AppOk`'s `logterm` clause
  have Hterm_at := Hterm_at rfl
  have Hlo : uint.Z s.logst.prev.index' + 1 ≤ uint.Z p.next := by word
  wp_auto
  -- `pr.State`, `pr.Inflights.Full()`, `pr.Next`: borrow `pr` again
  icases ownRaftPhysC_pr c r id s to pr p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  iNamed Hpa
  obtain ⟨-, Hst, -, Hnx, -⟩ := (progressAbs_Some _ _ _).1 Habs
  wp_auto
  -- the three arms of the `||`, each ending at the same state (Rocq's `msa_pkg`)
  wp_if_destruct
  · have Hrep : p.state = .replicate := prstateW64_inj _ _ (by rw [← Hst, Hif]; rfl)
    wp_apply wp_Inflights_Full $$ [$Hinfl] as Hinfl
    cases Hfull : inflightsFull p.infl
    · -- in `StateReplicate` with room: fetch `ents`
      wp_auto
      msa_fetch
      have Hwin : p.state = .replicate → es_e ≠ [] → inflightsFull p.infl = false :=
        fun _ _ => Hfull
      have Hpkgin : ∀ e ∈ es_e, e ∈ (toPState s).log := Hin
      have Hpkgpre : es_e <+: plogFrom (toPState s).base (toPState s).log p.next := Hpre
      clear Hin Hpre
      msa_tail
    · -- in `StateReplicate` with the window full: no entries are fetched
      wp_auto
      ihave Hphys := Hpback $$ [Hpv Hinfl]
      · iapply ownProgress_intro $$ Hpv Hinfl
        ipureintro; exact Habs
      -- `ents` is the zero slice, so `len(ents) == 0` was decided by `wp_auto`
      cases sendIfEmpty
      · -- no entries, and the caller does not want an empty append
        wp_auto
        ihave Hphys := ownRaftPhysC_send_nil c r id s $$ Hphys
        iapply HΦ $$ %false %([] : List Msg) %s.prvals
        isplitl
        · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
          cases s; rfl
        ipureintro
        exact ⟨fun _ h => (nomatch h), rfl⟩
      · wp_auto
        ihave #Hents : entsRO (GF := GF) (zero_val GoSlice : GoSlice) ([] : List EntryM) $$ []
        · iapply entsPts_nil
        generalize (zero_val GoSlice : GoSlice) = sl_e
        generalize Hes : ([] : List EntryM) = es_e
        have Hwin : p.state = .replicate → es_e ≠ [] → inflightsFull p.infl = false :=
          fun _ Hne => absurd Hes.symm Hne
        have Hpkgin : ∀ e ∈ es_e, e ∈ (toPState s).log := by
          subst Hes; intro e He; cases He
        have Hpkgpre : es_e <+: plogFrom (toPState s).base (toPState s).log p.next := by
          subst Hes; exact List.nil_prefix
        ihave %Hlen := entsPts_len _ _ _ $$ Hents
        msa_send
  · -- not in `StateReplicate`: the first disjunct is true, fetch `ents`
    have Hnrep : p.state ≠ .replicate := by
      intro Hc; apply Hif; rw [Hst, Hc]; rfl
    msa_fetch
    have Hwin : p.state = .replicate → es_e ≠ [] → inflightsFull p.infl = false :=
      fun Hc => absurd Hc Hnrep
    have Hpkgin : ∀ e ∈ es_e, e ∈ (toPState s).log := Hin
    have Hpkgpre : es_e <+: plogFrom (toPState s).base (toPState s).log p.next := Hpre
    clear Hin Hpre
    msa_tail

end proof

end EtcdGrove
end Perennial
