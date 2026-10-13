/-
Port of election_proof/proof_raft__maybeSendAppend.v.

Lean notes: Rocq's `msa_pkg` and its one `;`-chained script for the three arms are the
macros `msa_fetch`/`msa_tail`/`msa_send`, which work on hypotheses of fixed names
(`Hents : sl_e ↦*□ es_e`, `Hphys`, `Hwin`, `Hpkgin`, `Hpkgpre`). In the full-window
arm `wp_auto` already decides `len(ents) == 0` on the zero slice, so that arm splits on
`sendIfEmpty` itself and then calls `msa_send`. `msa_app_facts` is inlined
(`app_payload_from_log`). The `MsgApp` send is `wp_send_app`.
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

/-- `r.send(pb.Message{To: to, Type: pb.MsgApp, Index: .., LogTerm: .., Entries: ..,
Commit: ..})`: `SendOk`'s second clause. -/
private theorem wp_send_app (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (dst idx lt cm : w64) (sl : GoSlice)
    (es : List raftpb.Entry) (Hdst : dst ≠ id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s ∗
        sl ↦*□ es }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"send"))
        (Val #({ Type' := W32 3, To' := dst, From' := 0, Term' := 0,
                 LogTerm' := lt, Index' := idx, Entries' := sl,
                 Commit' := cm, Vote' := 0, Snapshot' := null, Reject' := false,
                 RejectHint' := 0, Context' := slice.nil, Responses' := slice.nil } :
                raftpb.Message)))
    {{ RET #(); ownRaftPhys cfg r id (sendMsgs s
          [Msg.mk .app id dst s.term false idx lt cm (W64 0) es]) }} := by
  iintro %Φ ⟨#Hpkg, Hphys, #Hes⟩ HΦ
  wp_apply wp_raft_send cfg r id s _ es [] [Msg.mk .app id dst s.term false idx lt cm (W64 0) es]
      (Or.inl rfl)
      (Or.inr (Or.inl ⟨.app, Or.inl rfl, rfl, rfl, Hdst, rfl⟩)) $$ [$Hphys] as Hphys
  · isplitr
    · iexact Hes
    isplitr
    · iapply ownSlice_nil
    · iapply send_no_snap
      exact (by decide : W32 3 ≠ W32 7)
  iapply HΦ
  iexact Hphys

set_option hygiene false in
/-- One arm's fetch of `ents := r.raftLog.entries(pr.Next, r.maxMsgSize)`, after giving
`pr` back. -/
local macro "msa_fetch" : tactic => `(tactic| (
  try rw [Hnx]
  ihave Hphys := Hpback $$ [Hpv Hinfl]
  · iapply ownProgress_intro $$ Hpv Hinfl
    ipureintro; exact Habs
  wp_apply raft.wp_load_maxMsgSize $$ Hphys as %mms Hphys
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  wp_apply wp_raftLog_entries _ s.logst _ _ Hlo $$ [Hlog]
    as %sl_e %es_e ⟨Hlog, #Hents, %Hin, %Hpre⟩
  · iframe
  ihave Hphys := Hlogback $$ Hlog
  try wp_auto))

set_option hygiene false in
/-- The message goes out: `r.send(MsgApp)`, `pr.SentEntries`, `pr.SentCommit`,
`return true`. -/
local macro "msa_send" : tactic => `(tactic| (
  -- the literal reads `r.raftLog.committed` through the log's record
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lvc, Hl, %Hlvc, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hlogback $$ Hlog
  wp_apply wp_send_app wp_raft_send cfg r id s _ _ _ _ _ es_e Hto $$ [Hphys]
    as Hphys
  · iframe # ∗
  wp_apply wp_payloadsSize $$ [] as %psz ⟨-, -⟩
  · iframe # ∗
  -- `pr.SentEntries(...)`: `send` changed only the outbox, so `pr` is still at `p`
  icases ownRaftPhys_pr_upd cfg r id _ to pr p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  have Hwin2 : p.state = .replicate → 0 < sint.Z sl_e.len → inflightsFull p.infl = false :=
    fun H1 H2 => Hwin H1 (fun Heq => by rw [Heq] at Hlen; simp at Hlen; omega)
  wp_apply wp_Progress_SentEntries pr p _ _ Hnosnap Hwin2 $$ [Hpa] as Hpa
  · iframe
  ihave Hphys := Hpback $$ %_ Hpa
  -- `pr.SentCommit(r.raftLog.committed)`: the argument first, then `pr` once more, at
  -- the value `SentEntries` left
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lvc2, Hl, %Hlvc2, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hlogback $$ Hlog
  icases ownRaftPhys_pr_upd cfg r id _ to pr (progressSentEntries p sl_e.len psz)
    $$ Hphys %Hlk %(GMap.lookup_insert_eq _ _ _) with ⟨Hpa, Hpback⟩
  wp_apply wp_Progress_SentCommit $$ [Hpa] as Hpa
  · iframe
  ihave Hphys := Hpback $$ %_ Hpa
  iapply HΦ $$ %true
    %([Msg.mk MsgType.app id to s.term false (p.next - W64 1) pterm lvc.committed' (W64 0)
        es_e] : List Msg)
    %(<[to := progressSentCommit (progressSentEntries p sl_e.len psz) lvc2.committed']>
        (<[to := progressSentEntries p sl_e.len psz]> s.prvals))
  isplitl
  · iapply ownRaftPhys_eq cfg r id _ _ ?_ $$ Hphys
    rfl
  ipureintro
  constructor
  · intro m Hm
    simp only [List.mem_singleton] at Hm
    subst Hm
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
  ihave %Hlen := slice_len_Z _ _ _ $$ Hents
  -- `if len(ents) == 0 && !sendIfEmpty { return false }`
  wp_if_destruct
  · cases sendIfEmpty
    · -- no entries, and the caller does not want an empty append
      wp_auto
      ihave Hphys := ownRaftPhys_send_nil cfg r id s $$ Hphys
      iapply HΦ $$ %false %([] : List Msg) %s.prvals
      isplitl
      · iapply ownRaftPhys_eq cfg r id _ _ ?_ $$ Hphys
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
the struct for each stretch of the body that touches it (`ownRaftPhys_pr` and its
variants) and given back before the next access to the struct, and what the proof knows
about it survives the calls in between because the state records its value
(`NState.prvals`, `s.prvals !! to = some p`) and `send` changes only the outbox. Each
`raftLog` call and each read of `r.raftLog.committed` takes the log out with
`ownRaftPhys_log_same` and puts it back.

- `pr := r.trk.Progress[to]` hits because `to ∈ cfg`.
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
    (wp_payloadsSize : payloadsSize.spec (GF := GF) (hG := hG)) :
    raft.maybeSendAppend.spec (GF := GF) (hG := hG) := by
  intro cfg r id s to sendIfEmpty Hto Hcfg
  wp_start as Hpre
  iNamed Hpre
  -- `r.trk.Progress` is read through the tracker field
  icases ownRaftPhys_tracker_same cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_progress_map cfg _ _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  icases ownTracker_prvals_dom cfg _ _ $$ Htrk with ⟨%Hpdom, Htrk⟩
  dsimp only at Hdom Hpdom
  obtain ⟨pr, Hlk⟩ : ∃ pr, s.progress !! to = some pr := by
    rw [← GMap.elem_of_dom, Hdom]; exact Hcfg
  obtain ⟨p, Hpvs⟩ : ∃ p, s.prvals !! to = some p := by
    rw [← GMap.elem_of_dom, Hpdom, GMap.elem_of_dom, Hlk]; exact ⟨_, rfl⟩
  wp_auto
  ihave Hphys := Hback $$ %tv Htrkf Htrk
  wp_apply wp_map_lookup1 $$ Hprs as -
  rw [Hlk]
  dsimp only [Option.getD_some]
  -- `pr.IsPaused()` and `prevIndex := pr.Next - 1`, on `pr` borrowed
  icases ownRaftPhys_pr cfg r id s to pr p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  wp_apply wp_Progress_IsPaused $$ [$Hpa] as Hpa
  cases Hpaused : progressIsPaused p
  case true =>
    -- paused: nothing is sent, `false`
    wp_auto
    ihave Hphys := Hpback $$ Hpa
    ihave Hphys := ownRaftPhys_send_nil cfg r id s $$ Hphys
    iapply HΦ $$ %false %([] : List Msg) %s.prvals
    isplitl
    · iapply ownRaftPhys_eq cfg r id _ _ ?_ $$ Hphys
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
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  -- `r.raftLog.term(pr.Next - 1)`
  icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hnw, Hlog⟩
  icases ownRaftLog_wf _ _ $$ Hlog with ⟨%Hlwf, Hlog⟩
  wp_apply wp_raftLog_term _ s.logst _ $$ [$Hlog] as %pterm %err ⟨Hlog, %Herr, %Hterm_at, -⟩
  ihave Hphys := Hlogback $$ Hlog
  cases err with
  | ok eok =>
    -- the log no longer has `pr.Next - 1`: fall back to a snapshot
    wp_auto
    wp_apply wp_raft_maybeSendSnapshot cfg r id s to pr Hto Hlk $$ [$Hphys]
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
  icases ownRaftPhys_pr cfg r id s to pr p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
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
        ihave Hphys := ownRaftPhys_send_nil cfg r id s $$ Hphys
        iapply HΦ $$ %false %([] : List Msg) %s.prvals
        isplitl
        · iapply ownRaftPhys_eq cfg r id _ _ ?_ $$ Hphys
          cases s; rfl
        ipureintro
        exact ⟨fun _ h => (nomatch h), rfl⟩
      · wp_auto
        ihave #Hents : (zero_val GoSlice : GoSlice) ↦*□ ([] : List raftpb.Entry) $$ []
        · iapply ownSlice_nil
        generalize (zero_val GoSlice : GoSlice) = sl_e
        generalize Hes : ([] : List raftpb.Entry) = es_e
        have Hwin : p.state = .replicate → es_e ≠ [] → inflightsFull p.infl = false :=
          fun _ Hne => absurd Hes.symm Hne
        have Hpkgin : ∀ e ∈ es_e, e ∈ (toPState s).log := by
          subst Hes; intro e He; cases He
        have Hpkgpre : es_e <+: plogFrom (toPState s).base (toPState s).log p.next := by
          subst Hes; exact List.nil_prefix
        ihave %Hlen := slice_len_Z _ _ _ $$ Hents
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
