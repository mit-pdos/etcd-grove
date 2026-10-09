/- Port of election_proof/proof_raft__Step.v.

The per-message-type lemmas are **proof structure, not specification**. `Step` is one
Go function and therefore has exactly one spec, in `Spec/raft__Step.lean`; giving each
branch its own spec would put several Hoare triples for `r.Step` in several files,
which is the thing this layout exists to prevent. The branches live in modules of their
own (`Proof/raft__Step/`, Rocq `proof_raft__Step_helpers/`), so that they check in
parallel; only this module (and the modules of that directory) may import them.

**The replication branches (2026-10-02).** `MsgProp` is `raft__Step/MsgProp.lean`;
`MsgApp`, `MsgHeartbeat`, `MsgAppResp`, `MsgHeartbeatResp` and `MsgBeat` were written in
parallel against statements fixed in advance, so this file's dispatch for each of them is
a lemma (`dispatch_App`, ...), and `raft.Step.wp_proof` applies it. The ghost-side work
-- deriving each branch's protocol premises from `ownRaftGhost` and `isMessage`, and
taking `ownRaftGhost_step` with the branch's `recv` -- is in those lemmas.

Lean notes:
* The callee specs (Rocq `STEP_POSTULATES`) are bundled as `raft.Step.Postulates`
  (`raft__Step/Base.lean`, with `stepPost`, `StepProof.ghost_step_recv`,
  `StepProof.finish_branch`, `StepProof.finish_branch0` and the `w32_ne` macro). The
  fourteen branch lemmas `StepProof.wp_Step_<Msg>` are in `raft__Step/<Msg>.lean`, one
  module per Rocq file of `proof_raft__Step_helpers/` (names kept: `MsgVote_gt`,
  `repl_lemmas`, ...).
* The proof works at `HeapGS HasLC.hasLC GF` with `[AllG GF]`, as the spec does.
* Rocq's dispatch lemmas take the branch lemma as a hypothesis `HB`; here they take the
  postulates `P` and call the imported branch lemma.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgHup
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgVote
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgVoteResp
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgProp
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgApp
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgHeartbeat
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgAppResp
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgHeartbeatResp
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgBeat
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgSnap
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgPreVote
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgPreVoteResp
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgStorageAppendResp
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgStorageApplyResp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open StepProof

section dispatch
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-! ### The dispatch for the branches written elsewhere

Each proves `Step`'s spec for one message type from its branch lemma. The branch
lemmas' statements are their own (2026-10-02). `MsgApp` and `MsgHeartbeat` also take
`FollowerVotesOk` (`Protocol/Model.lean`), and one guard each (marked GUARD, also in the
branch statements): the protocol fact behind the conflict premise
(`app_no_conflict_below_commit`) and the commit premise (`heartbeat_commit_le_last`)
holds only for a message no older than the receiver's term -- a stale `MsgApp` from a
deposed leader can conflict below the commit index -- and a stale message never reaches
`maybeAppend`/`commitTo` (`Step`'s preamble drops it), so the branch lemma needs the
premise only under `uint.Z s.term ≤ uint.Z m.Term`. -/

private theorem dispatch_App (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hin : id ∈ cfg) (Hwf : NStateWf s) (Hty : m.Type' = MsgApp)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Entries' ↦*□ ents -∗
      ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) -∗
      isMessage γ (absMsg .app m ents) -∗
      ▷ stepPost γ cfg r id (toPState s) m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost #Hents Hcap #Hm HΦ
  -- `maybeAppend`'s batch facts: carried by the message
  ihave %Hbatch := app_recv_wf γ id (toPState s) (absMsg .app m ents) rfl Hto $$ Hghost Hm
  obtain ⟨Hpwf, Hnw, Hnorm⟩ := Hbatch
  -- the conflict fact: the protocol's, for a message no older than us
  have Hconf_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) -∗
      isMessage γ (absMsg .app m ents) -∗
      ⌜uint.Z s.term ≤ uint.Z m.Term' →
       uint.Z s.logst.committed ≤ uint.Z m.Index' →
       PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents)
         (entryID.mk m.LogTerm' m.Index') →
       plogFindConflict s.logst.prev (s.logst.sents ++ s.logst.uents) ents = W64 0 ∨
       uint.Z s.logst.committed <
         uint.Z (plogFindConflict s.logst.prev (s.logst.sents ++ s.logst.uents) ents)⌝ := by
    iintro Hg #Hm
    by_cases hc : uint.Z s.term ≤ uint.Z m.Term' ∧ uint.Z s.logst.committed ≤ uint.Z m.Index'
    · ihave %Hc := app_no_conflict_below_commit γ id (toPState s) (absMsg .app m ents) rfl Hto
        hc.1 hc.2 $$ Hg Hm
      ipureintro
      exact fun _ _ => Hc
    · ipureintro
      exact fun h1 h2 => absurd ⟨h1, h2⟩ hc
  ihave %Hconf := Hconf_lem $$ Hghost Hm
  -- a follower's tally is empty: the code's `r.lead = m.From` and the model's
  -- `padoptLeader` agree
  ihave %Hfv0 := ownRaftGhost_follower_votes γ id (toPState s) $$ Hghost
  have Hfv : s.role = .follower → s.votes = ∅ := followerVotesOk_phys s Hfv0
  wp_apply (wp_Step_MsgApp P cfg r id s m ents Hty Hto Hterm Hfnz Hfid Hin Hwf Hpwf Hnw Hnorm
      Hconf Hfv) $$ [$Hphys $Hents $Hcap] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep $$ Hm Hghost Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

/-- A leader of the message's term is its sender: a heartbeat or a snapshot of the
receiver's own term cannot reach a leader (`isLeader_unique`). -/
private theorem not_leader_of_msg (γ : RaftNames) (id : w64) (s : NState)
    (m : raftpb.Message) (Hfid : m.From' ≠ id) :
    ⊢ ownRaftGhost (GF := GF) γ id (toPState s) -∗ isLeader γ m.From' m.Term' -∗
      ⌜m.Term' = s.term → s.role ≠ .leader⌝ := by
  iintro Hg #Hl2
  by_cases Hnl : m.Term' = s.term ∧ s.role = .leader
  · obtain ⟨Heq, Hr⟩ := Hnl
    ihave #Hl1 := ownRaftGhost_isLeader γ id (toPState s)
      (by rw [toPState_role, Hr]; rfl) $$ Hg
    rw [show m.Term' = (toPState s).term by rw [Heq]; rfl]
    ihave %Hid := isLeader_unique γ id m.From' (toPState s).term $$ Hl1 Hl2
    exfalso; exact Hfid Hid.symm
  · ipureintro
    exact fun Heq Hr => Hnl ⟨Heq, Hr⟩

/-- A heartbeat is the sender's as a leader of its term (`isMessage`). -/
private theorem isMessage_heartbeat_isLeader (γ : RaftNames) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    isMessage (GF := GF) γ (absMsg .heartbeat m ents) ⊢ isLeader γ m.From' m.Term' := by
  unfold isMessage absMsg absMsgFrom
  iintro ⟨H, -⟩
  iexact H

/-- The same, for a snapshot. -/
private theorem isMessage_snap_isLeader (γ : RaftNames) (m : raftpb.Message)
    (sv : raftpb.Snapshot) (voters : List w64) :
    isMessage (GF := GF) γ (absSnap m sv voters) ⊢ isLeader γ m.From' m.Term' := by
  unfold isMessage absSnap absSnapFrom
  iintro ⟨H, -⟩
  iexact H

private theorem dispatch_Heartbeat (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hin : id ∈ cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgHeartbeat)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Entries' ↦*□ ents -∗
      isMessage γ (absMsg .heartbeat m ents) -∗
      ▷ stepPost γ cfg r id (toPState s) m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost #Hents #Hm HΦ
  have Hcl_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) -∗
      isMessage γ (absMsg .heartbeat m ents) -∗
      ⌜uint.Z s.term ≤ uint.Z m.Term' →
       uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents)⌝ := by
    iintro Hg #Hm
    by_cases Hle : uint.Z s.term ≤ uint.Z m.Term'
    · -- a leader receiving a heartbeat of its own term: the sender is a second leader
      -- of the term, which `isLeader_unique` excludes
      ihave #Hl2 := isMessage_heartbeat_isLeader γ m ents $$ Hm
      ihave %Hnl := not_leader_of_msg γ id s m Hfid $$ Hg Hl2
      ihave %Hc := heartbeat_commit_le_last γ id (toPState s) (absMsg .heartbeat m ents) rfl
        Hto Hle (fun Heq Hr => Hnl Heq ((proleRole_leader _).1 Hr)) $$ Hg Hm
      ipureintro
      exact fun _ => Hc
    · ipureintro
      exact fun h => absurd h Hle
  ihave %Hcl := Hcl_lem $$ Hghost Hm
  ihave %Hfv0 := ownRaftGhost_follower_votes γ id (toPState s) $$ Hghost
  have Hfv : s.role = .follower → s.votes = ∅ := followerVotesOk_phys s Hfv0
  wp_apply (wp_Step_MsgHeartbeat P cfg r id s m ents Hty Hto Hterm Hfnz Hfid Hin Hwf Hcl Hfv)
    $$ [$Hphys $Hents] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep $$ Hm Hghost Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

private theorem dispatch_AppResp (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hin : id ∈ cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgAppResp)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ (m.Reject' = true → m.From' ≠ id)) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Entries' ↦*□ ents -∗
      isMessage γ (absMsg .appResp m ents) -∗
      ▷ stepPost γ cfg r id (toPState s) m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hrej⟩ := Hm
  iintro #Hinit Hphys Hghost #Hents #Hm HΦ
  wp_apply (wp_Step_MsgAppResp P cfg r id s m ents Hty Hto Hterm Hfnz Hrej Hin Hwf)
    $$ [$Hphys $Hents] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep $$ Hm Hghost Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

private theorem dispatch_HeartbeatResp (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hin : id ∈ cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgHeartbeatResp)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Entries' ↦*□ ents -∗
      m.Context' ↦*□ ([] : List w8) -∗
      isMessage γ (absMsg .heartbeatResp m ents) -∗
      ▷ stepPost γ cfg r id (toPState s) m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost #Hents #Hctx0 #Hm HΦ
  wp_apply (wp_Step_MsgHeartbeatResp P cfg r id s m ents Hty Hto Hterm Hfnz Hfid Hin Hwf)
    $$ [$Hphys $Hents $Hctx0] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep $$ Hm Hghost Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

private theorem dispatch_Beat (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hin : id ∈ cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgBeat) (Hterm : m.Term' = W64 0) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      ▷ stepPost γ cfg r id (toPState s) m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  iintro #Hinit Hphys Hghost HΦ
  wp_apply (wp_Step_MsgBeat P cfg r id s m Hty Hterm Hin Hwf)
    $$ [$Hphys] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
  iapply finish_branch0 γ cfg r id s s' m err Φ Hcfg Hwf' Hst $$ Hghost Hphys [] HΦ
  ileft; ipureintro; exact Herr

/-- `MsgSnap` (2026-10-02): the snapshot and its voters come from `"Hsnap"`. At the
current term the receiver is not a leader -- the sender leads that term (`isMessage`'s
`isLeader`, `isLeader_unique`) -- and a follower's tally is empty (`FollowerVotesOk`);
the three `step_snap_*` rules need no other protocol fact: a restore replaces the log
wholesale and the fast-forward's `commitTo` is in range by `matchTerm`. -/
private theorem dispatch_Snap (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (sv : raftpb.Snapshot) (voters : List w64) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hin : id ∈ cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgSnap)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id)
    (Hscope : SnapScope cfg sv voters) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Snapshot' ↦□ sv -∗
      sv.Metadata'.ConfState'.Voters' ↦*□ voters -∗
      isMessage γ (absSnap m sv voters) -∗
      ▷ stepPost γ cfg r id (toPState s) m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost #Hsv #Hvs #Hm HΦ
  -- at the current term the receiver is not a leader: the sender leads it
  ihave #Hl2 := isMessage_snap_isLeader γ m sv voters $$ Hm
  ihave %Hnl := not_leader_of_msg γ id s m Hfid $$ Hghost Hl2
  ihave %Hfv0 := ownRaftGhost_follower_votes γ id (toPState s) $$ Hghost
  have Hfv : s.role = .follower → s.votes = ∅ := followerVotesOk_phys s Hfv0
  wp_apply (wp_Step_MsgSnap P cfg r id s m sv voters Hty Hto Hterm Hfnz Hfid Hin Hwf Hscope
      Hnl Hfv) $$ [$Hphys $Hsv $Hvs] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep $$ Hm Hghost Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

/-- The top-level dispatch: the one triple for `Step`, and **the one place in this
development where ghost state is updated**. Each branch lemma hands back a pure `Step`
witness together with the list of messages it consumed; here that becomes a single
`ownRaftGhost_step`.

`iapply wp_fupd` up front is what makes that possible: the ghost update has to happen
after the branch lemma returns, when the goal would otherwise be the bare postcondition
with no fancy update to absorb.

The type is decided one candidate at a time, in `stepMsgTypes`'s order; what is left is
none of them, which `StepMsg` excludes. -/
theorem raft.Step.wp_proof
    (wp_raft_hup : raft.hup.spec (GF := GF) (hG := hG))
    (wp_raft_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (wp_voteRespMsgType : voteRespMsgType.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_stepCandidate : stepCandidate.spec (GF := GF) (hG := hG))
    (wp_stepFollower : stepFollower.spec (GF := GF) (hG := hG))
    (wp_stepLeader : stepLeader.spec (GF := GF) (hG := hG))
    (wp_traceReceiveMessage : traceReceiveMessage.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (wp_raftLog_isUpToDate : raftLog.isUpToDate.spec (GF := GF) (hG := hG))
    -- the storage acknowledgements (2026-10-05)
    (wp_raftLog_stableTo : raftLog.stableTo.spec (GF := GF) (hG := hG))
    (wp_raft_appliedTo : raft.appliedTo.spec (GF := GF) (hG := hG))
    (wp_raft_reduceUncommittedSize : raft.reduceUncommittedSize.spec (GF := GF) (hG := hG))
    (wp_entsSize : entsSize.spec (GF := GF) (hG := hG))
    (wp_payloadsSize : payloadsSize.spec (GF := GF) (hG := hG)) :
    raft.Step.spec (GF := GF) (hG := hG) := by
  have P : raft.Step.Postulates (GF := GF) (hG := hG) :=
    ⟨wp_raft_hup, wp_raft_becomeFollower, wp_voteRespMsgType, wp_raft_send, wp_stepCandidate,
     wp_stepFollower, wp_stepLeader, wp_traceReceiveMessage, wp_raftLog_lastEntryID,
     wp_raftLog_isUpToDate, wp_raftLog_stableTo, wp_raft_appliedTo,
     wp_raft_reduceUncommittedSize, wp_entsSize, wp_payloadsSize⟩
  intro cfg γ r id s ps m ents Qs Hcfg Hsm Hin Hhup Hvote Hvoteresp Hprevote Hprevoteresp
    Happ Hhb Happresp Hhbresp Hsnapt Hbeat Hprop Hsar Hsapr Hrel
  obtain ⟨rfl, Hwf⟩ := Hrel
  iintro %Φ ⟨#Hinit, Hphys, Hghost, Hm, Hprops, #Hctx, #Hsnap⟩ HΦ
  icases Hm with ⟨Hents, Hcap, %Hpents, %Happly, #Hmsg0⟩
  iapply wp_fupd
  by_cases Hty : m.Type' = MsgProp
  · -- MsgProp: forward, append or drop (`proof_raft__Step_MsgProp.v`). The node's own
    -- `LeadOk` is what the follower's forwarding needs. Decided first (2026-10-06)
    -- because it is the one type whose postcondition carries more than `stepPost`: the
    -- proposals' updates, registered or handed back.
    simp only [ite_eq_left Hty]
    obtain ⟨Hterm, Hfrom⟩ := Hprop Hty
    obtain ⟨Hne, Hnorm, Hlen⟩ := Hpents Hty
    ihave %Hlok0 := ownRaftGhost_lead_ok γ id (toPState s) $$ Hghost
    -- a follower's leader is its physical one
    have Hlok : s.role = .follower → s.lead ≠ id := by
      intro Hf
      rw [← toPState_lead_nonpre s (by rw [Hf]; decide)]
      apply Hlok0
      rw [toPState_role, Hf]; decide
    ihave #Hm' := Hmsg0 $$ %MsgType.propose %(by rw [Hty]; exact mtypeOf_MsgProp) %(by decide)
    ihave %HlenQ := BigSepL2.bigSepL2_length $$ Hprops
    -- `Hents` is owned: the `by_cases` above reduced its `if m.Type' = MsgProp`
    wp_apply (wp_Step_MsgProp P cfg r id s m ents Hty Hterm Hfrom Hne Hnorm Hlen Hlok Hin Hwf)
      $$ [$Hphys $Hents $Hcap] as %err %s' ⟨Hphys, %Hwf', %Hfr, %Hst, Herr⟩
    rcases Hst with ⟨recv, Hrecv, Hstep⟩ | ⟨rfl, Hrl, Hnorm0, Hnw, Hstep⟩
    · -- forwarded or dropped: one uniform ghost step, the updates back
      imod ghost_step_recv γ cfg id _ _ _ recv Hcfg Hrecv Hstep $$ Hm' Hghost with Hghost
      imodintro
      iapply HΦ $$ %err %s' %(toPState s')
      iframe Hphys Hghost
      isplitr
      · ipureintro; exact ⟨rfl, Hwf'⟩
      isplitr
      · ipureintro; exact ⟨recv, Hstep⟩
      isplitr
      · ipureintro; exact fun _ => ⟨Hfr.1, fun _ => Hfr.2⟩
      isplitl [Herr]
      · icases Herr with (%Herr | #Hd)
        · ileft; ipureintro; exact Herr
        · iright; iframe Hd; ipureintro; exact Hty
      iright
      iexact Hprops
    · -- appended at the leader: `Step.propose`'s ghost update registers the proposals
      -- (`ownRaftGhost_step_propose_reg`); the broadcast after it is the uniform ghost
      -- step, consuming nothing
      imod ownRaftGhost_step_propose_reg γ id (toPState s) ents Qs Hrl Hnw (by omega)
        $$ Hghost Hprops with ⟨Hghost, Hout⟩
      have Hstep' : Step γ.reCfg id
          (psendMsgs (pappend (toPState s)
              (ents.mapIdx (stamp (toPState s).term (plastIndex (toPState s)))))
            [pselfAck id (pappend (toPState s)
              (ents.mapIdx (stamp (toPState s).term (plastIndex (toPState s)))))])
          [] (toPState s') := by
        rw [Hcfg]; exact Hstep
      imod ownRaftGhost_step_0 γ id _ _ Hstep' $$ Hghost with Hghost
      imodintro
      iapply HΦ $$ %interface.nil %s' %(toPState s')
      iframe Hphys Hghost
      isplitr
      · ipureintro; exact ⟨rfl, Hwf'⟩
      isplitr
      · ipureintro
        exact ⟨[] ++ [], .trans _ _ _ _ _ (.propose _ _ Hrl Hnorm0 Hnw) Hstep⟩
      isplitr
      · ipureintro; exact fun _ => ⟨Hfr.1, fun _ => Hfr.2⟩
      isplitr
      · ileft; ipureintro; rfl
      ileft
      iframe Hout
      ipureintro
      exact ⟨rfl, Hrl⟩
  -- every other type: `Hprops` is `True` in the pre- and postcondition, and the
  -- postcondition is `stepPost`
  simp only [ite_eq_right Hty]
  iclear Hprops
  -- and the entries are read-only: the `by_cases` reduced `"Hents"`'s
  -- `if m.Type' = MsgProp`
  icases Hents with #Hents
  -- the two storage acknowledgements (2026-10-05), before the conversion to `stepPost`
  -- below: their postcondition also says what is kept of the physical state
  -- (`LocalStepOk`, 2026-10-09)
  by_cases HtyA : m.Type' = MsgStorageAppendResp
  · -- MsgStorageAppendResp: `stableTo`, invisible to the protocol.
    obtain ⟨Hsn, Hle, Hstok⟩ := Hsar HtyA
    wp_apply (wp_Step_MsgStorageAppendResp P cfg r id s m HtyA Hsn Hle Hstok Hwf) $$ [$Hphys]
      as %err %s' ⟨Hphys, %Hwf', %Hfr, %Hst, %Herr⟩
    have Hst' : Step γ.reCfg id (toPState s) [] (toPState s') := by rw [Hcfg]; exact Hst
    imod ownRaftGhost_step_0 γ id _ _ Hst' $$ Hghost with Hghost
    imodintro
    iapply HΦ $$ %err %s' %(toPState s')
    iframe Hphys Hghost
    isplitr
    · ipureintro; exact ⟨rfl, Hwf'⟩
    isplitr
    · ipureintro; exact ⟨[], Hst⟩
    isplitr
    · ipureintro; exact fun _ => ⟨Hfr.1, fun _ => Hfr.2⟩
    isplitr
    · ileft; ipureintro; exact Herr
    itrivial
  by_cases HtyB : m.Type' = MsgStorageApplyResp
  · -- MsgStorageApplyResp: `appliedTo`, invisible to the protocol.
    -- `Hents` is already read-only: the `MsgProp` case split reduced its `if`
    wp_apply (wp_Step_MsgStorageApplyResp P cfg r id s m ents HtyB (Hsapr HtyB) (Happly HtyB)
        Hwf) $$ [$Hphys $Hents] as %err %s' ⟨Hphys, %Hwf', %Hfr, %Hst, %Herr⟩
    have Hst' : Step γ.reCfg id (toPState s) [] (toPState s') := by rw [Hcfg]; exact Hst
    imod ownRaftGhost_step_0 γ id _ _ Hst' $$ Hghost with Hghost
    imodintro
    iapply HΦ $$ %err %s' %(toPState s')
    iframe Hphys Hghost
    isplitr
    · ipureintro; exact ⟨rfl, Hwf'⟩
    isplitr
    · ipureintro; exact ⟨[], Hst⟩
    isplitr
    · ipureintro; exact fun _ => ⟨Hfr.1, fun H => Hfr.2 (H HtyB)⟩
    isplitr
    · ileft; ipureintro; exact Herr
    itrivial
  ihave HΦ : ▷ stepPost γ cfg r id (toPState s) m Φ $$ [HΦ]
  · inext
    unfold stepPost
    iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, Herr⟩
    iapply HΦ $$ %err %s' %ps'
    iframe Hphys Hghost Herr
    ipureintro
    -- `LocalStepOk` is about the three types handled above
    exact ⟨Hrel', Href, fun Hl => by rcases Hl with h | h | h <;> contradiction⟩
  by_cases Hns : m.Type' = MsgSnap
  · -- MsgSnap: `dispatch_Snap`, with the snapshot from `"Hsnap"`.
    icases Hsnap $$ %Hns with ⟨%sv, %voters, #Hsv, #Hvs, %Hscope, #Hm'⟩
    iapply dispatch_Snap P γ cfg r id s m sv voters Φ Hcfg Hin Hwf Hns (Hsnapt Hns) Hscope
      $$ Hinit Hphys Hghost Hsv Hvs Hm' HΦ
  -- from here on `m` is not a `MsgSnap`, so `Hm`'s `ty ≠ .snap` guard always holds
  ihave #Hmsg : (□ ∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗ isMessage γ (absMsg ty m ents)) $$ []
  · imodintro
    iintro %ty %Hty'
    iapply Hmsg0 $$ %ty %Hty' %(fun h => Hns (mtypeOf_Snap _ (h ▸ Hty')))
  iclear Hsnap Hmsg0
  by_cases Hty : m.Type' = MsgHup
  · -- MsgHup: a local message, handled by `hup`.
    obtain ⟨Hmterm, Hnowrap⟩ := Hhup Hty
    wp_apply (wp_Step_MsgHup P cfg r id s m Hty Hmterm Hnowrap Hwf) $$ [$Hphys]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
    iapply finish_branch0 γ cfg r id s s' m err Φ Hcfg Hwf' Hst $$ Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgVote
  · -- MsgVote: answer the vote request, stepping down first if needed.
    obtain ⟨Hto, Hterm, Hfnz⟩ := Hvote Hty
    ihave #Hm' := Hmsg $$ %MsgType.vote %(by rw [Hty]; exact mtypeOf_MsgVote)
    ihave #Hctx' : (∃ (ctx : List w8), m.Context' ↦*□ ctx ∗ ⌜ctx ≠ campaignTransfer⌝) $$ []
    · icases Hctx with ⟨%ctx, #Hc, %Hc2, -⟩
      iexists ctx
      iframe Hc
      ipureintro; exact Hc2
    wp_apply (wp_Step_MsgVote P cfg r id s m ents Hty Hto Hterm Hfnz Hwf) $$ [$Hphys $Hctx']
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
      $$ Hm' Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgVoteResp
  · -- MsgVoteResp: tally the vote, possibly winning or losing.
    obtain ⟨Hto, Hterm⟩ := Hvoteresp Hty
    ihave #Hm' := Hmsg $$ %MsgType.voteResp %(by rw [Hty]; exact mtypeOf_MsgVoteResp)
    wp_apply (wp_Step_MsgVoteResp P cfg r id s m ents Hty Hto Hterm Hin Hwf) $$ [$Hphys]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
      $$ Hm' Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgPreVote
  · -- MsgPreVote (2026-10-04): answered with a free `MsgPreVoteResp`; nothing
    -- received, nothing recorded.
    obtain ⟨Hto, Hterm, Hfnz, -, Hutd0⟩ := Hprevote Hty
    ihave #Hctx' : (∃ (ctx : List w8), m.Context' ↦*□ ctx ∗ ⌜ctx ≠ campaignTransfer⌝) $$ []
    · icases Hctx with ⟨%ctx, #Hc, %Hc2, -⟩
      iexists ctx
      iframe Hc
      ipureintro; exact Hc2
    wp_apply (wp_Step_MsgPreVote P cfg r id s m Hty Hto Hterm Hfnz Hwf Hutd0)
      $$ [$Hphys $Hctx'] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
    iapply finish_branch0 γ cfg r id s s' m err Φ Hcfg Hwf' Hst $$ Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgPreVoteResp
  · -- MsgPreVoteResp (2026-10-04): a pre-candidate's tally, or a step-down on a
    -- rejection of a higher term.
    obtain ⟨Hto, Hterm, -, Hnw⟩ := Hprevoteresp Hty
    ihave #Hm' := Hmsg $$ %MsgType.preVoteResp %(by rw [Hty]; exact mtypeOf_MsgPreVoteResp)
    wp_apply (wp_Step_MsgPreVoteResp P cfg r id s m ents Hty Hto Hterm Hnw Hin Hwf)
      $$ [$Hphys] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
      $$ Hm' Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgApp
  · -- MsgApp: `dispatch_App`.
    ihave #Hm' := Hmsg $$ %MsgType.app %(by rw [Hty]; exact mtypeOf_MsgApp)
    iapply dispatch_App P γ cfg r id s m ents Φ Hcfg Hin Hwf Hty (Happ Hty)
      $$ Hinit Hphys Hghost Hents Hcap Hm' HΦ
  by_cases Hty : m.Type' = MsgAppResp
  · -- MsgAppResp: `dispatch_AppResp`.
    ihave #Hm' := Hmsg $$ %MsgType.appResp %(by rw [Hty]; exact mtypeOf_MsgAppResp)
    iapply dispatch_AppResp P γ cfg r id s m ents Φ Hcfg Hin Hwf Hty (Happresp Hty)
      $$ Hinit Hphys Hghost Hents Hm' HΦ
  by_cases Hty : m.Type' = MsgHeartbeat
  · -- MsgHeartbeat: `dispatch_Heartbeat`.
    ihave #Hm' := Hmsg $$ %MsgType.heartbeat %(by rw [Hty]; exact mtypeOf_MsgHeartbeat)
    iapply dispatch_Heartbeat P γ cfg r id s m ents Φ Hcfg Hin Hwf Hty (Hhb Hty)
      $$ Hinit Hphys Hghost Hents Hm' HΦ
  by_cases Hty : m.Type' = MsgHeartbeatResp
  · -- MsgHeartbeatResp: `dispatch_HeartbeatResp`; the `Context` is empty.
    ihave #Hm' := Hmsg $$ %MsgType.heartbeatResp
      %(by rw [Hty]; exact mtypeOf_MsgHeartbeatResp)
    icases Hctx with ⟨%ctx, #Hctxp, -, %Hctx0⟩
    rw [Hctx0 Hty] at *
    iapply dispatch_HeartbeatResp P γ cfg r id s m ents Φ Hcfg Hin Hwf Hty (Hhbresp Hty)
      $$ Hinit Hphys Hghost Hents Hctxp Hm' HΦ
  by_cases Hty : m.Type' = MsgBeat
  · -- MsgBeat: `dispatch_Beat`.
    iapply dispatch_Beat P γ cfg r id s m Φ Hcfg Hin Hwf Hty (Hbeat Hty)
      $$ Hinit Hphys Hghost HΦ
  -- none of the fourteen (the two storage acknowledgements were handled above)
  exfalso
  simp only [StepMsg, stepMsgTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at Hsm
  rcases Hsm with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> contradiction

end dispatch

end EtcdGrove
end Perennial
