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
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgReadIndex
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgReadIndexResp
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgRest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open StepProof

set_option hygiene false in
/-- `RespStep` for a type that is none of the three responses (2026-10-10): by `Hty`. -/
local macro "resp_other" : tactic =>
  `(tactic| exact RespStep.of_type (by rw [Hty]; w32_ne) (by rw [Hty]; w32_ne)
    (by rw [Hty]; w32_ne))

section dispatch
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

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
    (Hcfg : γ.reCfg = cfg) (Hwf : NStateWf s) (Hty : m.Type' = MsgApp)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Entries' ↦*□ ents -∗
      ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) -∗
      isMessage γ (absMsg .app m ents) -∗
      ▷ stepPost γ cfg r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost #Hents Hcap #Hm HΦ
  -- `maybeAppend`'s batch facts: carried by the message
  ihave %Hbatch := app_recv_wf γ id (toPState s) (absMsg .app m ents) rfl Hto $$ Hghost Hm
  obtain ⟨Hpwf, Hnw⟩ := Hbatch
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
  wp_apply (wp_Step_MsgApp P cfg r id s m ents Hty Hto Hterm Hfnz Hfid Hwf Hpwf Hnw
      Hconf Hfv) $$ [$Hphys $Hents $Hcap] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
    (fun _ => Hfr) (fun _ => Htm) (by resp_other) $$ Hm Hghost Hphys
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
    (ents : List raftpb.Entry) (ctx : List w8 := []) :
    isMessage (GF := GF) γ (absMsg .heartbeat m ents ctx) ⊢ isLeader γ m.From' m.Term' := by
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
    (m : raftpb.Message) (ents : List raftpb.Entry) (ctx : List w8) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgHeartbeat)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Entries' ↦*□ ents -∗
      m.Context' ↦*□ ctx -∗
      isMessage γ (absMsg .heartbeat m ents ctx) -∗
      ▷ stepPost γ cfg r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost #Hents #Hctxp #Hmc HΦ
  have Hcl_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) -∗
      isMessage γ (absMsg .heartbeat m ents ctx) -∗
      ⌜uint.Z s.term ≤ uint.Z m.Term' →
       uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents)⌝ := by
    iintro Hg #Hm
    by_cases Hle : uint.Z s.term ≤ uint.Z m.Term'
    · -- a leader receiving a heartbeat of its own term: the sender is a second leader
      -- of the term, which `isLeader_unique` excludes
      ihave #Hl2 := isMessage_heartbeat_isLeader γ m ents ctx $$ Hm
      ihave %Hnl := not_leader_of_msg γ id s m Hfid $$ Hg Hl2
      ihave %Hc := heartbeat_commit_le_last γ id (toPState s) (absMsg .heartbeat m ents ctx) rfl
        Hto Hle (fun Heq Hr => Hnl Heq ((proleRole_leader _).1 Hr)) $$ Hg Hm
      ipureintro
      exact fun _ => Hc
    · ipureintro
      exact fun h => absurd h Hle
  ihave %Hcl := Hcl_lem $$ Hghost Hmc
  ihave %Hfv0 := ownRaftGhost_follower_votes γ id (toPState s) $$ Hghost
  have Hfv : s.role = .follower → s.votes = ∅ := followerVotesOk_phys s Hfv0
  wp_apply (wp_Step_MsgHeartbeat P cfg r id s m ents ctx Hty Hto Hterm Hfnz Hfid Hwf Hcl Hfv)
    $$ [$Hphys $Hents $Hctxp] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
    (fun _ => Hfr) (fun _ => Htm) (by resp_other) $$ Hmc Hghost Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

private theorem dispatch_AppResp (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgAppResp)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ (m.Reject' = true → m.From' ≠ id)) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Entries' ↦*□ ents -∗
      isMessage γ (absMsg .appResp m ents) -∗
      ▷ stepPost γ cfg r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hrej⟩ := Hm
  iintro #Hinit Hphys Hghost #Hents #Hm HΦ
  -- (2026-10-13) the read-only facts a commit's release needs, from the ghost state
  have Hlrd_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) -∗
      ⌜s.role = .leader → RdOk cfg s.rd ∧ s.term ≠ W64 0⌝ := by
    iintro Hg
    by_cases hl : s.role = .leader
    · ihave %H1 := ghost_rdOk γ id s hl $$ Hg
      ipureintro; intro _; rw [← Hcfg]; exact H1
    · ipureintro; exact fun h => absurd h hl
  ihave %Hlrd := Hlrd_lem $$ Hghost
  wp_apply (wp_Step_MsgAppResp P cfg r id s m ents Hlrd Hty Hto Hterm Hfnz Hrej Hwf)
    $$ [$Hphys $Hents] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hresp, %Hfr, %Htm⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
    (fun _ => Hfr) (fun _ => Htm) Hresp $$ Hm Hghost Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

private theorem dispatch_HeartbeatResp (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (ctx : List w8) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgHeartbeatResp)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Entries' ↦*□ ents -∗
      m.Context' ↦*□ ctx -∗
      isMessage γ (absMsg .heartbeatResp m ents ctx) -∗
      ▷ stepPost γ cfg r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost #Hents #Hctx0 #Hm HΦ
  -- (2026-10-13) the read-only facts `stepLeader`'s read path needs, from the ghost state
  have Hlrd_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) -∗
      isMessage γ (absMsg .heartbeatResp m ents ctx) -∗
      ⌜s.role = .leader → m.Term' = s.term →
        (RdOk cfg s.rd ∧ s.term ≠ W64 0) ∧ (ctx = [] ∨ 8 ≤ ctx.length) ∧
        (ctx ≠ [] → uint.Z (leToU64 (ctx.take 8))
                      ≤ uint.Z s.rd.ro.confirmed + (s.rd.ro.pending.length : Int))⌝ := by
    iintro Hg #Hm
    by_cases hl : s.role = .leader
    · by_cases ht : m.Term' = s.term
      · ihave %H1 := ghost_rdOk γ id s hl $$ Hg
        ihave %H2 := ghost_hbResp_ctx γ id s m ents ctx hl Hto ht $$ Hg Hm
        ipureintro
        intro _ _
        rw [← Hcfg]
        exact ⟨H1, H2⟩
      · ipureintro; exact fun _ h => absurd h ht
    · ipureintro; exact fun h => absurd h hl
  ihave %Hlrd := Hlrd_lem $$ Hghost Hm
  wp_apply (wp_Step_MsgHeartbeatResp P cfg r id s m ents ctx Hlrd Hty Hto Hterm Hfnz Hfid Hwf)
    $$ [$Hphys $Hents $Hctx0] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  obtain ⟨c, recv, Hc, Hrecv, Hstep⟩ := Hst
  ihave #Hmc : isMessage γ (absMsg .heartbeatResp m ents c) $$ []
  · rcases Hc with rfl | rfl
    · unfold isMessage; simp only [absMsg, absMsgFrom]; ileft; ipureintro; trivial
    · iexact Hm
  iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
    (fun _ => Hfr) (fun _ => Htm) (by resp_other) $$ Hmc Hghost Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

private theorem dispatch_Beat (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgBeat) (Hterm : m.Term' = W64 0) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      ▷ stepPost γ cfg r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  iintro #Hinit Hphys Hghost HΦ
  wp_apply (wp_Step_MsgBeat P cfg r id s m Hty Hterm Hwf)
    $$ [$Hphys] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  iapply finish_branch0 γ cfg r id s s' m err Φ Hcfg Hwf' Hst (fun _ => Hfr) (fun _ => Htm)
      (by resp_other) $$ Hghost Hphys [] HΦ
  ileft; ipureintro; exact Herr

/-- `MsgSnap` (2026-10-02): the snapshot and its voters come from `"Hsnap"`. At the
current term the receiver is not a leader -- the sender leads that term (`isMessage`'s
`isLeader`, `isLeader_unique`) -- and a follower's tally is empty (`FollowerVotesOk`);
the three `step_snap_*` rules need no other protocol fact: a restore replaces the log
wholesale and the fast-forward's `commitTo` is in range by `matchTerm`. -/
private theorem dispatch_Snap (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (sv : raftpb.Snapshot) (voters learners : List w64)
    (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hin : id ∈ cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgSnap)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id)
    (Hscope : SnapScope cfg sv voters learners) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Snapshot' ↦□ sv -∗
      sv.Metadata'.ConfState'.Voters' ↦*□ voters -∗
      ownIdList sv.Metadata'.ConfState'.Learners' DFrac.discard learners -∗
      isMessage γ (absSnap m sv voters) -∗
      ▷ stepPost γ cfg r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost #Hsv #Hvs #Hls #Hm HΦ
  -- at the current term the receiver is not a leader: the sender leads it
  ihave #Hl2 := isMessage_snap_isLeader γ m sv voters $$ Hm
  ihave %Hnl := not_leader_of_msg γ id s m Hfid $$ Hghost Hl2
  ihave %Hfv0 := ownRaftGhost_follower_votes γ id (toPState s) $$ Hghost
  have Hfv : s.role = .follower → s.votes = ∅ := followerVotesOk_phys s Hfv0
  wp_apply (wp_Step_MsgSnap P cfg r id s m sv voters learners Hty Hto Hterm Hfnz Hfid Hin Hwf
      Hscope Hnl Hfv) $$ [$Hphys $Hsv $Hvs $Hls] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  -- the frame and the term step are not claimed for a snapshot
  iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
    (fun h => absurd Hty h) (fun h => absurd Hty h) (by resp_other)
    (by simp [absSnap, absSnapFrom]) $$ Hm Hghost Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

/-- `MsgReadIndex` (2026-10-13): a local or forwarded request, `Term = 0`. -/
private theorem dispatch_ReadIndex (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (ctx : List w8) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgReadIndex) (Hm : m.Term' = W64 0 ∧ 1 < GMap.size cfg) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Entries' ↦*□ ents -∗
      m.Context' ↦*□ ctx -∗
      isMessage γ (absMsg .readIndex m ents ctx) -∗
      rdCred γ 1 -∗
      ▷ stepPost γ cfg r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hterm, Hsz⟩ := Hm
  iintro #Hinit Hphys Hghost #Hents #Hctxp #Hm Hcred HΦ
  -- a request has an entry (its context)
  have Hne_lem : ⊢ isMessage (GF := GF) γ (absMsg .readIndex m ents ctx) -∗ ⌜ents ≠ []⌝ := by
    unfold isMessage
    simp only [absMsg, absMsgFrom]
    iintro ⟨%e, %c, %Lc, %He, -⟩
    ipureintro
    try simp only [Msg.mkV] at He
    rw [He]; exact List.cons_ne_nil _ _
  ihave %Hne := Hne_lem $$ Hm
  -- a follower's leader is another node
  ihave %Hlok0 := ownRaftGhost_lead_ok γ id (toPState s) $$ Hghost
  have Hlok : s.role = .follower → s.lead ≠ id := by
    intro Hf
    rw [← toPState_lead_nonpre s (by rw [Hf]; decide)]
    apply Hlok0
    rw [toPState_role, Hf]; decide
  -- a leader's read-only state
  have Hlrd_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) -∗
      ⌜s.role = .leader → RdOk cfg s.rd ∧ s.term ≠ W64 0⌝ := by
    iintro Hg
    by_cases hl : s.role = .leader
    · ihave %H1 := ghost_rdOk γ id s hl $$ Hg
      ipureintro; intro _; rw [← Hcfg]; exact H1
    · ipureintro; exact fun h => absurd h hl
  ihave %Hlrd := Hlrd_lem $$ Hghost
  wp_apply (wp_Step_MsgReadIndex P cfg r id s m ents ctx Hty Hterm Hsz Hne Hlok Hlrd Hwf)
    $$ [$Hphys $Hents $Hctxp] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  obtain ⟨recv, Hrecv, Hlen, Hstep⟩ := Hst
  -- the request's credit goes with it, if it was received
  have Hcnt : rdCount recv ≤ 1 := by
    have : rdCount recv ≤ recv.length := List.countP_le_length
    omega
  ihave Hc := (rdCred_split γ (rdCount recv) (1 - rdCount recv)).1 $$ [Hcred]
  · rw [show rdCount recv + (1 - rdCount recv) = 1 by omega]; iexact Hcred
  icases Hc with ⟨Hc, -⟩
  ihave Hall : ([∗list] x ∈ recv, isMessage (GF := GF) γ x) $$ []
  · iapply (BigSepL.bigSepL_intro
      (P := iprop(□ isMessage (GF := GF) γ (absMsg .readIndex m ents ctx)))
      (fun k x hx => by
        rw [Hrecv x (List.mem_of_getElem? hx)]
        exact intuitionistically_elim))
    iexact Hm
  have Hst' : Step γ.reCfg id (toPState s) recv (toPState s') := by rw [Hcfg]; exact Hstep
  -- the code's `Step` witness, at the ghost state's configuration (`StepC`, 2026-10-14)
  imod ownRaftGhost_stepC γ _ (CfgStatic.simple γ ∅) id _ recv _
    ((CfgStatic.stepC_iff γ ∅ id _ _ _).1 Hst') $$ Hall Hc Hghost with Hghost
  imodintro
  unfold stepPost
  ihave Herr' : (⌜err = interface.nil⌝ ∨
      (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err) : IProp GF) $$ []
  · ileft; ipureintro; exact Herr
  iapply HΦ $$ %err %s' %(toPState s')
  iframe Hphys Hghost Herr'
  ipureintro
  exact ⟨⟨rfl, Hwf'⟩, ⟨recv, Hstep⟩, fun _ => Hfr, fun _ => Htm, by resp_other⟩

/-- `MsgReadIndexResp` (2026-10-13): a leader's answer to a forwarded request. -/
private theorem dispatch_ReadIndexResp (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (ctx : List w8) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgReadIndexResp)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhys cfg r id s -∗
      ownRaftGhost γ id (toPState s) -∗
      m.Entries' ↦*□ ents -∗
      m.Context' ↦*□ ctx -∗
      isMessage γ (absMsg .readIndexResp m ents ctx) -∗
      ▷ stepPost γ cfg r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, -, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost #Hents #Hctxp #Hm HΦ
  -- a response carries its request's entry
  have He_lem : ⊢ isMessage (GF := GF) γ (absMsg .readIndexResp m ents ctx) -∗
      ⌜∃ e, ents = [e]⌝ := by
    unfold isMessage
    simp only [absMsg, absMsgFrom]
    iintro ⟨%e, %c, %He, -⟩
    ipureintro
    try simp only [Msg.mkV] at He
    exact ⟨e, He⟩
  ihave %He := He_lem $$ Hm
  obtain ⟨e, rfl⟩ := He
  wp_apply (wp_Step_MsgReadIndexResp P cfg r id s m e ctx Hty Hto Hterm Hfid Hwf)
    $$ [$Hphys $Hents] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
    (fun _ => Hfr) (fun _ => Htm) (by resp_other) $$ Hm Hghost Hphys [] HΦ
  ileft; ipureintro; exact Herr

/-- The top-level dispatch: the one triple for `Step`, and **the one place in this
development where ghost state is updated**. Each branch lemma hands back a pure `Step`
witness together with the list of messages it consumed; here that becomes a single
`ownRaftGhost_step` (since 2026-10-14, reconfiguration stage B2, `ownRaftGhost_stepC`: the
witness is read as one of `StepC` at `CfgM.simple γ.reCfg ∅`, `CfgStatic.stepC_iff`).

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
    ⟨(raft.hup.spec_simple wp_raft_hup), (raft.becomeFollower.spec_simple wp_raft_becomeFollower), wp_voteRespMsgType, (raft.send.spec_simple wp_raft_send), (stepCandidate.spec_simple wp_stepCandidate),
     (stepFollower.spec_simple wp_stepFollower), (stepLeader.spec_simple wp_stepLeader), wp_traceReceiveMessage, wp_raftLog_lastEntryID,
     wp_raftLog_isUpToDate, wp_raftLog_stableTo, wp_raft_appliedTo,
     wp_raft_reduceUncommittedSize, wp_entsSize, wp_payloadsSize⟩
  intro cfg γ r id s ps m ents ctx Hcfg Hsm Hin Hhup Hvote Hvoteresp Hprevote Hprevoteresp
    Happ Hhb Happresp Hhbresp Hsnapt Hbeat Hprop Hsar Hsapr Hri Hrir Hrest Hrel
  obtain ⟨rfl, Hwf⟩ := Hrel
  iintro %Φ ⟨#Hinit, Hphys, Hghost, Hm, #Hctxp, Hcred, #Hsnap⟩ HΦ
  icases Hm with ⟨Hents, Hcap, %Hpents, %Happly, #Hmsg0⟩
  iapply wp_fupd
  by_cases Hty : m.Type' = MsgProp
  · -- MsgProp: forward, append or drop (`proof_raft__Step_MsgProp.v`). The node's own
    -- `LeadOk` is what the follower's forwarding needs. Decided first (2026-10-06)
    -- because it is the one type whose postcondition carries more than `stepPost`: the
    -- proposals' updates, registered or handed back.
    simp only [ite_eq_left Hty]
    obtain ⟨Hterm, Hfrom⟩ := Hprop Hty
    obtain ⟨Hne, Hlen⟩ := Hpents Hty
    icases Hents with ⟨Hents, %cs, #Hcc⟩
    ihave %Hlok0 := ownRaftGhost_lead_ok γ id (toPState s) $$ Hghost
    -- a follower's leader is its physical one
    have Hlok : s.role = .follower → s.lead ≠ id := by
      intro Hf
      rw [← toPState_lead_nonpre s (by rw [Hf]; decide)]
      apply Hlok0
      rw [toPState_role, Hf]; decide
    ihave #Hm' := Hmsg0 $$ %MsgType.propose %(by rw [Hty]; exact mtypeOf_MsgProp) %(by decide)
    -- a leader's term is nonzero (2026-10-10): `appendEntry` stamps its
    -- self-acknowledgement with it
    have Hlnz_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) -∗
        ⌜s.role = .leader → s.term ≠ W64 0⌝ := by
      iintro Hg
      by_cases hl : s.role = .leader
      · ihave %H := ownRaftGhost_term_nz γ id (toPState s)
          (by rw [toPState_role, hl]; decide) $$ Hg
        ipureintro; exact fun _ => H
      · ipureintro; exact fun h => absurd h hl
    ihave %Hlnz := Hlnz_lem $$ Hghost
    -- `Hents` is owned: the `by_cases` above reduced its `if m.Type' = MsgProp`
    wp_apply (wp_Step_MsgProp P cfg r id s m ents ctx cs Hty Hterm Hfrom Hne Hlen Hlok Hlnz
      Hwf)
      $$ [$Hphys $Hents $Hcc $Hcap $Hctxp] as %err %s' ⟨Hphys, %Hwf', %Hfr, %Hst, Herr⟩
    have Hst' : ∃ recv, (∀ m' ∈ recv, m' = absMsg .propose m ents ctx) ∧
        Step cfg id (toPState s) recv (toPState s') := by
      rcases Hst with H | ⟨-, Hrl, ents', Hrepl, Hnw, Hstep⟩
      · exact H
      · -- appended at the leader: `Step.propose` receives the proposal (2026-10-10), the
        -- batch after the conf-change loop (2026-10-13)
        exact ⟨[absMsg .propose m ents ctx] ++ [], by simp,
          .trans _ _ _ _ _ (.propose (absMsg .propose m ents ctx) _ ents' rfl Hrepl Hrl Hnw)
            Hstep⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst'
    imod ghost_step_recv γ cfg id _ _ _ recv Hcfg Hrecv Hstep (by simp [absMsg, absMsgFrom])
      $$ Hm' Hghost with Hghost
    imodintro
    iapply HΦ $$ %err %s' %(toPState s')
    iframe Hphys Hghost
    isplitr
    · ipureintro; exact ⟨rfl, Hwf'⟩
    isplitr
    · ipureintro; exact ⟨recv, Hstep⟩
    isplitr
    · ipureintro; exact fun _ => ⟨Hfr.1, fun _ => Hfr.2⟩
    isplitr
    · ipureintro; exact fun _ _ => ⟨Hfr.2, Hfr.1.2.2.2.1, Hfr.1.2.2.1, Hfr.1.2.2.2.2.1, Hfr.1.2.2.2.2.2⟩
    isplitr
    · ipureintro; exact fun _ => TermStep.of_local Hfr.1
    isplitr
    · ipureintro; resp_other
    icases Herr with (%Herr | #Hd)
    · ileft; ipureintro; exact Herr
    · iright; iframe Hd; ipureintro; exact Hty
  -- every other type: the postcondition is `stepPost`
  simp only [ite_eq_right Hty]
  -- and the entries are read-only: the `by_cases` reduced `"Hents"`'s
  -- `if m.Type' = MsgProp`
  icases Hents with #Hents
  -- the two storage acknowledgements (2026-10-05), before the conversion to `stepPost`
  -- below: their postcondition also says what is kept of the physical state
  -- (`LocalStepOk`, 2026-10-09)
  by_cases HtyA : m.Type' = MsgStorageAppendResp
  · -- MsgStorageAppendResp: `stableTo`, invisible to the protocol.
    obtain ⟨Hsn, Hle, Hstok, Hghoff⟩ := Hsar HtyA
    wp_apply (wp_Step_MsgStorageAppendResp P cfg r id s m HtyA Hsn Hle Hstok Hghoff Hwf)
      $$ [$Hphys]
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
    · ipureintro; exact fun _ _ => ⟨Hfr.2, Hfr.1.2.2.2.1, Hfr.1.2.2.1, Hfr.1.2.2.2.2.1, Hfr.1.2.2.2.2.2⟩
    isplitr
    · ipureintro; exact fun _ => TermStep.of_local Hfr.1
    isplitr
    · ipureintro; exact RespStep.of_type (by rw [HtyA]; w32_ne) (by rw [HtyA]; w32_ne)
        (by rw [HtyA]; w32_ne)
    ileft; ipureintro; exact Herr
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
    · ipureintro; exact fun _ h => absurd HtyB h
    isplitr
    · ipureintro; exact fun _ => TermStep.of_local Hfr.1
    isplitr
    · ipureintro; exact RespStep.of_type (by rw [HtyB]; w32_ne) (by rw [HtyB]; w32_ne)
        (by rw [HtyB]; w32_ne)
    ileft; ipureintro; exact Herr
  ihave HΦ : ▷ stepPost γ cfg r id s m Φ $$ [HΦ]
  · inext
    unfold stepPost
    iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, %Hfr', %Htm', %Hresp', Herr⟩
    iapply HΦ $$ %err %s' %ps'
    iframe Hphys Hghost Herr
    ipureintro
    -- `LocalStepOk` is about the three types handled above
    exact ⟨Hrel', Href, fun Hl => by rcases Hl with h | h | h <;> contradiction,
      fun h _ => Hfr' h, Htm', Hresp'⟩
  by_cases Hns : m.Type' = MsgSnap
  · -- MsgSnap: `dispatch_Snap`, with the snapshot from `"Hsnap"`.
    icases Hsnap $$ %Hns with ⟨%sv, %voters, %learners, #Hsv, #Hvs, #Hls, %Hscope, #Hm'⟩
    iapply dispatch_Snap P γ cfg r id s m sv voters learners Φ Hcfg (Hin Hns) Hwf Hns
      (Hsnapt Hns) Hscope $$ Hinit Hphys Hghost Hsv Hvs Hls Hm' HΦ
  -- from here on `m` is not a `MsgSnap`, so `Hm`'s `ty ≠ .snap` guard always holds
  ihave #Hmsgc : (□ ∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗ isMessage γ (absMsg ty m ents ctx)) $$ []
  · imodintro
    iintro %ty %Hty'
    iapply Hmsg0 $$ %ty %Hty' %(fun h => Hns (mtypeOf_Snap _ (h ▸ Hty')))
  ihave #Hmsg : (□ ∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗ ⌜ty ≠ .heartbeat ∧ ty ≠ .heartbeatResp⌝ -∗
      isMessage γ (absMsg ty m ents)) $$ []
  · imodintro
    iintro %ty %Hty' %Hhb'
    rw [← isMessage_absMsg_ctx γ ty m ents ctx Hhb']
    iapply Hmsgc $$ %ty %Hty'
  iclear Hsnap Hmsg0
  by_cases Hty : m.Type' = MsgHup
  · -- MsgHup: a local message, handled by `hup`.
    obtain ⟨Hmterm, Hnowrap⟩ := Hhup Hty
    wp_apply (wp_Step_MsgHup P cfg r id s m Hty Hmterm Hnowrap Hwf) $$ [$Hphys]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    iapply finish_branch0 γ cfg r id s s' m err Φ Hcfg Hwf' Hst (fun _ => Hfr) (fun _ => Htm)
      (by resp_other) $$ Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgVote
  · -- MsgVote: answer the vote request, stepping down first if needed.
    obtain ⟨Hto, Hterm, Hfnz⟩ := Hvote Hty
    ihave #Hm' := Hmsg $$ %MsgType.vote %(by rw [Hty]; exact mtypeOf_MsgVote) %(And.intro (by decide) (by decide))
    ihave #Hctx' : (∃ (ctx : List w8), m.Context' ↦*□ ctx) $$ []
    · iexists ctx
      iexact Hctxp
    wp_apply (wp_Step_MsgVote P cfg r id s m ents Hty Hto Hterm Hfnz Hwf) $$ [$Hphys $Hctx']
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) (by resp_other) $$ Hm' Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgVoteResp
  · -- MsgVoteResp: tally the vote, possibly winning or losing.
    obtain ⟨Hto, Hterm⟩ := Hvoteresp Hty
    ihave #Hm' := Hmsg $$ %MsgType.voteResp %(by rw [Hty]; exact mtypeOf_MsgVoteResp) %(And.intro (by decide) (by decide))
    wp_apply (wp_Step_MsgVoteResp P cfg r id s m ents Hty Hto Hterm Hwf) $$ [$Hphys]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hresp, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) Hresp $$ Hm' Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgPreVote
  · -- MsgPreVote (2026-10-04): answered with a free `MsgPreVoteResp`; nothing
    -- received, nothing recorded.
    obtain ⟨Hto, Hterm, Hfnz, Hfid, Hutd0, Hpvon⟩ := Hprevote Hty
    ihave #Hctx' : (∃ (ctx : List w8), m.Context' ↦*□ ctx) $$ []
    · iexists ctx
      iexact Hctxp
    wp_apply (wp_Step_MsgPreVote P cfg r id s m Hty Hto Hterm Hfnz Hfid Hwf Hutd0 Hpvon)
      $$ [$Hphys $Hctx'] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    iapply finish_branch0 γ cfg r id s s' m err Φ Hcfg Hwf' Hst (fun _ => Hfr) (fun _ => Htm)
      (by resp_other) $$ Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgPreVoteResp
  · -- MsgPreVoteResp (2026-10-04): a pre-candidate's tally, or a step-down on a
    -- rejection of a higher term.
    obtain ⟨Hto, Hterm, -, Hnw⟩ := Hprevoteresp Hty
    ihave #Hm' := Hmsg $$ %MsgType.preVoteResp %(by rw [Hty]; exact mtypeOf_MsgPreVoteResp) %(And.intro (by decide) (by decide))
    wp_apply (wp_Step_MsgPreVoteResp P cfg r id s m ents Hty Hto Hterm Hnw Hwf)
      $$ [$Hphys] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hresp, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) Hresp $$ Hm' Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgApp
  · -- MsgApp: `dispatch_App`.
    ihave #Hm' := Hmsg $$ %MsgType.app %(by rw [Hty]; exact mtypeOf_MsgApp) %(And.intro (by decide) (by decide))
    iapply dispatch_App P γ cfg r id s m ents Φ Hcfg Hwf Hty (Happ Hty)
      $$ Hinit Hphys Hghost Hents Hcap Hm' HΦ
  by_cases Hty : m.Type' = MsgAppResp
  · -- MsgAppResp: `dispatch_AppResp`.
    ihave #Hm' := Hmsg $$ %MsgType.appResp %(by rw [Hty]; exact mtypeOf_MsgAppResp) %(And.intro (by decide) (by decide))
    iapply dispatch_AppResp P γ cfg r id s m ents Φ Hcfg Hwf Hty (Happresp Hty)
      $$ Hinit Hphys Hghost Hents Hm' HΦ
  by_cases Hty : m.Type' = MsgHeartbeat
  · -- MsgHeartbeat: `dispatch_Heartbeat`.
    ihave #Hm' := Hmsgc $$ %MsgType.heartbeat %(by rw [Hty]; exact mtypeOf_MsgHeartbeat)
    iapply dispatch_Heartbeat P γ cfg r id s m ents ctx Φ Hcfg Hwf Hty (Hhb Hty)
      $$ Hinit Hphys Hghost Hents Hctxp Hm' HΦ
  by_cases Hty : m.Type' = MsgHeartbeatResp
  · -- MsgHeartbeatResp: `dispatch_HeartbeatResp`, with its context (2026-10-13).
    ihave #Hm' := Hmsgc $$ %MsgType.heartbeatResp
      %(by rw [Hty]; exact mtypeOf_MsgHeartbeatResp)
    iapply dispatch_HeartbeatResp P γ cfg r id s m ents ctx Φ Hcfg Hwf Hty (Hhbresp Hty)
      $$ Hinit Hphys Hghost Hents Hctxp Hm' HΦ
  by_cases Hty : m.Type' = MsgBeat
  · -- MsgBeat: `dispatch_Beat`.
    iapply dispatch_Beat P γ cfg r id s m Φ Hcfg Hwf Hty (Hbeat Hty)
      $$ Hinit Hphys Hghost HΦ
  by_cases Hty : m.Type' = MsgReadIndex
  · -- MsgReadIndex (2026-10-13): `dispatch_ReadIndex`, with the request's credit.
    ihave #Hm' := Hmsgc $$ %MsgType.readIndex %(by rw [Hty]; rfl)
    rw [if_pos Hty]
    iapply dispatch_ReadIndex P γ cfg r id s m ents ctx Φ Hcfg Hwf Hty (Hri Hty)
      $$ Hinit Hphys Hghost Hents Hctxp Hm' Hcred HΦ
  by_cases Hty : m.Type' = MsgReadIndexResp
  · -- MsgReadIndexResp (2026-10-13): `dispatch_ReadIndexResp`.
    ihave #Hm' := Hmsgc $$ %MsgType.readIndexResp %(by rw [Hty]; rfl)
    iapply dispatch_ReadIndexResp P γ cfg r id s m ents ctx Φ Hcfg Hwf Hty (Hrir Hty)
      $$ Hinit Hphys Hghost Hents Hctxp Hm' HΦ
  -- (2026-10-13) the types outside the model: a free message justifies a step-down
  ihave #Hsd := isMessage_stepdown (GF := GF) γ id m
  obtain ⟨Hloc, Htn, Htl⟩ := Hrest
  by_cases HtyL : m.Type' = MsgForgetLeader ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus
  · -- the local reports and `ForgetLeader`
    ihave %Hfv0 := ownRaftGhost_follower_votes γ id (toPState s) $$ Hghost
    have Hfv : s.role = .follower → s.votes = ∅ := followerVotesOk_phys s Hfv0
    wp_apply (wp_Step_MsgLocal P cfg r id s m HtyL (Hloc HtyL) Hwf Hfv) $$ [$Hphys]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    have Hn : m.Type' ≠ MsgVoteResp ∧ m.Type' ≠ MsgAppResp ∧ m.Type' ≠ MsgPreVoteResp := by
      rcases HtyL with h | h | h <;> rw [h] <;> exact ⟨by w32_ne, by w32_ne, by w32_ne⟩
    iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) (RespStep.of_type Hn.1 Hn.2.1 Hn.2.2)
      (by simp [stepdownMsg, Msg.plain]) $$ Hsd Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgTransferLeader
  · -- leader transfer: a request
    obtain ⟨Hent, Hctx0, Htr⟩ := Htl Hty
    ihave %Hlok0 := ownRaftGhost_lead_ok γ id (toPState s) $$ Hghost
    have Hlok : s.role = .follower → s.lead ≠ id := by
      intro Hf
      rw [← toPState_lead_nonpre s (by rw [Hf]; decide)]
      apply Hlok0
      rw [toPState_role, Hf]; decide
    wp_apply (wp_Step_MsgTransferLeader P cfg r id s m Hty Hent Hctx0 Htr Hlok Hwf) $$ [$Hphys]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) (by resp_other)
      (by simp [stepdownMsg, Msg.plain]) $$ Hsd Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgTimeoutNow
  · -- leader transfer: the transferee campaigns
    obtain ⟨Hnw, Hnwm⟩ := Htn Hty
    wp_apply (wp_Step_MsgTimeoutNow P cfg r id s m Hty Hnw Hnwm Hwf) $$ [$Hphys]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ cfg r id s s' m _ recv err Φ Hcfg Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) (by resp_other)
      (by simp [stepdownMsg, Msg.plain]) $$ Hsd Hghost Hphys [] HΦ
    ileft; ipureintro; exact Herr
  -- none of the twenty-one (the two storage acknowledgements were handled above)
  exfalso
  simp only [StepMsg, stepMsgTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at Hsm
  rcases Hsm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h <;> first | contradiction | exact HtyL (by simp [h])

end dispatch

end EtcdGrove
end Perennial
