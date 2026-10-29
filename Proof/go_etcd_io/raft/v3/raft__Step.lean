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

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `"Hmsg_in" ∷ msgIn ml
(if MsgProp then 1 else □) ⟨m, ents, sn, ctx, rs⟩`, which every branch takes whole (the old
`Entries`/`Context` points-tos and the `Entries` capacity are its parts); the `MsgSnap` premise is
pure (`sn = some sv`, `scfg = sv...lists`). The getter specs and `MessageType.Enum` are extra
hypotheses of `raft.Step.wp_proof`, bundled as `raft.Step.ReplPbPostulates` (`ReplLemmas.lean`,
the replication branches') and `raft.Step.PbPostulates` (`ElectionLemmas.lean`, the election
branches').
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
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgCheckQuorum
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
    (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (γ : RaftNames) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc) (Φ : val → IProp GF)
    (md : GMode) (Hdh : ∀ s', DynHypFor md m s s') (Hwf : NStateWf s) (Hty : m.Type' = MsgApp)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhysCV c c.voters r id s -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ -∗
      isMessage γ (absMsg .app m ents) -∗
      ▷ stepPostT γ md c r id s m (AppTrunc m ents s) Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost Hrest Hmsg #Hm HΦ
  -- `maybeAppend`'s batch facts: carried by the message
  ihave %Hbatch := app_recv_wf γ id (toPState s) (absMsg .app m ents) rfl Hto $$ Hghost Hm
  obtain ⟨Hpwf, Hnw⟩ := Hbatch
  -- the conflict fact: the protocol's, for a message no older than us
  have Hconf_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md.isDyn -∗
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
  wp_apply (wp_Step_MsgApp P Q c r id s ml m sn ctx rs ents Hty Hto Hterm Hfnz Hfid Hwf Hpwf Hnw
      Hconf Hfv) $$ [$Hphys $Hmsg] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm, %Htr⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branchT γ md c r id s s' m _ recv err Φ (AppTrunc m ents s) Htr (Hdh s') Hwf'
    Hrecv Hstep (fun _ => Hfr) (fun _ => Htm) (by resp_other) Hfr.nsst $$ Hm Hghost Hrest Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

/-- A leader of the message's term is its sender: a heartbeat or a snapshot of the
receiver's own term cannot reach a leader (`isLeader_unique`). -/
private theorem not_leader_of_msg (γ : RaftNames) (id : w64) (s : NState)
    (m : MessageM) (Hfid : m.From' ≠ id) {md : Bool} :
    ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md -∗ isLeader γ m.From' m.Term' -∗
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
private theorem isMessage_heartbeat_isLeader (γ : RaftNames) (m : MessageM)
    (ents : List EntryM) (ctx : List w8 := []) :
    isMessage (GF := GF) γ (absMsg .heartbeat m ents ctx) ⊢ isLeader γ m.From' m.Term' := by
  unfold isMessage absMsg absMsgFrom
  iintro ⟨H, -⟩
  iexact H

/-- The same, for a snapshot. -/
private theorem isMessage_snap_isLeader (γ : RaftNames) (m : MessageM)
    (sv : SnapshotM) (voters : CSLists) :
    isMessage (GF := GF) γ (absSnap m sv voters) ⊢ isLeader γ m.From' m.Term' := by
  unfold isMessage absSnap absSnapFrom
  iintro ⟨H, -⟩
  iexact H

private theorem dispatch_Heartbeat (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (γ : RaftNames) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc) (Φ : val → IProp GF)
    (md : GMode) (Hdh : ∀ s', DynHypFor md m s s') (Hwf : NStateWf s)
    (Hty : m.Type' = MsgHeartbeat)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhysCV c c.voters r id s -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ -∗
      isMessage γ (absMsg .heartbeat m ents ctx) -∗
      ▷ stepPost γ md c r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost Hrest Hmsg #Hmc HΦ
  have Hcl_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md.isDyn -∗
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
  wp_apply (wp_Step_MsgHeartbeat P Q c r id s ml m sn ctx rs ents Hty Hto Hterm Hfnz Hfid Hwf Hcl Hfv)
    $$ [$Hphys $Hmsg] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ md c r id s s' m _ recv err Φ (Hdh s') Hwf' Hrecv Hstep
    (fun _ => Hfr) (fun _ => Htm) (by resp_other) Hfr.nsst $$ Hmc Hghost Hrest Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

private theorem dispatch_AppResp (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (γ : RaftNames) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc) (Φ : val → IProp GF)
    (md : GMode) (Hdh : ∀ s', DynHypFor md m s s') (Hwf : NStateWf s)
    (Hty : m.Type' = MsgAppResp)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ (m.Reject' = true → m.From' ≠ id))
    (Hnsb : s.gh.ns = true → γ.reBoot ≠ []) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhysCV c c.voters r id s -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ -∗
      isMessage γ (absMsg .appResp m ents) -∗
      ▷ stepPost γ md c r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hrej⟩ := Hm
  iintro #Hinit Hphys Hghost Hrest Hmsg #Hm HΦ
  -- (2026-10-13) the read-only facts a commit's release needs, from the ghost state
  have Hlrd_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md.isDyn -∗
      ⌜s.role = .leader → RdOk c.voters s.rd ∧ s.term ≠ W64 0⌝ := by
    iintro Hg
    by_cases hl : s.role = .leader
    · ihave %H1 := ghost_rdOk γ id s hl c.voters $$ Hg
      ipureintro; intro _; exact H1
    · ipureintro; exact fun h => absurd h hl
  ihave %Hlrd := Hlrd_lem $$ Hghost
  -- (2026-10-16, stage R8a, D11) an accepted acknowledgement of the leader's term is within its
  -- log: the message's ghost witness (`ackIn`, `isMessage_appResp_ackIn`) at the leader
  -- (`ownRaftGhost_ackIn_le`), in `logLast` through `lastIndex() + 1` not wrapping
  icases ownRaftPhysC_prvals_ok c r id s $$ Hphys with ⟨-, %Hnw, Hphys⟩
  have Hack_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md.isDyn -∗
      isMessage γ (absMsg .appResp m ents) -∗
      ⌜s.role = .leader → m.Term' = s.term →
        (m.Reject' = false → uint.Z m.Index' ≤ uint.Z (logLast s.logst)) ∧
        (m.Reject' = true → s.gh.ns = true →
          2 ≤ uint.Z m.Index' ∧ 1 ≤ uint.Z m.RejectHint' ∧ uint.Z m.RejectHint' ≤ uint.Z m.Index' ∧
          (∀ t0, plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) (W64 1) = some t0 →
            uint.Z t0 ≤ 1))⌝ ∗
      ownRaftGhost γ id (toPState s) md.isDyn := by
    iintro Hg #Hmsg
    -- (2026-10-19, D21 M3) a rejection in the no-snapshot mode: the message's clause
    -- (`isMessage_appResp_rej_inv`), and the leader's term at `1` (`ownRaftGhost_term1`)
    icases ownRaftGhost_term1 γ id (toPState s) $$ Hg with ⟨%Ht1, Hg⟩
    ihave %Hrejp : ⌜m.Reject' = true → s.gh.ns = true →
        2 ≤ uint.Z m.Index' ∧ 1 ≤ uint.Z m.RejectHint' ∧ uint.Z m.RejectHint' ≤ uint.Z m.Index' ∧
        (∀ t0, plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) (W64 1) = some t0 →
          uint.Z t0 ≤ 1)⌝ $$ []
    · by_cases hrj : m.Reject' = true
      · icases isMessage_appResp_rej_inv γ (absMsg .appResp m ents) rfl hrj $$ Hmsg with %Hc
        ipureintro
        intro _ hns
        have Hne := Hnsb hns
        obtain ⟨h1, h2, h3⟩ := Hc Hne
        have Hbl := List.length_pos_iff.mpr Hne
        exact ⟨by simp only [absMsg, absMsgFrom] at h1; omega, h2, h3, Ht1 Hne⟩
      · ipureintro; intro h; exact absurd h hrj
    by_cases hl : s.role = .leader
    rotate_left
    · iframe Hg; ipureintro; exact fun h => absurd h hl
    by_cases ht : m.Term' = s.term
    rotate_left
    · iframe Hg; ipureintro; exact fun _ h => absurd h ht
    by_cases hr : m.Reject' = false
    rotate_left
    · iframe Hg; ipureintro; exact fun _ _ => ⟨fun h => absurd h hr, Hrejp⟩
    ihave #Hai := isMessage_appResp_ackIn γ (absMsg .appResp m ents) rfl hr $$ Hmsg
    ihave Hai' := ackIn_cast γ (show (absMsg .appResp m ents).term = (toPState s).term from ht)
      (show (absMsg .appResp m ents).index = m.Index' from rfl) $$ Hai
    icases ownRaftGhost_ackIn_le γ id (toPState s) m.Index'
        (by rw [toPState_role, proleRole_leader]; exact hl) $$ Hg Hai' with ⟨%H, Hg⟩
    iframe Hg
    ipureintro
    intro _ _
    refine ⟨fun _ => ?_, Hrejp⟩
    rw [Hnw.logLast_Z]
    simp only [toPState, plogLastIndexZ, List.length_append] at H
    push_cast at H
    omega
  icases Hack_lem $$ Hghost Hm with ⟨%Hack, Hghost⟩
  wp_apply (wp_Step_MsgAppResp P Q c r id s ml m sn ctx rs ents Hlrd Hack Hty Hto Hterm Hfnz Hrej Hwf)
    $$ [$Hphys $Hmsg] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hresp, %Hfr, %Htm⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ md c r id s s' m _ recv err Φ (Hdh s') Hwf' Hrecv Hstep
    (fun _ => Hfr) (fun _ => Htm) Hresp Hfr.nsst $$ Hm Hghost Hrest Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

private theorem dispatch_HeartbeatResp (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (γ : RaftNames) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc) (Φ : val → IProp GF)
    (md : GMode) (Hdh : ∀ s', DynHypFor md m s s') (Hwf : NStateWf s)
    (Hty : m.Type' = MsgHeartbeatResp)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhysCV c c.voters r id s -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ -∗
      isMessage γ (absMsg .heartbeatResp m ents ctx) -∗
      ▷ stepPost γ md c r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost Hrest Hmsg #Hm HΦ
  -- (2026-10-25, T-M M2c) the configuration has a voter, from the ghost state
  icases ghostRest_voters_ne γ md c id s $$ Hrest with ⟨%Hvne, Hrest⟩
  -- (2026-10-13) the read-only facts `stepLeader`'s read path needs, from the ghost state
  have Hlrd_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md.isDyn -∗
      isMessage γ (absMsg .heartbeatResp m ents ctx) -∗
      ⌜s.role = .leader → m.Term' = s.term →
        (RdOk c.voters s.rd ∧ s.term ≠ W64 0) ∧ (ctx = [] ∨ 8 ≤ ctx.length) ∧
        (ctx ≠ [] → uint.Z (leToU64 (ctx.take 8))
                      ≤ uint.Z s.rd.ro.confirmed + (s.rd.ro.pending.length : Int)) ∧
        c.voters ≠ ∅⌝ := by
    iintro Hg #Hm
    by_cases hl : s.role = .leader
    · by_cases ht : m.Term' = s.term
      · ihave %H1 := ghost_rdOk γ id s hl c.voters $$ Hg
        ihave %H2 := ghost_hbResp_ctx γ id s m ents ctx hl Hto ht $$ Hg Hm
        ipureintro
        intro _ _
        exact ⟨H1, H2.1, H2.2, Hvne hl⟩
      · ipureintro; exact fun _ h => absurd h ht
    · ipureintro; exact fun h => absurd h hl
  ihave %Hlrd := Hlrd_lem $$ Hghost Hm
  wp_apply (wp_Step_MsgHeartbeatResp P Q c r id s ml m sn ctx rs ents Hlrd Hty Hto Hterm Hfnz Hfid Hwf)
    $$ [$Hphys $Hmsg] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  obtain ⟨cx, recv, Hc, Hrecv, Hstep⟩ := Hst
  ihave #Hmc : isMessage γ (absMsg .heartbeatResp m ents cx) $$ []
  · rcases Hc with rfl | rfl
    · unfold isMessage; simp only [absMsg, absMsgFrom]; ileft; ipureintro; trivial
    · iexact Hm
  iapply finish_branch γ md c r id s s' m _ recv err Φ (Hdh s') Hwf' Hrecv Hstep
    (fun _ => Hfr) (fun _ => Htm) (by resp_other) Hfr.nsst $$ Hmc Hghost Hrest Hphys
    [] HΦ
  ileft; ipureintro; exact Herr

private theorem dispatch_Beat (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (γ : RaftNames) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc) (Φ : val → IProp GF)
    (md : GMode) (Hdh : ∀ s', DynHypFor md m s s') (Hwf : NStateWf s)
    (Hty : m.Type' = MsgBeat) (Hterm : m.Term' = W64 0) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhysCV c c.voters r id s -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ -∗
      ▷ stepPost γ md c r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
        {{ v, |={⊤}=> Φ v }} := by
  iintro #Hinit Hphys Hghost Hrest Hmsg HΦ
  -- (2026-10-29, stage U7) a leader's term past `0`, for `send`'s stamp (`stepLeader`'s premise)
  have HLT_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md.isDyn -∗
      ⌜s.role = .leader → s.term ≠ W64 0⌝ := by
    iintro Hg
    by_cases hl : s.role = .leader
    · ihave %H := ownRaftGhost_term_nz γ id (toPState s)
        (by rw [toPState_role, hl]; decide) $$ Hg
      ipureintro; exact fun _ => H
    · ipureintro; exact fun h => absurd h hl
  ihave %HLT := HLT_lem $$ Hghost
  wp_apply (wp_Step_MsgBeat P Q c r id s ml m sn ctx rs ents Hty Hterm Hwf HLT)
    $$ [$Hphys $Hmsg] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  iapply finish_branch0 γ md c r id s s' m err Φ (Hdh s') Hwf' Hst (fun _ => Hfr) (fun _ => Htm)
      (by resp_other) Hfr.nsst $$ Hghost Hrest Hphys [] HΦ
  ileft; ipureintro; exact Herr

/-- `MsgCheckQuorum` (2026-10-17, `CheckQuorum` on): as `MsgBeat`, a local message; the leader
may step down at its term. -/
private theorem dispatch_CheckQuorum (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (γ : RaftNames) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc) (Φ : val → IProp GF)
    (md : GMode) (Hdh : ∀ s', DynHypFor md m s s') (Hwf : NStateWf s)
    (Hty : m.Type' = MsgCheckQuorum) (Hterm : m.Term' = W64 0) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhysCV c c.voters r id s -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ -∗
      ▷ stepPost γ md c r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
        {{ v, |={⊤}=> Φ v }} := by
  iintro #Hinit Hphys Hghost Hrest Hmsg HΦ
  wp_apply (wp_Step_MsgCheckQuorum P Q c r id s ml m sn ctx rs ents Hty Hterm Hwf)
    $$ [$Hphys $Hmsg] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  iapply finish_branch0 γ md c r id s s' m err Φ (Hdh s') Hwf' Hst (fun _ => Hfr) (fun _ => Htm)
      (by resp_other) Hfr.nsst $$ Hghost Hrest Hphys [] HΦ
  ileft; ipureintro; exact Herr

/-- `MsgSnap` (2026-10-02): the snapshot and its `ConfState` come from `"Hsnap"`. At the
current term the receiver is not a leader -- the sender leads that term (`isMessage`'s
`isLeader`, `isLeader_unique`) -- and a follower's tally is empty (`FollowerVotesOk`);
the three `step_snap_*` rules need no other protocol fact: a restore replaces the log
wholesale and the fast-forward's `commitTo` is in range by `matchTerm`. In either mode since
2026-10-14 (stage B8): the branch's `StepCDS` witness updates the mode's ghost state
(`ghost_stepCDS`), with what the mode asks of the snapshot (`GMode.SnapOk`). -/
private theorem dispatch_Snap (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc) (sv : SnapshotM) (scfg : CSLists)
    (Φ : val → IProp GF) (Hwf : NStateWf s)
    (Hty : m.Type' = MsgSnap)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id)
    (Hidx : uint.Z sv.Metadata'.Index' < 2^61)
    (Hsn : sn = some sv) (Hcl : scfg = sv.Metadata'.ConfState'.lists)
    (Hnsf : s.gh.ns = false) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhysCV c c.voters r id s -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ -∗
      isMessageC γ (absSnap m sv scfg) -∗
      -- (D22 S-r, 2026-10-21) its data certificate, registered with its configuration's
      snapDataOk γ sv.Metadata'.Index' sv.Data' -∗
      ▷ snapPost γ md c r id s m sn Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, Hfnz, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost Hrest Hmsg #HmC #Hdat HΦ
  ihave #Hm := isMessageC_isMessage γ _ $$ HmC
  -- (D22 S-b′3; U8 v2) the snapshot's certificate, pinned at the node's storage names (`certLink`,
  -- `ksnCert`); (D22 S-r) with its data certificate
  ihave #Hcr : raftSnapCert γ (snapTrip sv sv.Metadata'.ConfState'.lists) $$ []
  · rw [← Hcl, show raftSnapCert (GF := GF) γ (snapTrip sv scfg) =
      raftSnapCert γ (msgSnapTrip (absSnap m sv scfg)) from rfl]
    iapply isMessageC_snap_cert γ (absSnap m sv scfg) (by simp [absSnap, absSnapFrom]) $$ HmC
  ihave #HcrD : raftSnapCertD γ (snapTrip sv sv.Metadata'.ConfState'.lists) $$ []
  · unfold raftSnapCertD
    isplitr
    · iexact Hcr
    · simp only [snapTrip, snapId]; iexact Hdat
  icases ghostRest_nsLink γ md c id s $$ Hrest with ⟨%Hnlk, Hrest⟩
  icases ghostRest_certLink γ md c id s $$ Hrest with ⟨#Hlink, Hrest⟩
  iunfold certLink at Hlink
  iunfold storCertOk at Hlink
  icases Hlink with ⟨-, -, #Hreg⟩
  imod Hreg $$ %_ %⊤ %CoPset.subseteq_top HcrD with #Hcert
  -- (D22 S-b′4) the lists' scope and the mode's need, from the certificate
  ihave %Hlo : ⌜∀ x, scfg.Has x → SnapScope sv scfg⌝ $$ []
  · unfold raftSnapCert
    icases Hcr with ⟨%Hl, -⟩
    ipureintro; intro x hx; subst Hcl; exact Hl x hx
  have Hscope : SnapScopeIf id sv scfg := ⟨Hlo id, Hidx⟩
  icases snapOkIf_of_cert γ md id (toPState s) sv scfg Hcl $$ Hghost [] with ⟨#Hso, Hghost⟩
  · rw [Hcl]; iexact Hcr
  -- at the current term the receiver is not a leader: the sender leads it
  ihave #Hl2 := isMessage_snap_isLeader γ m sv scfg $$ Hm
  ihave %Hnl := not_leader_of_msg γ id s m Hfid $$ Hghost Hl2
  ihave %Hfv0 := ownRaftGhost_follower_votes γ id (toPState s) $$ Hghost
  have Hfv : s.role = .follower → s.votes = ∅ := followerVotesOk_phys s Hfv0
  wp_apply (wp_Step_MsgSnap (B := plogLastIndexZ (toPState s).base (toPState s).log) P Q c r id s
      ml m sn ctx rs ents scfg sv Hnsf Hty Hto Hterm Hfnz Hfid
      Hwf Hscope Hsn Hcl Hnl Hfv) $$ [$Hphys $Hmsg $Hcert]
    as %err %s' %c1 ⟨Hphys, %Hc1, %Hwf', %Hst, %Herr, %Hng, %Hsf⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  -- the received messages, each the snapshot message, none a read-index request
  have Hcnt : rdCount recv = 0 := by
    unfold rdCount; rw [List.countP_eq_zero]
    intro x hx; rw [Hrecv x hx]; simp [absSnap, absSnapFrom]
  imod rdCred_zero_upd (GF := GF) γ with Hz
  ihave Hall : ([∗list] x ∈ recv, isMessage (GF := GF) γ x) $$ []
  · iapply (BigSepL.bigSepL_intro (P := iprop(□ isMessage (GF := GF) γ (absSnap m sv scfg)))
      (fun k x hx => by
        rw [Hrecv x (List.mem_of_getElem? hx)]
        exact intuitionistically_elim))
    iexact Hm
  unfold snapPost
  icases HΦ with ⟨Hlc, HΦ⟩
  -- (2026-10-18, D19b stage 5) a step that creates no entry, at the node's last index
  ihave ⟨#Hlr, %HL⟩ := ownRaftGhost_lastRec γ id (toPState s) $$ Hghost
  imod lastRec_receipt γ _ $$ Hlr with #Hrc0
  imod ghost_stepCDS γ md c c1 id m Hty sv scfg s recv s' (absSnap m sv scfg) ⟨rfl, rfl⟩ _ HL
      Hstep (.inl Hc1) ⟨Hng, Hsf.1.2.2.2.1⟩ $$ Hrc0 Hm Hall [Hz] [] Hlc Hso Hghost Hrest with ⟨%md', %Hout, Hghost, Hrest⟩
  · rw [Hcnt]; iexact Hz
  · iapply msgsTks_noprop γ recv (fun x hx => by rw [Hrecv x hx]; simp [absSnap, absSnapFrom])
  imodintro
  ihave Hghost : ownStepGhost γ md' c1 id s' $$ [Hghost Hrest]
  · unfold ownStepGhost; iframe
  iapply HΦ $$ %err %s' %c1 %md'
  iframe Hphys Hghost
  ipureintro
  -- (2026-10-20, D22 S-c) the snapshot's frame and configuration (until then not claimed; since
  -- 2026-10-28, stage U0, the configuration kept)
  refine ⟨Hwf', Hout, by resp_other, ⟨Hsf.1, Hc1, fun sv' h => ?_⟩, Herr⟩
  rw [Hsn] at h; cases h; exact Hsf.2

/-- `MsgReadIndex` (2026-10-13): a local or forwarded request, `Term = 0`. -/
private theorem dispatch_ReadIndex (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (γ : RaftNames) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc) (Φ : val → IProp GF)
    (md : GMode) (Hdh : ∀ s', DynHypFor md m s s') (Hwf : NStateWf s)
    (Hty : m.Type' = MsgReadIndex)
    (Hterm : m.Term' = W64 0) (Hnors : rs = []) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhysCV c c.voters r id s -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ -∗
      isMessage γ (absMsg .readIndex m ents ctx) -∗
      rdCred γ 1 -∗
      ▷ stepPost γ md c r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
        {{ v, |={⊤}=> Φ v }} := by
  iintro #Hinit Hphys Hghost Hrest Hmsg #Hm Hcred HΦ
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
  have Hlrd_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md.isDyn -∗
      ⌜s.role = .leader → RdOk c.voters s.rd ∧ s.term ≠ W64 0⌝ := by
    iintro Hg
    by_cases hl : s.role = .leader
    · ihave %H1 := ghost_rdOk γ id s hl c.voters $$ Hg
      ipureintro; intro _; exact H1
    · ipureintro; exact fun h => absurd h hl
  ihave %Hlrd := Hlrd_lem $$ Hghost
  wp_apply (wp_Step_MsgReadIndex P Q c r id s ml m sn ctx rs ents Hty Hterm Hne Hlok Hlrd Hwf Hnors)
    $$ [$Hphys $Hmsg] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  obtain ⟨recv, Hrecv, Hlen, Hstep⟩ := Hst
  -- the request's credit goes with it, if it was received
  have Hcnt : rdCount recv ≤ 1 := by
    have : rdCount recv ≤ recv.length := List.countP_le_length
    omega
  -- the step in the mode's model (2026-10-14)
  unfold stepPost
  icases HΦ with ⟨Hlc, HΦ⟩
  -- (2026-10-18, D19b stage 5) a step that creates no entry, at the node's last index
  ihave ⟨#Hlr, %HL⟩ := ownRaftGhost_lastRec γ id (toPState s) $$ Hghost
  imod lastRec_receipt γ _ $$ Hlr with #Hrc0
  imod ghost_step_md γ md c id m s s' _ recv 1 _ HL Hrecv Hstep (Hdh s') Hcnt Hfr.nsst $$ Hrc0 Hm Hcred
      [] Hlc Hghost Hrest with ⟨%md', %Hout, Hghost⟩
  · iapply msgsTks_noprop γ recv (fun x hx => by rw [Hrecv x hx]; simp [absMsg, absMsgFrom])
  imodintro
  ihave Herr' : (⌜err = interface.nil⌝ ∨
      (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err) : IProp GF) $$ []
  · ileft; ipureintro; exact Herr
  iapply HΦ $$ %err %s' %c %md'
  iframe Hphys Hghost Herr'
  ipureintro
  exact ⟨Hwf', Hout, fun _ => rfl, fun _ => Hfr, fun _ => Htm, by resp_other⟩

/-- `MsgReadIndexResp` (2026-10-13): a leader's answer to a forwarded request. -/
private theorem dispatch_ReadIndexResp (P : raft.Step.Postulates (GF := GF) (hG := hG))
    (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (γ : RaftNames) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc) (Φ : val → IProp GF)
    (md : GMode) (Hdh : ∀ s', DynHypFor md m s s') (Hwf : NStateWf s)
    (Hty : m.Type' = MsgReadIndexResp)
    (Hm : m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗
      ownRaftPhysCV c c.voters r id s -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ -∗
      isMessage γ (absMsg .readIndexResp m ents ctx) -∗
      ▷ stepPost γ md c r id s m Φ -∗
      WP (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
        {{ v, |={⊤}=> Φ v }} := by
  obtain ⟨Hto, Hterm, -, Hfid⟩ := Hm
  iintro #Hinit Hphys Hghost Hrest Hmsg #Hm HΦ
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
  wp_apply (wp_Step_MsgReadIndexResp P Q c r id s ml m sn ctx rs e Hty Hto Hterm Hfid Hwf)
    $$ [$Hphys $Hmsg] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
  obtain ⟨recv, Hrecv, Hstep⟩ := Hst
  iapply finish_branch γ md c r id s s' m _ recv err Φ (Hdh s') Hwf' Hrecv Hstep
    (fun _ => Hfr) (fun _ => Htm) (by resp_other) Hfr.nsst $$ Hm Hghost Hrest Hphys [] HΦ
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
    -- (D22 S-d2) a snapshot's acknowledgement
    (wp_raft_appliedSnap : raft.appliedSnap.spec (GF := GF) (hG := hG))
    (wp_raft_reduceUncommittedSize : raft.reduceUncommittedSize.spec (GF := GF) (hG := hG))
    (wp_entsSize : entsSize.spec (GF := GF) (hG := hG))
    (wp_payloadsSize : payloadsSize.spec (GF := GF) (hG := hG))
    -- (stage R4) the message's getters and `MessageType.Enum` (protobuf-go v2)
    (wp_Message_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_Message_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_Message_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_Message_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_Message_GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG))
    (wp_Message_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Message_GetCommit : raftpb.Message.GetCommit.spec (GF := GF) (hG := hG))
    (wp_Message_GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG))
    (wp_Message_GetEntries : raftpb.Message.GetEntries.spec (GF := GF) (hG := hG))
    (wp_Message_GetSnapshot : raftpb.Message.GetSnapshot.spec (GF := GF) (hG := hG))
    (wp_Message_GetContext : raftpb.Message.GetContext.spec (GF := GF) (hG := hG))
    (wp_Entry_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.Step.spec (GF := GF) (hG := hG) := by
  have P : raft.Step.Postulates (GF := GF) (hG := hG) :=
    ⟨wp_raft_hup, wp_raft_becomeFollower, wp_voteRespMsgType, wp_raft_send, wp_stepCandidate,
     wp_stepFollower, wp_stepLeader, wp_traceReceiveMessage, wp_raftLog_lastEntryID,
     wp_raftLog_isUpToDate, wp_raftLog_stableTo, wp_raft_appliedTo, wp_raft_appliedSnap,
     wp_raft_reduceUncommittedSize, wp_entsSize, wp_payloadsSize⟩
  have Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG) :=
    ⟨wp_Message_GetType, wp_Message_GetTerm, wp_Message_GetFrom, wp_Message_GetTo,
     wp_Message_GetIndex, wp_Message_GetLogTerm, wp_Message_GetCommit, wp_Message_GetReject,
     wp_Message_GetEntries, wp_Message_GetSnapshot, wp_Message_GetContext, wp_Entry_GetIndex,
     wp_MessageType_Enum⟩
  have PB : raft.Step.PbPostulates (GF := GF) (hG := hG) :=
    ⟨wp_Message_GetType, wp_Message_GetTerm, wp_Message_GetFrom, wp_Message_GetLogTerm,
     wp_Message_GetIndex, wp_Message_GetReject, wp_Message_GetContext, wp_MessageType_Enum⟩
  intro c md γ r id s ml m ents ctx sn rs Hsm Hhup Hvote Hvoteresp Hprevote Hprevoteresp
    Happ Hhb Happresp Hhbresp Hsnapt Hbeat Hprop Hsar Hsapr Hri Hrir Hrest Hwf Hpre Hnsx
  iintro %Φ ⟨#Hinit, Hphys, Hghost, Hm, Hcred, Hlc, #Hsnap⟩ HΦ
  -- (2026-10-14, stage B7) the ghost state in its mode: `ownRaftGhost` (what the protocol facts
  -- below read) and the rest
  iunfold ownStepGhost at Hghost
  icases Hghost with ⟨Hghost, Hrest⟩
  icases Hm with ⟨Hmi, Hents, %Hpents, %Hnors, %Happly, #Hmsg0⟩
  iapply wp_fupd
  by_cases Hty : m.Type' = MsgProp
  · -- MsgProp: forward, append or drop (`proof_raft__Step_MsgProp.v`). The node's own
    -- `LeadOk` is what the follower's forwarding needs. Decided first (2026-10-06)
    -- because it is the one type whose postcondition carries more than `stepPost`: the
    -- proposals' updates, registered or handed back.
    simp only [ite_eq_left Hty]
    obtain ⟨Hterm, Hfrom⟩ := Hprop Hty
    obtain ⟨Hne, Hlen⟩ := Hpents Hty
    icases Hents with ⟨⟨%cs, #Hcc⟩, Htks⟩
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
    have Hlnz_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md.isDyn -∗
        ⌜s.role = .leader → s.term ≠ W64 0⌝ := by
      iintro Hg
      by_cases hl : s.role = .leader
      · ihave %H := ownRaftGhost_term_nz γ id (toPState s)
          (by rw [toPState_role, hl]; decide) $$ Hg
        ipureintro; exact fun _ => H
      · ipureintro; exact fun h => absurd h hl
    ihave %Hlnz := Hlnz_lem $$ Hghost
    -- `Hents` is owned: the `by_cases` above reduced its `if m.Type' = MsgProp`
    -- (2026-10-18, D19b stage 5) the receipt of the log's last index (`lastRec`)
    ihave ⟨#Hlr, %HL⟩ := ownRaftGhost_lastRec γ id (toPState s) $$ Hghost
    imod lastRec_receipt γ _ $$ Hlr with #Hrc0
    wp_apply (wp_Step_MsgProp P.traceReceiveMessage P.stepFollower P.stepCandidate P.stepLeader
      Q c r id s ml m sn ctx rs ents cs _ Hty Hterm Hfrom Hne Hlen Hlok
      Hlnz Hwf HL (Hnors (.inl Hty)))
      $$ [$Hphys $Hmi $Hcc $Hrc0] as %err %s' %B ⟨Hphys, %HBb, Hrcb, %Hwf', %Hfr, -, %Hpk, %Hst, Herr⟩
    obtain ⟨recv, Hrecv, Hrl, Hstep⟩ := Hst
    -- the receipt of the bound: the last index's, or the appended batch's
    ihave #HrcB : ⧖ (B.toNat - γ.reBoot.length) $$ [Hrcb]
    · by_cases hlt : plogLastIndexZ (toPState s).base (toPState s).log < B
      · ihave #H := Hrcb $$ %hlt
        have Hpl : plogLastIndexZ (toPState s).base (toPState s).log =
            plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) := rfl
        iapply (preceipt_mono (GF := GF) (show B.toNat - γ.reBoot.length ≤
          ((plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents)).toNat
            - γ.reBoot.length) + ents.length by omega))
        iexact H
      · iapply (preceipt_mono (GF := GF) (show B.toNat - γ.reBoot.length ≤
          (plogLastIndexZ (toPState s).base (toPState s).log).toNat - γ.reBoot.length by omega))
        iexact Hrc0
    have Hcnt : rdCount recv = 0 := by
      unfold rdCount; rw [List.countP_eq_zero]
      intro x hx; rw [Hrecv x hx]; simp [absMsg, absMsgFrom]
    imod rdCred_zero (GF := GF) γ with Hz
    imod ghost_step_md γ md c id m s s' _ recv 0 B HBb.2.2 Hrecv Hstep
      (fun _ _ _ _ hmd _ HI => Hpre.dynHyp (fun h => absurd (Hty.symm.trans h) (by w32_ne))
        (fun h => absurd (Hty.symm.trans h) (by w32_ne)) hmd HI)
      (by omega) (Hfr.1.nsst) $$ HrcB Hm' Hz [Htks] Hlc Hghost Hrest with ⟨%md', %Hout, Hghost⟩
    · -- (2026-10-19, D21 M6) the proposal's tickets, for the step that appends or forwards it
      iapply msgsTks_recv γ _ recv Hrecv Hrl
      unfold msgTks
      simp only [absMsg, absMsgFrom, ↓reduceIte]
      iexact Htks
    imodintro
    iapply HΦ $$ %err %s' %c %md'
    iframe Hphys Hghost
    isplitr
    · ipureintro; exact Hwf'
    isplitr
    · ipureintro; exact Hout
    isplitr
    · ipureintro; exact fun _ => rfl
    isplitr
    · ipureintro
      exact ⟨fun _ _ => ⟨Hfr.1, fun _ => Hfr.2, fun h => absurd h (by first | (rw [HtyA]; w32_ne) | (rw [Hty]; w32_ne)),
          fun h => absurd h (by rw [Hty]; w32_ne)⟩,
        fun h => absurd h (by rw [Hty]; w32_ne)⟩
    isplitr
    · ipureintro; exact fun _ _ _ => ⟨Hfr.2, Hfr.1.2.2.2.1, Hfr.1.2.2.1, Hfr.1.2.2.2.2.1, Hfr.1.2.2.2.2.2.1, Hfr.1.2.2.2.2.2.2.1, Hfr.1.2.2.2.2.2.2.2.1, Hfr.1.2.2.2.2.2.2.2.2.1, Hfr.1.2.2.2.2.2.2.2.2.2.2.1, Hfr.1.2.2.2.2.2.2.2.2.2.2.2⟩
    isplitr
    · ipureintro; exact fun _ => TermStep.of_local Hfr.1 Hpk
    isplitr
    · ipureintro; resp_other
    isplitr
    · ipureintro; exact fun h => absurd h (by rw [Hty]; w32_ne)
    isplitr
    · ipureintro; exact fun h => absurd h (by rw [Hty]; w32_ne)
    icases Herr with (%Herr | #Hd)
    · ileft; ipureintro; exact Herr
    · iright; iframe Hd; ipureintro; exact Hty
  -- every other type: the postcondition is `stepPost`
  simp only [ite_eq_right Hty]
  -- and the entries are read-only: the `by_cases` reduced `"Hents"`'s
  -- `if m.Type' = MsgProp`
  iclear Hents
  -- the two storage acknowledgements (2026-10-05), before the conversion to `stepPost`
  -- below: their postcondition also says what is kept of the physical state
  -- (`LocalStepOk`, 2026-10-09)
  by_cases HtyA : m.Type' = MsgStorageAppendResp
  · obtain ⟨Hsnp, Hle, Hstok, Hghoff⟩ := Hsar HtyA
    rcases Option.eq_none_or_eq_some sn with Hsn | ⟨sv, Hsv⟩
    · -- MsgStorageAppendResp without a snapshot: `stableTo`, invisible to the protocol.
      have Hstok' : m.Term' = W64 0 ∨ m.Term' = s.term → m.Index' ≠ W64 0 →
          StableOk s.logst (entryID.mk m.LogTerm' m.Index') := by
        intro a b; have := Hstok a b; rw [Hsn] at this; exact this
      wp_apply (wp_Step_MsgStorageAppendResp_none P Q c r id s ml m sn ctx rs ents HtyA Hsn Hle
          Hstok' Hghoff Hwf)
        $$ [$Hphys $Hmi]
        as %err %s' ⟨Hphys, %Hwf', %Hfr, %Happ0, %Hpk, %Hst, %Herr⟩
      imod ghost_step_md0 γ md c id m s s' Hst
        (fun _ _ _ _ hmd _ HI => Hpre.dynHyp (fun h => absurd (HtyA.symm.trans h) (by w32_ne))
          (fun h => absurd (HtyA.symm.trans h) (by w32_ne)) hmd HI) Hfr.1.nsst
        $$ Hlc Hghost Hrest with ⟨%md', %Hout, Hghost⟩
      imodintro
      iapply HΦ $$ %err %s' %c %md'
      iframe Hphys Hghost
      isplitr
      · ipureintro; exact Hwf'
      isplitr
      · ipureintro; exact Hout
      isplitr
      · ipureintro; exact fun _ => rfl
      isplitr
      · ipureintro
        exact ⟨fun _ _ => ⟨Hfr.1, fun _ => Hfr.2, fun h => absurd h (by first | (rw [HtyA]; w32_ne) | (rw [Hty]; w32_ne)),
          fun _ => Happ0⟩,
          fun _ sv h => absurd (Hsn.symm.trans h) (by simp)⟩
      isplitr
      · ipureintro; exact fun _ _ _ => ⟨Hfr.2, Hfr.1.2.2.2.1, Hfr.1.2.2.1, Hfr.1.2.2.2.2.1, Hfr.1.2.2.2.2.2.1, Hfr.1.2.2.2.2.2.2.1, Hfr.1.2.2.2.2.2.2.2.1, Hfr.1.2.2.2.2.2.2.2.2.1, Hfr.1.2.2.2.2.2.2.2.2.2.2.1, Hfr.1.2.2.2.2.2.2.2.2.2.2.2⟩
      isplitr
      · ipureintro; exact fun _ => TermStep.of_local Hfr.1 Hpk
      isplitr
      · ipureintro; exact RespStep.of_type (by rw [HtyA]; w32_ne) (by rw [HtyA]; w32_ne)
          (by rw [HtyA]; w32_ne)
      isplitr
      · ipureintro; exact fun h => absurd h (by rw [HtyA]; w32_ne)
      isplitr
      · ipureintro; exact fun h => absurd h (by rw [HtyA]; w32_ne)
      ileft; ipureintro; exact Herr
    · -- (D22 S-d2) with a snapshot: `appliedSnap` (after `stableTo` in the current-term arm),
      -- invisible to the protocol, in the static mode
      subst Hsv
      obtain ⟨Hhit, Hle', Hrole, Hmode, Hsxp, Hkxp⟩ := Hsnp sv rfl
      have Hscope : SnapScope sv sv.Metadata'.ConfState'.lists := by
        rcases Hmode with ⟨-, h⟩ | h
        · exact h.1
        · cases md with
          | static => exact h.elim
          | dyn => exact h.1
      -- (2026-10-28, stage U0) `appliedSnap`'s rebuild: a follower's tally is empty
      ihave %Hfv0 := ownRaftGhost_follower_votes γ id (toPState s) $$ Hghost
      have Hvotes : s.votes = ∅ := followerVotesOk_phys s Hfv0 Hrole
      wp_apply (wp_Step_MsgStorageAppendResp_snap P Q c r id s ml m sv ctx rs ents HtyA Hhit Hle'
          Hrole Hvotes Hscope Hle Hstok Hghoff Hwf Hsxp Hkxp)
        $$ [$Hphys $Hmi] as %err ⟨Hphys, %Herr⟩
      icases Hphys with ⟨%prs, %pvs, %il, Hphys⟩
      obtain ⟨Hp1, Hp2, Hp3, Hp4, Hp5⟩ := ackSnapLog_proto s.logst m s.term sv
      have Hps : toPState { s with logst := ackSnapLog s.logst m s.term sv, progress := prs,
                                   prvals := pvs, isLearner := il } = toPState s := by
        simp only [toPState, Hp1, Hp2, Hp3, Hrole]; rfl
      -- the node at the snapshot's configuration: statically `SnapAckOk`, (2026-10-28, stage U3)
      -- dynamically `SnapAckDyn` (`StepR.applySnap`)
      obtain ⟨Hsa1, Hsa2⟩ := ackSnapLog_snapAck s.logst m s.term sv
      have Hmode' : (md.isDyn = false ∧ CfgStatic γ (snapCfg sv sv.Metadata'.ConfState'.lists) ∧
            TrackedOk γ (snapCfg sv sv.Metadata'.ConfState'.lists) id) ∨
          (∃ dec c0 h0 g, md = .dyn dec c0 h0 g ∧
            s.role = .follower ∧
            (ackSnapLog s.logst m s.term sv).applied = sv.Metadata'.Index' ∧
            uint.Z s.logst.applied < uint.Z sv.Metadata'.Index' ∧
            uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.prev.index' ∧
            ((ackSnapLog s.logst m s.term sv).snap = none →
              sv.Metadata'.Index' = s.logst.prev.index') ∧
            ∃ cs', cfgFold (effDec dec g.decs) c0 (g.fp.take (uint.nat sv.Metadata'.Index')) = some cs' ∧
              cs'.cfg = snapCfg sv sv.Metadata'.ConfState'.lists) := by
        rcases Hmode with ⟨h1, h2⟩ | h
        · exact .inl ⟨h1, h2.2⟩
        · right
          cases md with
          | static => exact h.elim
          | dyn dec c0 h0 g =>
            obtain ⟨-, Hlt, Hsn, cs', Hf, Hc⟩ := h
            refine ⟨dec, c0, h0, g, rfl, Hrole, ?_, Hlt, Hle', fun h => Hsn (Hsa2 h), cs', Hf, Hc⟩
            rw [Hsa1]; unfold w64Max; split <;> word
      imod ghost_step_snapack γ md c (snapCfg sv sv.Metadata'.ConfState'.lists) id m s
        { s with logst := ackSnapLog s.logst m s.term sv, progress := prs, prvals := pvs,
                 isLearner := il } sv.Metadata'.Index' HtyA Hps rfl ⟨rfl, Hp4⟩ Hmode'
        $$ Hlc Hghost Hrest with ⟨%md', ⟨%Hout, %Hmd'⟩, Hghost⟩
      imodintro
      iapply HΦ $$ %err %_ %_ %md'
      iframe Hphys Hghost
      isplitr
      · ipureintro; exact Hwf
      isplitr
      · ipureintro; exact Hout
      isplitr
      · ipureintro; exact fun h => absurd (h HtyA) (by simp)
      isplitr
      · ipureintro
        exact ⟨fun h => absurd (h HtyA) (by simp),
          fun _ sv' h => by cases h; exact ⟨rfl, ⟨prs, pvs, il, rfl⟩, Hmd'⟩⟩
      isplitr
      · ipureintro; exact fun _ _ h => absurd (h HtyA) (by simp)
      isplitr
      · ipureintro
        obtain ⟨Hk1, Hk2⟩ := ackSnapLog_keep s.logst m s.term sv
        exact fun _ => TermStep.of_term rfl (fun _ => Hp5)
          ⟨fun h => ⟨rfl, .inl ⟨h, Hp1, Hp2, Hp3, Hk1, Hk2⟩⟩, fun h1 h2 => ⟨h1, fun hn => h2 (Hk1 hn)⟩⟩
      isplitr
      · ipureintro; exact RespStep.of_type (by rw [HtyA]; w32_ne) (by rw [HtyA]; w32_ne)
          (by rw [HtyA]; w32_ne)
      isplitr
      · ipureintro; exact fun h => absurd h (by rw [HtyA]; w32_ne)
      isplitr
      · ipureintro; exact fun h => absurd h (by rw [HtyA]; w32_ne)
      ileft; ipureintro; exact Herr
  by_cases HtyB : m.Type' = MsgStorageApplyResp
  · -- MsgStorageApplyResp: `appliedTo`, and (2026-10-29, stage U5) a leader's automatic leave,
    -- whose proposal is received (`recv`) when appended: `isMessage_leave`, no ticket.
    -- `Hents` is already read-only: the `MsgProp` case split reduced its `if`
    ihave %HlnzB : ⌜s.role = .leader → s.term ≠ W64 0⌝ $$ [Hghost]
    · by_cases hl : s.role = .leader
      · ihave %H := ownRaftGhost_term_nz γ id (toPState s)
          (by rw [toPState_role, hl]; decide) $$ Hghost
        ipureintro; exact fun _ => H
      · ipureintro; exact fun h => absurd h hl
    ihave ⟨#Hlr, %HL⟩ := ownRaftGhost_lastRec γ id (toPState s) $$ Hghost
    imod lastRec_receipt γ _ $$ Hlr with #Hrc0
    wp_apply (wp_Step_MsgStorageApplyResp P Q c r id s ml m sn ctx rs ents _ HtyB (Hsapr HtyB)
        (Happly HtyB) Hwf HlnzB HL) $$ [$Hphys $Hmi $Hrc0]
      as %err %s' %B %recv ⟨Hphys, %Hwf', %Hfr, %Hpk, %Hrecv, %HBb, Hrcb, %Hst, %Happ', %Happ2,
        %Herr⟩
    -- the receipt of the bound: the last index's, or the leave's entry's
    ihave #HrcB : ⧖ (B.toNat - γ.reBoot.length) $$ [Hrcb]
    · by_cases hlt : plogLastIndexZ (toPState s).base (toPState s).log < B
      · ihave #H := Hrcb $$ %hlt
        have Hpl : plogLastIndexZ (toPState s).base (toPState s).log =
            plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) := rfl
        iapply (preceipt_mono (GF := GF) (show B.toNat - γ.reBoot.length ≤
          ((plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents)).toNat
            - γ.reBoot.length) + 1 by
            have := HBb.2.1
            omega))
        iexact H
      · iapply (preceipt_mono (GF := GF) (show B.toNat - γ.reBoot.length ≤
          (plogLastIndexZ (toPState s).base (toPState s).log).toNat - γ.reBoot.length by omega))
        iexact Hrc0
    have Hcnt : rdCount recv = 0 := by
      unfold rdCount; rw [List.countP_eq_zero]
      intro x hx; rw [Hrecv.1 x hx]; simp [leaveAbs, absMsg, absMsgFrom]
    imod rdCred_zero (GF := GF) γ with Hz
    ihave #Hml := isMessage_leave (GF := GF) γ
    imod ghost_step_md γ md c id m s s' leaveAbs recv 0 B HBb.2.2 Hrecv.1 Hst
      (fun _ _ _ _ hmd _ HI => Hpre.dynHyp (fun h => absurd (HtyB.symm.trans h) (by w32_ne))
        (fun _ => Happ') hmd HI)
      (by omega) Hfr.1.nsst $$ HrcB Hml Hz [] Hlc Hghost Hrest with ⟨%md', %Hout, Hghost⟩
    · iapply msgsTks_recv γ _ recv Hrecv.1 Hrecv.2
      iapply msgTks_leave
    imodintro
    iapply HΦ $$ %err %s' %c %md'
    iframe Hphys Hghost
    isplitr
    · ipureintro; exact Hwf'
    isplitr
    · ipureintro; exact Hout
    isplitr
    · ipureintro; exact fun _ => rfl
    isplitr
    · ipureintro
      exact ⟨fun _ _ => ⟨Hfr.1, fun H => Hfr.2 (H HtyB), fun _ => Happ2,
          fun h => absurd h (by rw [HtyB]; w32_ne)⟩,
        fun h => absurd h (by rw [HtyB]; w32_ne)⟩
    isplitr
    · ipureintro; exact fun _ h => absurd HtyB h
    isplitr
    · ipureintro; exact fun _ => TermStep.of_local Hfr.1 Hpk
    isplitr
    · ipureintro; exact RespStep.of_type (by rw [HtyB]; w32_ne) (by rw [HtyB]; w32_ne)
        (by rw [HtyB]; w32_ne)
    isplitr
    · ipureintro; exact fun h => absurd h (by rw [HtyB]; w32_ne)
    isplitr
    · ipureintro; exact fun h => absurd h (by rw [HtyB]; w32_ne)
    ileft; ipureintro; exact Herr
  by_cases Hns : m.Type' = MsgSnap
  · -- MsgSnap: `dispatch_Snap`, with the snapshot from `"Hsnap"` (either mode since 2026-10-14,
    -- stage B8); (2026-10-20, D22 S-c) its continuation `snapPost`, with the snapshot's frame
    ihave HΦs : ▷ snapPost γ md c r id s m sn Φ $$ [HΦ Hlc]
    · inext
      unfold snapPost
      iframe Hlc
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hresp', %Hsf, %Herr⟩
      iapply HΦ $$ %err %s' %c' %md'
      iframe Hphys Hghost
      ihave Herr' : (⌜err = interface.nil⌝ ∨
          (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err) : IProp GF) $$ []
      · ileft; ipureintro; exact Herr
      iframe Herr'
      ipureintro
      exact ⟨Hwf', Href, fun _ => Hsf.2.1,
        ⟨fun _ Hl => by rcases Hl with h | h | h <;> contradiction,
         fun h => absurd h (by rw [Hns]; w32_ne)⟩,
        fun h => absurd Hns h, fun h => absurd Hns h, Hresp', fun _ => ⟨Hsf.1, Hsf.2.2⟩,
        fun h => absurd h (by rw [Hns]; w32_ne)⟩
    icases Hsnap $$ %Hns with ⟨%sv, %scfg, %Hsc, #Hm', #Hdat⟩
    obtain ⟨Hsn, Hcl, Hidx⟩ := Hsc
    have Hnsf : s.gh.ns = false := Hnsx Hns
    iapply dispatch_Snap P Q γ md c r id s ml m ents sn ctx rs sv scfg Φ Hwf Hns (Hsnapt Hns) Hidx Hsn Hcl Hnsf
      $$ Hinit Hphys Hghost Hrest Hmi Hm' Hdat HΦs
  -- (D22 S-d3b, 2026-10-21) MsgApp: `dispatch_App`, with the truncation's mark (`AppTrunc`), which
  -- `stepPost` does not carry
  by_cases HtyApp : m.Type' = MsgApp
  · have Hdh : ∀ s', DynHypFor md m s s' := fun _ _ _ _ _ hmd _ HI =>
      Hpre.dynHyp Hns (fun h => absurd h HtyB) hmd HI
    ihave HΦa : ▷ stepPostT γ md c r id s m (AppTrunc m ents s) Φ $$ [HΦ Hlc]
    · inext
      unfold stepPostT
      iframe Hlc
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hc', %Hfr', %Htm', %Hresp', %Htr,
        Herr⟩
      iapply HΦ $$ %err %s' %c' %md'
      iframe Hphys Hghost Herr
      ipureintro
      exact ⟨Hwf', Href, fun _ => Hc' Hns, ⟨fun _ Hl => by rcases Hl with h | h | h <;> contradiction,
          fun h => absurd h HtyA⟩,
        fun h _ _ => Hfr' h, Htm', Hresp', fun h => absurd h Hns, fun _ => Htr⟩
    ihave #Hm' := Hmsg0 $$ %MsgType.app %(by rw [HtyApp]; exact mtypeOf_MsgApp) %(by decide)
    rw [isMessage_absMsg_ctx γ .app m ents ctx (And.intro (by decide) (by decide))]
    iapply dispatch_App P Q γ c r id s ml m ents sn ctx rs Φ md Hdh Hwf HtyApp (Happ HtyApp)
      $$ Hinit Hphys Hghost Hrest Hmi Hm' HΦa
  ihave HΦ : ▷ stepPost γ md c r id s m Φ $$ [HΦ Hlc]
  · inext
    unfold stepPost
    iframe Hlc
    iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hc', %Hfr', %Htm', %Hresp', Herr⟩
    iapply HΦ $$ %err %s' %c' %md'
    iframe Hphys Hghost Herr
    ipureintro
    -- `LocalStepOk` is about the three types handled above, `SnapStep` about the snapshot
    exact ⟨Hwf', Href, fun _ => Hc' Hns, ⟨fun _ Hl => by rcases Hl with h | h | h <;> contradiction,
        fun h => absurd h HtyA⟩,
      fun h _ _ => Hfr' h, Htm', Hresp', fun h => absurd h Hns, fun h => absurd h HtyApp⟩
  -- the remaining types are no storage acknowledgement and no snapshot: the dynamic premises
  -- from `Hpre`
  have Hdh : ∀ s', DynHypFor md m s s' := fun _ _ _ _ _ hmd _ HI =>
    Hpre.dynHyp Hns (fun h => absurd h HtyB) hmd HI
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
    obtain ⟨Hmterm, Hnowrap, Htc, Hfla⟩ := Hhup Hty
    wp_apply (wp_Step_MsgHup P PB c r id s ml m ents sn ctx rs Hty Hmterm Hnowrap Htc Hwf Hfla) $$ [$Hphys $Hmi]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    iapply finish_branch0 γ md c r id s s' m err Φ (Hdh s') Hwf' Hst (fun _ => Hfr) (fun _ => Htm)
      (by resp_other) Hfr.nsst $$ Hghost Hrest Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgVote
  · -- MsgVote: answer the vote request, stepping down first if needed.
    obtain ⟨Hto, Hterm, Hfnz⟩ := Hvote Hty
    ihave #Hm' := Hmsg $$ %MsgType.vote %(by rw [Hty]; exact mtypeOf_MsgVote) %(And.intro (by decide) (by decide))
    wp_apply (wp_Step_MsgVote P PB c r id s ml m ents sn ctx rs Hty Hto Hterm Hfnz Hwf) $$ [$Hphys $Hmi]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ md c r id s s' m _ recv err Φ (Hdh s') Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) (by resp_other) Hfr.nsst $$ Hm' Hghost Hrest Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgVoteResp
  · -- MsgVoteResp: tally the vote, possibly winning or losing.
    obtain ⟨Hto, Hterm⟩ := Hvoteresp Hty
    ihave #Hm' := Hmsg $$ %MsgType.voteResp %(by rw [Hty]; exact mtypeOf_MsgVoteResp) %(And.intro (by decide) (by decide))
    -- (2026-10-18, D19b stage 5) the receipt of the log's last index (`lastRec`), raised by one
    -- in the step for a win's entry
    ihave ⟨#Hlr, %HL⟩ := ownRaftGhost_lastRec γ id (toPState s) $$ Hghost
    imod lastRec_receipt γ _ $$ Hlr with #Hrc0
    wp_apply (wp_Step_MsgVoteResp P PB c r id s ml m ents sn ctx rs _ Hty Hto Hterm Hwf HL)
      $$ [$Hphys $Hmi $Hrc0]
      as %err %s' %B ⟨Hphys, %HBb, #Hrcb, %Hwf', %Hst, %Herr, %Hresp, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branchB γ md c r id s s' m _ recv err Φ B HBb.2.2 (Hdh s') Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) Hresp Hfr.nsst $$ [] Hm' Hghost Hrest Hphys [] HΦ
    · have Hpl : plogLastIndexZ (toPState s).base (toPState s).log =
          plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) := rfl
      iapply (preceipt_mono (GF := GF) (show B.toNat - γ.reBoot.length ≤
        ((plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents)).toNat
          - γ.reBoot.length) + 1 by omega))
      iexact Hrcb
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgPreVote
  · -- MsgPreVote (2026-10-04): answered with a free `MsgPreVoteResp`; nothing
    -- received, nothing recorded.
    obtain ⟨Hto, Hterm, Hfnz, Hfid, Hutd0, Hptc⟩ := Hprevote Hty
    wp_apply (wp_Step_MsgPreVote P PB c r id s ml m ents sn ctx rs Hty Hto Hterm Hfnz Hfid Hwf Hutd0 Hptc)
      $$ [$Hphys $Hmi] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    iapply finish_branch0 γ md c r id s s' m err Φ (Hdh s') Hwf' Hst (fun _ => Hfr) (fun _ => Htm)
      (by resp_other) Hfr.nsst $$ Hghost Hrest Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgPreVoteResp
  · -- MsgPreVoteResp (2026-10-04): a pre-candidate's tally, or a step-down on a
    -- rejection of a higher term.
    obtain ⟨Hto, Hterm, -, Hnw⟩ := Hprevoteresp Hty
    ihave #Hm' := Hmsg $$ %MsgType.preVoteResp %(by rw [Hty]; exact mtypeOf_MsgPreVoteResp) %(And.intro (by decide) (by decide))
    wp_apply (wp_Step_MsgPreVoteResp P PB c r id s ml m ents sn ctx rs Hty Hto Hterm Hnw Hwf)
      $$ [$Hphys $Hmi] as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hresp, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ md c r id s s' m _ recv err Φ (Hdh s') Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) Hresp Hfr.nsst $$ Hm' Hghost Hrest Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgAppResp
  · -- MsgAppResp: `dispatch_AppResp`.
    ihave #Hm' := Hmsg $$ %MsgType.appResp %(by rw [Hty]; exact mtypeOf_MsgAppResp) %(And.intro (by decide) (by decide))
    icases ghostRest_nsLink γ md c id s $$ Hrest with ⟨%Hnl, Hrest⟩
    iapply dispatch_AppResp P Q γ c r id s ml m ents sn ctx rs Φ md Hdh Hwf Hty (Happresp Hty) Hnl.boot
      $$ Hinit Hphys Hghost Hrest Hmi Hm' HΦ
  by_cases Hty : m.Type' = MsgHeartbeat
  · -- MsgHeartbeat: `dispatch_Heartbeat`.
    ihave #Hm' := Hmsgc $$ %MsgType.heartbeat %(by rw [Hty]; exact mtypeOf_MsgHeartbeat)
    iapply dispatch_Heartbeat P Q γ c r id s ml m ents sn ctx rs Φ md Hdh Hwf Hty (Hhb Hty)
      $$ Hinit Hphys Hghost Hrest Hmi Hm' HΦ
  by_cases Hty : m.Type' = MsgHeartbeatResp
  · -- MsgHeartbeatResp: `dispatch_HeartbeatResp`, with its context (2026-10-13).
    ihave #Hm' := Hmsgc $$ %MsgType.heartbeatResp
      %(by rw [Hty]; exact mtypeOf_MsgHeartbeatResp)
    iapply dispatch_HeartbeatResp P Q γ c r id s ml m ents sn ctx rs Φ md Hdh Hwf Hty (Hhbresp Hty)
      $$ Hinit Hphys Hghost Hrest Hmi Hm' HΦ
  by_cases Hty : m.Type' = MsgBeat
  · -- MsgBeat: `dispatch_Beat`.
    iapply dispatch_Beat P Q γ c r id s ml m ents sn ctx rs Φ md Hdh Hwf Hty (Hbeat (.inl Hty))
      $$ Hinit Hphys Hghost Hrest Hmi HΦ
  by_cases Hty : m.Type' = MsgCheckQuorum
  · -- MsgCheckQuorum (2026-10-17): `dispatch_CheckQuorum`.
    iapply dispatch_CheckQuorum P Q γ c r id s ml m ents sn ctx rs Φ md Hdh Hwf Hty (Hbeat (.inr Hty))
      $$ Hinit Hphys Hghost Hrest Hmi HΦ
  by_cases Hty : m.Type' = MsgReadIndex
  · -- MsgReadIndex (2026-10-13): `dispatch_ReadIndex`, with the request's credit.
    ihave #Hm' := Hmsgc $$ %MsgType.readIndex %(by rw [Hty]; rfl)
    rw [ite_eq_left Hty]
    iapply dispatch_ReadIndex P Q γ c r id s ml m ents sn ctx rs Φ md Hdh Hwf Hty (Hri Hty)
      (Hnors (.inr (.inl Hty)))
      $$ Hinit Hphys Hghost Hrest Hmi Hm' Hcred HΦ
  by_cases Hty : m.Type' = MsgReadIndexResp
  · -- MsgReadIndexResp (2026-10-13): `dispatch_ReadIndexResp`.
    ihave #Hm' := Hmsgc $$ %MsgType.readIndexResp %(by rw [Hty]; rfl)
    iapply dispatch_ReadIndexResp P Q γ c r id s ml m ents sn ctx rs Φ md Hdh Hwf Hty (Hrir Hty)
      $$ Hinit Hphys Hghost Hrest Hmi Hm' HΦ
  -- (2026-10-13) the types outside the model: a free message justifies a step-down
  ihave #Hsd := isMessage_stepdown (GF := GF) γ id m
  obtain ⟨Hloc, Htn, Htl⟩ := Hrest
  by_cases HtyL : m.Type' = MsgForgetLeader ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus
  · -- the local reports and `ForgetLeader`
    ihave %Hfv0 := ownRaftGhost_follower_votes γ id (toPState s) $$ Hghost
    have Hfv : s.role = .follower → s.votes = ∅ := followerVotesOk_phys s Hfv0
    wp_apply (wp_Step_MsgLocal P PB c r id s ml m ents sn ctx rs HtyL (Hloc HtyL) Hwf Hfv) $$ [$Hphys $Hmi]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    have Hn : m.Type' ≠ MsgVoteResp ∧ m.Type' ≠ MsgAppResp ∧ m.Type' ≠ MsgPreVoteResp := by
      rcases HtyL with h | h | h <;> rw [h] <;> exact ⟨by w32_ne, by w32_ne, by w32_ne⟩
    iapply finish_branch γ md c r id s s' m _ recv err Φ (Hdh s') Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) (RespStep.of_type Hn.1 Hn.2.1 Hn.2.2) Hfr.nsst
      (by simp [stepdownMsg, Msg.plain]) (by simp [stepdownMsg, Msg.plain]) $$ Hsd Hghost Hrest Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgTransferLeader
  · -- leader transfer: a request
    obtain ⟨Hent, Hctx0, Htr, Hxo⟩ := Htl Hty
    ihave %Hlok0 := ownRaftGhost_lead_ok γ id (toPState s) $$ Hghost
    have Hlok : s.role = .follower → s.lead ≠ id := by
      intro Hf
      rw [← toPState_lead_nonpre s (by rw [Hf]; decide)]
      apply Hlok0
      rw [toPState_role, Hf]; decide
    -- (2026-10-29, stage U7) a leader's term past `0`, for `send`'s stamp (`stepLeader`'s premise)
    have HLT_lem : ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md.isDyn -∗
        ⌜s.role = .leader → s.term ≠ W64 0⌝ := by
      iintro Hg
      by_cases hl : s.role = .leader
      · ihave %H := ownRaftGhost_term_nz γ id (toPState s)
          (by rw [toPState_role, hl]; decide) $$ Hg
        ipureintro; exact fun _ => H
      · ipureintro; exact fun h => absurd h hl
    ihave %HLT := HLT_lem $$ Hghost
    wp_apply (wp_Step_MsgTransferLeader P PB c r id s ml m ents sn ctx rs Hty Hent Hctx0 Hxo Htr Hlok Hwf
      (Hnors (.inr (.inr Hty))) HLT) $$ [$Hphys $Hmi]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ md c r id s s' m _ recv err Φ (Hdh s') Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) (by resp_other) Hfr.nsst
      (by simp [stepdownMsg, Msg.plain]) (by simp [stepdownMsg, Msg.plain]) $$ Hsd Hghost Hrest Hphys [] HΦ
    ileft; ipureintro; exact Herr
  by_cases Hty : m.Type' = MsgTimeoutNow
  · -- leader transfer: the transferee campaigns
    obtain ⟨Hnw, Hnwm, Hfla⟩ := Htn Hty
    wp_apply (wp_Step_MsgTimeoutNow P PB c r id s ml m ents sn ctx rs Hty Hnw Hnwm Hwf Hfla) $$ [$Hphys $Hmi]
      as %err %s' ⟨Hphys, %Hwf', %Hst, %Herr, %Hfr, %Htm⟩
    obtain ⟨recv, Hrecv, Hstep⟩ := Hst
    iapply finish_branch γ md c r id s s' m _ recv err Φ (Hdh s') Hwf' Hrecv Hstep
      (fun _ => Hfr) (fun _ => Htm) (by resp_other) Hfr.nsst
      (by simp [stepdownMsg, Msg.plain]) (by simp [stepdownMsg, Msg.plain]) $$ Hsd Hghost Hrest Hphys [] HΦ
    ileft; ipureintro; exact Herr
  -- none of the twenty-two (the two storage acknowledgements were handled above)
  exfalso
  simp only [StepMsg, stepMsgTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at Hsm
  rcases Hsm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h <;> first | contradiction | exact HtyL (by simp [h])

end dispatch

end EtcdGrove
end Perennial
