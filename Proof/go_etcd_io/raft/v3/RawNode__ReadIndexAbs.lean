/-
Antithesis parity B1, phase 2 (#33, `notes/antithesis-parity-design.md` §4). **`RawNode.ReadIndex`, the
strengthened triple** (`RawNode.ReadIndex.absSpec`, `RawNodeAbsSpecs.lean`). The proof is
`RawNode__ReadIndex.lean`'s (the deposit, the request's message with its one-entry batch), over
`ownRawNodeAt` at a mode `md` with reads, without snapshots or configuration changes, `raft.Step` at the
no-snapshot flag (`raft.Step.untracedNs`). Its end state (`StepEnd` on a local `MsgReadIndex`) is the
start state but for the outbox, the read state and `Progress` values of the same `Match` (`RdFrame`):
a leader defers the request, answers it at once (a single voter) or queues it with heartbeats; a follower
with a leader forwards it; anything else drops it (`readIdxEnd_of_stepEnd`: `ReadIdxEnd`, the
`MsgReadIndex` arm of `HandleEnd`).
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__ReadIndex
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Proof.go_etcd_io.raft.v3.TracedUntracedRaftStep
public import Proof.go_etcd_io.raft.v3.RaftStepNoSnap
public import Proof.go_etcd_io.raft.v3.RawNodeAtScope
public import Proof.go_etcd_io.raft.v3.RawNodeReadyAt
public import Proof.go_etcd_io.raft.v3.StepEndIp
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgReadIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- What a `MsgReadIndex` step leaves of the state: all but the outbox (no `MsgSnap` added), the read
state and `Progress` values of the same `Match`. -/
def RdFrame (s s' : NState) : Prop :=
  ∃ (o : List Msg) (rd : RdState) (pvs : GMap w64 Progress),
    s' = { s with outbox := o, rd := rd, prvals := pvs } ∧ prvalsMatch pvs = prvalsMatch s.prvals ∧
    ∀ x ∈ o, x ∈ s.outbox ∨ x.ty ≠ .snap

theorem RdFrame.refl (s : NState) : RdFrame s s :=
  ⟨s.outbox, s.rd, s.prvals, rfl, rfl, fun _ hx => .inl hx⟩

/-- A frame that only appends messages of other types. -/
theorem RdFrame.send (s : NState) (ms : List Msg) (h : ∀ x ∈ ms, x.ty ≠ .snap) :
    RdFrame s (sendMsgs s ms) :=
  ⟨s.outbox ++ ms, s.rd, s.prvals, rfl, rfl, fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact .inl hx
    · exact .inr (h x hx)⟩

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- `m.Type' = MsgReadIndex` (`hty`) refutes a hypothesis `h` about another type. -/
local macro "ri_absurd" : tactic => `(tactic| (rw [hty] at h; simp [MsgUnreachable, MsgHup, MsgBeat,
  MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgSnap, MsgHeartbeat, MsgHeartbeatResp,
  MsgSnapStatus, MsgCheckQuorum, MsgTransferLeader, MsgTimeoutNow, MsgReadIndex, MsgReadIndexResp,
  MsgPreVote, MsgPreVoteResp, MsgStorageAppendResp, MsgStorageApplyResp, MsgForgetLeader] at h))

set_option maxHeartbeats 1000000 in
/-- **The end state of a local `MsgReadIndex`** (`StepEnd`, term `0`): `ReadIdxEnd` at the protocol
reading, and the state framed (`RdFrame`). `hpc`: the progress map tracks the configuration's ids
(`ownRaftPhysC_trkDoms`), so a leader's heartbeats go to peers of `c`. -/
theorem readIdxEnd_of_stepEnd {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hty : m.Type' = MsgReadIndex) (hT0 : m.Term' = W64 0)
    (hpc : domSet s.progress = c.ids) (h : StepEnd c id m ents ctx s s') :
    ReadIdxEnd c id (toPState s) (absMsg .readIndex m ents ctx) (toPState s') ∧ RdFrame s s' := by
  have hnbf : ¬ PreBF m s := by
    unfold PreBF; rw [hT0]; intro h'; have := h'.1; simp at this
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hety : StepEndTy m.Type' := by unfold StepEndTy; simp [hty]
  have hnh : m.Type' ≠ MsgHup := fun h => by ri_absurd
  have hnv : m.Type' ≠ MsgVote := fun h => by ri_absurd
  have hnp : m.Type' ≠ MsgProp := fun h => by ri_absurd
  obtain ⟨pvs0, hfn⟩ := (h hety (by xtrec_tac)).2.2.2 (fun h' => h'.1 hT0) hnh hnv
  rw [hpre pvs0] at hfn
  obtain ⟨hf, hc, hl⟩ := hfn
  cases hr : s.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    obtain ⟨-, -, Hs1⟩ := StepProof.followerStepResult_readIndex c id s m ents sv d s' ctx hty hres
    have Hpr : (toPState s).role = .follower := by simp [toPState, hr, proleRole]
    have Hld : (toPState s).lead = s.lead := toPState_lead_nonpre s (by rw [hr]; exact PRole.noConfusion)
    by_cases Hl0 : s.lead = W64 0
    · rw [if_pos Hl0] at Hs1; subst s'
      refine ⟨?_, RdFrame.refl s⟩
      unfold ReadIdxEnd
      rw [if_neg (by rw [Hpr]; decide), if_neg (by rw [Hld]; exact fun h => h.2 Hl0)]
    · rw [if_neg Hl0] at Hs1; subst s'
      refine ⟨?_, RdFrame.send s _ (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; simp [readForward])⟩
      unfold ReadIdxEnd
      rw [if_neg (by rw [Hpr]; decide), if_pos ⟨Hpr, by rw [Hld]; exact Hl0⟩,
        toPState_sendMsgs, Hld]
      congr 2
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    obtain ⟨-, -, Hs1⟩ := StepProof.candidateStepResult_readIndex c id s m ents sv d s' ctx (.inl hty) hres
    subst s'
    refine ⟨?_, RdFrame.refl s⟩
    unfold ReadIdxEnd
    simp [toPState, hr, proleRole]
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    obtain ⟨-, -, Hs1⟩ := StepProof.candidateStepResult_readIndex c id s m ents sv d s' ctx (.inl hty) hres
    subst s'
    refine ⟨?_, RdFrame.refl s⟩
    unfold ReadIdxEnd
    simp [toPState, hr, proleRole]
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    have Hpr : (toPState s).role = .leader := by simp [toPState, hr, proleRole]
    have Hrd := StepProof.toPState_rd_leader' s hr
    unfold LeaderStepResultC at hres
    rw [if_neg hnp] at hres
    obtain ⟨-, hres⟩ := hres
    unfold LeaderNonpropResultC at hres
    rcases hres with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, Hri⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    rotate_left 3
    all_goals try (exfalso; ri_absurd; done)
    rcases Hri with ⟨Hnct, rfl⟩ | ⟨Hct, ⟨Hsg, rfl⟩ | ⟨Hns, ms, pvs, rfl, Hms, Hpm⟩⟩
    · -- no entry of the term committed: deferred
      refine ⟨?_, ⟨s.outbox, _, s.prvals, rfl, rfl, fun _ hx => .inl hx⟩⟩
      unfold ReadIdxEnd
      rw [if_pos Hpr]
      refine .inl ⟨by simpa [toPState, hr] using Hnct, m, rfl, ?_⟩
      rw [Hrd]; simp [toPState, hr, absMsg, absMsgFrom]
    · -- the leader the single voter: answered at once
      refine ⟨?_, ?_⟩
      · unfold ReadIdxEnd
        rw [if_pos Hpr]
        refine .inr (.inl ⟨by simpa [toPState, hr] using Hct, Hsg, ?_⟩)
        have e : readRespond id s (arriveReq s m ents) = readRespondAll id s [arriveReq s m ents] := rfl
        rw [e, StepProof.toPState_readRespondAll id s hr]
        first
          | rfl
          | (simp only [absMsg, absMsgFrom, toPState, arriveReq, hr]; rfl)
          | simp [absMsg, absMsgFrom, toPState, arriveReq, hr]
      · unfold readRespond
        split
        · split
          · exact ⟨s.outbox, _, s.prvals, rfl, rfl, fun _ hx => .inl hx⟩
          · exact RdFrame.refl s
        · exact RdFrame.send s _ (fun x hx => by
            simp only [List.mem_singleton] at hx; subst hx; simp)
    · -- queued, the heartbeats with the queue's new position
      refine ⟨?_, ⟨s.outbox ++ ms, _, pvs, rfl, Hpm, fun x hx => ?_⟩⟩
      · unfold ReadIdxEnd
        rw [if_pos Hpr]
        refine .inr (.inr ⟨by simpa [toPState, hr] using Hct, ?_, ms, fun x hx => ?_, ?_⟩)
        · exact Hns
        · obtain ⟨Hhb, Hcx, Hsh⟩ := Hms x hx
          obtain ⟨hi, hlt, he, hd⟩ := Hsh
          refine ⟨⟨Hhb, hi, hlt, he, by rw [← hpc]; exact hd⟩, ?_⟩
          rw [Hcx]
          simp [arriveReq, toPState, hr, absMsg, absMsgFrom]
        · rw [toPState_prvals (sendMsgs (arriveState id s m ents) ms) pvs (fun _ => Hpm),
            toPState_sendMsgs]
          congr 1
          simp [arriveState, arriveReq, toPState, hr, absMsg, absMsgFrom]
      · rcases List.mem_append.1 hx with hx | hx
        · exact .inl hx
        · exact .inr (by rw [(Hms x hx).1.1]; simp)

/-- A premise of `Step` about another message type: `MsgReadIndex` (`W32 15`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndexResp, MsgForgetLeader,
  MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

set_option maxHeartbeats 2000000 in
/-- **`RawNode.ReadIndex`, strengthened** (`RawNode.ReadIndex.absSpec`). -/
theorem RawNode.ReadIndex.wp_absProof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.ReadIndex.absSpec (GF := GF) (hG := hG) := by
  have wp_raft_StepNs := raft.Step.untracedNs wp_raft_Step
  intro md hsn hcc γ rn id rs ps qs ip rctx c Qr L0 hrd HtrG
  have hreads : md.reads = true := hrd md rfl
  wp_start as H
  iNamed H
  iNamed Hrn
  -- the scope at `md`: no snapshot, and without configuration changes no automatic leave
  icases rnScopeAt_someMd md rs s $$ Hsc with ⟨%Hscp, #Hcap0, Hsc⟩
  ihave #Hcap := Hcap0 $$ %hsn
  obtain ⟨Hrsc, Hcin, -, -⟩ := Hscp
  obtain ⟨-, Hprev, -, Hnsq⟩ := Hrsc.2.2.2.2.1 hsn
  icases ownRaftPhysC_ackScope cf rnv.raft' id s $$ Hphys with ⟨%Hal0, Hphys⟩
  icases ownStepGhost_cfgScope γ rs fp _ cf id s $$ Hghost with ⟨%Hcfm, Hghost⟩
  icases ownRaftPhysC_trkDoms cf rnv.raft' id s $$ Hphys with ⟨%Htd, Hphys⟩
  have Hcfe : rs.cfg.cfg = cf := Hcfm.2 Hcin.2.2.2
  have Hal : AckScope cf := by
    have ho := Hrsc.1 hcc Hcin.2.2.2
    rw [Hcfe] at ho
    exact Hal0 ho
  have Hp0 : uint.Z s.logst.prev.index' = 0 := by rw [Hprev]; rfl
  -- the deposit: the update fired at the global committed log `Lc`
  ihave #Hcinv := ownStepGhost_inv γ _ cf id s $$ Hghost
  imod read_deposit γ c Qr L0 $$ Hcinv Hfr Hau HL0 with ⟨%Lc, %HL0c, #Hrq, #Hrd⟩
  wp_auto_lc 1
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 15) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  wp_apply wp_slice_literal_ex (V := Loc)
  wp_alloc l0 as Hl0
  wp_auto
  iexists [l0]
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, Hsl_cap⟩
  have Hsz : go.arrayLiteralSize [KeyedElement none (ElementLiteralValue
      [KeyedElement (some (KeyField go!"Data")) (ElementExpression go.byte.SliceType #rctx)])] = 1 := rfl
  simp only [Hsz]
  icases ownStepGhost_certLink γ _ cf id s $$ Hghost with ⟨#Hlink, Hghost⟩
  iunfold certLink at Hlink
  icases Hlink with ⟨-, -, %Hszl, %Hmb⟩
  have Hdsz : s.gh.sn.sz = true → (propEntryM c).Data'.length ≤ entBytesMax := fun hs => by
    rw [Hszl] at hs
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
    have := Hmd b hb; have := (Hmb b hb).1
    simp only [propEntryM, entBytesMax]; omega
  imod entRZ_of_struct s.gh.sn.sz l0 (⟨zero_val _, null, null, null, rctx, slice.nil, 0⟩ : raftpb.Entry)
      (propEntryM c) ⊤ rfl Hdsz $$ [Hl0] with #He
  · iframe Hl0
    simp only [propEntryM]
    iframe Hctx
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  imod ownSlice_persist $$ Hsl with #Hsl
  wp_auto
  ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  imod msgInC_of_struct s.gh.sn.sz «$a0_ptr» (⟨zero_val _, pty, null, null, null, null, null,
      slice.mk slp (W64 1) (W64 1), null, null, null, null, null, slice.nil, slice.nil, slice.nil,
      0⟩ : raftpb.Message) DFrac.discard [l0]
      ⟨{ (zero_val MessageM) with Type' := W32 15 }, [propEntryM c], none, [], []⟩
      ⊤ rfl rfl rfl rfl rfl (fun _ => ⟨by simp, by simp [entBytesMax]⟩) $$ [«$a0»] with Hm
  · iframe «$a0» Hsl Hnilb cTy
    msg_nulls
    isplitl []
    · iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ p e => entRZ (GF := GF) s.gh.sn.sz p e)).2
      iexact He
    iapply ownSlice_nil
  have hP : (W32 15 : w32) ≠ MsgProp := by simp [MsgProp]
  have hR : (W32 15 : w32) = MsgReadIndex := rfl
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
  wp_apply wp_raft_StepNs cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 15 } : MessageM)
    [propEntryM c] [] none []
    (by simp [StepMsg, stepMsgTypes, MsgReadIndex])
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (fun _ => rfl)
    (by msg_ne) (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
    (by tr_none) Hal $$ [$Hphys $Hghost $Hlc1 Hm Hcred]
  · -- the message: its one-entry batch, read-only; `Context` nil; the client's request
    simp only [hP, ↓reduceIte, named]
    isplitr
    · imodintro
      iintro %h
      exact absurd h.1 (by msg_ne)
    isplitl [Hm]
    · isplitl [Hm]
      · rw [flag_moves (by decide : movesB (W32 15) = true)]; iexact Hm
      isplitr
      · iempintro
      isplitr
      · ipureintro; msg_ne
      isplitr
      · ipureintro; simp
      isplitr
      · ipureintro; msg_ne
      imodintro
      iintro %ty %Hty _
      rw [show mtypeOf (W32 15) = some .readIndex from rfl] at Hty
      cases Hty
      unfold isMessage absMsg absMsgFrom
      iexists propEntryM c, c, Lc
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; rfl
      iframe Hrq
    isplitl [Hcred]
    · rw [ite_eq_left hR]; iexact Hcred
    isplitr
    · imodintro
      iintro %Hc
      exfalso
      revert Hc
      msg_ne
    isplitr
    · iexact Hcap
    isplitr
    · ipureintro; exact Hp0
    · ipureintro; exact Hnsq
  simp only [hP]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, -, %Htm, -, -, -, -,
    %Hend, -, %Hns', -⟩
  -- the end state: `ReadIdxEnd`, and `s` but for the outbox, the read state, the `Progress` values
  obtain ⟨Hri, o, rd, pvs, rfl, Hpm, Hout⟩ := readIdxEnd_of_stepEnd (s := s) rfl rfl Htd.2 Hend
  have Hc := Href.commit_mono
  have e1 := Href.keep (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)); subst e1
  have e2 := Hcc (by msg_ne); subst c'
  wp_auto
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩ := Hfr (by msg_ne) (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)) (fun h => absurd h (by msg_ne))
  icases ownRaftPhysC_sn cf rnv.raft' id _ $$ Hphys with ⟨%Hsn1, Hphys⟩
  obtain ⟨Ht1, -, -, Hip4, -, Hpcs⟩ := Htm (by msg_ne)
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 (by msg_ne)) $$ Hstrecs
  -- the scope at `md` kept (reads on: the read state may grow), the reading's end
  ihave Hsc := rnScopeAt_keepSome md rs rs s { s with outbox := o, rd := rd, prvals := pvs }
    (fun Hs => by
      obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := Hs
      have h4 : md.reads = false → rd.pend = [] ∧ (s.role = .leader → rd.ro.pending = []) :=
        fun h => absurd (hreads.symm.trans h) (by decide)
      have h5' : md.snapshots = false → rs.slent = none ∧ s.logst.prev = base0 ∧ s.logst.snap = none ∧
          ∀ x ∈ o, x.ty ≠ .snap := fun hs => by
        obtain ⟨h51, h52, h53, h54⟩ := h5 hs
        exact ⟨h51, h52, h53, fun x hx => (Hout x hx).elim (h54 x) (fun h => h)⟩
      exact ⟨h1, h2, h3, h4, h5', h6, h7⟩) rfl $$ Hsc
  ihave Hrntr := rnTrace_none (GF := GF) γ rnv.raft' id cf rs.delivered _
    (by rw [Hgh]; exact Hgtr.trans HtrG)
  have Hbk : BkStep s { s with outbox := o, rd := rd, prvals := pvs } :=
    ⟨rfl, fun h => .inl ⟨h, rfl⟩⟩
  have Hrecv : ∀ Adm, RecvEndR Adm rs.k id ps (readMsg c)
      (toRState rs fp { s with outbox := o, rd := rd, prvals := pvs }) := fun Adm => by
    rw [← Hps]
    refine recvEndR_of_bk (.inl ⟨rfl, ?_⟩) Hbk rfl rfl ⟨rfl, rfl⟩ (by simp [readMsg])
    show ReadIdxEnd rs.cfg.cfg id _ (readMsg c) _
    rw [Hcfe]
    exact Hri
  ihave #Hpost : iprop(∃ Lc, ⌜L0 <+: Lc⌝ ∗ readReq γ c Lc ∗ isRead γ c Qr) $$ []
  · iexists Lc
    iframe Hrq Hrd
    ipureintro; exact HL0c
  iapply HΦ
  simp only [named]
  isplitr [Hpost]
  rotate_left
  isplitr
  · iexact Hpost
  · ipureintro
    intro md'' hmd Adm
    subst hmd
    exact Hrecv Adm
  · ihave #Hhist' := restoredSnapHistory_keep γ id Hsd $$ Hhist
    ihave Hledger' := restoreLedger_keep γ id rs.sn (s := s)
      (s' := { s with outbox := o, rd := rd, prvals := pvs })
      (by first | exact Href.voteLe.1 | exact Hcv.1.voteLe.1 | exact Hvr.1 | omega)
      (logStoreRec_ksn Hsd) (by first | exact Href.commit_mono | exact Hcv.commit | exact Hc) (by first | exact Href.snapQueue | exact Hcv.queue | exact Hcv.1.snapQueue) $$ Hledger
    ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
    iapply ownRawNodeAt_intro γ rn id rs _ qs ip (some md) { s with outbox := o, rd := rd, prvals := pvs }
      cf fp rnv sv hprev steps Hwf' Hin
      Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
      (stepsOk_mono_le s _ _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) Htrm
      (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hgh, ← Hns0.2]; exact Hstor.2⟩)
      (Hpvoff.step rfl rfl Hpre Hgh Hpvoff.2.2.1 Hpcs (by msg_ne))
      (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
      (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' (logStoreRec_stored Hsd) Hu Ha Hc)
      (Hsdt.ofRec Hsn Hsd) Hrole
      (Hphs.keep rfl rfl rfl (HsLe.of_step Href.voteLe Hc) Hsn (.inl (Hip4 (by msg_ne)))) rfl Hip
      (by rw [Hgh]; exact Hgtr) (by rw [Hgh]; exact Hglq)
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' Hhist' Hledger' [Hdur] Hrntr Hsc
    · -- (durability stage II (i)) the step keeps `durTie`'s fields
      iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur

end proof

end EtcdGrove
end Perennial
