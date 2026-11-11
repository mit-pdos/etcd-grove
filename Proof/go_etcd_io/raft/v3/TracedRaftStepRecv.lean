/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on the receive paths of the traced
message types** (2026-11-10, trace-check Q8 stage 1 slice 18b, `notes/decisions.md`, "Q8 stage 1
(slice 18b)"): proofs of `stepBundle_traced.on`'s receive paths (`TracedRaftStep.lean`; the premises
slice 18b found needed, `s.role ≠ .preCandidate` and `TrRecvShape`, folded into it by slice 19b).

Every path of a traced type starts with the receive hook, whose gate is the receive line's
(`trCapB_hookGateRecv`): its phase step `PhaseStepR` at the pinned idle phase (`trCapB_pinDir`: the
share named, the voters the trace directory's), its facts `FxPresR` at the phantoms
`recvPhantoms` of amendment A2, and the message's token (`recvTokOf`). The pieces common to every
receive path:
- `recvLine_pred`: a receive event's line matches the received message (`PhaseStepR`'s `recvPred`
  clause), from the event's parse, by type;
- `recvEvTy_of`: the traced types' receive events at `absMsg`, with the shape `TrRecvShape` (a
  heartbeat carries no entries, a heartbeat response does not reject: what the line's parse reads of
  the physical message and the specification's message does not record);
- `ownStepGhost_traceOk`: the node's commit and last index below `traceNumBound`, from the receipts'
  fit (`ownRaftGhost_traceBound`), for the event's `TraceEv.Ok`;
- `hookGateOpt_frame`: a resource framed into a hook gate's result.

**Proved paths** (`stepBundle_traced.on`):
- the stale messages (`StaleRecv`, `stepBundle_traced_staleRecv`): the receive line, which the
  specification answers by the phantom refusal for a request (`fxPresR_staleReq`) and drops for a
  response (`fxPresR_staleResp`); raft ignores both (pre-vote and check-quorum off);
- a response a role does not handle, at the node's term (`IgnResp`, `stepBundle_traced_ignResp`): the
  receive line only; the specification records it (`respSrv`) where that role's idle relation does
  not look;
- a vote request of the node's term (`VoteReq`, `stepBundle_traced_voteReq`): the receive line (the
  specification's decision, which is raft's: `voteGrant_iff`), then the answer's send line, which the
  specification skips (`phaseStepB_skip`, `fxPres_skip`).

**Not here** (`notes/decisions.md`, "Q8 stage 1 (slice 18b)"): a higher-term message (the receive line's
`UpdateTerm` changes the term, so the receiver's `srvFacts` need its commit certificate at the new term);
a follower's or candidate's `MsgHeartbeat`/`MsgApp` (the raised commit index's `isCommitted`/`commitIn`
come from raft's message facts, `isMessage`, which the bundle does not take); a candidate's
`MsgVoteResp` (the tally); the leader's broadcasts.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepPaths

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- A receive event's type, by the message's: the event constants of `recvEvt`, with the shape the
line's parse needs (`TrRecvShape`). -/
def RecvEvTy (m : Msg) (evt : w64) : Prop :=
  (m.ty = .app ∧ evt = W64 10) ∨ (m.ty = .heartbeat ∧ m.entries = [] ∧ evt = W64 10) ∨
    (m.ty = .vote ∧ evt = W64 14) ∨
    ((m.ty = .appResp ∧ evt = W64 12) ∨ (m.ty = .voteResp ∧ evt = W64 16) ∨
      (m.ty = .heartbeatResp ∧ m.reject = false ∧ evt = W64 12))

/-- `msgAbs` does not read a message's context. -/
theorem msgAbs_absMsg_ctx (C : List w64) (bl : Nat) (ty : MsgType) (m : MessageM) (ents : List EntryM)
    (ctx : List w8) : TraceSim.msgAbs C bl (absMsg ty m ents ctx) = TraceSim.msgAbs C bl (absMsg ty m ents) := by
  cases ty <;> rfl

/-- **A receive event's line matches its message**: the event's parse is the message line, which
`recvPred` accepts for the message's specification counterpart (`PhaseStepR`'s clause). -/
theorem recvLine_pred (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (mabs : Etcdraft.Msg) (hty : RecvEvTy m evt) (hev : SendEvOf evt m.dst s cfg m e)
    (hout : cfg.outgoing = ∅)
    (bmt : uint.Z m.term < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63) (blt : uint.Z m.logterm < 2 ^ 63)
    (bk : m.entries.length < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (hmabs : TraceSim.msgAbs C C.length m = some mabs) :
    ∀ ln, Etcdraft.parseLine 0 (evConv e) = .ok ln → recvPred ln mabs = true := by
  obtain ⟨hname, hnid, -, hvote, -, -, -, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  suffices h : Etcdraft.parseLine 0 (evConv e) =
        .ok (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) ∧
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true by
    intro ln hln
    rw [h.1] at hln
    cases hln
    exact h.2
  rcases hty with ⟨hty, rfl⟩ | ⟨hty, hents, rfl⟩ | ⟨hty, rfl⟩ | hresp
  · obtain ⟨-, -, hrp⟩ := aerLine e s cfg m hname
    refine ⟨aerParse e s cfg m tm hname hnid hvote xs hxs hconf hmsg hm (Or.inl hty), ?_⟩
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_app C C.length e m.dst s.vote xs m tm hmsg hm hty bmt bmc bi blt bk
    simp only [hmabs, Option.get_some] at this; exact this
  · obtain ⟨-, -, hrp⟩ := aerLine e s cfg m hname
    refine ⟨aerParse e s cfg m tm hname hnid hvote xs hxs hconf hmsg hm (Or.inr hty), ?_⟩
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_heartbeat C C.length e m.dst s.vote xs m tm hmsg hm hty hents bmt bmc
    simp only [hmabs, Option.get_some] at this; exact this
  · have hname' := (recvName_of _ e hname).2.2.1 rfl
    refine ⟨?_, ?_⟩
    · rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
      exact parseLine_msg 0 e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
        (by rw [hm.1, hty]; rfl) (by rw [hname']; decide)
    · rw [recvPred_rvreq _ _ (by rw [msgLine_name, hname'])]
      have := isRVReq_vote C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty bmt bi blt
      simp only [hmabs, Option.get_some] at this; exact this
  · obtain ⟨nm, hname', hrn, htyp, -, -, -, hpred⟩ :=
      respLine C e s cfg m evt hresp hname tm hmsg hm bmt bi mabs hmabs
    refine ⟨?_, hpred⟩
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg 0 e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [hm.1]; exact htyp)
      (by rw [hname']; intro h; rw [h] at hrn; exact absurd hrn (by decide))

/-- The message type constant of a `mtypeOf` value (the six traced ones). -/
theorem mtypeOf_eq_of (t : w32) (ty : MsgType) (h : mtypeOf t = some ty) :
    (ty = .app → t = MsgApp) ∧ (ty = .heartbeat → t = MsgHeartbeat) ∧ (ty = .vote → t = MsgVote) ∧
    (ty = .appResp → t = MsgAppResp) ∧ (ty = .voteResp → t = MsgVoteResp) ∧
    (ty = .heartbeatResp → t = MsgHeartbeatResp) := by
  unfold mtypeOf at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hty <;> subst hty <;> split at h <;> simp_all <;>
    rename_i h' <;> exact uint_Z_inj.1 (by rw [h']; rfl)

/-- `roleAbs` is injective. -/
theorem roleAbs_ne_of {r r' : Role} (h : r ≠ r') : roleAbs r ≠ roleAbs r' := by
  cases r <;> cases r' <;> first | exact absurd rfl h |
    simp [roleAbs, Etcdraft.follower, Etcdraft.candidate, Etcdraft.leader]

/-- A vote request is none of the other types a gate guards on. -/
theorem vote_ne {t : w32} (h : t = MsgVote) :
    t ≠ MsgApp ∧ t ≠ MsgHeartbeat ∧ t ≠ MsgProp ∧ t ≠ MsgReadIndex ∧ t ≠ MsgTransferLeader ∧
    t ≠ MsgTimeoutNow ∧ t ≠ MsgBeat ∧ t ≠ MsgCheckQuorum ∧ t ≠ MsgPreVoteResp ∧ t ≠ MsgVoteResp ∧
    t ≠ MsgHeartbeatResp ∧ t ≠ MsgAppResp ∧ t ≠ MsgPreVote ∧ t ≠ MsgHup := by
  subst h
  simp [MsgAppResp, MsgHeartbeatResp, MsgVoteResp, MsgApp, MsgHeartbeat, MsgProp, MsgReadIndex,
    MsgTransferLeader, MsgTimeoutNow, MsgBeat, MsgCheckQuorum, MsgPreVoteResp, MsgVote, MsgPreVote, MsgHup]

/-- The responses are none of the types a gate guards on. -/
theorem resp_ne {t : w32} (h : t = MsgAppResp ∨ t = MsgHeartbeatResp ∨ t = MsgVoteResp) :
    t ≠ MsgApp ∧ t ≠ MsgHeartbeat ∧ t ≠ MsgProp ∧ t ≠ MsgReadIndex ∧ t ≠ MsgTransferLeader ∧
    t ≠ MsgTimeoutNow ∧ t ≠ MsgBeat ∧ t ≠ MsgCheckQuorum ∧ t ≠ MsgPreVoteResp ∧ t ≠ MsgVote ∧
    t ≠ MsgPreVote ∧ t ≠ MsgHup := by
  rcases h with rfl | rfl | rfl <;>
    simp [MsgAppResp, MsgHeartbeatResp, MsgVoteResp, MsgApp, MsgHeartbeat, MsgProp, MsgReadIndex,
      MsgTransferLeader, MsgTimeoutNow, MsgBeat, MsgCheckQuorum, MsgPreVoteResp, MsgVote, MsgPreVote, MsgHup]

/-- **A traced type's receive event** at `absMsg`, with its line's shape (`TrRecvShape`). -/
theorem recvEvTy_of (ty : MsgType) (m : MessageM) (ents : List EntryM) (hty : mtypeOf m.Type' = some ty)
    (htr : ty.traced = true) (hsh : TrRecvShape m ents) :
    ∃ evt, recvEvt ty = some evt ∧ RecvEvTy (absMsg ty m ents) evt := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mtypeOf_eq_of _ _ hty
  cases ty with
  | app => exact ⟨_, rfl, .inl ⟨rfl, rfl⟩⟩
  | heartbeat => exact ⟨_, rfl, .inr (.inl ⟨rfl, hsh.1 (h2 rfl), rfl⟩)⟩
  | vote => exact ⟨_, rfl, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
  | appResp => exact ⟨_, rfl, .inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))⟩
  | voteResp => exact ⟨_, rfl, .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))⟩
  | heartbeatResp => exact ⟨_, rfl, .inr (.inr (.inr (.inr (.inr ⟨rfl, hsh.2.1 (h6 rfl), rfl⟩))))⟩
  | _ => cases htr

/-- A receive event is not a bootstrap line. -/
theorem recvEvTy_notBoot {m : Msg} {evt : w64} (h : RecvEvTy m evt) :
    uint.nat evt ≠ 0 ∧ uint.nat evt ≠ 2 ∧ uint.nat evt ≠ 7 ∧ uint.nat evt ≠ 6 := by
  rcases h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | (⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩) <;> decide

/-- A message's numbers below `traceNumBound` are below `2^63`. -/
theorem numsBelow_63 {m : Msg} (h : m.NumsBelow traceNumBound) :
    uint.Z m.term < 2 ^ 63 ∧ m.entries.length < 2 ^ 63 ∧ uint.Z m.logterm < 2 ^ 63 ∧
    uint.Z m.index < 2 ^ 63 ∧ uint.Z m.commit < 2 ^ 63 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
  have hb : traceNumBound = 2 ^ 61 := rfl
  rw [hb] at h1 h2 h3 h4 h5
  refine ⟨?_, by omega, ?_, ?_, ?_⟩ <;> word

/-- The specification's message of a received request or response, by type. -/
theorem msgAbs_recvTy {C : List w64} {bl : Nat} {m : Msg} {evt : w64} {ma : Etcdraft.Msg}
    (h : RecvEvTy m evt) (hma : TraceSim.msgAbs C bl m = some ma) :
    ma.term = uint.Z m.term ∧ ma.dest = idAbs m.dst ∧ ma.source = idAbs m.src ∧
    ((m.ty = .app ∨ m.ty = .heartbeat) → ma.type = .appendEntriesRequest) ∧
    (m.ty = .vote → ma.type = .requestVoteRequest) ∧
    ((m.ty = .appResp ∨ m.ty = .heartbeatResp) → ma.type = .appendEntriesResponse) ∧
    (m.ty = .voteResp → ma.type = .requestVoteResponse) := by
  rcases h with ⟨hty, -⟩ | ⟨hty, -, -⟩ | ⟨hty, -⟩ | (⟨hty, -⟩ | ⟨hty, -⟩ | ⟨hty, -, -⟩) <;>
    simp [TraceSim.msgAbs, hty] at hma <;> subst hma <;> simp [hty]

/-- No phantom for a response. -/
theorem recvPhantoms_resp (m : Etcdraft.Msg) (a : Etcdraft.Server)
    (hty : m.type = .appendEntriesResponse ∨ m.type = .requestVoteResponse) : recvPhantoms m a = [] := by
  unfold recvPhantoms
  split
  · rename_i h
    rcases h.1 with h | h <;> rcases hty with h' | h' <;> rw [h] at h' <;> cases h'
  · rfl

/-! ### (slice 18b) A response a role does not handle, at the node's term

Raft ignores a `MsgAppResp`/`MsgHeartbeatResp` at a follower or candidate and a `MsgVoteResp` at a
follower or leader; the specification records it (`respSrv`: a vote response's tally, a successful
append response's match index), in fields the idle relation does not read at that role. -/

/-- **The idle relation after a recorded response** at a role that does not read what it records. -/
theorem simServerR_respSrv {C : List w64} {bl : Nat} {p : PState} {a : Etcdraft.Server} (ma : Etcdraft.Msg)
    (h : SimServerR C bl p a) (hc : p.role ≠ .candidate ∨ ma.type ≠ .requestVoteResponse)
    (hl : p.role ≠ .leader ∨ ma.type = .requestVoteResponse) : SimServerR C bl p (respSrv a ma) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  unfold respSrv
  split
  · rename_i hv
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun hr => absurd hv (hc.resolve_left (by rw [hr]; simp)), h11⟩
  · rename_i hv
    split
    · refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun hr => absurd (hl.resolve_left (by rw [hr]; simp)) hv⟩
    · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- `respSrv` reads a server only through `toC`. -/
theorem toC_respSrv (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (ma : Etcdraft.Msg)
    (h : toC S x = toC S y) : toC S (respSrv x ma) = toC S (respSrv y ma) := by
  have hM : S.map x.matchIndex = S.map y.matchIndex := congrArg ServerC.matchIndex h
  have hpw : ∀ k ∈ S, x.matchIndex k = y.matchIndex k := List.map_inj_left.1 hM
  have hR : x.votesResponded = y.votesResponded := congrArg ServerC.votesResponded h
  have hG : x.votesGranted = y.votesGranted := congrArg ServerC.votesGranted h
  unfold respSrv
  split
  · simp only [toC] at h ⊢
    injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · split
    · simp only [toC] at h ⊢
      injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      rw [h1, h2, h3, h4, h5, h6, h7, h10, h11, h12]
      congr 1
      apply List.map_inj_left.2
      intro k hk
      split
      · rename_i hks; subst hks; rw [hpw _ hk]
      · exact hpw k hk
    · exact h

/-- **`SpecInv` after a recorded response** at a role that does not read what it records (a vote
response at a non-candidate, an append response at a non-leader): the response consumed, the server
recorded (`respSrv`). -/
theorem specInv_respSrv (σ : Etcdraft.State) (i : Etcdraft.ID) (ma : Etcdraft.Msg)
    (h : TraceSpecInv.SpecInv σ)
    (hc : (σ.s i).state ≠ Etcdraft.candidate ∨ ma.type ≠ .requestVoteResponse)
    (hl : (σ.s i).state ≠ Etcdraft.leader ∨ ma.type = .requestVoteResponse) :
    TraceSpecInv.SpecInv (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id) := by
  have hd := TraceSpecInv.specInv_discard ma h
  have hs : ∀ j, (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j =
      if j = i then respSrv (σ.s i) ma else (σ.discard ma).s j := fun _ => rfl
  by_cases hv : ma.type = .requestVoteResponse
  · refine TraceSpecInv.specInv_congr_v hd rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (try (intro j; rw [hs]; split <;> (try subst_vars) <;> simp only [respSrv, hv, ↓reduceIte] <;> rfl))
    intro j hcand _ _
    rw [hs]
    split
    · rename_i hj; subst hj
      exact absurd hcand (hc.resolve_right (fun h => h hv))
    · assumption
  · refine TraceSpecInv.specInv_congr_m hd rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (try (intro j; rw [hs]; split <;> (try subst_vars) <;> simp only [respSrv, hv, ↓reduceIte] <;>
        (try split) <;> rfl))
    intro j hj hlead k hk
    rw [hs]
    split
    · rename_i hji; subst hji
      exact absurd hlead (hl.resolve_right hv)
    · exact (hd.2.1 j hj hlead).2.2.1 k hk

end pure

section stale
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The idle phase at `s`, pinned (`trCapB_pinDir`): the voters, the share's server and list named. -/
abbrev IdlePin (s : NState) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) :
    List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => C = C0 ∧ cs = cs0 ∧ P = P0 ∧ SimIdle C s cs P

/-- **A stale message's receive line's phase step** (the server and the share unchanged): the
specification refuses a request with the phantom (`lineEffect_staleReq`, `recvPhantoms`) and drops a
response (`lineEffect_staleResp`). -/
theorem phaseStepR_stale (id : w64) (c : CfgM) (s : NState) (ty : MsgType) (m : MessageM)
    (ents : List EntryM) (evt : w64) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg)
    (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg ty m ents) evt) (hto : m.To' = id)
    (hlt : uint.Z m.Term' < uint.Z s.term) (hpre : s.role ≠ .preCandidate)
    (hb : (absMsg ty m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg ty m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg ty m ents)) (fun _ => False) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0) (IdlePin s C0 cs0 P0) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC⟩ e he
  obtain ⟨a0, ha0, hR0, hs, hP, bt, bc, bl⟩ := hI
  have hdst : (absMsg ty m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg ty m ents).dst s c (absMsg ty m ents) e := by rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha0.trans ha.symm) hR0
  have hC' : (absMsg ty m ents).dst ∈ C := by rw [hdst]; exact hC
  have hlt' : uint.Z (absMsg ty m ents).term < uint.Z s.term := hlt
  obtain ⟨hmt, hmd, -, hq, hv, hr, hvr⟩ := msgAbs_recvTy hev hma
  have hat : ma.term < a.currentTerm := by
    rw [hmt, hR.1]; show uint.Z m.Term' < uint.Z (toPState s).term; exact hlt
  refine ⟨a, [], ⟨rfl, ha, by rw [List.append_nil], ⟨a, rfl, hR, hs, by simpa using hP, bt, bc, bl⟩⟩,
    fun x hx => by simp at hx, ?_⟩
  rw [← hdst]
  rcases hev with ⟨hty, hevt⟩ | ⟨hty, hents, hevt⟩ | ⟨hty, hevt⟩ | hresp
  · have hph := recvPhantoms_stale ma a (.inl (hq (.inl hty))) hat
    simp only [List.nil_append, hph, List.foldl_cons, List.foldl_nil]
    exact lineEffect_staleReq C e s c _ evt a ma _ (.inl ⟨hty, hevt⟩) he' hin hout hC' hR hs hpre hlt'
      bt bc bl bi blt bk bmc hma
  · have hph := recvPhantoms_stale ma a (.inl (hq (.inr hty))) hat
    simp only [List.nil_append, hph, List.foldl_cons, List.foldl_nil]
    exact lineEffect_staleReq C e s c _ evt a ma _ (.inr (.inr ⟨hty, hents, hevt⟩)) he' hin hout hC' hR hs
      hpre hlt' bt bc bl bi blt bk bmc hma
  · have hph := recvPhantoms_stale ma a (.inr (hv hty)) hat
    simp only [List.nil_append, hph, List.foldl_cons, List.foldl_nil]
    exact lineEffect_staleReq C e s c _ evt a ma _ (.inr (.inl ⟨hty, hevt⟩)) he' hin hout hC' hR hs hpre
      hlt' bt bc bl bi blt bk bmc hma
  · have hrt : ma.type = .appendEntriesResponse ∨ ma.type = .requestVoteResponse := by
      rcases hresp with ⟨hty, -⟩ | ⟨hty, -⟩ | ⟨hty, -, -⟩
      · exact .inl (hr (.inl hty))
      · exact .inr (hvr hty)
      · exact .inl (hr (.inr hty))
    have hph := recvPhantoms_resp ma a hrt
    simp only [List.nil_append, hph, List.foldl_nil]
    exact lineEffect_staleResp C e s c _ evt a ma _ hresp he' hin hout hC' hR hs hpre hlt' bt bc bl bi hma

/-- **The facts of a lower-term response's receive line** (`FxPresR` at `recvPhantoms m`, none for a
response): raft ignores it, the specification drops it; the phases keep the share's server and list. -/
theorem fxPresR_staleResp (γ : RaftNames) (id : w64) (m : Etcdraft.Msg) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (hty : m.type = .appendEntriesResponse ∨ m.type = .requestVoteResponse)
    (hΦ' : ∀ C cs P cs' P', Φ C cs P → Φ' C cs' (P ++ P') → cs' = cs ∧ P' = []) :
    ⊢ FxPresR (GF := GF) γ id m E (fun _ => False) (recvPhantoms m) Φ Φ' := by
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨hΦ, -, hcs, hΦ1, -, hsrv, hσa, -, -, -, -⟩ := hpre
  obtain ⟨hcs', hP'⟩ := hΦ' C cs P _ P' hΦ hΦ1
  subst hP'
  have hph : recvPhantoms m a = [] := recvPhantoms_resp m a hty
  ihave #H1 := simFx_discard γ C σ m $$ Hfx
  have hs : ∀ j, toC (σ.discard m).server
      ((withNode σ (idAbs id) a' (fun b => b.without m)
        (fun b => ([] ++ recvPhantoms m a).foldl Etcdraft.Bag.with b)).s j) =
      toC (σ.discard m).server ((σ.discard m).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) = toC σ.server (σ.s j)
    split
    · rename_i hj; subst hj; rw [hσa, hsrv, hcs', hcs]
    · rfl
  ihave #H3 := simFx_congr γ C (σ.discard m)
    (withNode σ (idAbs id) a' (fun b => b.without m) (fun b => ([] ++ recvPhantoms m a).foldl Etcdraft.Bag.with b))
    rfl rfl (by rw [hph]; rfl) hs $$ H1
  iframe Htbl
  isplitl
  · iexact H3
  · iintro %v %hv
    exact hv.elim

end stale

/-- A gate at a resource `⌜False⌝` (its premises introduced, the resource among them). -/
macro "ifalse_gate" : tactic => `(tactic| first
  | (iintro **; contradiction)
  | (imodintro; iintro **; contradiction))

/-- A gate at a resource `⌜False⌝`, or whose pure guard the facts `ts` refute (by `simp`). -/
macro "iguard_false" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| first
  | (iintro %hg; exfalso; simp [$ts,*] at hg; done)
  | (imodintro; iintro %hg; exfalso; simp [$ts,*] at hg; done)
  | (iintro **; contradiction)
  | (imodintro; iintro **; contradiction))

section ign
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A response a role does not handle, at the node's term**: a `MsgAppResp`/`MsgHeartbeatResp` at a
follower or candidate, a `MsgVoteResp` at a follower or leader. -/
def IgnResp (s : NState) (m : MessageM) : Prop :=
  m.Term' = s.term ∧ ∃ ty, mtypeOf m.Type' = some ty ∧
    (ty = .appResp ∨ ty = .heartbeatResp ∨ ty = .voteResp) ∧
    (s.role = .follower ∨ (s.role = .candidate ∧ ty ≠ .voteResp) ∨ (s.role = .leader ∧ ty = .voteResp))

/-- The end state of an `IgnResp` path's step function: unchanged. -/
theorem ignResp_end {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hp : IgnResp s m) (h : StepFnEnd c id s m ents ctx s') : s' = s := by
  obtain ⟨-, ty, hmty, hresp, hrole⟩ := hp
  obtain ⟨-, -, -, h4, h5, h6⟩ := mtypeOf_eq_of _ _ hmty
  obtain ⟨hf, hc, hl⟩ := h
  rcases hrole with hr | ⟨hr, hnv⟩ | ⟨hr, rfl⟩
  · obtain ⟨_, _, _, _, -, hres⟩ := hf hr
    rcases hresp with rfl | rfl | rfl
    · rw [h4 rfl] at hres; simp [MsgAppResp, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat] at hres
      exact hres.2
    · rw [h6 rfl] at hres; simp [MsgHeartbeatResp, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat] at hres
      exact hres.2
    · rw [h5 rfl] at hres; simp at hres; exact hres.2
  · obtain ⟨_, _, _, _, -, hres⟩ := hc (.inl hr)
    rcases hresp with rfl | rfl | rfl
    · rw [h4 rfl] at hres; simp [MsgAppResp, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat] at hres
      exact hres.2
    · rw [h6 rfl] at hres; simp [MsgHeartbeatResp, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat] at hres
      exact hres.2
    · exact absurd rfl hnv
  · obtain ⟨_, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    rw [h5 rfl] at hres
    simp [MsgVoteResp, MsgProp, MsgBeat, MsgHeartbeatResp, MsgReadIndex, MsgAppResp, MsgForgetLeader,
      MsgTimeoutNow, MsgUnreachable, MsgSnapStatus, MsgTransferLeader, MsgCheckQuorum, MsgApp, MsgHeartbeat,
      MsgPreVoteResp, MsgReadIndexResp] at hres
    exact hres.2

/-- What `respSrv` keeps: every field but the tally and the match indices. -/
theorem respSrv_fields (v : Etcdraft.Server) (m : Etcdraft.Msg) :
    (respSrv v m).log = v.log ∧ (respSrv v m).commitIndex = v.commitIndex ∧
    (respSrv v m).currentTerm = v.currentTerm ∧ (respSrv v m).state = v.state ∧
    (respSrv v m).config = v.config ∧ (respSrv v m).durable = v.durable := by
  unfold respSrv
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The facts after a recorded response** at a role that does not read what it records. -/
theorem simFx_resp (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (i : Etcdraft.ID) (ma : Etcdraft.Msg)
    (hc : (σ.s i).state ≠ Etcdraft.candidate ∨ ma.type ≠ .requestVoteResponse)
    (hl : (σ.s i).state ≠ Etcdraft.leader ∨ ma.type = .requestVoteResponse) :
    simFx (GF := GF) γ C σ ⊢ simFx γ C (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id) := by
  have hF : ∀ j, ((withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j).log = (σ.s j).log ∧
      ((withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j).commitIndex = (σ.s j).commitIndex ∧
      ((withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j).currentTerm = (σ.s j).currentTerm ∧
      ((withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j).state = (σ.s j).state ∧
      ((withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j).config = (σ.s j).config := by
    intro j
    have hj : (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j =
        if j = i then respSrv (σ.s i) ma else σ.s j := rfl
    rw [hj]
    split
    · rename_i hj; subst hj
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := respSrv_fields (σ.s j) ma
      exact ⟨h1, h2, h3, h4, h5⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hsub : ∀ x ∈ (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).messages.domain ++
      (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).pendingMessages.domain,
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx
  iintro Hfx
  iunfold simFx at Hfx
  iunfold simFx
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
  isplitl
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %j %hj
    obtain ⟨h1, h2, h3, h4, -⟩ := hF (idAbs j)
    iapply srvFacts_congr γ C j _ _ h1 h2 h3 h4
    iapply Hal $$ %j %hj
  isplitl
  · imodintro
    iintro %x %hx
    iapply Hmf
    ipureintro
    exact hsub x hx
  isplitl
  · iapply quorumLogF_congr γ C σ (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id) rfl
      (fun k => (hF k).1) (fun k => (hF k).2.1) (fun k => by rw [(hF k).2.2.1]; exact Int.le_refl _) $$ Hq
  ipureintro
  refine ⟨specInv_respSrv σ i ma hsi hc hl,
    msgsUniq_mono hsub hu, fun x hx => hsh x (hsub x hx), ?_⟩
  intro m hm hty j hj hlj htj hs k e he
  rw [(hF j).1]
  rw [(hF j).2.2.2.1] at hlj; rw [(hF j).2.2.1] at htj
  exact has m (hsub m hm) hty j hj hlj htj hs k e he

/-- **The facts of a response's receive line at a role that does not handle it** (`FxPresR` at
`recvPhantoms m`, none for a response): raft ignores it, the specification records it (`respSrv`) in
fields that role's idle relation does not read; the phases keep the list and take the server to the
recorded one (`hΦ'`). -/
theorem fxPresR_ignResp (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (hty : ma.type = .appendEntriesResponse ∨ ma.type = .requestVoteResponse)
    (hrole : ∀ C cs P, Φ C cs P → (cs.state ≠ Etcdraft.candidate ∨ ma.type ≠ .requestVoteResponse) ∧
      (cs.state ≠ Etcdraft.leader ∨ ma.type = .requestVoteResponse))
    (hΦ' : ∀ C cs P cs' P', Φ C cs P → Φ' C cs' (P ++ P') →
      P' = [] ∧ ∀ a, toC (confAbs C) a = cs → cs' = toC (confAbs C) (respSrv a ma)) :
    ⊢ FxPresR (GF := GF) γ id ma E (fun _ => False) (recvPhantoms ma) Φ Φ' := by
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨hΦ, -, hcs, hΦ1, -, hsrv, hσa, -, -, -, -⟩ := hpre
  obtain ⟨hP', hcs'⟩ := hΦ' C cs P _ P' hΦ hΦ1
  subst hP'
  have hcs1 := hcs' a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_resp ma a hty
  obtain ⟨hc, hl⟩ := hrole C cs P hΦ
  have hst : (σ.s (idAbs id)).state = cs.state := by rw [hσa, ← hcs]; rfl
  rw [← hst] at hc hl
  ihave #H1 := simFx_resp γ C σ (idAbs id) ma hc hl $$ Hfx
  have hs : ∀ j, toC (withNode σ (idAbs id) (respSrv (σ.s (idAbs id)) ma) (fun b => b.without ma) _root_.id).server
      ((withNode σ (idAbs id) a' (fun b => b.without ma)
        (fun b => ([] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b)).s j) =
      toC (withNode σ (idAbs id) (respSrv (σ.s (idAbs id)) ma) (fun b => b.without ma) _root_.id).server
        ((withNode σ (idAbs id) (respSrv (σ.s (idAbs id)) ma) (fun b => b.without ma) _root_.id).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) =
      toC σ.server (if j = idAbs id then respSrv (σ.s (idAbs id)) ma else σ.s j)
    split
    · rw [hsrv, hcs1, hσa]
    · rfl
  ihave #H3 := simFx_congr γ C
    (withNode σ (idAbs id) (respSrv (σ.s (idAbs id)) ma) (fun b => b.without ma) _root_.id)
    (withNode σ (idAbs id) a' (fun b => b.without ma) (fun b => ([] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b))
    rfl rfl (by rw [hph]; rfl) hs $$ H1
  iframe Htbl
  isplitl
  · iexact H3
  · iintro %v %hv
    exact hv.elim

/-- **A response's receive line's phase step at a role that does not handle it**: the server
recorded (`respSrv`, at the pinned server `toC a0`), the list kept (`lineEffect_resp`). -/
theorem phaseStepR_ignResp (id : w64) (c : CfgM) (s : NState) (ty : MsgType) (m : MessageM)
    (ents : List EntryM) (evt : w64) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg)
    (a0 : Etcdraft.Server) (ha0 : toC (confAbs C0) a0 = cs0)
    (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg ty m ents) evt) (hto : m.To' = id)
    (hresp : ty = .appResp ∨ ty = .heartbeatResp ∨ ty = .voteResp)
    (hterm : m.Term' = s.term) (hpre : s.role ≠ .preCandidate)
    (hc : (toPState s).role ≠ .candidate ∨ ty ≠ .voteResp) (hl : (toPState s).role ≠ .leader ∨ ty = .voteResp)
    (hb : (absMsg ty m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg ty m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg ty m ents)) (fun _ => False) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0) (IdlePin s C0 (toC (confAbs C0) (respSrv a0 ma)) P0) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC⟩ e he
  obtain ⟨a1, ha1, hR0, hs, hP, bt, bc, bl⟩ := hI
  have hdst : (absMsg ty m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg ty m ents).dst s c (absMsg ty m ents) e := by rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha1.trans ha.symm) hR0
  have hC' : (absMsg ty m ents).dst ∈ C := by rw [hdst]; exact hC
  obtain ⟨-, -, -, -, -, hr, hvr⟩ := msgAbs_recvTy hev hma
  have hty0 : (absMsg ty m ents).ty = ty := rfl
  have hmc : (toPState s).role ≠ .candidate ∨ ma.type ≠ .requestVoteResponse := by
    rcases hc with h | h
    · exact .inl h
    · right; intro hv
      rcases hresp with rfl | rfl | rfl
      · rw [hr (.inl rfl)] at hv; cases hv
      · rw [hr (.inr rfl)] at hv; cases hv
      · exact h rfl
  have hml : (toPState s).role ≠ .leader ∨ ma.type = .requestVoteResponse := by
    rcases hl with h | h
    · exact .inl h
    · right; exact hvr (h ▸ rfl)
  have hRr := simServerR_respSrv ma hR hmc hml
  have htoC : toC (confAbs C) (respSrv a ma) = toC (confAbs C) (respSrv a0 ma) :=
    toC_respSrv _ _ _ ma (ha.trans ha0.symm)
  have hrt : ma.type = .appendEntriesResponse ∨ ma.type = .requestVoteResponse := by
    rcases hresp with rfl | rfl | rfl
    · exact .inl (hr (.inl rfl))
    · exact .inl (hr (.inr rfl))
    · exact .inr (hvr rfl)
  have hph := recvPhantoms_resp ma a hrt
  have hrev : (absMsg ty m ents).ty = .appResp ∧ evt = W64 12 ∨ (absMsg ty m ents).ty = .voteResp ∧ evt = W64 16 ∨
      (absMsg ty m ents).ty = .heartbeatResp ∧ (absMsg ty m ents).reject = false ∧ evt = W64 12 := by
    rcases hev with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | h
    · rw [hty0] at h; subst h; rcases hresp with h | h | h <;> cases h
    · rw [hty0] at h; subst h; rcases hresp with h | h | h <;> cases h
    · rw [hty0] at h; subst h; rcases hresp with h | h | h <;> cases h
    · exact h
  refine ⟨respSrv a ma, [], ⟨rfl, htoC, by rw [List.append_nil],
      ⟨respSrv a ma, by first | exact htoC | rfl, hRr, hs, by simpa using hP, bt, bc, bl⟩⟩,
    fun x hx => by simp at hx, ?_⟩
  rw [← hdst]
  simp only [List.nil_append, hph, List.foldl_nil]
  exact lineEffect_resp C e s c _ evt a ma _ hrev he' hin hout hC' hR hs hpre hterm bt bc bl bi hma

end ign

section vote
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ### (slice 18b) A vote request of the node's term

`Step`'s `MsgVote` arm: the receive line (the specification's `HandleRequestVoteRequest`: the grant
decision, the vote recorded, the response pending, `lineEffect_voteReq`), then the response's send line
(`SendRequestVoteResponse`, skipped by the specification: `lineEffect_skipResp`); raft decides as the
specification does (`sim_vote_grant`). -/

/-- The specification's grant decision reads a server through `toC`. -/
theorem vrGrant_toC (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (j : Etcdraft.ID) (m : Etcdraft.Msg)
    (h : toC S x = toC S y) : vrGrant x j m = vrGrant y j m := by
  have h1 : x.currentTerm = y.currentTerm := congrArg ServerC.currentTerm h
  have h2 : x.log = y.log := congrArg ServerC.log h
  have h3 : x.votedFor = y.votedFor := congrArg ServerC.votedFor h
  have h4 : x.lead = y.lead := congrArg ServerC.lead h
  unfold vrGrant; rw [h1, h2, h3, h4]

theorem toC_vrSrv (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (j : Etcdraft.ID) (m : Etcdraft.Msg)
    (h : toC S x = toC S y) : toC S (vrSrv x j m) = toC S (vrSrv y j m) := by
  unfold vrSrv
  rw [vrGrant_toC S x y j m h]
  split
  · simp only [toC] at h ⊢
    injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    rw [h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · exact h

theorem vrResp_toC (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (i j : Etcdraft.ID) (m : Etcdraft.Msg)
    (h : toC S x = toC S y) : vrResp x i j m = vrResp y i j m := by
  have h1 : x.currentTerm = y.currentTerm := congrArg ServerC.currentTerm h
  unfold vrResp; rw [h1, vrGrant_toC S x y j m h]

/-- What `vrSrv` keeps: every field but the vote. -/
theorem vrSrv_fields (v : Etcdraft.Server) (j : Etcdraft.ID) (m : Etcdraft.Msg) :
    (vrSrv v j m).log = v.log ∧ (vrSrv v j m).commitIndex = v.commitIndex ∧
    (vrSrv v j m).currentTerm = v.currentTerm ∧ (vrSrv v j m).state = v.state ∧
    (vrSrv v j m).config = v.config := by
  unfold vrSrv; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The specification's vote request handling, as a step. -/
theorem handleRV_some (σ : Etcdraft.State) (i j : Etcdraft.ID) (m : Etcdraft.Msg)
    (hle : m.term ≤ (σ.s i).currentTerm) :
    σ.handleRequestVoteRequest i j m = some (voteReqResult σ i j m) := by
  unfold voteReqResult
  cases h : σ.handleRequestVoteRequest i j m with
  | none =>
    unfold Etcdraft.State.handleRequestVoteRequest at h
    simp [hle] at h
  | some σ' => rfl

/-- **The facts after the specification's handling of a vote request of the node's term**: the
request consumed, the vote recorded, the response pending. -/
theorem simFx_voteReq (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (i j : Etcdraft.ID) (ma : Etcdraft.Msg)
    (hle : ma.term ≤ (σ.s i).currentTerm) (hsrc : ma.source = j) (hmem : ma ∈ σ.messages.domain) :
    simFx (GF := GF) γ C σ ⊢
      simFx γ C (withNode σ i (vrSrv (σ.s i) j ma) (fun b => b.without ma) (fun b => b.with (vrResp (σ.s i) i j ma))) := by
  have heq := voteReqResult_eq σ i j ma hle
  have hx0 : canonMsg (vrResp (σ.s i) i j ma) = vrResp (σ.s i) i j ma := by unfold vrResp canonMsg; rfl
  have hxq : (vrResp (σ.s i) i j ma).type ≠ .appendEntriesRequest := by unfold vrResp; simp
  have hxe : (vrResp (σ.s i) i j ma).entries = [] := rfl
  obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 =
      withNode σ i (vrSrv (σ.s i) j ma) (fun b => b.without ma) (fun b => b.with (vrResp (σ.s i) i j ma)) :=
    ⟨_, rfl⟩
  rw [← hσ1]
  have hF : ∀ k, (σ1.s k).log = (σ.s k).log ∧ (σ1.s k).commitIndex = (σ.s k).commitIndex ∧
      (σ1.s k).currentTerm = (σ.s k).currentTerm ∧ (σ1.s k).state = (σ.s k).state ∧
      (σ1.s k).config = (σ.s k).config := by
    intro k
    have hk : σ1.s k = if k = i then vrSrv (σ.s i) j ma else σ.s k := by rw [hσ1]; rfl
    rw [hk]
    split
    · rename_i hki; subst hki; exact vrSrv_fields _ _ _
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  -- the bags: the old ones' (but the request), and the response
  have hsub : ∀ x ∈ σ1.messages.domain ++ σ1.pendingMessages.domain,
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain ∨ x = vrResp (σ.s i) i j ma := by
    intro x hx
    have hx' : x ∈ ((σ.discard ma).send (vrResp (σ.s i) i j ma)).messages.domain ++
        ((σ.discard ma).send (vrResp (σ.s i) i j ma)).pendingMessages.domain := by rw [hσ1] at hx; exact hx
    rcases TraceSpecInv.mem_msgs_send _ _ x hx' with hx | rfl
    · left
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
      · exact List.mem_append_right _ hx
    · right; rfl
  iintro Hfx
  iunfold simFx at Hfx
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
  have hsi' : TraceSpecInv.SpecInv σ1 := by
    rw [hσ1, ← heq]
    exact TraceSpecInv.specInv_handleRequestVoteRequest hsi hmem hsrc (handleRV_some σ i j ma hle)
  -- uniqueness and shape: after the discard, the response sent
  have hud : MsgsUniq (σ.discard ma) := msgsUniq_mono (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx) hu
  have hshd : MsgsShape (σ.discard ma) := fun x hx => hsh x (by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx)
  obtain ⟨hu', hsh'⟩ := msgsUniq_send_canon (σ.discard ma) _ hud hshd hx0
    (fun y _ => ContentLogged.pinned (fun h => absurd h hxq) y)
  iunfold simFx
  isplitl
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %k %hk
    obtain ⟨h1, h2, h3, h4, -⟩ := hF (idAbs k)
    iapply srvFacts_congr γ C k _ _ h1 h2 h3 h4
    iapply Hal $$ %k %hk
  isplitl
  · imodintro
    iintro %x %hx
    rcases hsub x hx with hx | rfl
    · iapply Hmf; ipureintro; exact hx
    · iapply msgFacts_plain γ C _ hxq hxe
  isplitl
  · iapply quorumLogF_congr γ C σ σ1 (by rw [hσ1]; rfl) (fun k => (hF k).1) (fun k => (hF k).2.1)
      (fun k => by rw [(hF k).2.2.1]; exact Int.le_refl _) $$ Hq
  ipureintro
  refine ⟨hsi', by rw [hσ1]; exact hu', by rw [hσ1]; exact hsh', ?_⟩
  intro m hm hty k hk hlk htk hs k' e he
  have hk' : k ∈ σ.server := by rw [hσ1] at hk; exact hk
  rcases hsub m hm with hm | rfl
  · rw [(hF k).1]
    rw [(hF k).2.2.2.1] at hlk; rw [(hF k).2.2.1] at htk
    exact has m hm hty k hk' hlk htk hs k' e he
  · exact absurd hty hxq

/-- A phase pinned to a share (no idle relation: between the receive line and `Step`'s end). -/
abbrev VPin (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) :
    List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => C = C0 ∧ cs = cs0 ∧ P = P0

/-- No phantom for a message not of a lower term. -/
theorem recvPhantoms_nolow (m : Etcdraft.Msg) (a : Etcdraft.Server) (h : ¬ m.term < a.currentTerm) :
    recvPhantoms m a = [] := by
  unfold recvPhantoms
  split
  · rename_i h'; exact absurd h'.2 h
  · rfl

/-- **A vote request's receive line's phase step, at the node's term**: the server to the
specification's `vrSrv`, its response `vrResp` added (both read the server through `toC`, so they are
pinned at the pinned server's `a0`). -/
theorem phaseStepR_voteReq (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server)
    (ha0 : toC (confAbs C0) a0 = cs0) (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .vote m ents) evt)
    (hto : m.To' = id) (hterm : m.Term' = s.term) (hpre : s.role ≠ .preCandidate)
    (hb : (absMsg .vote m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .vote m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .vote m ents)) (fun _ => False) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (VPin C0 (toC (confAbs C0) (vrSrv a0 (idAbs m.From') ma))
        (P0 ++ [vrResp a0 (idAbs id) (idAbs m.From') ma])) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC⟩ e he
  obtain ⟨a1, ha1, hR0, hs, hP, bt, bc, bl⟩ := hI
  have hdst : (absMsg .vote m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg .vote m ents).dst s c (absMsg .vote m ents) e := by rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha1.trans ha.symm) hR0
  have hC' : (absMsg .vote m ents).dst ∈ C := by rw [hdst]; exact hC
  have hev14 : evt = W64 14 := by
    rcases hev with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨-, h⟩ | (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩) <;> first | exact h | cases h
  subst hev14
  obtain ⟨hmt, -⟩ := msgAbs_recvTy hev hma
  have hnl : ¬ ma.term < a.currentTerm := by
    rw [hmt, hR.1]; show ¬ uint.Z m.Term' < uint.Z (toPState s).term; rw [hterm]; exact Int.lt_irrefl _
  have hph := recvPhantoms_nolow ma a hnl
  have hcx : toC (confAbs C) a = toC (confAbs C) a0 := ha.trans ha0.symm
  refine ⟨vrSrv a (idAbs m.From') ma, [vrResp a (idAbs id) (idAbs m.From') ma],
    ⟨rfl, toC_vrSrv _ _ _ _ _ hcx, by rw [vrResp_toC _ _ _ _ _ _ hcx]⟩, ?_, ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl
  rw [← hdst]
  simp only [hph, List.append_nil, List.foldl_cons, List.foldl_nil]
  exact lineEffect_voteReq C e s c _ a ma _ he' hin hout hC' hR hs hpre rfl hterm bt bc bl bi blt hma

/-- **The facts of a vote request's receive line, at the node's term** (`FxPresR` at
`recvPhantoms m`, none): the specification's handling (`simFx_voteReq`) at the pinned phases. -/
theorem fxPresR_voteReq (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (r1 : Etcdraft.Msg) (j : Etcdraft.ID)
    (hsrc : ma.source = j)
    (hpin : ∀ a, toC (confAbs C0) a = cs0 → cs1 = toC (confAbs C0) (vrSrv a j ma) ∧
      r1 = vrResp a (idAbs id) j ma ∧ ma.term = a.currentTerm) :
    ⊢ FxPresR (GF := GF) γ id ma E (fun _ => False) (recvPhantoms ma) (IdlePin s C0 cs0 P0)
      (VPin C0 cs1 (P0 ++ [r1])) := by
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, rfl, rfl, -⟩, -, hcs, ⟨-, hcs', hP⟩, -, hsrv, hσa, -, -, -, hmem⟩ := hpre
  have hP' : P' = [r1] := List.append_cancel_left hP
  subst hP'
  obtain ⟨hc1, hr1, hle⟩ := hpin a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_nolow ma a (by rw [hle]; exact Int.lt_irrefl _)
  ihave #H1 := simFx_voteReq γ C σ (idAbs id) j ma (by rw [hσa, hle]; exact Int.le_refl _) hsrc hmem $$ Hfx
  have hs : ∀ k, toC (withNode σ (idAbs id) (vrSrv (σ.s (idAbs id)) j ma) (fun b => b.without ma)
        (fun b => b.with (vrResp (σ.s (idAbs id)) (idAbs id) j ma))).server
      ((withNode σ (idAbs id) a' (fun b => b.without ma)
        (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b)).s k) =
      toC (withNode σ (idAbs id) (vrSrv (σ.s (idAbs id)) j ma) (fun b => b.without ma)
        (fun b => b.with (vrResp (σ.s (idAbs id)) (idAbs id) j ma))).server
        ((withNode σ (idAbs id) (vrSrv (σ.s (idAbs id)) j ma) (fun b => b.without ma)
          (fun b => b.with (vrResp (σ.s (idAbs id)) (idAbs id) j ma))).s k) := by
    intro k
    show toC σ.server (if k = idAbs id then a' else σ.s k) =
      toC σ.server (if k = idAbs id then vrSrv (σ.s (idAbs id)) j ma else σ.s k)
    split
    · rw [hsrv, hcs', hc1, hσa]
    · rfl
  ihave #H3 := simFx_congr γ C
    (withNode σ (idAbs id) (vrSrv (σ.s (idAbs id)) j ma) (fun b => b.without ma)
      (fun b => b.with (vrResp (σ.s (idAbs id)) (idAbs id) j ma)))
    (withNode σ (idAbs id) a' (fun b => b.without ma) (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b))
    rfl rfl (by rw [hph, hr1, hσa]; rfl) hs $$ H1
  iframe Htbl
  isplitl
  · iexact H3
  · iintro %v %hv
    exact hv.elim

/-- **A response's send line that the specification skips** (`SendRequestVoteResponse`,
`SendAppendEntriesResponse`: the receive line already put the response in the bags), at a pinned
phase: nothing changes. -/
theorem phaseStepB_skip (id : w64) (c : CfgM) (s1 : NState) (evt : w64) (x : Msg) (C0 : List w64)
    (cs0 : ServerC) (P0 : List Etcdraft.Msg) (hevt : evt = W64 11 ∨ evt = W64 15) (hne : x.src ≠ x.dst)
    (htr : x.ty = .appResp ∨ x.ty = .heartbeatResp ∨ x.ty = .voteResp) :
    PhaseStepB id c (fun e => ∃ mm ∈ [x], SendEvOf evt id s1 c mm e) (VPin C0 cs0 P0) (VPin C0 cs0 P0) := by
  rintro C cs P ⟨rfl, rfl, rfl⟩ ⟨-, hout, -⟩ e ⟨mm, hmm, he⟩
  simp only [List.mem_singleton] at hmm
  subst hmm
  refine ⟨he.2.1, ?_, fun a ha => ⟨a, [], ⟨rfl, ha, by rw [List.append_nil]⟩, fun _ h => by simp at h, ?_⟩⟩
  · have hname := he.1
    rcases hevt with rfl | rfl <;> simp only [evtNames] at hname <;>
      (have h := hname; simp at h; rw [← h]; decide)
  · exact lineEffect_skipResp C e id s1 c mm evt a _ hevt he hout hne htr

/-- **The facts of a skipped send line**: nothing changes (up to `toC`). -/
theorem fxPres_skip (γ : RaftNames) (id : w64) (E : TraceEv → Prop) (C0 : List w64) (cs0 : ServerC)
    (P0 : List Etcdraft.Msg) : ⊢ FxPres (GF := GF) γ id E (VPin C0 cs0 P0) (VPin C0 cs0 P0) := by
  iunfold FxPres
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, rfl, rfl⟩, -, hcs, ⟨-, hcs', hP⟩, -, hsrv, hσa, -⟩ := hpre
  have hP' : P' = [] := by simpa using hP
  subst hP'
  have hs : ∀ k, toC σ.server ((withNode σ (idAbs id) a' _root_.id
      (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b)).s k) = toC σ.server (σ.s k) := by
    intro k
    show toC σ.server (if k = idAbs id then a' else σ.s k) = toC σ.server (σ.s k)
    split
    · rename_i hk; subst hk; rw [hσa, hsrv, hcs', hcs]
    · rfl
  ihave #H := simFx_congr γ C σ (withNode σ (idAbs id) a' _root_.id
      (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b)) rfl rfl rfl hs $$ Hfx
  iframe Htbl
  iexact H

/-- **Raft's vote decision is the specification's**, at the node's term (`sim_vote_grant`): `VoteGrant`
of a `MsgVote` is `vrGrant` at the related server. -/
theorem voteGrant_iff (C : List w64) (s : NState) (m : MessageM) (ents : List EntryM) (a0 : Etcdraft.Server)
    (ma : Etcdraft.Msg) (hR : SimServerR C C.length (toPState s) a0) (hs : LogShapeOk C.length (toPState s))
    (hT : m.Type' = MsgVote) (hterm : m.Term' = s.term) (hnpc : s.role ≠ .preCandidate)
    (hma : TraceSim.msgAbs C C.length (absMsg .vote m ents) = some ma) :
    vrGrant a0 (idAbs m.From') ma = true ↔ VoteGrant s m := by
  simp only [TraceSim.msgAbs, absMsg, absMsgFrom, Msg.mkV] at hma
  cases hma
  have hg := (sim_vote_grant C C.length (toPState s) a0 m.From' m.LogTerm' m.Index' hR hs).1
  have ht : (uint.Z m.Term' == a0.currentTerm) = true := by rw [hR.1, hterm]; simp [toPState]
  have hnpv : m.Type' ≠ MsgPreVote := by rw [hT]; simp [MsgVote, MsgPreVote]
  unfold vrGrant VoteGrant
  dsimp only
  rw [ht, Bool.true_and]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, true_and] at hg ⊢
  rw [hg]
  simp only [PCanVote, toPState, hnpc, ↓reduceIte, hnpv, false_and, or_false]

/-- **The idle relation after a vote request's handling, at the node's term**: raft's end state
(`VoteEnd`) is related to the specification's server and pending list after the receive line. -/
theorem voteEnd_simIdle (C : List w64) (id : w64) (s s' : NState) (m : MessageM) (ents : List EntryM)
    (a0 : Etcdraft.Server) (ma : Etcdraft.Msg) (hR : SimServerR C C.length (toPState s) a0)
    (hs : LogShapeOk C.length (toPState s)) (bt : uint.Z s.term < 2 ^ 63)
    (bc : uint.Z s.logst.committed < 2 ^ 63) (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (hT : m.Type' = MsgVote) (hterm : m.Term' = s.term) (hnpc : s.role ≠ .preCandidate)
    (hma : TraceSim.msgAbs C C.length (absMsg .vote m ents) = some ma) (hend : VoteEnd id s m s') :
    SimIdle C s' (toC (confAbs C) (vrSrv a0 (idAbs m.From') ma))
      (pendAbs C s.outbox ++ [vrResp a0 (idAbs id) (idAbs m.From') ma]) := by
  have hiff := voteGrant_iff C s m ents a0 ma hR hs hT hterm hnpc hma
  have hgs := (sim_vote_grant C C.length (toPState s) a0 m.From' m.LogTerm' m.Index' hR hs).2
  have hvT : vrespMsgOf id s m false = Msg.plain .voteResp id m.From' m.Term' false := by
    simp [vrespMsgOf, hT]
  have hvF : vrespMsgOf id s m true = Msg.plain .voteResp id m.From' s.term true := by
    simp [vrespMsgOf, hT]
  rcases hend with ⟨hvg, rfl⟩ | ⟨hvg, rfl⟩
  · have hgr : vrGrant a0 (idAbs m.From') ma = true := hiff.2 hvg
    have hsrv : vrSrv a0 (idAbs m.From') ma = { a0 with votedFor := idAbs m.From' } := by
      unfold vrSrv; rw [hgr]; rfl
    rw [hsrv]
    refine ⟨_, rfl, ?_, hs, ?_, bt, bc, bl⟩
    · have hnpv : m.Type' ≠ MsgPreVote := by rw [hT]; simp [MsgVote, MsgPreVote]
      have hpc : PCanVote (toPState s) m.From' ∧
          plogUpToDate (toPState s).base (toPState s).log (entryID.mk m.LogTerm' m.Index') = true := by
        obtain ⟨h1, h2⟩ := hvg
        refine ⟨?_, h2⟩
        simp only [PCanVote, toPState, hnpc, ↓reduceIte]
        rcases h1 with h | h | ⟨h, -⟩
        · exact .inl h
        · exact .inr h
        · exact absurd h hnpv
      exact hgs ((sim_vote_grant C C.length (toPState s) a0 m.From' m.LogTerm' m.Index' hR hs).1.2 hpc)
    · show _ = pendAbs C (s.outbox ++ [vrespMsgOf id s m false])
      rw [pendAbs_append, hvT]
      simp [pendAbs, TraceSim.msgAbs, Msg.plain, vrResp, hgr, hR.1, hterm, toPState]
  · have hgr : vrGrant a0 (idAbs m.From') ma = false := by
      cases h : vrGrant a0 (idAbs m.From') ma
      · rfl
      · exact absurd (hiff.1 h) hvg
    have hsrv : vrSrv a0 (idAbs m.From') ma = a0 := by
      unfold vrSrv; rw [hgr]; rfl
    rw [hsrv]
    refine ⟨_, rfl, hR, hs, ?_, bt, bc, bl⟩
    show _ = pendAbs C (s.outbox ++ [vrespMsgOf id s m true])
    rw [pendAbs_append, hvF]
    simp [pendAbs, TraceSim.msgAbs, Msg.plain, vrResp, hgr, hR.1, toPState]

end vote

section gates
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `stepFollower`'s gates at resources no path reaches. -/
theorem followerGates_false (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (ents : List EntryM)
    (cl : List w8) :
    ⊢ followerGates (GF := GF) c r id s m ents cl (fun _ => iprop(⌜False⌝)) (fun _ => iprop(⌜False⌝)) := by
  iunfold followerGates
  dsimp only
  repeat (isplitr; · ifalse_gate)
  ifalse_gate

/-- `stepCandidate`'s gates at resources no path reaches (the log's `TrNoSnap` given). -/
theorem candidateGates_false (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (ents : List EntryM)
    (cl : List w8) (Tw : IProp GF) :
    TrNoSnap (GF := GF) s.gh.tr s.logst ⊢
      candidateGates (GF := GF) c r id s m ents cl (fun _ => iprop(⌜False⌝)) (fun _ => iprop(⌜False⌝))
        iprop(⌜False⌝) iprop(⌜False⌝) iprop(⌜False⌝) Tw := by
  iintro #Hns
  iunfold candidateGates
  dsimp only
  repeat (isplitr; · first | iexact Hns | ifalse_gate)
  ifalse_gate

/-- `stepLeader`'s gates at resources no path reaches (the log's `TrNoSnap` given). -/
theorem leaderGates_false (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (ents : List EntryM)
    (Tp : IProp GF) :
    TrNoSnap (GF := GF) s.gh.tr s.logst ⊢
      leaderGates (GF := GF) c r id s m ents Tp (fun _ => iprop(⌜False⌝)) (fun _ => iprop(⌜False⌝))
        iprop(⌜False⌝) (fun _ => iprop(⌜False⌝)) (fun _ _ _ => iprop(⌜False⌝)) := by
  iintro #Hns
  iunfold leaderGates
  dsimp only
  repeat (isplitr; · first | iexact Hns | ifalse_gate)
  ifalse_gate

/-- A hook gate after an update at `⊤` (`TracedRaftStepLocal.lean`'s `hookGateOpt_fupd`, a copy: this module does not import it). -/
theorem hookGateOpt_fupd_recv (tr : Option GName) (r : Loc) (oE : Option (TraceEv → Prop)) (Q : IProp GF) :
    iprop(|={⊤}=> HookGateOpt tr r oE Q) ⊢ HookGateOpt tr r oE Q := by
  iintro H
  iunfold HookGateOpt at H
  iunfold HookGateOpt
  imod H with H
  iexact H

/-- A resource framed into a hook gate's result. -/
theorem hookGateOpt_frame (tr : Option GName) (r : Loc) (oE : Option (TraceEv → Prop)) (X Q : IProp GF) :
    iprop(X ∗ HookGateOpt tr r oE Q) ⊢ HookGateOpt tr r oE iprop(X ∗ Q) := by
  iintro ⟨HX, H⟩
  iunfold HookGateOpt at H
  iunfold HookGateOpt
  imod H with ⟨%tl, #Htl, %Hok, H⟩
  imodintro
  iexists tl
  iframe Htl
  isplitr
  · ipureintro; exact Hok
  iapply traceFireOpt_mono tr tl oE Q iprop(X ∗ Q)
  iframe H
  iintro HQ
  iframe HX HQ

/-- **The node's numbers the lines read, below `traceNumBound`** (`ownRaftGhost_traceBound`, from the
receipts' fit): the last index and the commit index. -/
theorem ownStepGhost_traceOk (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (Hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    ownStepGhost (GF := GF) γ md c id s ⊢ |={⊤}=>
      ⌜uint.nat (plastIndex (toPState s)) < traceNumBound ∧ uint.nat s.logst.committed < traceNumBound⌝ ∗
      ownStepGhost γ md c id s := by
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  imod ownRaftGhost_traceBound γ id (toPState s) Hfit $$ Hg with ⟨%Hb, Hg⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨h1, h2⟩ := Hb
    have hb : traceNumBound = 2 ^ 61 := rfl
    have h0 : (0 : Int) ≤ plogLastIndexZ (toPState s).base (toPState s).log := by
      unfold plogLastIndexZ; have := uint_Z_nonneg (toPState s).base.index'; omega
    have hc : (toPState s).commit = s.logst.committed := rfl
    rw [hc] at h2
    rw [hb] at h1 h2 ⊢
    unfold plastIndex
    constructor
    · have : uint.Z (W64 (plogLastIndexZ (toPState s).base (toPState s).log)) =
          plogLastIndexZ (toPState s).base (toPState s).log := by word
      word
    · word
  iunfold ownStepGhost
  iframe Hg Hr

/-- Two trace directories at one name agree. -/
theorem traceDir_agree (γd : GName) (tn tn' : TraceNames) :
    (traceDir (GF := GF) γd tn ∗ traceDir γd tn' : IProp GF) ⊢ ⌜tn = tn'⌝ := by
  iintro ⟨H1, H2⟩
  iunfold traceDir at H1 H2
  iapply dghostVar_agree _ _ _ _ _ $$ H1 H2

/-- **The capability's share, pinned, with its trace directory**: `trCapB_pinMem` with the voters
the directory's (`tn.voters`), so that the received message's token (`recvTokOf`, at `tn.voters`)
names the same voters. -/
theorem trCapB_pinDir (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    trCapB (GF := GF) (some γd) γ r id c b Φ Λ ⊢
      ∃ (tn : TraceNames) (cs0 : ServerC) (P0 : List Etcdraft.Msg), traceDir γd tn ∗
        ⌜Φ tn.voters cs0 P0 ∧ id ∈ tn.voters⌝ ∗
        trCapB (some γd) γ r id c b (fun C cs P => C = tn.voters ∧ cs = cs0 ∧ P = P0 ∧ Φ C cs P) Λ := by
  iintro H
  iunfold trCapB at H
  icases H with ⟨%tn, %C, %tl, %cs, %P, #Hdir, %Hpf, #Htl, #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
  obtain ⟨hC, hpin, hpout, hid⟩ := Hpf
  subst hC
  iexists tn, cs, P
  iframe Hdir
  isplitr; · ipureintro; exact ⟨HΦ, hid⟩
  iunfold trCapB
  iexists tn, tn.voters, tl, cs, P
  iframe Hdir Htl Hlg Hinv Hrinv Hnode Hbt
  isplitr; · ipureintro; exact ⟨rfl, hpin, hpout, hid⟩
  isplitr; · ipureintro; exact Hnn
  ipureintro; exact ⟨rfl, rfl, rfl, HΦ⟩

/-- **The receive hook's gate, traced**, on a traced type: the receive line's law
(`trCapB_hookGateRecv`) at the hook's events (`recvGate`'s), with a frame `X`. -/
theorem recvGate_traced (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (s : NState)
    (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ty : MsgType) (evt : w64) (b : Bool) (k : Nat) (ma : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop)
    (ph : Etcdraft.Server → List Etcdraft.Msg) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Λ : Option TraceEv → Prop) (X : IProp GF)
    (htr : s.gh.tr = some γd) (hty : mtypeOf m.Type' = some ty) (hevt : recvEvt ty = some evt)
    (hps : PhaseStepR id c ma (SendEvOf evt id s c (absMsg ty m ents)) Mid ph Φ Φ')
    (hOk : ∀ e, SendEvOf evt id s c (absMsg ty m ents) e → TraceEv.Ok (elements c.incoming).length e) :
    (X ∗ trCapB (some γd) γ r id c b Φ Λ ∗
        FxPresR γ id ma (SendEvOf evt id s c (absMsg ty m ents)) Mid ph Φ Φ' ∗
        (∃ tn, traceDir γd tn ∗ inFlight tn k ma) : IProp GF) ⊢
      HookGateOpt s.gh.tr r (recvGate id s c ⟨m, ents, sn, ctx, rs⟩)
        iprop(X ∗ trCapB (some γd) γ r id c true Φ' (fun o => o.isSome = true)) := by
  have hrg : recvGate id s c ⟨m, ents, sn, ctx, rs⟩ = some (SendEvOf evt id s c (absMsg ty m ents)) := by
    simp [recvGate, hty, hevt]
  rw [hrg, htr]
  iintro ⟨HX, Hcap, Hfx, Htok⟩
  iapply hookGateOpt_frame
  iframe HX
  icases trCapB_logger γd γ r id c b Φ Λ $$ Hcap with ⟨%tl, #Htl, Hcap⟩
  iapply trCapB_hookGateRecv (some γd) γ r id c tl _ b k ma Mid ph Φ Φ' Λ (fun o => o.isSome = true) hps
    (fun _ _ => rfl) (fun _ => hOk) (fun h => by cases h)
  simp only [FxPresRT, recvTok]
  iframe Htl Hcap Hfx Htok

end gates

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A stale message of a traced type** (`Step`'s `m.Term < r.Term` arm). -/
def StaleRecv (s : NState) (m : MessageM) : Prop :=
  StaleMsg s m ∧ ∃ ty, mtypeOf m.Type' = some ty ∧ ty.traced = true

/-- `StaleRecv`'s resources: after the receive line, raft's ghost state and the capability at the
pinned idle phase (`G0`, where `Step` ends); `False` at every other resource (no other hook runs). -/
def staleR (bt : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (γd : GName)
    (tn : TraceNames) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (Λ : Option TraceEv → Prop) (k : Nat)
    (ma : Etcdraft.Msg) : StepG GF where
  G := iprop(trCapB (some γd) γ r id c bt (IdlePin s tn.voters cs0 P0) Λ ∗ inFlight tn k ma)
  G0 := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (IdlePin s tn.voters cs0 P0) (fun o => o.isSome = true))
  G1 := fun _ => iprop(⌜False⌝)
  GE := fun _ => iprop(⌜False⌝)
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := fun _ => iprop(⌜False⌝)
  Gc := fun _ _ _ => iprop(⌜False⌝)

/-- The pinned idle phase keeps the share's server and list (a line adding nothing). -/
theorem idlePin_keep (s : NState) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) :
    ∀ C cs P cs' P', IdlePin s C0 cs0 P0 C cs P → IdlePin s C0 cs0 P0 C cs' (P ++ P') → cs' = cs ∧ P' = [] := by
  rintro C cs P cs' P' ⟨-, rfl, rfl, -⟩ ⟨-, rfl, h, -⟩
  exact ⟨rfl, by simpa using h⟩

/-- The pinned idle phase's term is the node's. -/
theorem idlePin_term (s : NState) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) :
    ∀ C cs P, IdlePin s C0 cs0 P0 C cs P → cs.currentTerm = uint.Z s.term := by
  rintro C cs P ⟨-, -, -, a, rfl, hR, -⟩
  exact hR.1

/-- **`raft.Step`'s traced bundle on the stale messages of a traced type**: the receive line (the
specification's phantom refusal of a request, the drop of a response), nothing else. -/
theorem stepBundle_traced_staleRecv : stepBundle_traced.on (GF := GF) (hG := hG) StaleRecv := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom hnpc hsh hboot
  obtain ⟨hst, ty, hmty, htrd⟩ := hp
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of ty m ents hmty htrd hsh
  have hto' : m.To' = id := hto ty hmty htrd
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by have := hst.2; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hnhup : m.Type' ≠ MsgHup := fun h => by rw [h] at hmty; cases hmty
  have hnpv : m.Type' ≠ MsgPreVote := fun h => by
    rw [h] at hmty; cases hmty; cases htrd
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  have hmt2 : mtypeOf m.Type' = some ty ∧ ty.traced = true := ⟨hmty, htrd⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %ty %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  imodintro
  iexists staleR bfl γ md c r id s γd tn cs0 P0 Λ k ma
  isplitl [Hcap Htok]
  · dsimp only [staleR]; iframe Hcap Htok
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, staleR]
    isplitr
    · -- the receive line
      iintro ⟨Hgh, Hc, Htok⟩
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg ty m ents).NumsBelow traceNumBound := (hok ty hmty hreT htrd).1
      have hps := phaseStepR_stale id c s ty m ents evt tn.voters cs0 P0 ma hev hto' hst.2 hnpc hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg ty m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_traced γd γ r id c s m ents sn ctx rs ty evt bfl k ma (fun _ => False) (recvPhantoms ma)
        (IdlePin s tn.voters cs0 P0) (IdlePin s tn.voters cs0 P0) Λ (ownStepGhost γ md c id s) htr hmty hevt
        hps hOk
      iframe Hgh Hc
      isplitr
      · obtain ⟨hmt, hmd, -, hq, hv, hr, hvr⟩ := msgAbs_recvTy hev hma
        have hdst : ma.dest = idAbs id := by rw [hmd]; show idAbs m.To' = _; rw [hto']
        rcases hev with ⟨hty', -⟩ | ⟨hty', -, -⟩ | ⟨hty', -⟩ | hresp
        · iapply fxPresR_staleReq γ id ma _ _ _ (.inl (hq (.inl hty'))) hdst
            (fun C cs P h => by rw [hmt, idlePin_term s _ _ _ C cs P h]; exact hst.2)
            (idlePin_keep s _ _ _)
        · iapply fxPresR_staleReq γ id ma _ _ _ (.inl (hq (.inr hty'))) hdst
            (fun C cs P h => by rw [hmt, idlePin_term s _ _ _ C cs P h]; exact hst.2)
            (idlePin_keep s _ _ _)
        · iapply fxPresR_staleReq γ id ma _ _ _ (.inr (hv hty')) hdst
            (fun C cs P h => by rw [hmt, idlePin_term s _ _ _ C cs P h]; exact hst.2)
            (idlePin_keep s _ _ _)
        · have hrt : ma.type = .appendEntriesResponse ∨ ma.type = .requestVoteResponse := by
            rcases hresp with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
            · exact .inl (hr (.inl h))
            · exact .inr (hvr h)
            · exact .inl (hr (.inr h))
          iapply fxPresR_staleResp γ id ma _ _ _ hrt (idlePin_keep s _ _ _)
      · iexists tn; iframe Hdir Htok
    isplitr
    · -- the preamble: not reached (stale)
      unfold preGate
      iintro %h
      exfalso
      have := hst.2
      rcases h with h | h
      · exact hst.1 h
      · omega
    isplitr
    · -- a stale message's answer: none (pre-vote and check-quorum off)
      iintro %_ %ty' %mm %hlow
      exfalso
      rcases hlow with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · rw [hpv, hcq] at h; simp at h
      · exact hnpv h
    isplitr
    · iintro %_ %_ %_ %h; exact h.elim
    isplitr
    · iintro %h; exact (hnhup h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      isplit
      · iintro %_
        iapply followerGates_false
      isplit
      · iintro %_
        iapply candidateGates_false
        rw [htr]; iexact Hnosnap
      · iintro %_
        iapply leaderGates_false
        rw [htr]; iexact Hnosnap
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: the end state is `s`
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty htrd)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    have hs' : s' = s := by
      have h := ((hend (by rw [htr]; rfl)) hty).1 hst
      rcases h with h | ⟨ty', mm, hlow, -⟩
      · exact h
      · exfalso
        rcases hlow with ⟨-, h, -⟩ | ⟨-, h, -⟩
        · rw [hpv, hcq] at h; simp at h
        · exact hnpv h
    subst hs'
    unfold stepOut
    dsimp only [staleR]
    icases Hout with (⟨Hgh, Hc⟩ | %h | %h | %h | ⟨%b, %N, %h⟩)
    · iframe Hgh
      isplitl [Hc]
      · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
        iapply trCapB_mono (some γd) γ r id c true _ _ _ (fun C cs P h => h.2.2.2) $$ Hc
      · ipureintro; exact OutTrStep.of_sub (fun _ h => h)
    all_goals exact h.elim

/-- `IgnResp`'s resources: after the receive line, raft's ghost state and the capability at the
pinned phase with the recorded server (`G0`, `G1`, `GE`: no further hook runs); `False` at the
others. -/
def ignR (bt : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (γd : GName)
    (tn : TraceNames) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (Λ : Option TraceEv → Prop) (k : Nat)
    (ma : Etcdraft.Msg) : StepG GF where
  G := iprop(trCapB (some γd) γ r id c bt (IdlePin s tn.voters cs0 P0) Λ ∗ inFlight tn k ma)
  G0 := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (IdlePin s tn.voters cs1 P0) (fun o => o.isSome = true))
  G1 := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (IdlePin s tn.voters cs1 P0) (fun o => o.isSome = true))
  GE := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (IdlePin s tn.voters cs1 P0) (fun o => o.isSome = true))
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := fun _ => iprop(⌜False⌝)
  Gc := fun _ _ _ => iprop(⌜False⌝)

/-- **`raft.Step`'s traced bundle on a response a role does not handle, at the node's term**: the
receive line (the specification records it, `respSrv`), nothing else. -/
theorem stepBundle_traced_ignResp : stepBundle_traced.on (GF := GF) (hG := hG) IgnResp := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom hnpc hsh hboot
  have hp' := hp
  obtain ⟨hterm, ty, hmty, hresp, hrole⟩ := hp'
  have htrd : ty.traced = true := by rcases hresp with rfl | rfl | rfl <;> rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of ty m ents hmty htrd hsh
  have hto' : m.To' = id := hto ty hmty htrd
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  obtain ⟨-, -, -, h4, h5, h6⟩ := mtypeOf_eq_of _ _ hmty
  have hTy : m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp ∨ m.Type' = MsgVoteResp := by
    rcases hresp with rfl | rfl | rfl
    · exact .inl (h4 rfl)
    · exact .inr (.inl (h6 rfl))
    · exact .inr (.inr (h5 rfl))
  -- every type a gate guards on, but the responses' own where a role handles them
  obtain ⟨hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup⟩ := resp_ne hTy
  have hmt2 : mtypeOf m.Type' = some ty ∧ ty.traced = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %ty %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨a0, ha0, -⟩, -⟩ := hI0
  imodintro
  iexists ignR bfl γ md c r id s γd tn cs0 (toC (confAbs tn.voters) (respSrv a0 ma)) P0 Λ k ma
  isplitl [Hcap Htok]
  · dsimp only [ignR]; iframe Hcap Htok
  -- the roles, as the specification's
  have hc : (toPState s).role ≠ .candidate ∨ ty ≠ .voteResp := by
    rcases hrole with hr | ⟨hr, hv⟩ | ⟨hr, -⟩
    · left; simp [toPState, hr, proleRole]
    · exact .inr hv
    · left; simp [toPState, hr, proleRole]
  have hl : (toPState s).role ≠ .leader ∨ ty = .voteResp := by
    rcases hrole with hr | ⟨hr, -⟩ | ⟨-, hv⟩
    · left; simp [toPState, hr, proleRole]
    · left; simp [toPState, hr, proleRole]
    · exact .inr hv
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, ignR]
    isplitr
    · -- the receive line
      iintro ⟨Hgh, Hc, Htok⟩
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg ty m ents).NumsBelow traceNumBound := (hok ty hmty hreT htrd).1
      have hps := phaseStepR_ignResp id c s ty m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hresp hterm
        hnpc hc hl hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg ty m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_traced γd γ r id c s m ents sn ctx rs ty evt bfl k ma (fun _ => False) (recvPhantoms ma)
        (IdlePin s tn.voters cs0 P0) (IdlePin s tn.voters (toC (confAbs tn.voters) (respSrv a0 ma)) P0) Λ
        (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      iframe Hgh Hc
      isplitr
      · obtain ⟨-, -, -, -, -, hr, hvr⟩ := msgAbs_recvTy hev hma
        have hty0 : (absMsg ty m ents).ty = ty := rfl
        have hrt : ma.type = .appendEntriesResponse ∨ ma.type = .requestVoteResponse := by
          rcases hresp with rfl | rfl | rfl
          · exact .inl (hr (.inl rfl))
          · exact .inl (hr (.inr rfl))
          · exact .inr (hvr rfl)
        iapply fxPresR_ignResp γ id ma _ _ _ hrt
        · rintro C cs P ⟨-, -, -, a, rfl, hR, -⟩
          have hS : (toC (confAbs C) a).state = roleAbs (toPState s).role := hR.2.1
          refine ⟨?_, ?_⟩
          · rcases hc with h | h
            · left; rw [hS]; exact roleAbs_ne_of h
            · right; intro hv; rcases hresp with rfl | rfl | rfl
              · rw [hr (.inl rfl)] at hv; cases hv
              · rw [hr (.inr rfl)] at hv; cases hv
              · exact h rfl
          · rcases hl with h | h
            · left; rw [hS]; exact roleAbs_ne_of h
            · right; exact hvr (h ▸ rfl)
        · rintro C cs P cs' P' ⟨rfl, rfl, rfl, -⟩ ⟨-, rfl, h, -⟩
          refine ⟨by simpa using h, fun a ha => ?_⟩
          exact toC_respSrv _ _ _ ma (ha0.trans ha.symm)
      · iexists tn; iframe Hdir Htok
    isplitr
    · -- the preamble: no step-down at the node's term
      unfold preGate
      iintro %_ HG0
      simp only [hnbf, ↓reduceIte]
      imodintro
      iexact HG0
    isplitr
    · iintro %h; exact (hns h).elim
    isplitr
    · iintro %h; exact (h.elim hnV hnPV).elim
    isplitr
    · iintro %h; exact (hnHup h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      isplit
      · iintro %_
        iunfold followerGates
        repeat (isplitr; · iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup])
        iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup]
      isplit
      · iintro %hrc
        have hrc' : s.role = .candidate := by
          rcases hrc with h | h
          · exact h
          · exact absurd h hnpc
        have hnVR : m.Type' ≠ MsgVoteResp := by
          rcases hrole with hr | ⟨-, hv⟩ | ⟨hr, -⟩
          · rw [hr] at hrc'; cases hrc'
          · intro h; rw [h] at hmty; cases hmty; exact hv rfl
          · rw [hr] at hrc'; cases hrc'
        iunfold candidateGates
        repeat (isplitr; · first | (rw [htr]; iexact Hnosnap) | iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup, hnVR])
        iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup, hnVR]
      · iintro %hrl
        have hnHR : m.Type' ≠ MsgHeartbeatResp := by
          rcases hrole with hr | ⟨hr, -⟩ | ⟨-, rfl⟩
          · rw [hr] at hrl; cases hrl
          · rw [hr] at hrl; cases hrl
          · intro h; rw [h] at hmty; cases hmty
        have hnAR : m.Type' ≠ MsgAppResp := by
          rcases hrole with hr | ⟨hr, -⟩ | ⟨-, rfl⟩
          · rw [hr] at hrl; cases hrl
          · rw [hr] at hrl; cases hrl
          · intro h; rw [h] at hmty; cases hmty
        iunfold leaderGates
        repeat (isplitr; · first | (rw [htr]; iexact Hnosnap) | iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup, hnHR, hnAR])
        iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup, hnHR, hnAR]
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: the end state is `s`
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => (by obtain ⟨ty, h1, h2, -⟩ := hp.2; rcases h2 with rfl | rfl | rfl <;> exact CloseAt.of_traced h1 rfl))
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    have hs' : s' = s := by
      obtain ⟨pvs, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs] at h
      exact ignResp_end hp h
    subst hs'
    unfold stepOut
    dsimp only [ignR]
    ihave H : iprop(ownStepGhost γ md c id s' ∗
        trCapB (some γd) γ r id c true (IdlePin s' tn.voters (toC (confAbs tn.voters) (respSrv a0 ma)) P0)
          (fun o => o.isSome = true)) $$ [Hout]
    · icases Hout with (H | H | H | %h | ⟨%b, %N, %h⟩)
      · iexact H
      · iexact H
      · iexact H
      · exact h.elim
      · exact h.elim
    icases H with ⟨Hgh, Hc⟩
    iframe Hgh
    isplitl [Hc]
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (fun C cs P h => h.2.2.2) $$ Hc
    · ipureintro; exact OutTrStep.of_sub (fun _ h => h)

/-- A vote request's answer's numbers (the term is the node's or the request's). -/
theorem vresp_nums (id : w64) (s : NState) (m : MessageM) (rej : Bool)
    (hT : uint.Z s.term + 1 < traceNumBound) (hmT : uint.Z m.Term' < traceNumBound) :
    (vrespMsgOf id s m rej).NumsBelow traceNumBound := by
  have hb : traceNumBound = 2 ^ 61 := rfl
  rw [hb] at hT hmT
  unfold vrespMsgOf Msg.plain Msg.NumsBelow
  dsimp only
  rw [hb]
  refine ⟨?_, by simp, by simp, by simp, by simp, by simp⟩
  split <;> word

/-- The send line of a vote request's answer, skipped by the specification: its gate from the
capability at a pinned phase, with a frame `X`. -/
theorem skipGate_vresp (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (s1 : NState) (x : Msg)
    (C0 : List w64) (cs1 : ServerC) (P1 : List Etcdraft.Msg) (X : IProp GF)
    (hty : x.ty = .voteResp) (hne : x.src ≠ x.dst)
    (hOk : ∀ e, (∃ mm ∈ [x], SendEvOf (W64 15) id s1 c mm e) → TraceEv.Ok (elements c.incoming).length e) :
    (X ∗ trCapB (some γd) γ r id c true (VPin C0 cs1 P1) (fun o => o.isSome = true) : IProp GF) ⊢
      HookGateOpt (some γd) r (sendOutGate id s1 c MsgVoteResp [x])
        iprop(X ∗ (trCapB (some γd) γ r id c true (VPin C0 cs1 P1) (fun o => o.isSome = true) ∗ emp)) := by
  have hg : sendOutGate id s1 c MsgVoteResp [x] =
      some (fun e => ∃ mm ∈ [x], SendEvOf (W64 15) id s1 c mm e) := rfl
  rw [hg]
  iintro ⟨HX, Hc⟩
  iapply hookGateOpt_frame
  iframe HX
  icases trCapB_logger γd γ r id c true _ _ $$ Hc with ⟨%tl, #Htl, Hc⟩
  iapply hookGate_opt
  iapply trCapB_hookGate (some γd) γ r id c tl _ true _ _ _ _ iprop(emp)
    (phaseStepB_skip id c s1 (W64 15) x C0 cs1 P1 (.inr rfl) hne (.inr (.inr hty)))
    (fun h => by cases h) (fun _ _ => rfl) (fun _ => hOk) (fun h => by cases h)
  iframe Htl Hc
  simp only [FxPresUT]
  iapply fxPres_upd
  iapply fxPres_skip


/-- **A vote request of the node's term.** -/
def VoteReq (s : NState) (m : MessageM) : Prop := m.Type' = MsgVote ∧ m.Term' = s.term

/-- `VoteReq`'s resources: after the receive line, raft's ghost state and the capability at the pinned
phase of the specification's handling (`G0`, `G1`); after the answer's send line (`GE`) the same; `False`
at the others. -/
def voteR (bt : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (γd : GName)
    (tn : TraceNames) (cs0 cs1 : ServerC) (P0 P1 : List Etcdraft.Msg) (Λ : Option TraceEv → Prop) (k : Nat)
    (ma : Etcdraft.Msg) : StepG GF where
  G := iprop(trCapB (some γd) γ r id c bt (IdlePin s tn.voters cs0 P0) Λ ∗ inFlight tn k ma)
  G0 := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (VPin tn.voters cs1 P1) (fun o => o.isSome = true))
  G1 := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (VPin tn.voters cs1 P1) (fun o => o.isSome = true))
  GE := fun _ => iprop(ownStepGhost γ md c id s ∗
    (trCapB (some γd) γ r id c true (VPin tn.voters cs1 P1) (fun o => o.isSome = true) ∗ emp))
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := fun _ => iprop(⌜False⌝)
  Gc := fun _ _ _ => iprop(⌜False⌝)

/-- **`raft.Step`'s traced bundle on a vote request of the node's term**: the receive line (the
specification's grant decision, `HandleRequestVoteRequest`), then the answer's send line, which the
specification skips; raft's decision is the specification's (`voteEnd_simIdle`). -/
theorem stepBundle_traced_voteReq : stepBundle_traced.on (GF := GF) (hG := hG) VoteReq := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom hnpc hsh hboot
  obtain ⟨hTy, hterm⟩ := hp
  have hmty : mtypeOf m.Type' = some .vote := by rw [hTy]; rfl
  have htrd : MsgType.traced .vote = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .vote m ents hmty htrd hsh
  have hto' : m.To' = id := hto .vote hmty htrd
  have hne : id ≠ m.From' := fun h => hsh.2.2 (.inl hTy) (by rw [hto', h])
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hvt : vrespTyOf m = MsgVoteResp := by simp [vrespTyOf, hTy]
  obtain ⟨hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR, hnPV, hnHup⟩ := vote_ne hTy
  have hmt2 : mtypeOf m.Type' = some .vote ∧ MsgType.traced .vote = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %MsgType.vote %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨a0, ha0, hR0, hs0, hP0, bt, bc, bl⟩, -⟩ := hI0
  imodintro
  iexists voteR bfl γ md c r id s γd tn cs0 (toC (confAbs tn.voters) (vrSrv a0 (idAbs m.From') ma)) P0
    (P0 ++ [vrResp a0 (idAbs id) (idAbs m.From') ma]) Λ k ma
  isplitl [Hcap Htok]
  · dsimp only [voteR]; iframe Hcap Htok
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, voteR]
    isplitr
    · -- the receive line
      iintro ⟨Hgh, Hc, Htok⟩
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .vote m ents).NumsBelow traceNumBound := (hok .vote hmty hreT htrd).1
      have hps := phaseStepR_voteReq id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hterm hnpc hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .vote m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_traced γd γ r id c s m ents sn ctx rs .vote evt bfl k ma (fun _ => False) (recvPhantoms ma)
        _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      iframe Hgh Hc
      isplitr
      · obtain ⟨hmt, -, hms, -⟩ := msgAbs_recvTy hev hma
        iapply fxPresR_voteReq γ id ma _ s tn.voters cs0 _ P0 _ (idAbs m.From') hms
        intro a ha
        have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
        refine ⟨toC_vrSrv _ _ _ _ _ hcx, vrResp_toC _ _ _ _ _ _ hcx, ?_⟩
        have h1 : a0.currentTerm = a.currentTerm := congrArg ServerC.currentTerm hcx
        rw [hmt, ← h1, hR0.1]
        show uint.Z m.Term' = uint.Z (toPState s).term
        rw [hterm]; rfl
      · iexists tn; iframe Hdir Htok
    isplitr
    · -- the preamble: no step-down at the node's term
      unfold preGate
      iintro %_ HG0
      simp only [hnbf, ↓reduceIte]
      imodintro
      iexact HG0
    isplitr
    · iintro %h; exact (hns h).elim
    isplitr
    · -- the answer's send line, skipped by the specification
      iintro %_ %pvs %rej ⟨Hgh, Hc⟩
      rw [hpre pvs, hvt, htr]
      iapply hookGateOpt_fupd_recv
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      have hn := vresp_nums id s m rej hT hmT
      iapply skipGate_vresp γd γ r id c s (vrespMsgOf id s m rej) tn.voters _ _ (ownStepGhost γ md c id s)
        (by simp [vrespMsgOf, hTy, Msg.plain]) (by simp only [vrespMsgOf, Msg.plain]; exact hne)
        (fun e ⟨mm, hmm, he⟩ => by
          simp only [List.mem_singleton] at hmm; subst hmm
          exact sendEvOf_ok _ id s c _ e _ he (by decide) (by word) Hb.2 Hb.1 hn (Nat.le_refl _))
      iframe Hgh Hc
    isplitr
    · iintro %h; exact (hnHup h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      isplit
      · iintro %_
        iunfold followerGates
        repeat (isplitr; · iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR])
        iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR]
      isplit
      · iintro %_
        iunfold candidateGates
        repeat (isplitr; · first | (rw [htr]; iexact Hnosnap) |
          iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR])
        iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR]
      · iintro %_
        iunfold leaderGates
        repeat (isplitr; · first | (rw [htr]; iexact Hnosnap) |
          iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR])
        iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR]
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: raft's vote, the specification's
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty htrd)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    have hve : VoteEnd id s m s' := by
      rcases ((hend (by rw [htr]; rfl)) hty).2.2.1 hns hTy with ⟨h, -⟩ | ⟨pvs, h⟩
      · rw [hcq] at h; cases h
      · rw [hpre pvs] at h; exact h
    have hI := voteEnd_simIdle tn.voters id s s' m ents a0 ma hR0 hs0 bt bc bl hTy hterm hnpc hma hve
    have hP0' : P0 = pendAbs tn.voters s.outbox := hP0
    rw [← hP0'] at hI
    have hout : OutTrStep s s' := by
      intro _ x hx
      rcases hve with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        (simp only [sendMsgs, List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl
         · exact .inl hx
         · exact .inr (Msg.trOk_of_nums (by unfold vrespMsgOf; split <;> (intro h; cases h)) (by unfold vrespMsgOf; split <;> (intro h; cases h)) (fun _ => vresp_nums id s m _ hT hmT)))
    have hmono : ∀ C cs P, VPin tn.voters (toC (confAbs tn.voters) (vrSrv a0 (idAbs m.From') ma))
        (P0 ++ [vrResp a0 (idAbs id) (idAbs m.From') ma]) C cs P → SimIdle C s' cs P := by
      rintro C cs P ⟨rfl, rfl, rfl⟩; exact hI
    unfold stepOut
    dsimp only [voteR]
    icases Hout with (⟨Hgh, Hc⟩ | ⟨Hgh, Hc⟩ | ⟨Hgh, Hc, -⟩ | %h | ⟨%b, %N, %h⟩)
    · iframe Hgh
      isplitl [Hc]
      · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
        iapply trCapB_mono (some γd) γ r id c true _ _ _ hmono $$ Hc
      · ipureintro; exact hout
    · iframe Hgh
      isplitl [Hc]
      · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
        iapply trCapB_mono (some γd) γ r id c true _ _ _ hmono $$ Hc
      · ipureintro; exact hout
    · iframe Hgh
      isplitl [Hc]
      · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
        iapply trCapB_mono (some γd) γ r id c true _ _ _ hmono $$ Hc
      · ipureintro; exact hout
    · exact h.elim
    · exact h.elim

end paths

end EtcdGrove
end Perennial
