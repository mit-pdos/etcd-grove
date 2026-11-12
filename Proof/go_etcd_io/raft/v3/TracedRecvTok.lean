/-
Lean-first (no Rocq counterpart). **A traced message's token** (`recvTokOf`), moved here from
`TracedRaftStep.lean` (2026-11-11, trace-check Q8 stage 1 slice 26n, `notes/decisions.md`, "Q8 stage 1
(slice 26n)") so that `ownRawNode`'s queue (`pendingRel`, `InvRawnode.lean`) can hold the self-addressed
messages' tokens from `Ready` to `Advance` (plan, Q26 (a)).

(2026-11-12, trace-check implementation step 1; the design's Probe B, P3) Also the types a traced node
hands out (`TrNetTy`, moved from `TracedRawNode.lean`; `TrSent`) and a handed-out message's token over a
`RaftNames` (`trTokR`, moved from Probe B's `TracedEscrow.lean`), below `InvNodeChan`, whose gated
`netP`/`fwdP` and escrow (`InvRtk.lean`) read them.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimGhost
public import Proof.go_etcd_io.raft.v3.InvRaftlog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- **The network types a traced node steps** (`node.Step`'s, in the harness): the replication and
election messages of a cluster with pre-vote and check-quorum off, no snapshot, no read-index, no
leader transfer. (2026-11-12: moved here from `TracedRawNode.lean`, the design's Probe B, P3.) -/
def TrNetTy (t : w32) : Prop :=
  t = MsgApp ∨ t = MsgAppResp ∨ t = MsgVote ∨ t = MsgVoteResp ∨ t = MsgHeartbeat ∨ t = MsgHeartbeatResp

/-- A traced network type is none of the listed others. -/
theorem TrNetTy.ne {t : w32} (h : TrNetTy t) {u : w32}
    (hu : u ≠ MsgApp ∧ u ≠ MsgAppResp ∧ u ≠ MsgVote ∧ u ≠ MsgVoteResp ∧ u ≠ MsgHeartbeat ∧
      u ≠ MsgHeartbeatResp) : t ≠ u := by
  intro e; subst e
  rcases h with h | h | h | h | h | h
  · exact hu.1 h
  · exact hu.2.1 h
  · exact hu.2.2.1 h
  · exact hu.2.2.2.1 h
  · exact hu.2.2.2.2.1 h
  · exact hu.2.2.2.2.2 h

/-- **The types a traced node hands out** (the design's §3.6): a traced network type, or a forwarded
proposal of normal entries. -/
def TrSent (st : MsgSt) : Prop :=
  TrNetTy st.msg.Type' ∨ (st.msg.Type' = MsgProp ∧ ∀ e ∈ st.ents, e.Type' = EntryNormal)

/-- A handed-out message is no `MsgSnap`. -/
theorem TrSent.ne_snap {st : MsgSt} (h : TrSent st) : st.msg.Type' ≠ MsgSnap := by
  rcases h with h | ⟨h, -⟩
  · rcases h with h | h | h | h | h | h <;> rw [h] <;>
      simp [MsgSnap, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp]
  · rw [h]; simp [MsgProp, MsgSnap]

end pure

/-- `TrNetTy.ne` at a constant: the six inequalities by `decide`. -/
macro "trnet_ne" h:term:max : tactic =>
  `(tactic| exact TrNetTy.ne $h ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩)

section traced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The received message's token, traced** (the node API's, from the transport): for a message of a
traced type, its specification message (`msgAbs` at the cluster's voters) in flight under some token
`k` (`inFlight`, which the receive line consumes: `trCapB_hookGateRecv`); nothing for another type. -/
def recvTokOf (γd : GName) (m : MessageM) (ents : List EntryM) (ctx : List w8) : IProp GF :=
  iprop(∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
    ∃ (tn : TraceNames) (k : Nat) (ma : Etcdraft.Msg), traceDir γd tn ∗
      ⌜TraceSim.msgAbs tn.voters tn.voters.length (absMsg ty m ents ctx) = some ma⌝ ∗ inFlight tn k ma)

instance recvTokOf_timeless (γd : GName) (m : MessageM) (ents : List EntryM) (ctx : List w8) :
    Timeless (recvTokOf (GF := GF) γd m ents ctx) := by
  unfold recvTokOf TraceSim.traceDir TraceSim.inFlight; infer_instance

/-- **A handed-out message's token, over a `RaftNames`** (the node API's `trTok` body, `InvNode.lean`,
and the escrow's slots, `InvRtk.lean`; the design's §3.1, Probe B's P4): untraced nothing; traced,
its type handed out (`TrSent`) and the receiver's token. -/
def trTokR (ρ : RaftNames) (st : MsgSt) : IProp GF :=
  match ρ.reTrace with
  | none => iprop(True)
  | some γd => iprop(⌜TrSent st⌝ ∗ recvTokOf γd st.msg st.ents st.ctx)

instance trTokR_timeless (ρ : RaftNames) (st : MsgSt) : Timeless (trTokR (GF := GF) ρ st) := by
  unfold trTokR; cases ρ.reTrace <;> dsimp only <;> infer_instance

theorem trTokR_none (ρ : RaftNames) (st : MsgSt) (h : ρ.reTrace = none) : ⊢ trTokR (GF := GF) ρ st := by
  unfold trTokR; rw [h]; iintro; ipureintro; trivial

theorem trTokRs_none {A : Type} (ρ : RaftNames) (f : A → MsgSt) (l : List A) (h : ρ.reTrace = none) :
    ⊢ [∗list] x ∈ l, trTokR (GF := GF) ρ (f x) := by
  induction l with
  | nil => exact BigSepL.bigSepL_nil.2
  | cons x l ih =>
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iapply trTokR_none ρ (f x) h
    · iapply ih

end traced

end EtcdGrove
end Perennial
