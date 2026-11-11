/-
Lean-first (no Rocq counterpart). **What the node API gives the traced `raft.Step` of a received
message** (2026-11-10, trace-check Q8 stage 1 slice 21, `notes/decisions.md`, "Q8 stage 1 (slice
21)"). Raft-internal (not on `etc/api/raft.txt`).

`stepBundle_traced.on` (`TracedRaftStep.lean`) takes, of the message it steps, its raft facts
(`isMessageC` of its abstraction, for a traced type), its numbers (`MsgTrOk`, for every type) and
`TrRecvShape`. The node API holds the message's `isRaftMsg` (`ApiVocab.lean`, what `node.Step`'s and
`RawNode.Step`'s callers have of a message the transport delivers): `isRaftMsg_trRecv` reads the first
two and, in a traced cluster, `TrRecvShape` off it: its third clause (a vote request, an append
request or a heartbeat not from its destination) from `SentMsgShape`, its first two (a heartbeat without
entries, a heartbeat response not rejecting) from `MsgTrOk` (plan Q18 (b), 2026-11-11: `Msg.TrOk`'s
clauses, which raft establishes where it queues the message; `SentMsgShape` and `isMessage` do not
state them, slice 19b's finding).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStep
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section recv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`TrRecvShape`'s third clause from `SentMsgShape`**: a vote request, an append request or a
heartbeat is not from its destination. -/
theorem sentMsgShape_fromTo {st : MsgSt} (H : SentMsgShape st) :
    st.msg.Type' = MsgVote ∨ st.msg.Type' = MsgApp ∨ st.msg.Type' = MsgHeartbeat →
      st.msg.From' ≠ st.msg.To' := by
  intro hty
  obtain ⟨-, -, -, -, Hft, -⟩ := H
  rcases hty with h | h | h <;> rw [h] at Hft <;>
    exact Hft (by simp [MsgVote, MsgApp, MsgHeartbeat, MsgReadIndex]) (by simp [MsgVote, MsgApp,
      MsgHeartbeat, MsgVoteResp]) (by simp [MsgVote, MsgApp, MsgHeartbeat, MsgPreVoteResp])
      (by simp [MsgVote, MsgApp, MsgHeartbeat, MsgTransferLeader])
      (fun h' => by simp [MsgVote, MsgApp, MsgHeartbeat, MsgAppResp] at h')

/-- **`TrRecvShape` from the message's facts** (Q18 (b)): in a traced cluster, `MsgTrOk` of the
heartbeat's and the heartbeat response's abstractions gives the first two clauses (`Msg.TrOk`'s); the
third is `SentMsgShape`'s (`sentMsgShape_fromTo`). -/
theorem trRecvShape_of_trOk (γ : RaftNames) (m : MessageM) (ents : List EntryM) (ctx : List w8)
    (hre : γ.reTrace.isSome)
    (htr : ∀ ty, mtypeOf m.Type' = some ty → MsgTrOk γ (absMsg ty m ents ctx))
    (hft : m.Type' = MsgVote ∨ m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat → m.From' ≠ m.To') :
    TrRecvShape m ents := by
  refine ⟨fun h => ?_, fun h => ?_, hft⟩
  · have := (htr .heartbeat (by rw [h]; rfl) hre rfl).2.1 rfl
    simpa [absMsg, absMsgFrom, Msg.mkV] using this
  · have := (htr .heartbeatResp (by rw [h]; rfl) hre rfl).2.2 rfl
    simpa [absMsg, absMsgFrom, Msg.mkV] using this

/-- **What `stepBundle_traced.on` takes of the received message, from `isRaftMsg`**: its raft facts
for a traced type (`isMessageC` of `absMsg`: a traced type is not a snapshot, whose abstraction is
`absSnap`), its numbers for every type (`MsgTrOk`: `isMessageC`'s for a type with an abstraction,
vacuous for an untraced one), `TrRecvShape`'s third clause (`sentMsgShape_fromTo`), and (Q18 (b)) in a
traced cluster the whole of `TrRecvShape` (`trRecvShape_of_trOk`). -/
theorem isRaftMsg_trRecv (γ : RaftNames) (id : w64) (st : MsgSt) :
    isRaftMsg (GF := GF) γ id st ⊢
      (□ ∀ ty : MsgType, ⌜mtypeOf st.msg.Type' = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty st.msg st.ents st.ctx)) ∗
        ⌜∀ ty, mtypeOf st.msg.Type' = some ty → MsgTrOk γ (absMsg ty st.msg st.ents st.ctx)⌝ ∗
        ⌜st.msg.Type' = MsgVote ∨ st.msg.Type' = MsgApp ∨ st.msg.Type' = MsgHeartbeat →
          st.msg.From' ≠ st.msg.To'⌝ ∗
        ⌜γ.reTrace.isSome → TrRecvShape st.msg st.ents⌝ := by
  iintro #H
  ihave #H' := H
  unfold isRaftMsg
  icases H with ⟨%Hsh, ⟨%a, %Ha, #Hl⟩, -⟩
  -- the abstraction of a type with one, but a snapshot's
  have Habs : ∀ ty, mtypeOf st.msg.Type' = some ty → ty ≠ .snap →
      a = some (absMsg ty st.msg st.ents st.ctx) := by
    intro ty hty hns
    rcases Ha with ⟨Hn, -⟩ | ⟨ty', Hty', -, rfl⟩ | ⟨sv, Hs, -, -⟩
    · rw [hty] at Hn; cases Hn
    · rw [hty] at Hty'; cases Hty'; rfl
    · rw [hty] at Hs; cases Hs; exact absurd rfl hns
  have Hsnap : ∀ ty : MsgType, ty.traced = true → ty ≠ .snap := by
    intro ty h e; subst e; simp [MsgType.traced] at h
  ihave %Htr : ⌜∀ ty, mtypeOf st.msg.Type' = some ty → MsgTrOk γ (absMsg ty st.msg st.ents st.ctx)⌝ $$ []
  · iintro %ty %hty
    cases htr : ty.traced with
    | false => ipureintro; exact MsgTrOk.of_untraced γ (by simpa [absMsg, absMsgFrom, Msg.mkV] using htr)
    | true =>
      rw [Habs ty hty (Hsnap ty htr)]
      simp only [Option.toList_some]
      ihave #Hm := BigSepL.bigSepL_singleton.1 $$ Hl
      iapply isMessageC_trOk $$ Hm
  isplitl []
  · imodintro
    iintro %ty %hty
    rw [Habs ty hty.1 (Hsnap ty hty.2)]
    simp only [Option.toList_some]
    iapply BigSepL.bigSepL_singleton.1 $$ Hl
  isplitl []
  · ipureintro; exact Htr
  isplitl []
  · ipureintro; exact sentMsgShape_fromTo Hsh
  ipureintro
  exact fun hre => trRecvShape_of_trOk γ st.msg st.ents st.ctx hre Htr (sentMsgShape_fromTo Hsh)

end recv

end EtcdGrove
end Perennial
