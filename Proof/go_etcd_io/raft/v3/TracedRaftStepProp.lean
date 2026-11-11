/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on `MsgProp` at a leader: the lines'
pieces** (2026-11-11, trace-check Q8 stage 1 slice 22a, `notes/decisions.md`, "Q8 stage 1 (slice 22a)").

A leader's proposal logs one `Replicate` line per entry (`traceReplicate`, `"Hgprep"`), then the
self-acknowledgement's `SendAppendEntriesResponse` (`"Hgpack"`, at the state with the batch appended),
then one `SendAppendEntriesRequest` per peer (`"#Hgpapp"`). This file has the lines' phase steps:

- **the self-acknowledgement's** (`phaseStepB_selfAck`: `phaseStepB_send_pin` with
  `lineEffect_selfAck`, at a leader's state, `selfAck` being the protocol's `pselfAck`).

Not here yet (the decisions entry has the exact list): the `Replicate` lines' phase steps and facts
(the facts create the entries' records, raft's ghost state moving to the proposal's appended state),
`stepClose` relaxed to take that state back, and the bundle.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepHup

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- `appendEntry`'s self-acknowledgement is the protocol's (`pselfAck`): the new last index is the
log's last index. -/
theorem selfAck_eq_pselfAck (id : w64) (s : NState) : selfAck id s = pselfAck id (toPState s) := by
  have h : logLast s.logst = plastIndex (toPState s) := by
    simp only [logLast, plastIndex, plogLastIndexZ, toPState, List.length_append]
    push_cast; rw [Int.add_assoc]
  simp only [selfAck, pselfAck, h]
  rfl

end pure

section phases
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The self-acknowledgement's phase step, pinned** (`phaseStepB_send_pin` with `lineEffect_selfAck`),
at a leader's state `s1` (the proposal's appended state, on `MsgProp`'s path). -/
theorem phaseStepB_selfAck (id : w64) (c : CfgM) (s1 : NState) (o : List Msg)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (ma0 : Etcdraft.Msg)
    (hma : TraceSim.msgAbs C0 C0.length (selfAck id s1) = some ma0) (hrole : s1.role = .leader) :
    PhaseStepB id c (SendEvOf (W64 11) id s1 c (selfAck id s1)) (PinAt s1 C0 cs0 P0 o)
      (PinAt s1 C0 cs0 (P0 ++ [ma0]) (o ++ [selfAck id s1])) := by
  rw [selfAck_eq_pselfAck] at hma ⊢
  apply phaseStepB_send_pin id c s1 _ o _ C0 cs0 P0 ma0 hma rfl
    (fun e he => ⟨he.2.1, sendEvOf_notBoot he (by decide) (by decide) (by decide)⟩)
  intro C e a he hin hout hC hR hs bt bc bl
  exact ⟨_, rfl, lineEffect_selfAck C e id s1 c a _ he hin hout hC hR hs hrole bt bc bl⟩

end phases

end EtcdGrove
end Perennial
