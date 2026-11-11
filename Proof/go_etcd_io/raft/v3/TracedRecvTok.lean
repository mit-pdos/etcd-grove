/-
Lean-first (no Rocq counterpart). **A traced message's token** (`recvTokOf`), moved here from
`TracedRaftStep.lean` (2026-11-11, trace-check Q8 stage 1 slice 26n, `notes/decisions.md`, "Q8 stage 1
(slice 26n)") so that `ownRawNode`'s queue (`pendingRel`, `InvRawnode.lean`) can hold the self-addressed
messages' tokens from `Ready` to `Advance` (plan, Q26 (a)).
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimGhost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 TraceSim

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

end traced

end EtcdGrove
end Perennial
