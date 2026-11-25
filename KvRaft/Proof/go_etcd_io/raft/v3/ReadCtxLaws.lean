-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/ReadCtxLaws.lean` (etc/copy-part.py; rerun it, do not edit).
/-
(2026-11-22, kvraft's checker) **A read context's log is unique**: `readCtxAfter γ N c l0` (`InvNode`,
sealed) names the one log `l0` the context `c` was committed after (raft's `ctxs` map holds one entry
per context), so two of them agree. What a client needs that mints a read context in one place and
gets its answer in another: kvraft's checking client mints the context (`readCtx_commit_after`, after
the log of the read's start), and the replica's answer names the context's log existentially (the
wire protocol's fact); agreement says the answer's log is the client's.

A law of its own module, so that adding it rebuilds none of `InvNode`'s importers; raft's own
modules `import all` the API module, as this one does.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.InvNode
import all KvRaft.Proof.go_etcd_io.raft.v3.InvNode
import KvRaft.Proof.go_etcd_io.raft.v3.InvApi

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **Two logs a read context was committed after are the same.** -/
theorem readCtxAfter_agree (γ : Cluster) (N : Namespace) (c : List w8) (l0 l1 : List LogEntry) :
    readCtxAfter (GF := GF) γ N c l0 ∗ readCtxAfter γ N c l1 ⊢ ⌜l0 = l1⌝ := by
  unfold readCtxAfter ApiImpl.readCtxAfter
  iintro ⟨⟨%γq, #Hel⟩, ⟨%γq', #Hel'⟩⟩
  ihave %Hag := ghostMapElem_agree $$ Hel Hel'
  ipureintro
  simp only [Prod.mk.injEq] at Hag
  exact Hag.2

end api

end EtcdGrove
end Perennial
