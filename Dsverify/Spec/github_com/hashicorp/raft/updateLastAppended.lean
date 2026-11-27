/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/updateLastAppended.lean (241f27e).
-/
/-
`raft.updateLastAppended`'s spec (replication subsystem, internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `updateLastAppended(s, req)` (stage 2): after a successful request `req` of term `T` (any
fraction: pipelineDecode has it read-only), if it had entries, `j` acknowledged its last index in `T`
(`ackIs`; a heartbeat-shaped success carries none, and the code touches the commitment only when
`Entries ≠ []`): stores `nextIndex` (with the writer's half, `nextHalf`, and the shared cell;
REPL-3) and records the match in the commitment. No longer votes for verify futures (fix `d660d8b`). -/
abbrev github_com.hashicorp.raft.updateLastAppended.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s req : Loc) (rq : AppendEntriesRequest)
    (snd : SID) (prev pt : Nat) (ents : List Entry) (lci : Nat) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ replShared r γ rc i T j s ∗
     nextHalf s ∗ req ↦{dq} rq ∗ aeBody rq snd T prev pt ents lci ∗
     (⌜ents = []⌝ ∨ ackIs γ j T (prev + ents.length)) }}
    (App (App (Val (@! github_com.hashicorp.raft.updateLastAppended)) (Val #s)) (Val #req))
  {{ RET #(); nextHalf s ∗ req ↦{dq} rq }}

end spec

end Perennial
