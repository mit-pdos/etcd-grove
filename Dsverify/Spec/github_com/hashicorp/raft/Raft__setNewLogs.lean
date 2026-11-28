/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setNewLogs.lean (241f27e).
-/
/-
`raft.(*Raft).setNewLogs`'s spec (replication subsystem, internal).
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

/-- `(*Raft).setNewLogs`, by the replication goroutine of the leader `i` of term `T`: the
entries from `nextIndex = prev + 1` (at most `MaxAppendEntries`, up to `lastIndex`), read from the
log store (entries of `llog T`, or the term has moved on), or an error. -/
abbrev github_com.hashicorp.raft.Raft.setNewLogs.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (req : Loc)
    (rq : AppendEntriesRequest) (nextIndex lastIndex : w64) (prev : Nat) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     leaderIs γ T i ∗ termLb γ i T ∗ req ↦ rq ∗ rtok tid ∗ ⌜prev + 1 = uint.nat nextIndex⌝ }}
    (App (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setNewLogs")) (Val #req))
      (Val #nextIndex)) (Val #lastIndex))
  {{ (err : GoInterface), RET #err; rtok tid ∗ ∃ sl : GoSlice,
      req ↦ { rq with Entries' := sl } ∗
      (⌜err ≠ interface.nil⌝ ∗ (∃ c, isRaftErr c err) ∨
       ⌜err = interface.nil⌝ ∗ ∃ ents : List Entry, entPtrs sl prev ents ∗
         orStale γ i T (entsOk γ T prev ents)) }}

end spec

end Perennial
