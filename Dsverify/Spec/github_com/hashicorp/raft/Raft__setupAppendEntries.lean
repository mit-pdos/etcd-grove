/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setupAppendEntries.lean (241f27e).
-/
/-
`raft.(*Raft).setupAppendEntries`'s spec (replication subsystem, internal).
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

/-- `(*Raft).setupAppendEntries`, by the replication goroutine of the leader `i` of term `T`:
the request's contents (`aeBody`) and, from what it read, its validity or the term moved on;
or an error. -/
abbrev github_com.hashicorp.raft.Raft.setupAppendEntries.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s req : Loc)
    (rq : AppendEntriesRequest) (nextIndex lastIndex : w64) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     replShared r γ rc i T j s ∗ leaderIs γ T i ∗ termLb γ i T ∗ req ↦ rq ∗ rtok tid }}
    (App (App (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setupAppendEntries"))
      (Val #s)) (Val #req)) (Val #nextIndex)) (Val #lastIndex))
  {{ (err : GoInterface), RET #err; rtok tid ∗ ∃ rq' : AppendEntriesRequest, req ↦ rq' ∗
      (⌜err ≠ interface.nil⌝ ∗ (∃ c, isRaftErr c err) ∨
       ⌜err = interface.nil⌝ ∗ ∃ (prev pt : Nat) (ents : List Entry) (lci : Nat),
         aeBody rq' i T prev pt ents lci ∗ orStale γ i T (aeValid γ T prev pt ents lci)) }}

end spec

end Perennial
