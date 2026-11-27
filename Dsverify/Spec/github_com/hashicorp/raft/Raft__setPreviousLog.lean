/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setPreviousLog.lean (241f27e).
-/
/-
`raft.(*Raft).setPreviousLog`'s spec (replication subsystem, internal).
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

/-- `(*Raft).setPreviousLog`, by the replication goroutine of the leader `i` of term `T`: the
previous entry `(prev, pt)` of a request whose first entry is at `nextIndex`, read from the log
store (an entry of `llog T`, or the term has moved on), or an error. -/
abbrev github_com.hashicorp.raft.Raft.setPreviousLog.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (req : Loc)
    (rq : AppendEntriesRequest) (nextIndex : w64) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     leaderIs γ T i ∗ termLb γ i T ∗ req ↦ rq ∗ rtok tid }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setPreviousLog")) (Val #req))
      (Val #nextIndex))
  {{ (err : GoInterface), RET #err; rtok tid ∗ ∃ prev pt : w64,
      req ↦ { rq with PrevLogEntry' := prev, PrevLogTerm' := pt } ∗
      (⌜err ≠ interface.nil⌝ ∗ (∃ c, isRaftErr c err) ∨
       ⌜err = interface.nil ∧ uint.nat prev + 1 = uint.nat nextIndex⌝ ∗
         orStale γ i T (prevOk γ T (uint.nat prev) (uint.nat pt))) }}

end spec

end Perennial
