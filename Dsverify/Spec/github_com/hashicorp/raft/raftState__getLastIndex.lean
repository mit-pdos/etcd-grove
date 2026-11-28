/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__getLastIndex.lean (241f27e).
-/
/-
`raft.(*raftState).getLastIndex`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted). No snapshot: the last log index.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

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

/-- `(*raftState).getLastIndex`: Called through `*Raft` (promoted). By the main goroutine (with its
protocol state and `lastApplied` authority, as `getLastEntry`; stage 3, check N1): the last log index
(the last snapshot is within the log). By any goroutine: some index. -/
abbrev github_com.hashicorp.raft.raftState.getLastIndex.spec : Prop :=
  (∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (a : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗ srvV rc s ∗
     monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜a ≤ s.dur.1⌝ }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getLastIndex")) (Val #()))
  {{ (x : w64), RET #x; ⌜uint.nat x = s.log.length⌝ ∗
      ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗ srvV rc s ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half a }}) ∧
  (∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getLastIndex")) (Val #()))
  {{ (x : w64), RET #x; True }})

end spec

end Perennial
