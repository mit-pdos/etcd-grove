/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__getLastEntry.lean (241f27e).
-/
/-
`raft.(*raftState).getLastEntry`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted). No snapshot: the last log entry's index and term.
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

/-- `(*raftState).getLastEntry`: Called through `*Raft` (promoted), by the main goroutine. The last log
entry's index and term: (stage 3, review T1-1) the last snapshot is at most the last log index (it is
durable at `i`, or at most `lastApplied`, and `lastApplied ≤ dur ≤ |log|`), so the `max` returns the
log's. -/
abbrev github_com.hashicorp.raft.raftState.getLastEntry.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (a : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗ srvV rc s ∗
     monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜a ≤ s.dur.1⌝ }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getLastEntry")) (Val #()))
  {{ (x y : w64), RET (PairV #x #y); ⌜uint.nat x = s.log.length ∧ uint.nat y = lastTerm s.log⌝ ∗
      ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗ srvV rc s ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half a }}

end spec

end Perennial
