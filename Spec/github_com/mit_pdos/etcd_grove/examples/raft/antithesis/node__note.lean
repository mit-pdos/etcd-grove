/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 1: nothing proves `node.note.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`(*node).note(by, ents)`, batching: after an input (or a storage step's acknowledgement, or a
`Ready` taken alone), the report of what raft has in memory (`mem`, from `RawNode.BasicStatus` and the
logger's count of automatic leavings) if it changed or was a request to append; `items` counts the
reports with `w = 1` (`QueueView`). `ents` is what the input asked a leader to append.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDur

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev node.note.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg) (q : Qp)
    (sl : GoSlice) (es : List EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v (.loop net₀ xnet₀ r₁ xs₁) ∗ entsRO sl es ∗ netAdder c γ.toAntNames q ∗
      threadTok ∗ ⌜DrainB2 γ.scope γ.mode ∧ γ.mode.Batch' = true⌝ }}
    (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"note")) (Val #v.byE)) (Val #sl))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ netAdder c γ.toAntNames q ∗ threadTok ∗
      ⌜v'.byE = v.byE⌝ }}

end spec

end AntHarness
end EtcdGrove
end Perennial
