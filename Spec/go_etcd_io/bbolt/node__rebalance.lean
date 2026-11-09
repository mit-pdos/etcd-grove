/-
`n.rebalance()` (`node.go`): an unbalanced node below its fill merges with a sibling or is removed; the root branch of one child collapses; recursively up. Users: `Bucket.rebalance`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Changes** (verify-round, A11 F9): the post keeps the abstraction relation (`repKept`: merging
siblings, removing an empty node, collapsing a one-child root keep the entries; its freed pages are
pending, still readable in the snapshot), which `Bucket.rebalance` needs to reach `wtxAt … nodes`.
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) rebalanced (the entries of the tree unchanged). -/
def node.rebalance.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"rebalance")) (Val #()))
  {{ RET #(); ∃ C' : TxCore, wtxCore tx γ C' ∗ ⌜repKept C C'⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
