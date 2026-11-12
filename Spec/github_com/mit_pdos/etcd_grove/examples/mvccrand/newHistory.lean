/- Lean-first (no Rocq counterpart).

`newHistory()` (`examples/mvccrand/mvccrand.go`): a history at revisions `0` and `1`, both empty
(`hist0`), published `1`: the lock not yet set up (its zero value and what it is to guard, whole:
`Run` makes it a guarded lock and deals its reader slots, `History.lean`), the writer's part, the
counter, and the published revision's cell (for the tester's invariant).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.History

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev newHistory.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.newHistory)) (Val #()))
  {{ (h : Loc), RET #h; ∃ γ : HistNames,
      hMu h ↦ (zero_val sync.RWMutex) ∗ histR h γ 1 ∗ histW γ hist0 ∗
      sync.atomic.ownInt64 (hAbove h) (DFrac.own 1) (W64 0) ∗
      sync.atomic.ownInt64 (hPub h) (DFrac.own 1) (W64 1) }}

end spec

end mvccrand
end EtcdGrove
end Perennial
