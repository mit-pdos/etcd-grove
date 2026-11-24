/-
`membership.NewCluster(lg, opts...)` (`cluster.go:106-119`; claim #34, stage 2, 2026-11-25:
translated with its body). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Build

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewCluster(lg, opts...)`** with a zap logger and one option setting `maxLearners` to `ml`:
a fresh cluster, owned (`clusterOwned`), with no members, the id `0`. (The `lg == nil` branch,
`zap.NewNop()`, is not taken: `zapLoggerOk` says `lg` is not nil.) -/
abbrev membership.NewCluster.spec : Prop :=
  ∀ (lg : Loc) (opts : GoSlice) (f : GoFunc) (ml : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ zapLoggerOk lg ∗ opts ↦*□ [f] ∗ membership.clusterOptMax f ml }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewCluster)) (Val #lg)) (Val #opts))
  {{ (c : Loc), RET #c; ⌜c ≠ null⌝ ∗ membership.clusterOwned c ml ∅ ∅ (W64 0) }}

end spec

end EtcdGrove
end Perennial
