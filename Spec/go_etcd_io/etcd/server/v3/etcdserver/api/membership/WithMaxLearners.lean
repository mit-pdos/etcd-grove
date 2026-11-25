/-
`membership.WithMaxLearners(max)` (`cluster_opts.go:39-43`; claim #34, stage 2, 2026-11-25: translated
with its body). Lean-first.
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

/-- **`WithMaxLearners(ml)`** returns a cluster option that stores `ml` in a `*ClusterOptions`'s
`maxLearners` (the closure over a fresh `max`, which nothing else writes). -/
abbrev membership.WithMaxLearners.spec : Prop :=
  ∀ (ml : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.WithMaxLearners)) (Val #ml))
  {{ (f : GoFunc), RET #f; membership.clusterOptMax f ml }}

end spec

end EtcdGrove
end Perennial
