/-
`(*membership.ClusterOptions).applyOpts(opts)` (`cluster_opts.go:32-36`; claim #34, stage 2,
2026-11-25: translated with its body). Lean-first.
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

/-- **`co.applyOpts(opts)`** of one option setting `maxLearners` to `ml` (`opts` read-only): `co`'s
`maxLearners` is `ml`. -/
abbrev membership.ClusterOptions.applyOpts.spec : Prop :=
  ∀ (co : Loc) (opts : GoSlice) (f : GoFunc) (ml ml0 : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ opts ↦*□ [f] ∗ membership.clusterOptMax f ml ∗
      structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterOptions go!"maxLearners" co ↦ ml0 }}
    (App (Val (co @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterOptions.ty @!! go!"applyOpts")) (Val #opts))
  {{ RET #(); structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterOptions go!"maxLearners" co ↦ ml }}

end spec

end EtcdGrove
end Perennial
