/-
`membership.RaftCluster.Version` (`cluster.go:580-587`): under the lock, nil, or a fresh parse of
`c.version`'s rendering. Lean-first (no Rocq counterpart); prove-ps2-bootstage1, 2026-11-23 (#34 stage
1): until then names-only, its contracts trusted clauses of `bootOk` (`clusterVersionMono`,
`lease.clusterOk`, `isCluster`'s `Version` row).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

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

/-- `c.Version()` of the cluster `c` at the version name `γcv` (`isRaftClusterV`): nil only while
the version is not known (`known = false`: the caller holds no `monoNatLbOwn γcv 1`), otherwise a
version, read-only (`semver.MustParse`'s fresh result), with the witness that it is known. -/
abbrev membership.RaftCluster.Version.spec : Prop :=
  ∀ (c : Loc) (γcv : GName) (known : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftClusterV c γcv ∗ (if known then monoNatLbOwn γcv 1 else True) }}
    (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Version"))
      (Val #()))
  {{ (v : Loc), RET #v; ⌜v = null ∧ known = false⌝ ∨
      ⌜v ≠ null⌝ ∗ (∃ x : github_com.Masterminds.semver.v3.Version, v ↦□ x) ∗
        monoNatLbOwn γcv 1 }}

end spec

end EtcdGrove
end Perennial
