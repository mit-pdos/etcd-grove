/-
`semver.Version.LessThan`: the trust boundary (translated with its body since 2026-11-22; its body's
`Compare` is proved, `Version__Compare.lean`). Lean-first (no Rocq counterpart). (2026-11-23,
prove-ps2-version: prove-ps2-semver's proof, which took the receivers' points-tos, is reverted. Its caller
`applierV3backend.ClusterVersionSet` passes the cluster's `Version()`, whose ownership only the trusted
bootstrap contract (`apply.isCluster` through `clusterApplyOk`, `bootOk`) could give: Upamanyu's ruling on
etcd-grove#18, no top-level premise grows to retire an axiom. `notes/specs-only/ledger.md`, 2026-11-23.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `v.LessThan(o)` (both not nil: `Compare` reads both) returns some boolean. -/
abbrev semver.Version.LessThan.spec : Prop :=
  ∀ (v o : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ ⌜v ≠ null ∧ o ≠ null⌝ }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"LessThan")) (Val #o))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
