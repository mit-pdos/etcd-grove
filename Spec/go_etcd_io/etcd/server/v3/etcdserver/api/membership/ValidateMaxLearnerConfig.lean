/-
`membership.ValidateMaxLearnerConfig(maxLearners, members, scaleUpLearners)` (`cluster.go:875-892`;
claim #34, stage 2, 2026-11-25: translated with its body). Lean-first.
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

/-- **`ValidateMaxLearnerConfig(ml, members, scale)`** of owned members (`Members()`' answer): some
error (`ErrTooManyLearners` or nil, by the learners' count), the members kept. -/
abbrev membership.ValidateMaxLearnerConfig.spec : Prop :=
  ∀ (ml : w64) (sl : GoSlice) (ms : List Loc) (scale : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.membersAt sl ms }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.ValidateMaxLearnerConfig)) (Val #ml)) (Val #sl)) (Val #scale))
  {{ (err : GoInterface), RET #err; membership.membersAt sl ms }}

end spec

end EtcdGrove
end Perennial
