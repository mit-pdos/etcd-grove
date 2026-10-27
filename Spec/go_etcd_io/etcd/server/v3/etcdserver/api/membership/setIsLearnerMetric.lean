/-
`membership.setIsLearnerMetric(m)` (`metrics.go`: the `is_learner` gauge set to `1` or `0` from
`m.IsLearner`): the trust boundary (names only; D43 M5b, 2026-10-26). Lean-first.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `setIsLearnerMetric(m)` of a member `m` at some fraction returns, `m` kept. Faithful: it reads
`m.IsLearner` and sets the package's `isLearner` gauge (`prometheus.Gauge.Set`, which neither blocks
nor panics); it writes no memory the model describes. -/
abbrev membership.setIsLearnerMetric.spec : Prop :=
  ∀ (m : Loc) (q : Qp) (mm : apply.MemberM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.memberAt m q mm }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.setIsLearnerMetric))
      (Val #m))
  {{ RET #(); membership.memberAt m q mm }}

end spec

end EtcdGrove
end Perennial
