/-
`membership.Member.Clone` (`member.go`: a deep copy, the URL slices copied). Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
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

/-- `m.Clone()` of a member `m` at some fraction `q` with the value `mm` (not nil: the points-tos
say so) returns a fresh owned member with the same id; `m` kept. (Until D43 M5b, 2026-10-26, of
an owned member, `memberIs`: the cluster's lock now holds half of each member.) -/
abbrev membership.Member.Clone.spec : Prop :=
  ∀ (m : Loc) (q : Qp) (mm : apply.MemberM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.memberAt m q mm }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member.ty @!! go!"Clone")) (Val #()))
  {{ (mc : Loc), RET #mc; membership.memberAt m q mm ∗ membership.memberIs mc mm.id }}

end spec

end EtcdGrove
end Perennial
