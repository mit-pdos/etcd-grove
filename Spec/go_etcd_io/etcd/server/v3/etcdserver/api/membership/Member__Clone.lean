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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `m.Clone()` of an owned member `m` (not nil: the points-tos say so) returns a fresh owned
member with the same id; `m` kept. -/
abbrev membership.Member.Clone.spec : Prop :=
  ∀ (m : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.memberIs m id }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member.ty @!! go!"Clone")) (Val #()))
  {{ (mm : Loc), RET #mm; membership.memberIs m id ∗ membership.memberIs mm id }}

end spec

end EtcdGrove
end Perennial
