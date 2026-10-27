/-
`membership.MembersByID.Len` (`member.go`: `len(ms)`). Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
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

/-- `ms.Len()`: the slice's length. -/
abbrev membership.MembersByID.Len.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦*{dq} ps }}
    (App (Val (sl @!! go_etcd_io.etcd.server.v3.etcdserver.api.membership.MembersByID.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 ps.length); sl ↦*{dq} ps }}

end spec

end EtcdGrove
end Perennial
