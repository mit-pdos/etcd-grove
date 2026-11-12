/-
`membership.MembersByID.Less` (`member.go`: `ms[i].ID < ms[j].ID`). Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
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

/-- `ms.Less(i, j)` over the members `l` (pointer, id) of the slice `sl`, `i`, `j` in range:
`ms[i].ID < ms[j].ID` (unsigned). -/
abbrev membership.MembersByID.Less.spec : Prop :=
  ∀ (sl : GoSlice) (l : List (Loc × w64)) (dq : DFrac) (i j : w64) (a b : Loc × w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦*{dq} l.map Prod.fst ∗
      ([∗list] p ∈ l, membership.memberIs p.1 p.2) ∗
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b⌝ }}
    (App (App (Val (sl @!! go_etcd_io.etcd.server.v3.etcdserver.api.membership.MembersByID.ty @!! go!"Less")) (Val #i)) (Val #j))
  {{ RET #(decide (uint.Z a.2 < uint.Z b.2)); sl ↦*{dq} l.map Prod.fst ∗
      [∗list] p ∈ l, membership.memberIs p.1 p.2 }}

end spec

end EtcdGrove
end Perennial
