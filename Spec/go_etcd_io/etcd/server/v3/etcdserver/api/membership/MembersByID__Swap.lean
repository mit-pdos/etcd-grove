/-
`membership.MembersByID.Swap` (`member.go`: `ms[i], ms[j] = ms[j], ms[i]`). Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
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

/-- `ms.Swap(i, j)`, `i`, `j` in range: the two pointers exchanged. -/
abbrev membership.MembersByID.Swap.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (i j : w64) (a b : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦* ps ∗
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ ps[sint.nat i]? = some a ∧ ps[sint.nat j]? = some b⌝ }}
    (App (App (Val (sl @!! go_etcd_io.etcd.server.v3.etcdserver.api.membership.MembersByID.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); sl ↦* (ps.set (sint.nat i) b).set (sint.nat j) a }}

end spec

end EtcdGrove
end Perennial
