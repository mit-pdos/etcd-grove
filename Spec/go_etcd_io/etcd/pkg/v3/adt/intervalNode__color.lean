/-
`intervalNode.color` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Ctx.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `x.color(sentinel)` (internal, the fixups'): the sentinel is black; another node's colour is
its `c` field. -/
abbrev adt.intervalNode.color.spec : Prop :=
  ∀ (x s : Loc) (c : adt.RbColor) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.colorAt s x c dq }}
    (App (Val (x @!! go.GoType.PointerType intervalNode.ty @!! go!"color")) (Val #s))
  {{ RET #(adt.colorW c); adt.colorAt s x c dq }}

end spec

end EtcdGrove
end Perennial
