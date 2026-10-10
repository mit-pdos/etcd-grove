/-
`clientv3.Cmp.GetCompare()` (`client/v3/compare.go`, translated for `client/v3/leasing`). Lean-first (no
Rocq counterpart); see `InvCmp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvCmp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `cmp.GetCompare()` on a comparison that has a `*pb.Compare` (through a pointer): that
`*pb.Compare` (`ensureCompare` changes nothing). -/
abbrev Cmp.GetCompare.spec : Prop :=
  ∀ (cmpp : Loc) (c : go_etcd_io.etcd.client.v3.Cmp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cmpp ↦ c ∗ ⌜c.c' ≠ null⌝ }}
    (App (Val (cmpp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Cmp.ty @!! go!"GetCompare")) (Val #()))
  {{ RET #c.c'; cmpp ↦ c }}

end spec

end EtcdGrove
end Perennial
