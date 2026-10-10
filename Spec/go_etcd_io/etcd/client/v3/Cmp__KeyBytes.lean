/-
`clientv3.Cmp.KeyBytes()` (`client/v3/compare.go`, translated for `client/v3/leasing`). Lean-first (no
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

/-- `cmp.KeyBytes()` on a comparison that has a `*pb.Compare` (through a pointer, read on any
fraction): its `Key` slice (read-only). -/
abbrev Cmp.KeyBytes.spec : Prop :=
  ∀ (cmpp : Loc) (c : go_etcd_io.etcd.client.v3.Cmp) (dq : DFrac) (ksl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cmpp ↦{dq} c ∗ ⌜c.c' ≠ null⌝ ∗
      structFieldRef etcdserverpb.Compare go!"Key" c.c' ↦□ ksl }}
    (App (Val (cmpp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Cmp.ty @!! go!"KeyBytes")) (Val #()))
  {{ RET #ksl; cmpp ↦{dq} c }}

end spec

end EtcdGrove
end Perennial
