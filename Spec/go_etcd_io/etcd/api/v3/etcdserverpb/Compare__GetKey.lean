/-
`etcdserverpb.Compare.GetKey()` (`api/etcdserverpb/rpc.pb.go`, translated for
`clientv3.Cmp.WithPrefix`). Lean-first (no Rocq counterpart); see `InvCmp.lean`.
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
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `c.GetKey()` of a non-nil comparison: its `Key` field (read-only). -/
abbrev Compare.GetKey.spec : Prop :=
  ∀ (p : Loc) (ksl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ⌜p ≠ null⌝ ∗
      structFieldRef etcdserverpb.Compare go!"Key" p ↦□ ksl }}
    (App (Val (p @!! go.GoType.PointerType etcdserverpb.Compare.ty @!! go!"GetKey")) (Val #()))
  {{ RET #ksl; True }}

end spec

end EtcdGrove
end Perennial
