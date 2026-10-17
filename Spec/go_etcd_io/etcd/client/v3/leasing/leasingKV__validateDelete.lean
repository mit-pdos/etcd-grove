/-
`lkv.validateDelete(op)` (`client/v3/leasing/kv.go`, added by etcd#22118). Lean-first (no Rocq counterpart); see `InvLeasingPrefix.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingPrefix

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lkv.validateDelete(op)`**: an error exactly when `op` is a delete intersecting the lease
prefix (`leaseDelRejected`). -/
abbrev leasingKV.validateDelete.spec : Prop :=
  ∀ (lkv : Loc) (pfx : GoString) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗
      structFieldRef leasingKV go!"pfx" lkv ↦□ pfx ∗ opFullAt opv o }}
    (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"validateDelete")) (Val #opv))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil ↔ leaseDelRejected pfx o = false⌝ }}

end spec

end leasing
end EtcdGrove
end Perennial
