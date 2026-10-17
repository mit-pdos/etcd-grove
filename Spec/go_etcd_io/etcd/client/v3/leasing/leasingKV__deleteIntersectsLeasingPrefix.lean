/-
`lkv.deleteIntersectsLeasingPrefix(op)` (`client/v3/leasing/kv.go`, added by etcd#22118). Lean-first (no Rocq counterpart); see `InvLeasingPrefix.lean`.
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

/-- **`lkv.deleteIntersectsLeasingPrefix(op)`**: `leaseDelIntersects pfx o` (only `lkv.pfx` is
read). -/
abbrev leasingKV.deleteIntersectsLeasingPrefix.spec : Prop :=
  ∀ (lkv : Loc) (pfx : GoString) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗
      structFieldRef leasingKV go!"pfx" lkv ↦□ pfx ∗ opFullAt opv o }}
    (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"deleteIntersectsLeasingPrefix")) (Val #opv))
  {{ RET #(leaseDelIntersects pfx o); True }}

end spec

end leasing
end EtcdGrove
end Perennial
