/-
`lkv.validateDeleteOps(ops)` (`client/v3/leasing/kv.go`, added by etcd#22118). Lean-first (no Rocq counterpart); see `InvLeasingPrefix.lean`.
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

/-- **`lkv.validateDeleteOps(ops)`** for the operation trees `ts` (as `gatherOps`, which it calls):
an error exactly when one of their plain operations (`OpT.leavesL`, nested transactions'
included) is a delete intersecting the lease prefix (`leaseDelRejected`). -/
abbrev leasingKV.validateDeleteOps.spec : Prop :=
  ∀ (lkv : Loc) (pfx : GoString) (sl : GoSlice) (vs : List go_etcd_io.etcd.client.v3.Op)
    (ts : List OpT),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗
      structFieldRef leasingKV go!"pfx" lkv ↦□ pfx ∗ sl ↦*□ vs ∗ opListAtC true vs ts }}
    (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"validateDeleteOps")) (Val #sl))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil ↔ ∀ o ∈ OpT.leavesL ts, leaseDelRejected pfx o = false⌝ }}

end spec

end leasing
end EtcdGrove
end Perennial
