/-
`lkv.rescind(ctx, key, rev)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV

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

/-- **`lkv.rescind(ctx, key, rev)`** (the lease monitor's, after another client's `"REVOKE"` at
`rev`): evicts `key`'s entry (`LeaseCacheSt.evict`, a step of the cache's log); unless the entry
was newer than `rev`, deletes the lease key `pfx ++ key` with the guarded transaction "if its
create revision is below `rev`", retrying until it commits or `ctx` is done. It returns. -/
abbrev leasingKV.rescind.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (key : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ context.isContext ctx cs }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"rescind")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #rev))
  {{ RET #(); True }}

end spec

end leasing
end EtcdGrove
end Perennial
