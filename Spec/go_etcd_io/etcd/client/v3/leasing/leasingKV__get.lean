/-
`lkv.get(ctx, op)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lkv.get(ctx, op)`** for a get `op` (`o`), knowing that etcd reached `lo`, with a reader
slot, a monitor slot (a reader slot the lease monitor keeps), a fraction of the "open" token and
the thread's token: `getOutcome` (the client's answer, the cache's, an acquisition's — which
starts a lease monitor with the monitor slot — or a failed acquisition's). -/
abbrev leasingKV.get.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull)
    (lo : w64) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ lkvReader lkv γ pfx ∗ context.isContext ctx cs ∗ opFullAt opv o ∗ etcdReached lo ∗
      ⌜o.t = W64 1⌝ ∗ leasingOpen γ q ∗ threadTok }}
    (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"get")) (Val #(GoInterface.ok ctx))) (Val #opv))
  {{ (ret : Loc) (err : GoInterface), RET (PairV #ret #err); lkvReader lkv γ pfx ∗ leasingOpen γ q ∗ threadTok ∗
      getOutcome γ pfx lo o ret err (lkvReader lkv γ pfx) }}

end spec

end leasing
end EtcdGrove
end Perennial
