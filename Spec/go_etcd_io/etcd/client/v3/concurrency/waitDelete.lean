/-
`concurrency.waitDelete(ctx, client, key, rev)` (`client/v3/concurrency/key.go`). Lean-first (no Rocq counterpart); see
`InvMutex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`waitDelete(ctx, client, key, rev)`**, for a key under the client's prefix and a cancelable
context (`WithCancel`): `nil` only after a delete event of `key` at a revision `r ≥ rev`, so `key`
is absent from etcd's state at `r` (`isEtcdRangeWatcher`); otherwise an error (the watch's, the
context's, or "lost watcher" when the channel closes). -/
abbrev waitDelete.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (client : Loc) (pfx key : GoString)
    (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isEtcdMutexClient client pfx ∗ context.isContext ctx cs ∗
      context.isCancelCtxCtx ctx cs ∗ ⌜pfx <+: key ∧ 0 ≤ sint.Z rev⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.waitDelete))
      (Val #(GoInterface.ok ctx))) (Val #client)) (Val #key)) (Val #rev))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ GoInterface.nil⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ r : w64, etcdReached r ∗ etcdAbsent pfx key r ∗
        ⌜sint.Z rev ≤ sint.Z r⌝) }}

end spec

end concurrency
end EtcdGrove
end Perennial
