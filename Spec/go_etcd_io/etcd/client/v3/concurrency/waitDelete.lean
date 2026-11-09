/-
`concurrency.waitDelete(ctx, client, key, rev)` (`client/v3/concurrency/key.go`), internal.

Users: `waitDeletes`.

Proof sketch: `Context.WithCancel.spec`, `ctxPrin_child`; the `Watcher` field's `Watch(cctx, key,
WithRev(rev))` (`clientRest_fields`' `watcherAt`, 1b's `Watcher.WatchTriple`: `watchChAt`); receive
until a delete event or the channel's close (`watchChAt_recv`); `WatchResponse.Err` (1b),
`Context.Err.spec`, `errors.New` (Perennial); the deferred cancel (`cancelOk`).

Changes: from `specs-ref`'s `waitDelete.lean`: no post fact (`waitDeletes` does not use it: its
own `Get` decides).

Margin: `nil` means a delete event of `key` at a revision at least `rev` was received; not stated.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `waitDelete(ctx, c, key, rev)`: returns (some error, or `nil`); it only waits. -/
def waitDelete.spec : Prop :=
  ∀ (ctx : GoInterface) (c : Loc) (γ : Cluster) (who : Principal) (key : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isClient c γ who ∗ Context.ctxOk ctx ∗ ctxPrin ctx who }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.waitDelete)) (Val #ctx)) (Val #c)) (Val #key)) (Val #rev))
  {{ (err : GoInterface), RET #err; True }}

end spec

end Concurrency
end EtcdGrove
end Perennial
