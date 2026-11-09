/-
`(*concurrency.Election).observe(ctx, ch)` (`client/v3/concurrency/election.go`), internal: the
goroutine `Observe` starts.

Users: `Election.Observe`.

Proof sketch: the loop carries `observeProd ch γ pfx σ0`. Each round: the KV contract's
`Get(ctx, pfx, WithFirstCreate()...)` (update from `etcdPeek`; `Reach σ0` inside it) at `σ`: a
key-value `v` holds there (`ObservedAt` with `r := σ`'s revision; the header `σ`'s); none: a prefix watch from `σ`'s revision (`Context.WithCancel.spec`, the `Watcher` field's
`Watch`, 1b) until a put event: the watch's events are the history's from that revision, in
order, without gaps (1b, `req/go_etcd_io_etcd_client_v3.md`, "from 1d"), so the first put under
the prefix is of a key created after the empty prefix, nothing older at its revision; its header
is written to that revision (the response's header owned, 1b). The response is sent
(`observeProd`'s send, a `select` with `ctx.Done()`: `doneRecv`). Then a watch on `v`'s key from
the header's revision plus one: each put event before a delete is the same key (gap-free: not
deleted meanwhile, so its create revision unchanged and nothing older appeared), forwarded with
the watch response's header (at least the event's revision, at most a reached state's, after the
round's `Get`: 1b's `watchStep`). A
delete event ends the round; a closed channel or `ctx` done ends the goroutine (`close(ch)`,
deferred).

Changes: from `specs-ref`'s `Election__observe.lean`: as `Observe`.

Margin: as `Observe`.
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

/-- `e.observe(ctx, ch)`: sends observed leader values on `ch` (`observeProd`), then closes it. -/
def Election.observe.spec : Prop :=
  ∀ (e s c : Loc) (pfx : GoString) (γ : Cluster) (dflt who : Principal) (id : w64)
    (ctx : GoInterface) (ch : GoChan) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s pfx ∗ isSession s c γ id ∗ isClient c γ dflt ∗ Context.ctxOk ctx ∗
      ctxPrin dflt ctx who ∗ etcdPeek γ ∗ etcdLb γ σ0 ∗ observeProd ch γ pfx σ0 }}
    (App (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Election.ty @!! go!"observe")) (Val #ctx)) (Val #ch))
  {{ RET #(); True }}

end spec

end Concurrency
end EtcdGrove
end Perennial
