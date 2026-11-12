/-
`NewWatchServer(s)` (`watch.go`): the watch service of the member `s`.

**Users.** `v3rpc/grpc.go:81` (`Server`: `pb.RegisterWatchServer(grpcServer, NewWatchServer(s))`,
batch 2a, which registers the result's `watchServiceAt` at `/etcdserverpb.Watch/Watch`);
`etcdserver/api/v3client/v3client.go:39` (the in-process client, through the adapter's pipe stream;
`embed/serve.go:148-150` builds v3lock and v3election on it): this spec serves it (a
`watchServerAt`), but the handler's contract does not (the pipe passes message pointers, which the
stream slots do not model: `ApiWatch.lean`'s header, an open question). Snippet: `examples/specreq/v3rpcwatch/serve.go` (`ReqServeWatch`).

**Proof sketch.** `watchMemberAt_cfg` gives the configuration's fields read-only: the logger
(`nil`, replaced by `zap.NewNop()`, W0's `NewNop.spec`, or a logger), the request budget (the
config's `MaxRequestBytesWithOverhead`, 2e: a pure sum, no panic) and the interval `d` with
`watchIntervalCfgOk d`. The member's ids (`s.Cluster().ID()`, `s.MemberID()`) and `s.Watchable()`
by `watchMemberAt`'s triples (2c/2e, `req/go_etcd_io_etcd_server_v3_etcdserver.md`, `## from 2b`).
The struct is allocated and made read-only (`watchServerAt`'s realization: the fields, with
`watchMemberAt s γ` for `sg`, `ag` and `watchable`). If `d > 0`: below 100ms it is raised to 100ms
(the `Warn` log, zap's spec), and `SetProgressReportInterval(max d 100ms)` (its spec, with
`progressIntervalOk` from `watchIntervalCfgOk`'s second disjunct).

**Changes** from `specs-ref`'s `NewWatchServer.lean`: the server's internals in the precondition
(`watchSrvOk s E tag`, `srvKVAddr s ↦□ wsIface wsl`, `srvIdsOk s`, the configuration's fields by
address, the auth mode's tag) replaced by one slot of the server batches, `watchMemberAt s γ`, over
the cluster's names; the interval's premise `d ≤ 2 ^ 62` relaxed to what the code needs
(`watchIntervalCfgOk`: the jitter's sum fits an `int64`, `nonissues/etcd-watch-progress-interval-
overflow.md`) and moved into the slot (a configuration premise, taken by 2e where the server is
configured); the post's internal record (`⟨s, E, wsl, tag, cid, mid, lg, m + 512 KiB⟩`) replaced
by `watchServerAt p γ`.

**Margin.** The returned interface holds a `*watchServer` (stated: 2a needs the dynamic type for
`watchServerAt_service`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ApiWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`NewWatchServer(s)`** of a member `s` of `γ`: a `*watchServer` serving `γ`'s watches. -/
def NewWatchServer.spec : Prop :=
  ∀ (s : Loc) (γ : EtcdModel.Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      watchMemberAt s γ }}
    (App (Val (@! v3rpc.NewWatchServer)) (Val #s))
  {{ (ws : GoInterface), RET #ws; ∃ p : Loc,
      ⌜ws = interface.mkOk (go.GoType.PointerType v3rpc.watchServer.ty) #p⌝ ∗ watchServerAt p γ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
