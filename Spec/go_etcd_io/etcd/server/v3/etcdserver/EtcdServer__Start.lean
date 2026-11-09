/-
## `(*EtcdServer).Start()` (`server.go:530-543`)

**Users.** `embed.StartEtcd` (`embed/etcd.go:282`); `examples/lib/etcdstart` (`StartServer`,
`StartCompactingServer`, `StartPeriodicServer`, `StartMember`), `cluster3.StartMember`,
`restart.startMember`. Once per built server, before serving its gRPC API (`v3rpc.Server`, 2a,
takes `isServer`). Snippets: `etcdserverboot/boot.go`.

**Proof sketch.** `start()` (`EtcdServer.start.spec`, with `srvMember` and the caller's
`threadTok`, given back: `isServer`, the gate, `srvRunning`, the publication's and the purge's
rights), then ten `GoAttach`es (`EtcdServer.GoAttach.spec`, each at `isServer` with the caller's
`threadTok`, which it returns; the goroutine runs on its fork's fresh token and gives it back at its
end: C45's shape; re-review RR3):
`adjustTicks`, `publishV3` (with `srvPublish`), `purgeFile` (`srvPurge`), `monitorFileDescriptor`
(the stopping channel: `StoppingNotify`'s), `monitorClusterVersions`, `monitorStorageVersion`, the
read loop (2c's `Read.LinearizableReadLoop`, with the loop's token from `isServer`'s realization),
`monitorKVHash`, `monitorCompactHash`, `monitorDowngrade`; each goroutine's WP from its spec (posts
`True`).

**Changes** (from `specs-ref`'s `EtcdServer__Start.lean`): over `srvBuilt` and the two lifecycle
predicates in place of the built part's eighteen conjuncts and the auth mode's parameter.

**Margin.** The post says nothing of liveness (the member publishing itself, the read loop
answering): `servesAt` (2a) and the request path's specs carry what clients see.

Changes: re-review (R-A7 N3/N4): the caller's `threadTok` comes back (the goroutines it starts run with their forks' fresh tokens; `GoAttach` returns the caller's).

Changes: re-review (RR3): takes `srvMember s γ id` (`NewServer`'s post gives it with `srvBuilt`),
which `start` needs (the getters it calls, 2d's `srvNode` for `run`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Starts the built server `s`**: it serves `γ` (`isServer`) until stopped, and the caller may
stop it (`srvRunning`). -/
def EtcdServer.Start.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id ∗
      srvBuilt s γ id cfg ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Start")) (Val #()))
  {{ RET #(); isServer s γ ∗ srvGate s 1 ∗ srvRunning s γ id (Config.dirsOf cfg) ∗ threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
