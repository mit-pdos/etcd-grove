/-
## `NewServer(cfg)` (`server.go:295-442`): a member's construction

**Users.** etcd's `embed.StartEtcd` (`embed/etcd.go:262`: then `Start`, or `Cleanup` on a later
error); this repository's starters (`examples/lib/etcdstart`'s `newServerMode`, through `StartServer`,
`StartCompactingServer`, `StartPeriodicServer`, `BuildServer`, `NewMember`, `StartMember`;
`examples/lib/cluster3`'s `StartMember`; `examples/etcd/restart`'s `startMember`, which starts a
stopped member again on its directory); the integration framework's members. Patterns: a member of
a new cluster of one or of three (each with its fresh directory), a restart on the member's
directory, a member joining (etcd's `MemberAdd` then a start with `--initial-cluster-state
existing`), each with or without an auto-compactor. Snippets: `etcdserverboot/boot.go`
(`ReqStartOne`, `ReqStartThree`, `ReqRestart`, `ReqJoin`; `memberConfig`, the starters' configuration).

**Proof sketch.** Over the slots (`ApiBoot.lean`, "Slots"):
1. `bootstrap(cfg)` (`bootstrap.spec`, trusted): with `memberStart γ cfg c`, the configuration and
   the disk premise, `bootOk b γ id cfg` for the member id `id` it found (the boot token's, the
   joined URLs', the WAL's), or an error (returned; nothing to give back: `memberStart` is spent,
   see Margin). From here on the deferred `b.Close()` runs on an error (`bootstrappedServer.Close`:
   `bootOk`'s backend part, `bootBackendAt`, `beClosable`: 4a's `isBackend` with its whole open token).
2. `NewServerStats`, `NewLeaderStats` (`V2stats`), the struct literal: `b.raft.newRaftNode(…)`
   (`bootstrappedRaft.newRaftNode.spec`: `bootOk`'s raft record, the snapshotter, the opened WAL,
   the cluster: `raftNodeBuilt rn γ id st` with `st` the WAL's storage), `idutil.NewGenerator`
   (2c's), `notify.NewNotifier` (2c's).
3. `addFeatureGateMetrics` (`Features.serverGate`), the cluster's notifier (`SetVersionChangedNotifier`).
4. `lease.NewLessor` (3c, at `leaseBootRes cfg ecfg`), `auth.NewTokenProvider` (3d, at
   `authBootRes`: an error is returned), `mvcc.New` (3e, at `mvccBootCfg`; the store restores the
   backend's KV and reattaches keys to the lessor), `newCorruptionChecker`, `auth.NewAuthStore` (3d).
   From here on the second deferred cleanup closes the store first (`kv.Close`, 3e's closer giving
   its readers back: `.claude/skills/spec/examples/oneshot-close.md`).
5. The compactor: at `ret ≠ 0`, `V3compactor.bootCfg_build` gives `ecfg.autoCompact = true` and the
   periodic retention's bound; the `Compactable` is the server itself (`compactable` of its
   interface value: from 2c's `EtcdServer.Compact.spec`, whose atomic update the server builds from
   `envUpd γ ecfg`: a successful compaction is `EnvStep.compact`, an answer that changes nothing
   aborts it); the `RevGetter` the store (`V3compactor.revGetter`, 3e). `V3compactor.New.spec`: a
   compactor or an error (an unknown mode: returned).
6. `restoreAlarms` (`V3alarm`: the store over the backend's alarm bucket), `NewUberApplier` (3a),
   the lease checkpointer (3c), the backend's post-lock hook (4a, 2d).
7. The transport (2f, at the reserved peer addresses `memberStart` carries): `Start`, then `AddRemote`/`AddPeer` for the members
   `bootOk` names. An error from `Start` is returned (both deferred closers run).
8. The post: `srvMember s γ id` (the read-only fields) and `srvBuilt s γ id cfg`, the slots'
   conjunction (`ApiBoot.lean`, intended realization), with `envUpd γ ecfg` for the apply thread.

**Round 2 (crash restart).** The start right is `memberStart_disk`'s: the disk's persistent access
`diskAcc` (the durable state stays the program's, in its crash invariant; the server fires the
access at each durable write, with the raft loop's in-flight batch deposited before each `Save`) and
its idle token, at any kind (a new member's, a joiner's, a member's files after a stop or a crash,
`disk_crash` or `crashOutOfScope`); `UnsafeNoFsync` false (`diskCfgOk`).

**Round 1** (provability F3/F4/F7, completeness F1/F5; 2d's request): the start right carries
the reserved peer addresses (`cluster_alloc`, `urls_reserve`: 2f's `protoAt`/`peerAddr`, so two
allocations cannot alias) and the member id when it is known (`oid`, given back in the post with
`0 < id < 2 ^ 64`); (integration: the shared apply configuration `clusterApplyCfg` dropped: members
may be configured differently, 2d's `srvCfg` from `srvNode_cfg`, 3a's TTL-variant histories);
`rafthttpBootCfg` dropped (2f's needs are the addresses); every provisional slot has its
introduction law (`ApiBoot.lean`). Not covered: embed's `InitialCheck` between `NewServer` and
`Start` (untranslated callers only).

**Changes** (from `specs-ref`'s `NewServer.lean`, the 391-line hub: 46 revisions). One triple for
every mode (`NewServer.specG`'s `on`/`cmp` parameters, its `NewServer.spec`/`specM` instances gone:
auth and compaction are part of the state, W0's model). Every subsystem by its sealed slot, so the
hub's text names each subsystem once: the old inline premises (`batchLimitOk`,
`etcdMaxRequestBytesOk`, `maxTxnOpsOk`, the auth coupling `cmp = true → on = false`, the token TTL,
the thread and receipt bounds, `γ.boot.length ≤ 2 ^ 60`, the claim maps, `netDirOk`, `peerURLsDir`,
`authRecordsFit`, `backendUnderQuota`, `openMmapOk`, `rnLoggerZapOk`, ...) are inside the owners'
slots, the request path's realization or gone with W0's model (the quota's refusals and the
`NOSPACE` alarm are in the model: no workload premise; the bounds are at their owners, the bounds
plan). The boot resources of a first start only (`bootstrapContract`, `wal.bootRes`, `nodeBoot`,
the names chosen before the call, the fresh ghost maps) are one `memberStart`, introduced for a new
member, a joining one or a restart (K2). The post is two predicates (`srvMember`, `srvBuilt`) where
it was eighteen conjuncts (`srvWatchBuilt`, `srvBuiltG`, `srvBuildGap`, `srvServeBuilt`, ...): their
consumers (`Start`, `RaftHandler`, `CutPeer`, the request path) take the slots through `srvBuilt`'s
and `isServer`'s realizations. The member id is the post's (`∃ id`): a joiner runs as the id the
cluster has for its URLs.

**Margin.** On an error the start right is not given back: the member's directory may now hold a
backend file, a WAL with only its metadata, or nothing new, and a raft node started by
`StartNode` keeps running if the transport failed to start (Go leaks it: no `Stop` on that path).
A program that wants to retry must keep its own copy of the right (it cannot: one token per start).
Not covered: `--force-new-cluster` (`diskCfgOk`'s premise at a member's files), discovery (`bootstrap`'s
contract: no `DiscoveryCfg`; a scope restriction of `bootstrap.spec`).

**Integration (I4).** The lessor's checkpointer: `SetCheckpointer` takes 3c's `lessorCkptTok le`
with `ckptOk cp R` at `R := srvStarted s γ id` (the closure's `ensureLeadership` reads fields `start`
sets) and gives `ckptGate le R`, kept for the apply thread's `Promote`. The compactor's `RevGetter`
is the store: 3e's `mvccRevTok_of` (under the adequacy theorem's `ThreadBoundLe GF mvccRevN`) lends
the store's `Rev` pool for good, giving the persistent `mvccRevTok γ` (`mvccRevLent γ true` kept for
the shutdown); `V3compactor.revGetter_intro` takes the caller's `threadTok` per call, which with
`mvccRevTok` is 3e's `revRd γ true` (`KV.Rev.contract`). (The I4 gap, an exclusive `Rev` token
against a persistent `revGetter`, is closed: integration Y/X.) The stores' names are recorded
(`srvMvcc`, `srvLessor`, `srvAuth`).

**Integration (X, after Y).** *The post-lock hook* (`getTxPostLockInsideApplyHook`): proved once as
`∀ q, Backend.hookRun γ q Pk f Pre Q` (the closure reads `s.consistIndex` and the cluster's
`confState` under the batch lock: 4a's `hookRun`), then converted for each store: mvcc's
`Mvcc.hookRun B Pk f Pre Q` by `Backend.keyBackend_intro`'s conversion, the lessor's
`Lease.beHookRun (beIface b) Pk f Pre Q` by `Backend.leaseHookRun_intro`, the schema's `applyHook`
by `Backend.applyHook_intro`. *The lessor's backend resources*: the backend's open token `beOpen γ 1`
is split into `Backend.leaseShare` and the rest; `Lease.beOk` by `Backend.leaseBeOk_intro` from the
share (back by `leaseBeOk_elim` before `Close`, at the shutdown); `Lease.beHook` by
`leaseBeHook_intro`; `Lease.beLeases` by `leaseBeLeases_intro`, from the opener's `beCur γ leaseFp C`
after `beVis_drop` of the lease part to `beNoVis γ leaseFp`; the deleter's `rdOk` premise
(`mvccDeleter_rdOk`) by `leaseTxHeld_intro`, with the `mvccOn γ B` that `keyBackend_intro` gives (at `m = true`: `meta`'s existence cell in mvcc's footprint, the store creating the bucket; verify round, backend-schema's request).

Changes: verify-round (lease-auth's requests): `lease.NewLessor` takes the caller's `threadTok` (the lessor's `Stop` in `Cleanup` gives it back); the checkpointer closure's `ckptOk cp R` is at `context.Background()` with a `threadTok`, discharged with `reqCtxOk` (4b's and otel's `_background` laws) and `reqPrin` (`ctxNoIncoming_background`, `reqPrin_noIncoming`), `R := srvStarted s γ id` giving `isServer` (`srvStarted_isServer`) for `raftRequest` and `ensureLeadership`; `auth.NewTokenProvider` takes `waiterOk iw R` at `R := srvStarted s γ id`; `auth.NewAuthStore`'s `authGate γa R` and `authBeCur γa be` are kept in the server's state (`srvNode`'s realization: the gate persistent, `authBeCur` in the apply thread's `srvStores`); the lessor's `clusterOk (iface cluster)` from 2e's `RaftCluster.Version` triple (requested of server-boot). The store's `keyBackend_intro` at `m = true` (backend-schema's request).

Changes: verify-round (server-boot's requests): allocates `Membership.clusterVerInv γc` and, with `RaftCluster.Version.spec`, gives 3c's `Lease.clusterOk` at `server.go:344`; builds the compactor's `compactable c R` at `R := srvStarted s γ id` (a resource `start` publishes: `srvStarted_isServer` gives `Compact`'s `isServer`; the compactor's context a child of `Background`, `phys = false`, no `srvGate`), and `start` passes `□ R` to the compactor's `Run`; the backend through `bootstrap`'s `OpenBackend` (4a's `isBackend`, `beClosable` for the error path).

Changes: verify-round (apply-txn's request): `NewUberApplier`'s grown premises: `hooksOk` (the lessor's half from 4a's `leaseBeHook_intro`, the auth half from 4a's `authBeHook` introduction), `authSt`'s `authBeCur` at the auth backend wrapping `s.be` (`NewAuthStore`'s post), `lessorSt`'s `leasesLive` (an empty store), `ls.be = s.be`, `ls.rd ≠ nil` and `kvDelOk` (`srvStores_kv`: `NewStore` sets the deleter), `clusterVerInv`, the backend's version (`beVer`).

Changes: re-review (R-A7 N1): the compactor's `revGetter` (the store's `Rev`) returns a revision `≥ 1` (3e's store starts at `currentRev = 1` and never lowers it: its `Rev` contract), which `compactable`'s contract now asks (`rev ≠ 0`, server-boot's).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.features.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Api

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

/-- **Builds member of `γ` from `cfg`** (a new member, a joining one, or a restart, by the start
right), with the environment's permission and the subsystems' boot premises: either an error and a
nil server, or the server `s` of some member `id`, built and not started. -/
def NewServer.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (c : Config.Model) (γ : Cluster)
    (ecfg : EnvCfg) (oid : Option Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ Config.cfgHeap cfg c ∗ Zap.isLogger cfg.Logger' ∗
      Features.serverGate cfg.ServerFeatureGate' ∗ ⌜ServerStorage.diskOk⌝ ∗
      ⌜V3compactor.bootCfg cfg.AutoCompactionMode' cfg.AutoCompactionRetention' ecfg.autoCompact⌝ ∗
      ⌜raftNodeBootCfg cfg ∧ v3rpcBootCfg cfg ∧ mvccBootCfg cfg⌝ ∗
      backendBootRes cfg ∗ leaseBootRes cfg ecfg ∗ authBootRes cfg γ ∗
      envUpd γ ecfg ∗ memberStart γ cfg c oid }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.NewServer)) (Val #cfg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      ⌜s = null ∧ err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗ ∃ id : Nat, ⌜0 < id ∧ id < 2 ^ 64 ∧ ∀ i, oid = some i → id = i⌝ ∗
        srvMember s γ id ∗ srvBuilt s γ id cfg }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
