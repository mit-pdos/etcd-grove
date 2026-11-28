/-
`bootstrap(cfg)` (`bootstrap.go:53-130` at the etcd pin `edc800c6f`; translated with its body, claim
#34, stage 3, 2026-11-23). Lean-first; `notes/bootstrap-proof-plan.md` §0, §7.2, §7.3. The statement
`bootstrapContract` (`InvBoot.lean`, a premise of `NewServer.spec`) asks for, at Go's own values
(`BootValues.lean`): at any other id, peers or contexts `bootOk` is false (§0). To be proved in
`Proof/go_etcd_io/etcd/server/v3/etcdserver/bootstrap.lean` over its callees' specs
(`bootstrap{Snapshot,Backend,Cluster,Storage,Raft}`, `bootstrappedCluster.Finalize`, the config path
methods) and the laws of `BootParts.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **`bootstrap(cfg)` at a first start**: `bootstrapContract`'s precondition (and the package's
initialization), and its post at Go's values: this member's id `bootGo.id cfg U`, the peers'
contexts `bootGo.ctxs`, the directory `bootGo.dir`, for the token `cfg.InitialClusterToken`. For the
raft names `γ` whose voters are the peers (`γ.vs = bootGo.ps`, `bootOk`'s `Hraft`) and whose bootstrap
log is the node API's log of the peers and contexts (`BootLog`, so `srvBootLogOk`: `Hraft`), whose
members are the cluster's (`memBoot γ.boot = bootGo.memMap`: `Hmem`; `memBoot` decodes the contexts
through the opaque `membership.ccMemberOf`, so this holds at Go's values once `ccMemberOf
(bootGo.memberJSON m) = m`, stop S2 of the plan), and an initial cluster of plain URLs
(`bootGo.bootURLsPlain`: where `URL.String()` is `bootGo.urlStr`, the only case this repository
specifies). These are the conditions `bootPremise` puts on `γ` and `U` (§7.3). The restart branch is
not covered: `wal.Exist` of the fresh WAL area answers `false` (`bootFs.walExist.law`), so `haveWAL` is
false; stage 5 adds the restart's spec.

Why it is true of Go: see `BootParts.lean`'s header (which callee gives which row of `bootOk`, and the
hand-off states), `bootOk_of_parts` (the posts join into `bootOk`), and each callee's docstring. On an
error after `bootstrapBackend` (`bootstrapCluster`'s, `Finalize`'s) `bootstrap` closes the backend
(`:95`, `:103`) and returns it.

The thread and receipt bounds (`ThreadBoundLe GF (2 ^ 29)`, `ReceiptBoundLe GF (2 ^ 60)`) are
`storage.OpenBackend.spec`'s (through `bootstrapBackend.spec`), which is stated under them; NewServer's
context derives them.

(Claim #34 stage 4, 2026-11-25; ledger, "`bootstrapStorage.spec` without `UnsafeNoFsync = false`") With
`cfg.UnsafeNoFsync` false: otherwise `bootstrapNewWAL` sets the new WAL's `unsafeNoSync`, and the open WAL
of `bootOk`'s `Hwal` (`wal.bootOk`, whose `Sync`s fsync) is not the WAL Go has. `bootstrapContract` (a
trusted premise) does not have this condition yet: `notes/STATUS.md`, "`bootstrapContract` and
`UnsafeNoFsync`". And (the same day; ledger, "`bootstrapRaft.spec`: an id raft refuses") with this
member's id not one of raft's local targets (`bootGo.idRaftOk`): raft's `StartNode` refuses it, and
`bootOk`'s `Hraft` (`rnStartCfg`'s `ConfigValid`) excludes it; a pure fact of the URLs and the token.
And with every initial-cluster entry holding a peer URL (`bootGo.urlsNe`; ledger, "`bootstrapRaftFromCluster`: a
member with no peer URL"): the contexts `bootGo.ctxs` write each member's peer URLs as an array. -/
abbrev bootstrap.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft) (N : Nat),
  cfg.UnsafeNoFsync' = false → bootGo.idRaftOk cfg U → bootGo.urlsNe U →
  bootGo.bootURLsPlain U →
  -- (claim #34, stage 2, 2026-11-25) `bootstrapCluster`'s two new premises
  crypto.fips140.GodebugFips140Off → bootGo.initMapOk U cfg.InitialClusterToken' →
  γ.vs = bootGo.ps U cfg.InitialClusterToken' →
  (∃ bl : List LogEntry, BootLog (bootGo.ps U cfg.InitialClusterToken')
    (bootGo.ctxs U cfg.InitialClusterToken') bl ∧ γ.boot = LogEntry.toEntries bl 0) →
  memBoot γ.boot = bootGo.memMap U cfg.InitialClusterToken' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜bootCfgOk cfg ∧ bootCfgFresh cfg U ∧ N + 7 + bootWB ≤ backend.wbInit ∧ storage.dbOpensOk⌝ ∗
      zapLoggerOk cfg.Logger' ∗
      (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
      ⌜EtcdVerifyOff⌝ ∗ bootCfgRO cfg U ∗ memStorRegAuth (∅ : GMap Loc MemStorNamesRec) ∗
      wal.bootRes cfg ∗
      -- (keepfix (c), 2026-11-28) a committed entry of the cluster has a non-zero term (`srvTermPos`, from
      -- raft's `isCommittedLogLb_term_pos` at the caller's `isCluster`): what the backend hooks `bootstrap`
      -- builds need to keep the batch lock's resource `metaTMR γ.cl` across a save
      srvTermPos γ.cl }}
    (App (Val (@! bootstrap)) (Val #cfg))
  {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗
        bootOk cfg γ (bootGo.id cfg U) (bootGo.ctxs U cfg.InitialClusterToken') N
          (bootGo.dir U cfg.InitialClusterToken') b }}

end spec

end EtcdGrove
end Perennial
