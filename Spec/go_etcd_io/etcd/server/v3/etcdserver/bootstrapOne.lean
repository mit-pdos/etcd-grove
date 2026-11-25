/-
**`bootstrap(cfg)` at a one-member initial cluster of one peer URL** (the interim bootstrap axiom's
statement, 2026-11-24; `notes/decisions.md`, "The interim bootstrap axiom at one member"). Lean-first.

`bootstrap.spec` (claim #34's, `bootstrap.lean` beside this file) restricted to the initial clusters
the one-member examples start (`etcdstart.urls1`): the initial cluster's map has the one entry
`cfg.Name`, and that entry one peer URL. The body is `bootstrap.spec`'s, word for word, under these two
more premises, so `bootstrap.spec` implies it (`bootstrap.specOne_of_spec`,
`Proof/.../etcdserver/BootOneDefs.lean`): when #34 proves `bootstrap.spec` the interim axiom
`bootstrap.wp_proofOne` becomes that theorem applied to `bootstrap.wp_proof`'s linked result.

Why the restriction (found 2026-11-24, `notes/specs-only/ledger.md`): at a wider initial cluster
`bootstrap` does what `bootstrap.spec` does not allow. With two or more peer URLs in this member's entry,
`advertiseMatchesCluster` (`config.go:249-251`, through `VerifyBootstrap`) sorts the map's own slice in
place (`urls.Sort()`, `URLs.Sort` is `sort.Sort(us)`, `client/pkg/types/urls.go:72`), which
`bootCfgRO`'s persistent `sl ↦*□ U.initURLs k` says is never written; with another member,
`isMemberBootstrapped` (`cluster_util.go:41-42`) sends `GET <peer>/members` through the round tripper
(`getClusterFromRemotePeers`, `:80-82`), a request no protocol of the peer's was asked to accept. At
one member with one URL neither happens: `Sort` of one element swaps nothing, and
`getRemotePeerURLs` (`:131-141`) returns no URL, so `getClusterFromRemotePeers` sends nothing.

(2026-11-25, `notes/axiom-review/transport-emptycn.md`) Peer TLS with no certificate: `bootCfgOk`, in the
precondition, now carries `transport.tlsEmpty cfg.PeerTLSInfo'` (Go's `PeerTLSInfo.Empty()`), inherited
from `bootstrap.spec`. `bootstrap`'s round tripper (`bootstrap.go:72`, `rafthttp.NewRoundTripper(cfg.PeerTLSInfo,
...)`) is `transport.NewTimeoutTransport`'s, whose `ClientConfig` can panic with `EmptyCN` and a
certificate (`issues/etcd-transport-emptycn-cert-reread-panic.md`); until then this axiom covered that
case. `etcdstart/common.go` leaves `PeerTLSInfo` zero, so the member's configuration meets it.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrap

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

/-- **`bootstrap.spec` at a one-member initial cluster of one peer URL** (see the file header): the
initial cluster's map is the one entry `cfg.Name` (some slice), whose URLs are one URL; otherwise
`bootstrap.spec`'s premises, precondition and post, unchanged. -/
abbrev bootstrap.specOne : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft) (N : Nat),
  -- the restriction: one member, one peer URL
  (∃ sl : GoSlice, U.initMap = GMap.insert cfg.Name' sl ∅) → (U.initURLs cfg.Name').length = 1 →
  cfg.UnsafeNoFsync' = false → bootGo.idRaftOk cfg U → bootGo.urlsNe U →
  bootGo.bootURLsPlain U →
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
      wal.bootRes cfg }}
    (App (Val (@! bootstrap)) (Val #cfg))
  {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗
        bootOk cfg γ (bootGo.id cfg U) (bootGo.ctxs U cfg.InitialClusterToken') N
          (bootGo.dir U cfg.InitialClusterToken') b }}

end spec

end EtcdGrove
end Perennial
