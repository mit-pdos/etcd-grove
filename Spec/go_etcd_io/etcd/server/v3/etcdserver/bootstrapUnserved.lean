/-
**`bootstrap(cfg)` at a first start of a member of a cluster in one process, no other member's peer address served**
(the interim axiom `bootstrap.wp_proofUnserved`'s statement, 2026-11-27). Lean-first.

`bootstrap.spec` (claim #34's, `bootstrap.lean` beside this file) at `bootstrap.specDist`'s shape (one peer URL per
initial-cluster entry, this member's peer URLs its entry's, one client URL), where the other members run in the same
process and none of them serves its peer address yet (restartN's first boots: `examples/etcd/restartN`'s
`startMembers` builds every member before it serves any):
* the hosts of the other members' peer URLs are among `addrs`, numeric loopback literals (`netAddrLit`);
* the precondition lends `bootstrap` the right to listen at each address of `addrs`, reserved for HTTP
  (`http.httpAddrFree a`, `Proof/net/http/AddrNet.lean`: the claim `addrClaim a` and `a`'s net protocols net/http's),
  and the post gives it back, on an error too.

Otherwise its premises, precondition and post are `bootstrap.spec`'s, word for word.

Why the restriction (`bootstrap.specDist`'s header; the ledger, 2026-11-24): with other members, `isMemberBootstrapped`
(`cluster_util.go:41-55`) sends `GET <peer>/members` to each other member's peer URL (`getClusterFromRemotePeers`,
`:69-121`); an answer that decodes to a member list with a `null` element panics `bootstrap`
(`nonissues/etcd-bootstrap-members-null-panic.md`). With the addresses' rights held for the call, no HTTP server is
registered at them (`http.register` takes the listener's `addrClaim`) and no raw listener at them can write (their
net protocols are net/http's opaque ones), so every GET fails and `isMemberBootstrapped` answers `false`, as at one
member (`bootstrap.specOne`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrap
public import Proof.net.http.AddrNet

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

/-- **`bootstrap.spec` with every other member's peer address not served** (see the file header): one peer URL per
initial-cluster entry, this member's peer URLs its entry's, one client URL, the other entries' hosts among `addrs` (numeric loopback literals), and
the rights `http.httpAddrFree a` (`a ∈ addrs`) lent for the call; otherwise `bootstrap.spec`'s premises, precondition
and post. -/
abbrev bootstrap.specUnserved : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft) (N : Nat)
    (addrs : List GoString),
  -- the restriction: one peer URL per entry, this member's its entry's, one client URL, the others' hosts in `addrs`
  (∀ k, (U.initMap.lookup k).isSome → (U.initURLs k).length = 1) →
  U.peer = U.initURLs cfg.Name' → U.client.length = 1 →
  (∀ k, (U.initMap.lookup k).isSome → k ≠ cfg.Name' → ∀ u ∈ U.initURLs k, u.Host' ∈ addrs) →
  -- (review R1, 2026-11-28) the addresses numeric loopback literals: no proxy (`http.ProxyFromEnvironment`)
  (∀ a ∈ addrs, netAddrLit a = true) →
  -- `bootstrap.spec`'s premises
  cfg.UnsafeNoFsync' = false → bootGo.idRaftOk cfg U → bootGo.urlsNe U →
  bootGo.bootURLsPlain U →
  crypto.fips140.GodebugFips140Off → bootGo.initMapOk U cfg.InitialClusterToken' →
  γ.vs = bootGo.ps U cfg.InitialClusterToken' →
  (∃ bl : List LogEntry, BootLog (bootGo.ps U cfg.InitialClusterToken')
    (bootGo.ctxs U cfg.InitialClusterToken') bl ∧ γ.boot = LogEntry.toEntries bl 0) →
  memBoot γ.boot = bootGo.memMap U cfg.InitialClusterToken' →
  {{ -- the other members' peer addresses, not served (lent for the call)
      ([∗list] a ∈ addrs, http.httpAddrFree (hG := hG) a) ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜bootCfgOk cfg ∧ bootCfgFresh cfg U ∧ N + 7 + bootWB ≤ backend.wbInit ∧ storage.dbOpensOk⌝ ∗
      zapLoggerOk cfg.Logger' ∗
      (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
      ⌜EtcdVerifyOff⌝ ∗ bootCfgRO cfg U ∗ memStorRegAuth (∅ : GMap Loc MemStorNamesRec) ∗
      wal.bootRes cfg }}
    (App (Val (@! bootstrap)) (Val #cfg))
  {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
      ([∗list] a ∈ addrs, http.httpAddrFree (hG := hG) a) ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗
        bootOk cfg γ (bootGo.id cfg U) (bootGo.ctxs U cfg.InitialClusterToken') N
          (bootGo.dir U cfg.InitialClusterToken') b) }}

end spec

end EtcdGrove
end Perennial
