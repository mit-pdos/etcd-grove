/-
**`bootstrap(cfg)` at a restart: a data directory that holds a stopped member's image** (the interim
axiom `bootstrap.wp_proofRestart`'s statement, 2026-11-27). Lean-first.

Until 2026-11-27 the closed single-process theorem took this contract as an Iris premise
(`etcdstart.bootPremiseR`, `bootstrapRestartContract` at every configuration of the stopped member, in
restartN's and restart1's `premises`). Here it is `bootstrap`'s own statement, at Go's values as
`bootstrap.spec` (the first start's) states them: the member id `bootGo.id cfg U`, the directory
`bootGo.dir U cfg.InitialClusterToken`, for raft names `γ` whose voters are Go's peers, whose boot log is
the node API's log of them and whose members are the cluster's (`bootstrap.spec`'s premises, word for
word), and with this member one of the peers (`bootGo.id cfg U ∈ bootGo.ps U token`: `bootOkR`'s
`cv.ID' ∈ ps`; at a restart Go reads the id from the WAL's metadata, `srvFiles`' at this id, and checks
no membership).

The body is the reviewed contract `bootstrapRestartContract` (`InvRestart.lean`), by name: its premises
on the image, precondition and post (`bootOkR`) are the contract's, so a restatement of the contract is
a restatement of this axiom (and is reviewed as one). It is stated as an entailment from the package's
initialization (`isPkgInit`, which `bootstrap.spec`'s precondition carries; the contract's does not)
because the contract is a persistent family of triples (one per image), not one triple.

No network right: at a restart `bootstrap` sends no request (`bootstrapCluster`'s `haveWAL` case,
`bootstrapClusterWithWAL`, builds the cluster from the WAL's metadata and the backend; `isMemberBootstrapped`
is the first start's only), and no restriction of the initial cluster's shape (`advertiseMatchesCluster`
is the first start's, `bootstrapNewClusterNoWAL`/`bootstrapExistingClusterNoWAL`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrap
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart

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

/-- **`bootstrap(cfg)` on a stopped member's data directory** (see the file header): at Go's id and
directory, under `bootstrap.spec`'s premises and this member one of Go's peers, the package's
initialization gives `bootstrap`'s restart contract `bootstrapRestartContract`. -/
abbrev bootstrap.specRestart : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft) (N : Nat),
  -- `bootstrap.spec`'s premises
  cfg.UnsafeNoFsync' = false → bootGo.idRaftOk cfg U → bootGo.urlsNe U →
  bootGo.bootURLsPlain U →
  crypto.fips140.GodebugFips140Off → bootGo.initMapOk U cfg.InitialClusterToken' →
  γ.vs = bootGo.ps U cfg.InitialClusterToken' →
  (∃ bl : List LogEntry, BootLog (bootGo.ps U cfg.InitialClusterToken')
    (bootGo.ctxs U cfg.InitialClusterToken') bl ∧ γ.boot = LogEntry.toEntries bl 0) →
  memBoot γ.boot = bootGo.memMap U cfg.InitialClusterToken' →
  -- the restart's: this member one of the peers
  bootGo.id cfg U ∈ bootGo.ps U cfg.InitialClusterToken' →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
    bootstrapRestartContract cfg U γ (bootGo.id cfg U) N (bootGo.dir U cfg.InitialClusterToken')

end spec

end EtcdGrove
end Perennial
