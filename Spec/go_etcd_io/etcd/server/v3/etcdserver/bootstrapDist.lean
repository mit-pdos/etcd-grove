/-
**`bootstrap(cfg)` at a first start of a member of `etcd_safe`'s deployment** (the interim axiom
`bootstrap.wp_proof_dist`'s statement, 2026-11-25; `notes/etcd-dist-plan.md` §16.3). Lean-first.

`bootstrap.spec` (claim #34's, `bootstrap.lean` beside this file) at the shape `etcd_safe`'s members boot in
(`examples/etcd/dist`, `examples/lib/etcdstart`), with the other members' peer URLs on other machines:
* every initial-cluster entry has one peer URL (`http://addr`), at most 64 entries;
* this member's advertised peer URLs are its entry's (`advertiseMatchesCluster` compares equal strings and
  resolves nothing), and it has one client URL;
* a new cluster with no discovery (`bootCfgFresh`, in the precondition: `InitialClusterState=new`), a fresh WAL
  area (`wal.bootRes`), so the first-start branch: the restart branch is not covered (`ForceNewCluster` is read
  only there); no proof of `etcd_safe`'s line takes `bootstrap`'s restart or crash contract
  (`CrashInterim.lean`'s laws are statements no proof uses);
* the precondition gains the round-tripper contract `etcd_dist.bootRTOk` (`S5Interim.lean`): every other
  member's peer address set to etcd's peer protocols of the cluster `γ`, and no HTTP proxy.

Otherwise its premises, precondition and post are `bootstrap.spec`'s, word for word: the post names the values
Go computes (`bootGo.id`, `bootGo.ctxs`, `bootGo.dir`, the peers `bootGo.ps` as `γ.vs`), and a failure is a
returned error (`err ≠ nil`), never excluded. `bootstrap.specDist_of_spec` (`dist/BootDist.lean`) derives
this from `bootstrap.spec`, so when #34's restated spec is proved the axiom retires into that theorem.

Why the restriction (the ledger, 2026-11-24; `notes/bootstrap-proof-plan.md`, B4): with two or more peer URLs
in this member's entry `advertiseMatchesCluster` (`config.go:251`) sorts the map's own slice in place, which
`bootCfgRO` says is never written; with other members, `isMemberBootstrapped` (`cluster_util.go:41-55`) sends
`GET <peer>/members` through the round tripper (`getClusterFromRemotePeers`, `:69-121`), which
`bootstrap.spec`'s precondition gives no right to. Here each entry has one URL (`Sort` of one element swaps
nothing) and the GETs go to addresses `bootRTOk` names.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrap
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S5Interim

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Net go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **`bootstrap.spec` at `etcd_safe`'s deployment shape** (see the file header): one peer URL per
initial-cluster entry, at most 64 entries, this member's peer URLs its entry's, one client URL, and the
round-tripper contract `bootRTOk` for the other members' peer URLs; otherwise `bootstrap.spec`'s premises,
precondition and post. -/
abbrev bootstrap.specDist [π : Net.NetProtoGS] : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft) (N : Nat),
  -- the restriction: `etcd_safe`'s shape
  (∀ k, (U.initMap.lookup k).isSome → (U.initURLs k).length = 1) → GMap.size U.initMap ≤ 64 →
  U.peer = U.initURLs cfg.Name' → U.client.length = 1 →
  -- `bootstrap.spec`'s premises
  cfg.UnsafeNoFsync' = false → bootGo.idRaftOk cfg U → bootGo.urlsNe U →
  bootGo.bootURLsPlain U →
  crypto.fips140.GodebugFips140Off → bootGo.initMapOk U cfg.InitialClusterToken' →
  γ.vs = bootGo.ps U cfg.InitialClusterToken' →
  (∃ bl : List LogEntry, BootLog (bootGo.ps U cfg.InitialClusterToken')
    (bootGo.ctxs U cfg.InitialClusterToken') bl ∧ γ.boot = LogEntry.toEntries bl 0) →
  memBoot γ.boot = bootGo.memMap U cfg.InitialClusterToken' →
  {{ -- the round-tripper contract (the other members' peer URLs)
      etcd_dist.bootRTOk (hG := hG) γ (bootGo.id cfg U) (bootGo.dir U cfg.InitialClusterToken') ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
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
