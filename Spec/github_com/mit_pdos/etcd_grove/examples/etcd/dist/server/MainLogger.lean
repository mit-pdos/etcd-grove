/- Lean-first (no Rocq counterpart).

`server.MainLogger(c, lg)` (`examples/etcd/dist/server`) on member `i`'s machine of a well-formed deployment `d`
(`notes/etcd-dist-plan.md` §19): at member `i`'s configuration (`configRepr`), its machine's fresh WAL area,
`ETCD_VERIFY` off, and its share of the cluster's start (`memberShareD`), it never gets stuck: it checks the proxy
variables and its place in the initial cluster, builds and starts the server (`NewServer` on a member machine,
`NewServer_dist`), serves etcd's peer handler on its peer address (`NewPeerHandler_dist`, `PeerServe_dist`), waits
for `ReadyNotify`, serves etcd's gRPC API on its client address (`etcdstart.Serve` on a member machine,
`Serve_dist`) and runs until its machine crashes; each step's error returns.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MemberDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Repr
public import Proof.go_etcd_io.etcd.server.v3.storage.WalAreaFresh
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RevokeCtx
public import Spec.go_uber_org.zap.Defs
public import Perennial.TrustedCode.crypto.fips140

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
abbrev MainLogger.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)]
    (cv : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Config) (lg : Loc) (d : Deployment)
    (i : Nat) (m : Member) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (lm : lease.Mode),
  d.WellFormed → d.members[i]? = some m →
  -- the scope (option (a), `notes/specs-only/ledger.md` 2026-11-26): with auth on, in the revocable lease mode no
  -- lease expires (`NewServer_dist`'s `lease.bootCfg` auth row)
  (d.cfg.auth = true → lm = .revocable → lease.leasesNoExpiry) →
  crypto.fips140.GodebugFips140Off →
  -- `bootstrap`'s results as Go computes them (`BootCore`, `BootGoD`)
  BootCore ps ctxs boot → BootGoD d ps ctxs →
  -- the lease mode `lm` the start chose, with the running server's lease premise at it
  lease.runCfg (GF := GF) lm lm →
  srvLevels (GF := GF) →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server ∗
      zapLoggerOk lg ∗ threadTok ∗ configRepr cv d i ∗
      -- the machine's start
      ⌜EtcdVerifyOff⌝ ∗ memberAreasFresh (GF := GF) (memberDataDir m.name) ∗
      -- its share of the cluster's start
      ∃ c : ClusterNames,
        memberShareD (G := hG.goose_globalGS) c lm d ps ctxs boot i }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MainLogger)) (Val #cv))
      (Val #lg))
  {{ RET #(); True }}

end spec

end server
end etcd_dist
end EtcdGrove
end Perennial

end
