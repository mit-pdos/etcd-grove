/- Lean-first (no Rocq counterpart).

`server.MainDeploymentLogger(d, i, lg)` (`examples/etcd/dist/server`): member `i`'s machine of the deployment held
by the Go value `v`. If `d` is well formed (`deployment.WellFormed`), member `i`'s share of the cluster's start
applies and the machine runs `MainLogger` of member `i`'s configuration (`ConfigOf`), which never gets stuck;
otherwise it returns at once (`BootBad.lean` covers that case at `serverProg`).
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
abbrev MainDeploymentLogger.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)]
    (v : deployment.Deployment) (d : Deployment) (i : Nat) (m : Member) (lg : Loc)
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (lm : lease.Mode),
  d.members[i]? = some m →
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
      zapLoggerOk lg ∗ threadTok ∗ deploymentRepr (GF := GF) v d ∗
      -- the machine's start
      ⌜EtcdVerifyOff⌝ ∗ memberAreasFresh (GF := GF) (memberDataDir m.name) ∗
      -- its share of the cluster's start, if the deployment is well formed
      (⌜d.WellFormed⌝ -∗ ∃ c : ClusterNames,
        memberShareD (G := hG.goose_globalGS) c lm d ps ctxs boot i) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MainDeploymentLogger))
      (Val #v)) (Val #(W64 i))) (Val #lg))
  {{ RET #(); True }}

end spec

end server
end etcd_dist
end EtcdGrove
end Perennial

end
