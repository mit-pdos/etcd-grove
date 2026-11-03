/-
`serveClient(m, client)` (`examples/restart3/restart3.go`; the restart plan's R2a, 2026-11-02):
the started member's gRPC API served at `client` (`common.Serve` of the member's server). Lean-first
(no Rocq counterpart).

**The triple:** `common.Serve.spec`'s for the server in the `member` record at `m`, which it reads
and gives back.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.restart3.Defs
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

/-- See the file header. -/
abbrev serveClient.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (m s : Loc) (pl : GoInterface) (addr : GoString) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (Q : w64 → w64 → v3rpc.WSrv GF → IProp GF),
  cfg.Logger' ≠ null → cfg.TracerOptions' = slice.nil → cfg.WatchProgressNotifyInterval' = 0 →
  v3rpc.ServerMethodSets → apply.backendUnderQuota →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.restart3 ∗
      m ↦ (github_com.mit_pdos.etcd_grove.examples.restart3.member.mk s pl) ∗
      netAddrFree (GF := GF) addr ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ srvServeFacts s E cfg ∗ srvWatchReaders s E 64 ∗
      v3rpc.runsNoRequireLeader ∗
      srvLgReader s ∗ srvBemuReader s ∗ srvGoRes s ∗
      (∀ (gs : Loc) (lis : GoInterface) (cid mid : w64) (R : v3rpc.WSrv GF),
        common.grpcUp s E ρ γr gs lis addr cid mid R ={⊤}=∗ grpcServeTok gs lis ∗ Q cid mid R) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.restart3.serveClient))
      (Val #m)) (Val #addr))
  {{ (err : GoInterface), RET #err;
      m ↦ (github_com.mit_pdos.etcd_grove.examples.restart3.member.mk s pl) ∗
      (⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ (cid mid : w64) (R : v3rpc.WSrv GF), Q cid mid R)) }}

end spec

end restart3
end EtcdGrove
end Perennial
