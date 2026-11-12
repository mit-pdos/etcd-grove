/-
**`v3rpc.Server`'s premises and `etcd_kv_started`'s slots, from `NewServer` and `Start`** (D19g
(b), 2026-10-18; item 9's point 7). Lean-first (no Rocq counterpart).

* `grpcCfgOk_of_started`: the server's fields and contracts `v3rpc.Server` reads (`grpcCfgOk`),
  from `Start`'s views (`isServerReq`, `isServerRead`: `raftKV` through the server's linked
  specs, `raftKV_server`) and `NewServer`'s serving facts (`srvServeFacts`: the configuration
  fields) and `srvWatchBuilt` (the watchable store with its watch-token pool, which `NewServer`
  allocates), at the answers `etcd_kv_started` takes
  (`srvKVAns s E ρ γr 0 [] .none`). Two premises no construction gives, stated as such:
  `v3rpc.eofVar` (`io.EOF`'s value: Perennial's `io` fact does not keep it, D19j) and
  `runsNoRequireLeader` (no client asks for a leader on a stream), and the tracer options' slice.
  The rest of `watch.go`'s package variables (`watchVars`) comes from `isPkgInit v3rpc` (D19j,
  2026-10-18: until then the premise `watchVars`). (`membership.localKept`, the local member stays in the cluster, was
  a third until 2026-10-18: now the cluster's own fact, `localKept_of_isRaftCluster`.)
* (per-type stage B3, 2026-11-11) the run slots the served theorems took (`etcdGrpcSlots_of_started`,
  `watchRunSlots_of`, from the reader stocks `NewServer` and `Start` handed out) are gone: the served
  theorems borrow from the server's run pools (`srvRunPool`, `srvRevokeBuilt`), built at the serve step
  (`srvRunPool_init`); `grpcCfgOk_of_startedM` takes the watchable store's built part
  (`srvWatchBuilt`) instead of its reader stock.

The served theorems are unchanged: these lemmas give their premises.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServe
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWatchBuilt

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`v3rpc.Server`'s `grpcCfgOk`, from `Start`'s and `NewServer`'s postconditions** (see the
file header). -/
theorem grpcCfgOk_of_started (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (tos : List GoInterface)
    :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ zapLoggerOk cfg.Logger' ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvServeFacts s E cfg ∗
        srvWatchBuilt s E ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.eofVar ∗ v3rpc.runsNoRequireLeader ∗
        cfg.TracerOptions' ↦*□ tos ⊢
      |==> ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk s C ∗
        ⌜C.A = v3rpc.srvKVAns s E ρ γr (W64 0) [] .none ∧ C.E = E⌝ := by
  iintro ⟨#Hpkg, #Hzlg, #Hsrv, #Hsrd, #Hf, #Hwb, #Hv3, #Heof, #Hnrl, #Htos⟩
  imod (auth.modeTag_alloc (GF := GF) E.authMode) with ⟨%tag, #Htag⟩
  ihave #Hlb := srvAuthLb_off s E ρ $$ Hsrv
  ihave #Hwv := v3rpc.watchVars_of_init $$ [Hv3 Heof]
  · iframe #
  ihave #Hkv := v3rpc.raftKV_server s E ρ γr (W64 0) [] .none $$ [Hpkg Hsrv Hsrd]
  · iframe #
  ihave #Hkv' := Hkv
  iunfold v3rpc.raftKV at Hkv'
  icases Hkv' with ⟨-, -, -, -, #Hget⟩
  ihave #Hids := v3rpc.srvIdsOk_of_kvGetOk s _ $$ Hget
  iunfold v3rpc.kvGetOk at Hget
  icases Hget with ⟨-, -, -, #Hrs⟩
  iunfold srvServeFacts at Hf
  icases Hf with ⟨-, #Hcf⟩
  iunfold srvWatchBuilt at Hwb
  icases Hwb with ⟨%wsl, #Hkvf, %Hkvw, #Hmv⟩
  iunfold srvServeCfg at Hcf
  icases Hcf with ⟨#Hlg0, #Hqb, #Hn, %Hmto, #Hwd, #Hmt, #Htr, #Htsl, #Hmcs, -⟩
  iunfold isServerReq at Hsrv
  icases Hsrv with ⟨⟨%v, #Hv⟩, -⟩
  iunfold srvReqFieldsAt at Hv
  icases Hv with ⟨-, -, -, -, -, #Hmrb, #Hfgf, #Hfg, #Hcca, #Het, #Htm, #Hauth, #HisReq, -, -,
    #Hmid, #Hlead, #Hcl, -, #Hpeers, -, -, -, -⟩
  iunfold isServerRead at Hsrd
  icases Hsrd with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAt at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, #Hauth', #HisAuth, #Hlgf, #Hlgn, -, -, -, -, -, -, -,
    -, -, -, #Hstp, #Hstc, #Hrb⟩
  icombine Hauth Hauth' gives %Hae
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨-, #Hrc, -⟩
  imodintro
  iexists (⟨v3rpc.srvKVAns s E ρ γr (W64 0) [] .none, E, tag, wsl, w.lg, cfg.Logger',
    cfg.QuotaBackendBytes', v.memberID, cfg.MaxTxnOps', cfg.WarningUnaryRequestDuration',
    v.cluster, w.stopping, v.tickMs, v.electionTicks, v.maxReq, v.fg, cfg.Metrics',
    cfg.EnableDistributedTracing', cfg.TracerOptions', tos, cfg.MaxConcurrentStreams'⟩ :
      v3rpc.GrpcCfg GF)
  isplitl
  · iunfold v3rpc.grpcCfgOk
    simp only
    iframe #
    isplitr
    · iunfold v3rpc.watchSrvOk
      iframe #
      rw [← Hae]
      iexact HisReq
    isplitr
    · ipureintro; exact Hmto
    isplitr
    · iunfold srvLeadInv
      iunfold srvAtomicU64 at Hlead
      iexact Hlead
    iapply membership.localKept_of_isRaftCluster
    iexact Hrc
  · ipureintro; exact ⟨rfl, rfl⟩

/-- **`v3rpc.Server`'s premises from a started server, in the auth mode `on`** (the auth component's
stage 5; `Start.spec`'s views in the mode, `isServerReqM on`, `isServerReadM on`, `srvAuthLb`): at any KV answers
`A` the server's contract holds at (`raftKV s A`; `raftKV_serverM`'s at the mode's answers). -/
theorem grpcCfgOk_of_startedM (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (tos : List GoInterface)
    (on : Bool) (A : v3rpc.KVAns GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ zapLoggerOk cfg.Logger' ∗
        isServerReqM on s E ρ ∗ isServerReadM on s E γr ∗ srvAuthLb s E ∗ v3rpc.raftKV s A ∗
        srvServeFacts s E cfg ∗ srvWatchBuilt s E ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.eofVar ∗ v3rpc.runsNoRequireLeader ∗
        cfg.TracerOptions' ↦*□ tos ⊢
      |==> ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk s C ∗ ⌜C.A = A ∧ C.E = E⌝ := by
  iintro ⟨#Hpkg, #Hzlg, #Hsrv, #Hsrd, #Hlb, #Hkv, #Hf, #Hwb, #Hv3, #Heof, #Hnrl, #Htos⟩
  imod (auth.modeTag_alloc (GF := GF) E.authMode) with ⟨%tag, #Htag⟩
  ihave #Hwv := v3rpc.watchVars_of_init $$ [Hv3 Heof]
  · iframe #
  ihave #Hkv' := Hkv
  iunfold v3rpc.raftKV at Hkv'
  icases Hkv' with ⟨-, -, -, -, #Hget⟩
  ihave #Hids := v3rpc.srvIdsOk_of_kvGetOk s _ $$ Hget
  iunfold v3rpc.kvGetOk at Hget
  icases Hget with ⟨-, -, -, #Hrs⟩
  iunfold srvServeFacts at Hf
  icases Hf with ⟨-, #Hcf⟩
  iunfold srvWatchBuilt at Hwb
  icases Hwb with ⟨%wsl, #Hkvf, %Hkvw, #Hmv⟩
  iunfold srvServeCfg at Hcf
  icases Hcf with ⟨#Hlg0, #Hqb, #Hn, %Hmto, #Hwd, #Hmt, #Htr, #Htsl, #Hmcs, -⟩
  ihave #Hsp := (isServerReqM_split on s E ρ).1 $$ Hsrv
  icases Hsp with ⟨⟨%v, #Hv⟩, -⟩
  iunfold srvReqFieldsAtM at Hv
  icases Hv with ⟨-, -, -, -, -, #Hmrb, #Hfgf, #Hfg, #Hcca, #Het, #Htm, #Hauth, #HisReq, -, -,
    #Hmid, #Hlead, #Hcl, -, #Hpeers, -, -, -, -⟩
  iunfold isServerReadM at Hsrd
  icases Hsrd with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, #Hauth', #HisAuth, #Hlgf, #Hlgn, -, -, -, -, -, -, -,
    -, -, -, #Hstp, #Hstc, #Hrb⟩
  icombine Hauth Hauth' gives %Hae
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨-, #Hrc, -⟩
  imodintro
  iexists (⟨A, E, tag, wsl, w.lg, cfg.Logger',
    cfg.QuotaBackendBytes', v.memberID, cfg.MaxTxnOps', cfg.WarningUnaryRequestDuration',
    v.cluster, w.stopping, v.tickMs, v.electionTicks, v.maxReq, v.fg, cfg.Metrics',
    cfg.EnableDistributedTracing', cfg.TracerOptions', tos, cfg.MaxConcurrentStreams'⟩ :
      v3rpc.GrpcCfg GF)
  isplitr
  · iunfold v3rpc.grpcCfgOk
    simp only
    iframe #
    isplitr
    · iunfold v3rpc.watchSrvOk
      iframe #
      rw [← Hae]
      iexact HisReq
    isplitr
    · ipureintro; exact Hmto
    isplitr
    · iunfold srvLeadInv
      iunfold srvAtomicU64 at Hlead
      iexact Hlead
    iapply membership.localKept_of_isRaftCluster
    iexact Hrc
  ipureintro; exact ⟨rfl, rfl⟩

end start

end client
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.client.grpcCfgOk_of_started
