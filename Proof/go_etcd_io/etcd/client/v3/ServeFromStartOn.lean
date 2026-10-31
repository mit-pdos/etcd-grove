/-
**`v3rpc.Server`'s premises from a server started with auth on** (the auth plan's E3zb,
2026-10-28; `ServeFromStart.lean`'s `grpcCfgOk_of_started_w`, from `Start.specOn`'s views). The
watch server's contract (`watchSrvOk`) is generic in the auth mode already. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.ServedOn

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`grpcCfgOk_of_started_w` with auth on** (the auth plan's E3zb): from the views `Start.specOn`
gives (`isServerReqM true`, `isServerReadM true`, `srvAuthLb`), at the KV answers with auth on
(`srvKVAnsOn … 0 none`, what `etcd_kv_auth_served_on` takes; `raftKV_serverOn`). -/
theorem grpcCfgOk_of_started_on_w (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (tos : List GoInterface)
    (hlg : cfg.Logger' ≠ null) (K : Nat) (γa : auth.AuthNames) (hγa : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗ srvServeFacts s E cfg ∗
        srvWatchReaders s E K ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.eofVar ∗ v3rpc.runsNoRequireLeader ∗
        cfg.TracerOptions' ↦*□ tos ⊢
      ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk s C ∗
        ⌜C.A = v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none ∧ C.E = E⌝ ∗
        [∗list] _x ∈ List.replicate K (), mvcc.watchReader C.wsl E.s C.γ := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd, #Hlb, #Hf, Hwb, #Hv3, #Heof, #Hnrl, #Htos⟩
  ihave #Hwv := v3rpc.watchVars_of_init $$ [Hv3 Heof]
  · iframe #
  ihave #Hkv := v3rpc.raftKV_serverOn s E ρ γr (W64 0) [] .none 0 none γa hγa $$ [Hpkg Hsrv Hsrd Hlb]
  · iframe #
  ihave #Hkv' := Hkv
  iunfold v3rpc.raftKV at Hkv'
  icases Hkv' with ⟨-, -, -, -, #Hget⟩
  ihave #Hids := v3rpc.srvIdsOk_of_kvGetOk s _ $$ Hget
  iunfold v3rpc.kvGetOk at Hget
  icases Hget with ⟨-, -, -, #Hrs⟩
  iunfold srvServeFacts at Hf
  icases Hf with ⟨-, #Hcf⟩
  iunfold srvWatchReaders at Hwb
  icases Hwb with ⟨%wsl, %γ, #Hkvf, #Hws, %Hγ, #Hpool, #Htag, Hrds⟩
  iunfold srvServeCfg at Hcf
  icases Hcf with ⟨#Hlg0, #Hqb, #Hn, %Hmto, #Hwd, #Hmt, #Htr, #Htsl, #Hmcs⟩
  iunfold isServerReqM at Hsrv
  icases Hsrv with ⟨⟨%v, #Hv⟩, -⟩
  iunfold srvReqFieldsAtM at Hv
  icases Hv with ⟨-, -, -, -, -, #Hmrb, #Hfgf, #Hfg, #Hcca, #Het, #Htm, #Hauth, #HisReq, -, -,
    #Hmid, #Hlead, #Hcl, -, #Hpeers, -, -, -, -⟩
  iunfold isServerReadM at Hsrd
  icases Hsrd with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, -, #Hauth', #HisAuth, #Hlgf, %Hlgn, -, -, -, -, -, -, -,
    -, -, -, -, #Hstp, #Hstc, #Hrb⟩
  icombine Hauth Hauth' gives %Hae
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨-, #Hrc, -⟩
  iexists (⟨v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none, E, γ, wsl, w.lg, cfg.Logger',
    cfg.QuotaBackendBytes', v.memberID, cfg.MaxTxnOps', cfg.WarningUnaryRequestDuration',
    v.cluster, w.stopping, v.tickMs, v.electionTicks, v.maxReq, v.fg, cfg.Metrics',
    cfg.EnableDistributedTracing', cfg.TracerOptions', tos, cfg.MaxConcurrentStreams'⟩ :
      v3rpc.GrpcCfg GF)
  isplitr [Hrds]
  · iunfold v3rpc.grpcCfgOk
    simp only
    iframe #
    isplitr
    · iunfold v3rpc.watchSrvOk
      iframe #
      isplitr
      · ipureintro; exact Hγ
      rw [← Hae]
      iexact HisReq
    isplitr
    · ipureintro; exact hlg
    isplitr
    · ipureintro; exact Hlgn
    isplitr
    · ipureintro; exact Hmto
    isplitr
    · iunfold srvLeadInv
      iunfold srvAtomicU64 at Hlead
      iexact Hlead
    iapply membership.localKept_of_isRaftCluster
    iexact Hrc
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iexact Hrds

end start

end client
end EtcdGrove
end Perennial
