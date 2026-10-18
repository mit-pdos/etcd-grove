/-
**`v3rpc.Server`'s premises and `etcd_kv_started`'s slots, from `NewServer` and `Start`** (D19g
(b), 2026-10-18; item 9's point 7). Lean-first (no Rocq counterpart).

* `grpcCfgOk_of_started`: the server's fields and contracts `v3rpc.Server` reads (`grpcCfgOk`),
  from `Start`'s views (`isServerReq`, `isServerRead`: `raftKV` through the server's linked
  specs, `raftKV_server`) and `NewServer`'s serving facts (`srvServeFacts`: the configuration
  fields) and `srvWatchBuilt` (the watchable store with its watch-token pool, which `NewServer`
  allocates), at the answers `etcd_kv_started` takes
  (`srvKVAns s E ρ γr 0 [] .none`). Three premises no construction gives, stated as such:
  `v3rpc.watchVars` (package facts of `watch.go`'s variables, not yet among `v3rpc`'s
  initialization facts), `runsNoRequireLeader` (no client asks for a leader on a stream) and
  `membership.localKept` (the local member stays in the cluster; an axiomatized predicate), and
  the tracer options' slice.
* `etcdGrpcSlots_of_started`: `N` of `etcd_kv_started`'s slots (`etcdGrpcSlot`) from `2 N` reader
  slots each of `leadTimeMu`, `lgMu` and the auth store and `N` of the store (`srvServeBuilt`'s)
  and `N` of the read loop's (`Start`'s).

`etcd_kv_started` and `etcd_watch_served_chain` are unchanged: these lemmas give their premises.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
    (hlg : cfg.Logger' ≠ null) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvServeFacts s E cfg ∗
        srvWatchBuilt s E ∗
        v3rpc.watchVars ∗ v3rpc.runsNoRequireLeader ∗ (□ ∀ c : Loc, membership.localKept c) ∗
        cfg.TracerOptions' ↦*□ tos ⊢
      ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk s C ∗
        ⌜C.A = v3rpc.srvKVAns s E ρ γr (W64 0) [] .none ∧ C.E = E⌝ := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd, #Hf, #Hwb, #Hwv, #Hnrl, #Hlk, #Htos⟩
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
  icases Hwb with ⟨%wsl, %γ, #Hkvf, #Hws, %Hγ, #Hpool⟩
  iunfold srvServeCfg at Hcf
  icases Hcf with ⟨#Hlg0, #Hqb, #Hn, #Hwd, #Hmt, #Htr, #Htsl, #Hmcs⟩
  iunfold isServerReq at Hsrv
  icases Hsrv with ⟨%v, #Hv⟩
  iunfold srvReqFieldsAt at Hv
  icases Hv with ⟨-, -, -, -, -, #Hmrb, #Hfgf, #Hfg, #Hcca, #Het, #Htm, #Hauth, #HisReq, -, -,
    #Hmid, #Hlead, #Hcl, -, #Hpeers, -, -, -, -⟩
  iunfold isServerRead at Hsrd
  icases Hsrd with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAt at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, -, #Hauth', #HisAuth, #Hlgf, %Hlgn, -, -, -, -, -, -, -,
    -, -, -, -, #Hstp, #Hstc⟩
  icombine Hauth Hauth' gives %Hae
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨-, #Hrc, -⟩
  iexists (⟨v3rpc.srvKVAns s E ρ γr (W64 0) [] .none, E, γ, wsl, w.lg, cfg.Logger',
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
      isplitr
      · ipureintro; exact Hγ
      rw [← Hae]
      iexact HisReq
    isplitr
    · ipureintro; exact hlg
    isplitr
    · ipureintro; exact Hlgn
    isplitr
    · iunfold srvLeadInv
      iunfold srvAtomicU64 at Hlead
      iexact Hlead
    iapply Hlk
  · ipureintro; exact ⟨rfl, rfl⟩

/-- **`N` of `etcd_kv_started`'s slots** (see the file header). -/
theorem etcdGrpcSlots_of_started (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (N : Nat) :
    ∀ K S M : Nat, 2 * N ≤ K → N ≤ S → N ≤ M →
    ([∗list] _x ∈ List.replicate K (), srvLeadTimeReader (GF := GF) s) ∗
        ([∗list] _x ∈ List.replicate K (), srvLgReader s) ∗
        ([∗list] _x ∈ List.replicate K (), E.RD) ∗
        ([∗list] _x ∈ List.replicate S (), mvcc.storeReader E.s E.γ) ∗
        ([∗list] _x ∈ List.replicate M (), srvReadReader s γr) ⊢
      [∗list] _x ∈ List.replicate N (), etcdGrpcSlot s E γr := by
  induction N with
  | zero =>
    intro K S M _ _ _
    iintro -
    rw [List.replicate_zero]
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | succ n ih =>
    intro K S M hK hS hM
    iintro ⟨Hlt, Hlg, Hrd, Hst, Hrr⟩
    icases replicate_take2 _ _ (by omega) $$ Hlt with ⟨Hlt1, Hlt2, Hlt⟩
    icases replicate_take2 _ _ (by omega) $$ Hlg with ⟨Hlg1, Hlg2, Hlg⟩
    icases replicate_take2 _ _ (by omega) $$ Hrd with ⟨Hrd1, Hrd2, Hrd⟩
    icases replicate_take1 _ _ (by omega) $$ Hst with ⟨Hst1, Hst⟩
    icases replicate_take1 _ _ (by omega) $$ Hrr with ⟨Hrr1, Hrr⟩
    rw [List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hlt1 Hlt2 Hlg1 Hlg2 Hrd1 Hrd2 Hst1 Hrr1]
    · unfold etcdGrpcSlot etcdRunSlot etcdIcRs
      isplitl [Hlt1 Hst1 Hlg1 Hrr1 Hrd1 Hlt2 Hrd2]
      · iframe
      iapply BigSepL.bigSepL_cons.2
      iframe Hlg2
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · itrivial
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · itrivial
      iapply BigSepL.bigSepL_nil.2
      itrivial
    · iapply (ih (K - 2) (S - 1) (M - 1) (by omega) (by omega) (by omega))
      iframe Hlt Hlg Hrd Hst Hrr

end start

end client
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.client.grpcCfgOk_of_started
#print axioms Perennial.EtcdGrove.client.etcdGrpcSlots_of_started
