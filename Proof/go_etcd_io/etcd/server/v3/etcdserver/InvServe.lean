/-
**What `NewServer` leaves for serving** (D19g (b), 2026-10-18): the row of `NewServer.spec`'s
postcondition that `v3rpc.Server`'s premises (`grpcCfgOk`, the progress interval's field) and
`etcd_kv_started`'s request slots (`etcdGrpcSlot`) are derived from, with `Start`'s
postcondition (`v3rpc/ServeFromStart.lean`). Lean-first (no Rocq counterpart).

* `srvServeCfg s cfg` (persistent): the configuration fields `v3rpc.Server` and its callees read
  that `srvBuilt` does not hold (`Logger`, `QuotaBackendBytes`, `MaxTxnOps`,
  `WarningUnaryRequestDuration`, `Metrics`, `EnableDistributedTracing`, `TracerOptions`,
  `MaxConcurrentStreams`), at `cfg`'s values, read-only.
* `srvServeBuilt s E cfg K`: those, the KV field as the watchable store `NewServer` built
  (`isWatchableStore`), the progress interval's field (owned: `NewWatchServer` writes it), a
  reader slot of `bemu` (`v3rpc.Server`'s), and `K` reader slots each of `leadTimeMu`, `lgMu`,
  the auth store (`E.RD`) and the store (`mvcc.storeReader`), which `NewServer`'s proof dropped
  until D19g, and of `bemu` (the quota checks', which read the current backend: D22g (A)).
* `replicate_takeN`, `replicate_sepL`: splitting and pairing replicated resources.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `n` of `M ≥ n` copies of `P`. -/
theorem replicate_takeN (P : IProp GF) (n M : Nat) (h : n ≤ M) :
    ([∗list] _x ∈ List.replicate M (), P) ⊢
      ([∗list] _x ∈ List.replicate n (), P) ∗ [∗list] _x ∈ List.replicate (M - n) (), P := by
  obtain ⟨m, rfl⟩ : ∃ m, M = n + m := ⟨M - n, by omega⟩
  rw [← List.replicate_append_replicate, Nat.add_sub_cancel_left]
  iintro H
  icases BigSepL.bigSepL_append.1 $$ H with ⟨H1, H2⟩
  iframe H1 H2

/-- `n` copies of `P` and `n` of `Q` are `n` of `P ∗ Q`. -/
theorem replicate_sepL (P Q : IProp GF) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), P) ∗ ([∗list] _x ∈ List.replicate n (), Q) ⊢
      [∗list] _x ∈ List.replicate n (), iprop(P ∗ Q) := by
  induction n with
  | zero =>
    iintro -
    rw [List.replicate_zero]
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | succ n ih =>
    rw [List.replicate_succ]
    iintro ⟨HP, HQ⟩
    icases BigSepL.bigSepL_cons.1 $$ HP with ⟨HP1, HP⟩
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ1, HQ⟩
    iapply BigSepL.bigSepL_cons.2
    iframe HP1 HQ1
    iapply ih
    iframe HP HQ

/-- Each of `n` copies of `P` gives `Q`. -/
theorem replicate_mono (P Q : IProp GF) (n : Nat) (h : P ⊢ Q) :
    ([∗list] _x ∈ List.replicate n (), P) ⊢ [∗list] _x ∈ List.replicate n (), Q := by
  induction n with
  | zero => iintro -; rw [List.replicate_zero]; iapply BigSepL.bigSepL_nil.2; itrivial
  | succ n ih =>
    rw [List.replicate_succ]
    iintro HP
    icases BigSepL.bigSepL_cons.1 $$ HP with ⟨HP1, HP⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [HP1]
    · iapply h $$ HP1
    · iapply ih $$ HP

end lemmas

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The configuration fields `v3rpc.Server` reads that `srvBuilt` does not hold** (persistent;
see the file header). -/
def srvServeCfg (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(srvCfgFieldAddr s go!"Logger" ↦□ cfg.Logger' ∗
    srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ cfg.QuotaBackendBytes' ∗
    srvCfgFieldAddr s go!"MaxTxnOps" ↦□ cfg.MaxTxnOps' ∗
    srvCfgFieldAddr s go!"WarningUnaryRequestDuration" ↦□ cfg.WarningUnaryRequestDuration' ∗
    srvCfgFieldAddr s go!"Metrics" ↦□ cfg.Metrics' ∗
    srvCfgFieldAddr s go!"EnableDistributedTracing" ↦□ cfg.EnableDistributedTracing' ∗
    srvCfgFieldAddr s go!"TracerOptions" ↦□ cfg.TracerOptions' ∗
    srvCfgFieldAddr s go!"MaxConcurrentStreams" ↦□ cfg.MaxConcurrentStreams')

instance srvServeCfg_persistent (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) :
    Persistent (srvServeCfg (GF := GF) s cfg) := by
  unfold srvServeCfg; infer_instance

/-- **The facts `NewServer` leaves for serving** (persistent): the KV field as the watchable
store it built, and the configuration fields `srvServeCfg`. -/
def srvServeFacts (s : Loc) (E : apply.AEnv GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop((∃ (wsl : Loc) (γ : mvcc.WsNames),
      srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
      mvcc.isWatchableStore wsl E.s γ ∗ ⌜γ.st = E.γ⌝) ∗
    srvServeCfg s cfg)

instance srvServeFacts_persistent (s : Loc) (E : apply.AEnv GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) :
    Persistent (srvServeFacts (GF := GF) s E cfg) := by
  unfold srvServeFacts; infer_instance

/-- **What `NewServer` leaves for serving** (see the file header). -/
def srvServeBuilt (s : Loc) (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (K : Nat) : IProp GF :=
  iprop(srvServeFacts s E cfg ∗
    srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦ cfg.WatchProgressNotifyInterval' ∗
    srvBemuReader s ∗
    ([∗list] _x ∈ List.replicate K (), srvLeadTimeReader s) ∗
    ([∗list] _x ∈ List.replicate K (), srvLgReader s) ∗
    ([∗list] _x ∈ List.replicate K (), E.RD) ∗
    ([∗list] _x ∈ List.replicate K (), mvcc.storeReader E.s E.γ) ∗
    ([∗list] _x ∈ List.replicate K (), srvBemuReader s))

end defs

end EtcdGrove
end Perennial
