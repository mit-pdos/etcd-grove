/-
**What `NewServer` leaves for serving** (D19g (b), 2026-10-18): the row of `NewServer.spec`'s
postcondition that `v3rpc.Server`'s premises (`grpcCfgOk`, the progress interval's field) and
`etcd_kv_started`'s request slots (`etcdGrpcSlot`) are derived from, with `Start`'s
postcondition (`v3rpc/ServeFromStart.lean`). Lean-first (no Rocq counterpart).

* `srvServeCfg s cfg` (persistent): the configuration fields `v3rpc.Server` and its callees read
  that `srvBuilt` does not hold (`Logger`, `QuotaBackendBytes`, `MaxTxnOps`,
  `WarningUnaryRequestDuration`, `Metrics`, `EnableDistributedTracing`, `TracerOptions`,
  `MaxConcurrentStreams`, and since J8a-3 `WatchProgressNotifyInterval`), at `cfg`'s values,
  read-only.
* `srvServeBuilt s E cfg K`: those, the KV field as the watchable store `NewServer` built
  (`isWatchableStore`), a reader slot of `bemu` (`v3rpc.Server`'s), and `K` reader slots each of `leadTimeMu`, `lgMu`,
  the auth store (`E.RD`) and the store's reader tokens (`mvccReaders E.γ 1` each, one per request
  slot, what its reads of the store borrow; R6, 2026-11-07, the `lean` merge: `lean`'s
  `mvcc.storeReader`s, which strict M1 had dropped), which `NewServer`'s proof dropped
  until D19g, and of `bemu` (the quota checks', which read the current backend: D22g (A)).
  (Until J8a-3, 2026-11-01, also the progress interval's field, owned: `NewWatchServer` wrote it;
  the fork's `NewWatchServer` keeps the adjusted interval local, and the field is read-only in
  `srvServeCfg`.)
* `replicate_takeN`, `replicate_sepL`: splitting and pairing replicated resources.
* (Per-type stage B2, 2026-11-11, r5 §3.2-§3.3 and §4.2) `srvServeStock s E`: the raw stocks
  `NewServer` hands out beside `srvServeBuilt` until B3 (the revocation's built part, `srvRevokePoolN`
  store tokens with `bemu` slots, `Start`'s two `lgMu` slots); `srvRunReadStock`, the read loop's
  share; the gRPC run pool `srvRunPool` (level 3), built from both at the serve step
  (`srvRunPool_init`).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- `n` of `M ≥ n` copies of `P`. -/
theorem replicate_takeN (P : IProp GF) (n M : Nat) (h : n ≤ M) :
    ([∗list] _x ∈ List.replicate M (), P) ⊢
      ([∗list] _x ∈ List.replicate n (), P) ∗ [∗list] _x ∈ List.replicate (M - n) (), P := by
  obtain ⟨m, rfl⟩ : ∃ m, M = n + m := ⟨M - n, by omega⟩
  rw [← List.replicate_append_replicate, Nat.add_sub_cancel_left]
  iintro H
  icases BigSepL.bigSepL_append.1 $$ H with ⟨H1, H2⟩
  iframe H1 H2

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

/-- `n` copies of `P` and `n` of `Q` are `n` of `P ∗ Q` (as `InvBoot`'s `replicate_sep`). -/
theorem replicate_pair (P Q : IProp GF) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), P) ∗ ([∗list] _x ∈ List.replicate n (), Q) ⊢
      [∗list] _x ∈ List.replicate n (), iprop(P ∗ Q) :=
  BigSepL.bigSepL_sep_eqv.2

end lemmas

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The configuration fields `v3rpc.Server` reads that `srvBuilt` does not hold** (persistent;
see the file header); (2026-10-31) the transaction budget within protobuf's recursion limit
(`v3rpc.maxTxnOpsOk`, `NewServer`'s configuration premise); (J8a-3) the progress interval. -/
def srvServeCfg (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(srvCfgFieldAddr s go!"Logger" ↦□ cfg.Logger' ∗
    srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ cfg.QuotaBackendBytes' ∗
    srvCfgFieldAddr s go!"MaxTxnOps" ↦□ cfg.MaxTxnOps' ∗
    ⌜v3rpc.maxTxnOpsOk (sint.Z cfg.MaxTxnOps')⌝ ∗
    srvCfgFieldAddr s go!"WarningUnaryRequestDuration" ↦□ cfg.WarningUnaryRequestDuration' ∗
    srvCfgFieldAddr s go!"Metrics" ↦□ cfg.Metrics' ∗
    srvCfgFieldAddr s go!"EnableDistributedTracing" ↦□ cfg.EnableDistributedTracing' ∗
    srvCfgFieldAddr s go!"TracerOptions" ↦□ cfg.TracerOptions' ∗
    srvCfgFieldAddr s go!"MaxConcurrentStreams" ↦□ cfg.MaxConcurrentStreams' ∗
    srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦□ cfg.WatchProgressNotifyInterval')

instance srvServeCfg_persistent (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) :
    Persistent (srvServeCfg (GF := GF) s cfg) := by
  unfold srvServeCfg; infer_instance

/-- **The facts `NewServer` leaves for serving** (persistent): the KV field as the watchable
store it built (strict M1, 2026-11-06: the API's handle, `srvWatchBuilt`'s; until then
`mvcc.isWatchableStore wsl E.s γ`), and the configuration fields `srvServeCfg`. -/
def srvServeFacts (s : Loc) (E : apply.AEnv GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop((∃ wsl : Loc,
      srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
      ⌜E.kv = interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl⌝ ∗
      □ mvcc.api.isMvcc E.kv E.γ) ∗
    srvServeCfg s cfg)

instance srvServeFacts_persistent (s : Loc) (E : apply.AEnv GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) :
    Persistent (srvServeFacts (GF := GF) s E cfg) := by
  unfold srvServeFacts; infer_instance

/-- (J8a-3) **The progress interval's field, read-only** (`v3rpc.Server`'s premise). -/
theorem srvServeFacts_interval (s : Loc) (E : apply.AEnv GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) :
    srvServeFacts (GF := GF) s E cfg ⊢
      srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦□ cfg.WatchProgressNotifyInterval' := by
  iintro #H
  iunfold srvServeFacts at H
  icases H with ⟨-, #H⟩
  iunfold srvServeCfg at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, #H⟩
  iexact H

/-- **What `NewServer` leaves for serving** (see the file header). -/
def srvServeBuilt (s : Loc) (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (K : Nat) : IProp GF :=
  iprop(srvServeFacts s E cfg ∗
    srvBemuReader s ∗
    ([∗list] _x ∈ List.replicate K (), srvLeadTimeReader s) ∗
    ([∗list] _x ∈ List.replicate K (), srvLgReader s) ∗
    ([∗list] _x ∈ List.replicate K (), E.RD) ∗
    ([∗list] _x ∈ List.replicate K (), srvBemuReader s) ∗
    ([∗list] _x ∈ List.replicate K (), mvcc.api.mvccReaders E.γ 1))

/-- **The serving stocks `NewServer` hands out raw** (per-type stage B2, 2026-11-11; r5 §3.2 and
§4.2, beside `srvServeBuilt`'s 64-stocks until stage B3): the revocation's built part
(`srvRevokeBuilt`, persistent: the inner pool `I` of `leadTimeMu` and `E.RD` a gRPC run borrows at
level 2, `srvRevokeBuilt_innerBorrow`, and `raftPool` at level 1, `srvRevokeBuilt_raftPool`);
`srvRevokePoolN` copies of a store reader token with a reader slot of `bemu`, the raw stock the
gRPC run pool is made of (`srvRunPool_init`, at the serve step: r5's D6, so that a member that
never serves returns the store's tokens to its stop, `srvStopReaders_intro`); and `Start`'s counted
stock of two `lgMu` reader slots (r5 §3.2's row `lgMu`; until B3 `Start` still spends two of
`srvServeBuilt`'s). -/
def srvServeStock (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(srvRevokeBuilt s E ∗
    ([∗list] _x ∈ List.replicate srvRevokePoolN (),
      iprop(mvcc.api.mvccReaders E.γ 1 ∗ srvBemuReader s)) ∗
    srvLgReader s ∗ srvLgReader s)

/-- **The read loop's reader slots a started member keeps for its gRPC runs** (per-type stage B2,
r5 §3.2's row `readMu`): `srvRevokePoolN` of them, the run pool's other raw stock
(`srvRunPool_init`), carved from `start`'s by `etcdstart`'s `memberUp`. -/
def srvRunReadStock (s : Loc) (γr : ReadNames) : IProp GF :=
  iprop([∗list] _x ∈ List.replicate srvRevokePoolN (), srvReadReader s γr)

/-- The gRPC run pool's namespace. -/
def srvRunN : Namespace := nroot .@ "srvRun"

/-- **The gRPC run pool** (per-type stage B2, r5 §3.3: level 3; persistent): a store reader token,
a reader slot of the read loop's lock and one of `bemu`, which a KV or lease run (and the watch
loops) borrows with level 3 of its thread token (`threadPool.borrowL`). Built at the serve step from
the raw stocks (`srvRunPool_init`: r5's D6). Not sealed: the gRPC adapters are generic in the
pools (r5 §3.4). -/
def srvRunPool (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL srvRunN 3 γ
    iprop(mvcc.api.mvccReaders E.γ 1 ∗ srvReadReader s γr ∗ srvBemuReader s))

instance srvRunPool_persistent (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvRunPool (GF := GF) s E γr) := by
  unfold srvRunPool; infer_instance

end defs

section runPool
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The revocation's built part, out of the raw stocks** (persistent; the stock kept): what a gRPC
run borrows the inner pool `I` from at level 2 (`srvRevokeBuilt_innerBorrow`) and `raftPool` at
level 1 (`srvRevokeBuilt_raftPool`). -/
theorem srvServeStock_built (s : Loc) (E : apply.AEnv GF) :
    srvServeStock (GF := GF) s E ⊢ srvRevokeBuilt s E ∗ srvServeStock s E := by
  iintro Hst
  iunfold srvServeStock at Hst
  icases Hst with ⟨#Hb, Hp, Hlg1, Hlg2⟩
  iframe Hb
  iunfold srvServeStock
  iframe Hb
  isplitl [Hp]
  · iexact Hp
  iframe Hlg1 Hlg2

/-- **The gRPC run pool, from the raw stocks** (per-type stage B2, r5 §3.3): `threadPool.initL` at
level 3 over `srvServeStock`'s `srvRevokePoolN` store tokens with `bemu` slots and the read loop's
`srvRunReadStock`, paired; the bound `threadBound GF ≤ srvRevokePoolN + 1` from the built part
(`srvRevokeBuilt_bound`). The stock's other parts come back. -/
theorem srvRunPool_init (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (Em : CoPset) :
    srvServeStock (GF := GF) s E ∗ srvRunReadStock s γr ⊢
      |={Em}=> srvRunPool s E γr ∗ srvRevokeBuilt s E ∗ srvLgReader s ∗ srvLgReader s := by
  iintro ⟨Hst, Hrd⟩
  iunfold srvServeStock at Hst
  icases Hst with ⟨#Hb, Hp, Hlg1, Hlg2⟩
  ihave %Hbd := srvRevokeBuilt_bound s E $$ Hb
  iunfold srvRunReadStock at Hrd
  -- (paired at the elements' own forms, then rearranged element by element: no bare `iframe`
  -- over these `srvRevokePoolN`-long lists)
  ihave Hpr := replicate_pair iprop(mvcc.api.mvccReaders E.γ 1 ∗ srvBemuReader s)
    (srvReadReader s γr) srvRevokePoolN $$ [Hp Hrd]
  · isplitl [Hp]
    · iexact Hp
    · iexact Hrd
  ihave Hpr := replicate_mono
    iprop((mvcc.api.mvccReaders E.γ 1 ∗ srvBemuReader s) ∗ srvReadReader s γr)
    iprop(mvcc.api.mvccReaders E.γ 1 ∗ srvReadReader s γr ∗ srvBemuReader s) srvRevokePoolN
    (by iintro ⟨⟨H1, H2⟩, H3⟩; iframe H1 H2 H3) $$ Hpr
  imod threadPool.initL srvRunN 3
      iprop(mvcc.api.mvccReaders E.γ 1 ∗ srvReadReader s γr ∗ srvBemuReader s) Em srvRevokePoolN
      (by simp only [srvRevokePoolN, backend.rdPoolN] at Hbd ⊢; omega) $$ Hpr with ⟨%γ, #Hpool⟩
  imodintro
  isplitr
  · iunfold srvRunPool
    iexists γ
    iexact Hpool
  iframe Hb Hlg1 Hlg2

end runPool

end EtcdGrove
end Perennial
