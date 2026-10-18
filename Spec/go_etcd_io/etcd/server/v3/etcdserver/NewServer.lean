/-
`NewServer(cfg)` (`server.go`): the server's construction over `bootstrap`'s result. Lean-first
(no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16; D13 and D13a-d:
`notes/decisions.md`, "The server's construction: `NewServer` over `bootstrap`'s result").

**The premises.**
* `bootstrap`'s contract (`bootstrapContract`, `InvBoot.lean`; D13b): a premise, not an axiom.
* `PreVote` (etcd's embed sets it by default) and `CheckQuorum` (which etcd always sets) either
  way since 2026-10-17 (D15's patched fork, which turned `CheckQuorum` off, reverted; until then
  `cfg.PreVote` had to be unset).
* The cluster's ghost state, as `NodeStartSpec`'s: raft's names `γ` with this node's ghost state
  at the bootstrap log's state, the committed bootstrap log, raft's commit invariant, the budget;
  and the outputs of `allocClientBoot`'s continuation for this server (the fresh-token
  authorities and, since D19g (a), 2026-10-18, the KV invariant `kvInv` at the bootstrap log, which
  holds the client's half of the committed log and gives raft its standing update `noopAu`:
  until then `NewServer` took `rLog γ bootLog` and allocated `kvInv` itself, which no caller of
  raft's allocation could meet) and raft's read credits (`ownRaftGhost_alloc_boot`; all of it
  `srvRaftBoot_alloc`, `NewServerAlloc.lean`).
* **The names chosen before the call** (D13a): the request path's names `ρ` (the generator's,
  fresh; the read names at the cluster's raft names, the start log empty and the start index `0`,
  fresh, but the KV state's variable, `srvReadNamesFreshNK`), the store's index names and certificate map and the revisions' map (fresh), which the
  stand-in environment `E₀` carries (the construction's apply environment agrees with it,
  `envAgree`).
* The start `bootKV` at the consistent index `0` (the workload clause `clusterWorkloadOk`, a
  premise until D19c, D13c, is proved, `clusterWorkloadOk_of`; its residual size bound
  `clusterLogBound`, a premise until D19c's move, 2026-10-18, is gone: the apply thread checks the
  size clauses at the log it meets, small by the store's time receipts); the member id's 16 low
  bits not `0` and the conf-change policy
  `srvCCPolicy` admitting id-`0` conf changes only (D19c: no request claims the id `0` of raft's
  bootstrap conf changes); the lifetime bounds (D14g, D17, D19b): the logic's thread bound `threadBound GF ≤ 2 ^ 31`,
  and the time-receipt bounds `receiptBound GF ≤ 2 ^ 48` (D19b: the id generator's invariant holds
  a receipt per id issued, so fewer than `2 ^ 48` ids; until then the premise `idLifeBound`) and
  `receiptBound GF ≤ N + 1` (D19b: `start` puts the `N` write tokens in a receipt-backed budget,
  one taken per applied entry; until then the premise `srvLifeBound`, at most `N` entries); the
  first also bounds the store's sealed logs (`storeSmall_of_receipts`: mvcc's index writer holds
  a receipt per change; until D19b the premise `storeSmall`) and, given to the store
  (`mvcc.NewStore`'s premise, D19c's move), a write transaction's changes and the log the apply
  thread meets (until then the premise `clusterLogBound`); with the bootstrap log (the initial
  peers) shorter than `2 ^ 60` (D19b stage 5) it also bounds every index raft's `Ready`s hand out
  below `MemoryStorage.Append`'s `2 ^ 61` (until then the premise `rnLogFits`, an Iris statement
  on every `Ready`).
* `NodeStartSpec`'s trust-boundary premises (the raft wrapper's contracts; `rnTickerOk` at the
  server's raft environment `srvEr`), the configuration's logger and feature gate (a
  `*featuregate.featureGate`, for `addFeatureGateMetrics`'s type assertion), the packages' init
  facts `start` needs.

**The postcondition** (D13d): an error, the server `nil`; or the built part `srvBuilt`
(`InvBuild.lean`) at the server's raft environment `srvEr ρ E₀ …`, for an apply environment `E`
agreeing with `E₀`, auth disabled (the client's `etcdKV` at the bootstrap log's model comes from
the allocation since D19g (a)). The
row of `isServerBuilt` the built part leaves out, `run`'s snapshot contract `rnSnapOnce`
(`srvBuildGap`, `isServerBuilt_of_gap`, `BuildGap.lean`), is given too since D17d (2026-10-18):
`bootOk` hands the fresh `MemoryStorage`'s application snapshot token, which raft's `StartNode`
lends `InitialState` and gives back, and `MemoryStorage.Snapshot`'s application triple reads
(`rnSnapOnce_of_tok`); until then it was the residual premise of whoever composed `NewServer`
with `start`. The watch store
(`srvWatchBuilt`, 2026-10-18): the server's `kv` the watchable store, with the watch-token pool
allocated from `mvcc.New`'s tokens (`mvcc.watchTokPool_alloc`, under the time-receipt bound).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServe
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWatchBuilt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **`NewServer(cfg)`** (see the file header). -/
abbrev NewServer.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γ : RaftNames) (bud : BudgetNames)
    (id : w64) (bootLog : List EntryM) (ρ : ReqNames) (E₀ : apply.AEnv GF) (N : Nat),
  -- the read names: at the cluster's raft names, the start log empty, the start index `0`, the
  -- conf-change policy; the KV's start values, its certificate map the store's
  ρ.rd.raft = ⟨γ, [], W64 0⟩ → srvCCPolicy ρ.rd.raft →
  ρ.rd.kv.c0 = W64 0 → ρ.rd.kv.ch0 = apply.alarmChain false false false →
  ρ.rd.kv.log0 = [[], []] → ρ.rd.kv.cok = E₀.γ.cok →
  -- the configuration (`mvcc.New`'s premise on the batch limit: unit N1, 2026-10-17;
  -- `issues/etcd-compaction-negative-batch-limit.md`)
  cfg.Logger' ≠ null → 0 ≤ sint.Z cfg.CompactionBatchLimit' →
  -- the compactor off (D14e: `v3compactor.New` and its goroutine not reached)
  cfg.AutoCompactionRetention' = 0 →
  -- the logic's thread bound (D17: the adequacy theorem's `T`, its caller's choice)
  threadBound GF ≤ 2 ^ 31 →
  -- the time-receipt bound (D19b: the adequacy theorem's step bound `N`, its caller's choice):
  -- the id generator issues fewer than `2 ^ 48` ids; the apply thread takes at most `N` of the
  -- `N + 7` write tokens `bootstrap` gives (`start`'s `srvWTPool`)
  receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (D19b stage 5) the bootstrap log (one conf change per initial peer) shorter than `2 ^ 60`:
  -- with the receipts, raft's indices fit `MemoryStorage.Append`'s `2 ^ 61` (`rnLogFits`)
  γ.reBoot.length ≤ 2 ^ 60 →
  -- the member id's 16 low bits not `0` (D19c: the request ids' prefix is not, so no request
  -- claims the id `0` of raft's bootstrap conf changes,
  -- `issues/etcd-request-id-zero-bootstrap-confchange.md`)
  uint.Z id % 2 ^ 16 ≠ 0 →
  (∃ p : Loc, p ≠ null ∧ cfg.ServerFeatureGate' = interface.mkOk
    (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #p) →
  {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "#Hfg" ∷ isFeatureGate cfg.ServerFeatureGate' ∗
      -- `bootstrap`'s contract (D13b)
      "#Hboot" ∷ bootstrapContract cfg γ id bootLog N ∗
      -- the cluster's ghost state (as `NodeStartSpec`'s) and `allocClientBoot`'s outputs
      "Hghost" ∷ ownRaftGhost γ id (bootPState bootLog) ∗ "#Hcomm" ∷ isCommitted γ bootLog ∗
      "#Hcinv" ∷ raftCommitInv γ ∗
      "#Hbud" ∷ inv budgetN (budgetInv bud) ∗ "#HtermLB" ∷ termLB bud (W64 1) ∗
      "Hfresh" ∷ ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) ∗
      "HrdFresh" ∷ ghostMapAuth γ.reRdFresh 1 (∅ : GMap (List w8) Unit) ∗
      "HrdCred" ∷ rdCred γ (2 ^ 64 - 2) ∗
      -- the names chosen before the call (D13a), fresh
      "Hids" ∷ idNamesFresh ρ.ids ∗ "Hidx" ∷ mvcc.idxFresh E₀.γ.idx ∗
      "Hcok" ∷ ghostMapAuth E₀.γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      "Hrev" ∷ ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
      "Hrd" ∷ srvReadNamesFreshNK ρ.rd ∗
      -- the KV invariant at the bootstrap log (D19g (a): allocated with raft's ghost state,
      -- whose standing update `noopAu` it gives, `srvRaftBoot_alloc`)
      "#Hkvinv" ∷ kvInv ρ.rd.raft ρ.rd.kv ∗
      -- the named premises of the constructors' axioms (D14e, unit N4): the background
      -- goroutines' effects and the auth store's record bound
      "%Htrok" ∷ ⌜transportEffectsOk⌝ ∗ "%Hckok" ∷ ⌜ckptEffectsOk⌝ ∗ "%Haufit" ∷ ⌜authRecordsFit⌝ ∗
      "%Hbuq" ∷ ⌜apply.backendUnderQuota⌝ ∗
      -- `NodeStartSpec`'s trust-boundary premises
      "#Hzap" ∷ rnLoggerZapOk ∗ "#Hsetlg" ∷ rnSetLoggerOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
      "#Htkok" ∷ rnTickerOk (srvEr ρ E₀ (W64 0) (W64 0) bootKV bud) ∗ "#Hrs" ∷ rnRaftStatusOk ∗
      "#Hns" ∷ rnNewStorageOk ∗
      "#Hstop" ∷ (∀ n : Loc, rnStopOk n) ∗
      -- the packages' init facts `start` needs
      "#Hcci" ∷ context.isClosedchanInit ∗ "#Hwci" ∷ waitClosecInit }}
    (App (Val (@! NewServer)) (Val #cfg))
  {{ (srv : Loc) (err : GoInterface), RET (PairV #srv #err);
      ⌜srv = null ∧ err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗
        ∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
          (γn : RNNames) (b : GoInterface),
          ⌜envAgree E E₀ ∧ E.authOn = false⌝ ∗ srvWatchBuilt srv E ∗
          srvBuilt srv γA ci TM E ρ ρ.rd (srvEr ρ E₀ (W64 0) (W64 0) bootKV bud) γn b (W64 0)
            (W64 0) bootKV N ∗
          -- (D17d, 2026-10-18) `run`'s snapshot contract, from the storage's snapshot token
          srvBuildGap srv (W64 0) (W64 0) ∗
          -- (D19g (b), 2026-10-18) what serving needs: `v3rpc.Server`'s configuration fields and
          -- watchable store, the progress interval's field, and the request slots
          srvServeBuilt srv E cfg 64 }}

end spec

end EtcdGrove
end Perennial
