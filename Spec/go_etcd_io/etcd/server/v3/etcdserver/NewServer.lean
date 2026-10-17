/-
`NewServer(cfg)` (`server.go`): the server's construction over `bootstrap`'s result. Lean-first
(no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16; D13 and D13a-d:
`notes/decisions.md`, "The server's construction: `NewServer` over `bootstrap`'s result").

**The premises.**
* `bootstrap`'s contract (`bootstrapContract`, `InvBoot.lean`; D13b): a premise, not an axiom.
* **`CheckQuorum` and `PreVote` off** (D15, temporary): the raft start result covers only them
  off; etcd's own `raftConfig` sets `CheckQuorum: true`, the patched fork takes it from the field
  `cfg.DisableCheckQuorum` it adds (off by default), so the configuration must set it, and leave
  `cfg.PreVote` unset (etcd's embed sets it by default). Not etcd's default configuration.
* The cluster's ghost state, as `NodeStartSpec`'s: raft's names `γ` with this node's ghost state
  at the bootstrap log's state, the committed bootstrap log, raft's commit invariant, the budget;
  and the outputs of `allocClientBoot`'s continuation for this server (the client's half of the
  committed log, the fresh-token authorities) and raft's read credits
  (`ownRaftGhost_alloc_boot`).
* **The names chosen before the call** (D13a): the request path's names `ρ` (the generator's,
  fresh; the read names at the cluster's raft names, the start log empty and the start index `0`,
  fresh), the store's index names and certificate map and the revisions' map (fresh), which the
  stand-in environment `E₀` carries (the construction's apply environment agrees with it,
  `envAgree`).
* The workload clause `clusterWorkloadOk` at `E₀` (D13c), the start `bootKV` at the consistent
  index `0`.
* `NodeStartSpec`'s trust-boundary premises (the raft wrapper's contracts; `rnTickerOk` at the
  server's raft environment `srvEr`), the configuration's logger and feature gate (a
  `*featuregate.featureGate`, for `addFeatureGateMetrics`'s type assertion), the packages' init
  facts `start` needs.

**The postcondition** (D13d): an error, the server `nil`; or the built part `srvBuilt`
(`InvBuild.lean`) at the server's raft environment `srvEr ρ E₀ …`, for an apply environment `E`
agreeing with `E₀`, auth disabled, and the client's `etcdKV` at the bootstrap log's model. The
rows of `isServerBuilt` no `NewServer` proof gives are the residual `srvBuildGap`
(`isServerBuilt_of_gap`, `BuildGap.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

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
  -- raft's `CheckQuorum` and `PreVote` off (D15, temporary: not etcd's default configuration)
  cfg.DisableCheckQuorum' = true → cfg.PreVote' = false →
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
      "HrLog" ∷ rLog γ bootLog ∗
      "Hfresh" ∷ ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) ∗
      "HrdFresh" ∷ ghostMapAuth γ.reRdFresh 1 (∅ : GMap (List w8) Unit) ∗
      "HrdCred" ∷ rdCred γ (2 ^ 64 - 2) ∗
      -- the names chosen before the call (D13a), fresh
      "Hids" ∷ idNamesFresh ρ.ids ∗ "Hidx" ∷ mvcc.idxFresh E₀.γ.idx ∗
      "Hcok" ∷ ghostMapAuth E₀.γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      "Hrev" ∷ ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
      "Hrd" ∷ srvReadNamesFresh ρ.rd (kvStateOf (kvModel ρ.rd.kv (bootEntries bootLog))) ∗
      -- the workload clause (D13c)
      "#Hwork" ∷ clusterWorkloadOk ρ E₀ (W64 0) bootKV ∗
      -- the lifetime bound (D14g): at most `N` entries ever applied, `bootstrap`'s budget
      "#Hlife" ∷ srvLifeBound ρ.raft N ∗
      -- the named premises of the constructors' axioms (D14e, unit N4): the background
      -- goroutines' effects and the auth store's record bound
      "%Htrok" ∷ ⌜transportEffectsOk⌝ ∗ "%Hckok" ∷ ⌜ckptEffectsOk⌝ ∗ "%Haufit" ∷ ⌜authRecordsFit⌝ ∗
      -- `NodeStartSpec`'s trust-boundary premises
      "#Hzap" ∷ rnLoggerZapOk ∗ "#Hsetlg" ∷ rnSetLoggerOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
      "#Htkok" ∷ rnTickerOk (srvEr ρ E₀ (W64 0) (W64 0) bootKV bud) ∗ "#Hrs" ∷ rnRaftStatusOk ∗
      "#Hns" ∷ rnNewStorageOk ∗
      "#Hfits" ∷ (∀ γw : RNNames,
        ⌜γw.node.raft = γ ∧ γw.node.bud = bud ∧ γw.node.mode = RNMode.static⌝ -∗ rnLogFits γw) ∗
      "#Hstop" ∷ (∀ n : Loc, rnStopOk n) ∗
      -- the packages' init facts `start` needs
      "#Hcci" ∷ context.isClosedchanInit ∗ "#Hwci" ∷ waitClosecInit }}
    (App (Val (@! NewServer)) (Val #cfg))
  {{ (srv : Loc) (err : GoInterface), RET (PairV #srv #err);
      ⌜srv = null ∧ err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗
        ∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
          (γn : RNNames) (b : GoInterface),
          ⌜envAgree E E₀ ∧ E.authOn = false⌝ ∗
          srvBuilt srv γA ci TM E ρ ρ.rd (srvEr ρ E₀ (W64 0) (W64 0) bootKV bud) γn b (W64 0)
            (W64 0) bootKV N ∗
          etcdKV ρ.rd.kv (kvStateOf (kvModel ρ.rd.kv (bootEntries bootLog))) }}

end spec

end EtcdGrove
end Perennial
