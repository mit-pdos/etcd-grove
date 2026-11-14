/- `NewServer(cfg)` at a restart: `NewServer.specR` (restart S6, 2026-11-13; D1). Moved out of
`NewServer.lean` (2026-11-14, restart S6 B2, a form) into a file of its own, as a second spec of
`NewServer` (`etc/gen-link.py`'s `<fn>+<S>`: `NewServer+R`, proved by `NewServer.wp_proofR` in
`Proof/.../NewServerR.lean`). The text is unchanged. -/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewServer(cfg)` at a restart** (restart S6, 2026-11-13; D1, approved by the user via
etcd-grove-81, 2026-11-12; `/shared/tmp/restart-s56/plan.md` §2.1; linked since 2026-11-14, `wp_NewServerR`
in the server's `Link.lean`, but used by no closed theorem: S7/S8 link it through
`BuildServer.specRestart`). The same binary started again on the data directory its own
earlier incarnation left at a graceful stop (`HardStop.spec`'s `srvDiskImage`, at its witnesses: the
stopped incarnation's request names `ρo`, the durable raft state `S`, the WAL's records `σ`, the
consistent index `i`, the applied log `A`, the backend file's data `D`, the membership `mb` at `i`,
the storage registry `M`), in the stop's scope: auth off, no compaction mode (`srvStop.scope`).
`NewServer.specG false false` with these changes:
* binders: `ρo` and the image's witnesses; no `ctxs` (a restart has no peers, `RestartNode`) and no
  `γd` (the snapshot directory's invariant is the first start's, in the image);
* pure premises: `restartNames ρo ρ` (the restarted names agree with the stopped ones where the cluster
  sees them: raft's names, the KV invariant's fields, the claims); `bootCfgFresh` dropped (not a new
  cluster), `cfg.ForceNewCluster' = false` and `cfg.DedicatedWALDir' = ""` (what the restart contract
  covers; a first start's `wal.bootRes` holds the latter); the modes' premises at `on = cmp = false`;
* the boot rows: `bootstrap`'s restart contract (`bootstrapRestartContract`) in place of the first
  start's; the image (`srvDiskImageAt`) in place of the fresh data directory (`wal.bootRes`), the node's
  boot token, durable state and vacant id (`Hnboot`: the image holds `raftState γ.cl id S` and
  `nodeVacant`), the storage registry's empty authority (the image holds it at `M`) and the snapshot
  directory's ghost map (the image holds the first start's invariant); and the restart-only rows
  (`srvRestartRows`, D3: true of Go for row 4, false on a disclosed class for row 1, so this triple is
  honest only as an open triple; S7 deletes the premise);
* the post: the built part's restart form (`srvBuiltR`, its law `srvBuiltR_C` to `start`'s
  `isServerBuiltC .off`) at the restart's apply state (`restartKV ρ.rd.kv A`: the KV model of `A`)
  and some snapshot term `at₀`, in place of `srvBuiltG` and `srvBuildGap`; no lease-TTL row
  (`leaseTTLRowR`, a first start's: Q37 (a)); the auth-on conjunct gone; (CP2 review finding 2,
  2026-11-13) the lease subsystem's part with its lessor's history starting at the snapshot
  `NewLessor` recovers from the image's `lease` bucket (`lease.srvInvAt`: the bucket's records `recs`,
  one fresh lease of `ls` each, their TTLs raised to the lessor's minimum `mt`; `NewLessor.spec`'s
  post), in place of `lease.srvInv`'s empty first snapshot, false at a restart of a cluster that
  granted a live lease; the rest `specG`'s. -/
abbrev NewServer.specR : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft)
    (id : w64) (ρ ρo : ReqNames) (E₀ : apply.AEnv GF) (N : Nat)
    (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (γn : NetNames GF) (dir : w64 → List GoString) (m : lease.Mode)
    -- the stopped member's image, at its witnesses (`srvDiskImage`'s)
    (S : RaftState) (σ : StorContents) (i : w64) (A : List EntryModel) (D : backend.Data)
    (mb : Membership) (M : GMap Loc MemStorNamesRec),
  ρ.rd.raft = ⟨γ, [], W64 0⟩ →
  -- the restarted names the stopped ones where the cluster sees them
  restartNames ρo ρ →
  γ.rule = srvRule (W64 0) γ.boot →
  ρ.rd.kv.c0 = W64 0 → ρ.rd.kv.ch0 = apply.alarmChain false false false →
  ρ.rd.kv.log0 = [[], []] →
  ρ.rd.kv.cmp = false →
  mvcc.batchLimitOk cfg.CompactionBatchLimit' →
  v3rpc.etcdMaxRequestBytesOk (uint.nat cfg.MaxRequestBytes') →
  v3rpc.maxTxnOpsOk (sint.Z cfg.MaxTxnOps') →
  v3compactor.bootCfg cfg.AutoCompactionMode' cfg.AutoCompactionRetention' false ρ.rd.kv.cret →
  E₀.cmp = false →
  E₀.Nx = srvApi.kvNx ρ.rd false →
  threadBound GF ≤ backend.rdPoolN →
  receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.boot.length ≤ 2 ^ 60 →
  ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) → Φs ρ.ids.pfx = srvFloorFact E₀ →
  (∃ p : Loc, p ≠ null ∧ cfg.ServerFeatureGate' = interface.mkOk
    (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #p) →
  netDirOk dir →
  peerURLsDir dir id U.peer →
  raftNode.bootCfg cfg → rafthttp.bootCfg dir γ.vs →
  lease.bootCfg (GF := GF) ρ.rd.kv.lm m false →
  -- what the restart contract covers: no forced new cluster, the WAL in the data directory
  bootCfgOk cfg → cfg.ForceNewCluster' = false → cfg.DedicatedWALDir' = (go!"" : GoString) →
  N + 7 + bootWB ≤ backend.wbInit →
  letI : MemStorReg GF := ⟨γ.reg⟩
  {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Htok" ∷ threadTok ∗
      "#Hfg" ∷ isFeatureGate cfg.ServerFeatureGate' ∗
      "#Hlcp" ∷ featureIs cfg.ServerFeatureGate' go!"LeaseCheckpoint" false ∗
      -- `bootstrap`'s contract on the stopped member's data directory
      "#HbootR" ∷ bootstrapRestartContract cfg U γ id N dir ∗
      "#Hzlg" ∷ zapLoggerOk cfg.Logger' ∗
      "#Hvoff" ∷ envVerifyOff ∗
      "#Hcfgro" ∷ bootCfgRO cfg U ∗
      -- the stopped member's image, in the configuration's data directory
      "Himg" ∷ srvDiskImageAt γ ρo id cfg.DataDir' S σ i A D mb M ∗
      -- the restart-only rows (D3; S7 deletes them)
      "Hrows" ∷ srvRestartRows γ id A σ ∗
      "#Hsrl" ∷ srvRaftLogInv ρ.rd.raft ∗
      "#Hidc" ∷ idClusterInv ρ.ids.issued ρ.ids.cnt ρ.ids.wn ρ.ids.fs srvFloorFacts ∗
      "#Hidk" ∷ idKeyFactAt ρ.ids.fs ρ.ids.key E₀.γs.slog ∗ "#HNZ0" ∷ idNoZero ρ.ids ∗
      "#Hpmint" ∷ srvPropMint ρ.rd.raft ρ.ids ∗ "#Hrdctx" ∷ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
      "Hids" ∷ idShare ρ.ids ∗
      "Hwtok" ∷ idWaitTok ρ.ids ∗
      -- this incarnation's names, fresh (the caller allocates them per incarnation)
      "Hkvs" ∷ srvApi.newServerStoreFreshA E₀.γs ∗
      "Hcok" ∷ ghostMapAuth ρ.rd.kv.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      "Hrev" ∷ ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
      "Hrd" ∷ srvReadNamesFreshNK ρ.rd ∗
      -- the cluster's KV invariant (the caller has it at `ρo`: `kvInv_restartNames`)
      "#Hkvinv" ∷ kvInvM false ρ.rd.raft ρ.rd.kv srvAuthSt0 ∗
      "#Hnet" ∷ netHttpOk γn id ∗ "%Hγn" ∷ ⌜γn.N = srvNet γ ∧ γn.dir = dir⌝ ∗
      "%Haufit" ∷ ⌜authRecordsFit⌝ ∗
      "%Hbuq" ∷ ⌜apply.backendUnderQuota⌝ ∗
      "%Hdisk" ∷ ⌜storage.diskOk⌝ ∗
      "%Hmmap" ∷ ⌜storage.openMmapOk cfg⌝ ∗
      "#Hzap" ∷ rnLoggerZapOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
      "#Hns" ∷ rnNewStorageOk ∗
      "#Hcci" ∷ context.isClosedchanInit }}
    (App (Val (@! NewServer)) (Val #cfg))
  {{ (srv : Loc) (err : GoInterface), RET (PairV #srv #err);
      (⌜srv = null ∧ err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      ⌜err = GoInterface.nil⌝ ∗ threadTok ∗
        ∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
          (γrn : RNNames) (b : GoInterface) (γk : GName) (τ : SrvTr GF) (at₀ : w64),
          ⌜envAgree E E₀ ∧ E.authOn = false⌝ ∗
          srvServeStock srv E ∗
          srvWatchBuilt srv E ∗
          -- the built part's restart form, at the restart's apply state (the KV model of `A`)
          srvBuiltR srv γA ci TM E ρ ρ.rd
            (srvErM false ρ E₀ (W64 0) (W64 0) (restartKV ρ.rd.kv A) id (srvTrKey γn γk)
              (srvTrStopK γk))
            γrn b (W64 0) at₀ (W64 0) (restartKV ρ.rd.kv A) N ∗
          srvServeBuilt srv E cfg ∗
          srvSVRes srv E ∗
          srvMonitorCfg srv cfg ∗
          srvReadyCloser srv ∗
          srvNetMember γn srv id τ ∗ srvTrTok γn τ ∗
          ([∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ) ∗
          -- the lease subsystem's part, its lessor's history from the snapshot `NewLessor` recovers
          -- of the image's `lease` bucket (CP2 review finding 2: a first start's is empty)
          (∃ (recs : List (w64 × w64 × w64)) (ls : List Loc) (mt : w64),
            ⌜backend.bktEnts ((D.lookup go!"lease").getD ∅) = recs.map lease.leaseRecEnc ∧
              ls.length = recs.length⌝ ∗
            lease.srvInvAt false srv E m (lease.recMap (recs.zip ls), ∅, lease.recTTLs mt recs)) ∗
          srvCfgFieldAddr srv go!"ClientCertAuthEnabled" ↦□ cfg.ClientCertAuthEnabled' ∗
          srvStop.keep srv cfg E γrn γk }}

end spec

end EtcdGrove
end Perennial
