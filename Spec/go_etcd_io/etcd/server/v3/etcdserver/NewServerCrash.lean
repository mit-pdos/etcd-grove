/- `NewServer(cfg)` on a data directory a machine crash left: `NewServer.specC` (etcd-dist D6, spec
phase, 2026-11-24; `notes/etcd-dist-d6.md` §2). A third spec of `NewServer` (`etc/gen-link.py`'s
`<fn>+<S>`: `NewServer+C`, to be proved by `NewServer.wp_proofC`), not yet proved or linked.

**What it is.** `NewServer.specR` (the graceful restart) with the stopped image `srvDiskImageAt`
replaced by the crash image `srvCrashImageAt` (`InvCrashImage.lean`: the backend's index may be above
the WAL's commit, the WAL's read facts carried, the id's vacancy unarmed, any storage registry) and
`bootstrapRestartContract` by `bootstrapCrashContract` (its generalization to such images). The post
is `specR`'s word for word: the restarted incarnation's built part `srvBuiltR` at the restart's apply
state `restartKV ρ.rd.kv A`, the KV model of the backend's applied log `A` (which may now run past the
WAL's commit: the raft loop's replay of entries at or below the consistent index is skipped by the apply
thread, `applyEntryNormal`'s `index <= ci`; `notes/etcd-dist-d6.md` §4, the proof's main new step).

**One restart spec.** A graceful stop's image is a crash image (`srvDiskImageAt ⊢ srvCrashImageAt`:
unarm the vacancy, weaken `i ≤ σ.commit`; `walReadFacts σ` from the WAL's C6 or the graceful contract),
so `specC` subsumes `specR`, which can then be derived and retired. A first start stays `specG`
(`NewServer.lean`): Go takes the other branch of `bootstrap` (`haveWAL` false), and its post differs
(`srvBuiltG`, the lease-TTL row of a node `StartNode` made); the member's program reaches one or the
other by the files (`memberGen`'s two cases, `dist/crash/MemberGen.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCrashImage

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

/-- **`NewServer(cfg)` on a data directory a crash left** (D6; see the file header): `NewServer.specR`
at the crash image `srvCrashImageAt` and `bootstrap`'s crash contract. -/
abbrev NewServer.specC : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft)
    (id : w64) (ρ ρo : ReqNames) (E₀ : apply.AEnv GF) (N : Nat)
    (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (γn : NetNames GF) (dir : w64 → List GoString) (m : lease.Mode)
    -- the image the crash left, at its witnesses (`srvCrashImage`'s)
    (S : RaftState) (σ : StorContents) (i : w64) (A : List EntryModel) (D : backend.Data)
    (mb : Membership) (M : GMap Loc MemStorNamesRec),
  ρ.rd.raft = ⟨γ, [], W64 0⟩ →
  -- the restarted names the stopped ones where the cluster sees them
  restartNames ρo ρ →
  γ.rule = srvRule (W64 0) γ.boot →
  -- (auth-lease S4, 2026-11-16) a cluster outside raft's no-snapshot mode (`RestartNode`'s)
  ¬ clusterNoSnap γ.cl →
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
  -- what the crash contract covers: no forced new cluster, the WAL in the data directory's
  -- dedicated WAL directory (wal-link P2)
  bootCfgOk cfg → cfg.ForceNewCluster' = false → cfg.DedicatedWALDir' = srvWalDirOf cfg.DataDir' →
  N + 7 + bootWB ≤ backend.wbInit →
  letI : MemStorReg GF := ⟨γ.reg⟩
  {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Htok" ∷ threadTok ∗
      "#Hfg" ∷ isFeatureGate cfg.ServerFeatureGate' ∗
      "#Hlcp" ∷ featureIs cfg.ServerFeatureGate' go!"LeaseCheckpoint" false ∗
      -- `bootstrap`'s contract on a data directory a crash (or a stop) left
      "#HbootC" ∷ bootstrapCrashContract cfg U γ id N dir ∗
      "#Hzlg" ∷ zapLoggerOk cfg.Logger' ∗
      "#Hvoff" ∷ envVerifyOff ∗
      "#Hcfgro" ∷ bootCfgRO cfg U ∗
      -- the image the crash left, in the configuration's data directory
      "Himg" ∷ srvCrashImageAt γ ρo id cfg.DataDir' S σ i A D mb M ∗
      "#Hsrl" ∷ srvRaftLogInv ρ.rd.raft ∗
      "#Hidc" ∷ idClusterInv ρ.ids.issued ρ.ids.cnt ρ.ids.wn ρ.ids.fs ρ.ids.gen srvFloorFacts ∗
      "#Hpfxi" ∷ idPfxInv ρ.ids.gen ρ.ids.pfx ∗
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
          (γrn : RNNames GF) (b : GoInterface) (γk : GName) (τ : SrvTr GF) (at₀ : w64),
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
          srvReadyCloser srv E ∗
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
