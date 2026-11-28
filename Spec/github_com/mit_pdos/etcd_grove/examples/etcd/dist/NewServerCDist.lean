/- Lean-first (no Rocq counterpart).

**DRAFT (etcd_safe S0, 2026-11-26; unreached, not reviewed).** `etcdserver.NewServer(cfg)` on a member machine
of a distributed deployment, **on a data directory a crash (or a graceful stop) left**: `NewServer.specC`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServerCrash.lean`) with the in-process raft network replaced by
the peer addresses, as `NewServer.specG_dist` (`NewServerDist.lean`) does for a first start. The axiom is
`Proof/.../etcd/dist/NewServerCDist.lean`. `plans/etcd-safe-restart-design.md` §3, §4.3 (P1, restart).

**What changes from `NewServer.specC`** (nothing else; `etc/dist-axiom-diff.py` checks this list against the two
texts, `etc/dist-axiom-diff-allow.txt`): `NewServer.specG_dist`'s network changes, and only those:
* the binder `[π : Net.NetProtoGS]` (the net extension's protocol ghost state, for `httpAddrAt`);
* the network's names `γn` are no binder: the post gives them (`∃ γn`, with `γn.N = srvNet γ` and `γn.dir = dir`,
  what the premise `%Hγn` fixed before);
* `netHttpOk γn id` is replaced by `httpAddrAt γ pid a` for every other peer `pid`'s address `a` in the directory
  (`#Hpeers`, `S5Interim.lean`), and `noProxyEnv` is added (`#Hnoproxy`).
`NewServer.specG_dist`'s F7/F2 changes (the caller's auth names and lessor name) are not made: `specC` is auth off
(`ρ.rd.kv.ch0 = alarmChain false …`, `E.authOn = false`), and a restarted incarnation's lessor is its own
(`NewLessor` recovers it from the image's `lease` bucket, `specC`'s post): at lease mode `.none` no client axiom
reads the view's lessor name (`Serve_distR`, `ServeDistR.lean`).

**Not in this draft (open, S0's report):** the crash keeps beyond `specC`'s (B5 of `notes/etcd-dist-d6.md`:
`rnDurInvK`'s token and names, the WAL area's `walInv` and token, `dbCrashKeep`, the durable spine), and a crash
*during* the call (B4): `specC` is a triple, so its exclusive precondition (the image, `Hids`, the fresh names) is
the callee's until it returns. Whatever `specC` gains for these, this copy gains verbatim (the gate's `pair`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServerCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S5Interim

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Net go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewServer(cfg)` on a data directory a crash left, on a member machine** (DRAFT; see the file header):
`NewServer.specC` with `NewServer.specG_dist`'s network changes. -/
abbrev NewServer.specC_dist [π : Net.NetProtoGS] : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft)
    (id : w64) (ρ ρo : ReqNames) (E₀ : apply.AEnv GF) (N : Nat)
    (Φs : w64 → w64 → List w8 → GName → IProp GF)
    -- (dist) the raft network's names `γn` are the post's, as `NewServer.specG_dist`'s
    (dir : w64 → List GoString) (m : lease.Mode)
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
  -- (fmt stage 1, 2026-11-24) the URLs within etcd's URL bounds (`NewServer.spec`'s)
  etcdURLsFit U.peer → etcdURLsFit U.client →
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
      "#Hvoff" ∷ ⌜EtcdVerifyOff⌝ ∗
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
      -- (dist) in place of the in-process network's HTTP side (`netHttpOk γn id`, `γn.N = srvNet γ`,
      -- `γn.dir = dir`): every other peer's address in the directory set to etcd's peer protocols of the
      -- cluster (`httpAddrAt`, as `NewServer.specG_dist`'s `Hpeers`), and no HTTP proxy in this process
      "#Hpeers" ∷ (□ ∀ (pid : w64) (a : GoString), ⌜pid ∈ γ.vs ∧ pid ≠ id ∧ go!"http://" ++ a ∈ dir pid⌝ -∗
        etcd_dist.httpAddrAt (Gg := hG.goose_globalGS) γ pid a) ∗
      "#Hnoproxy" ∷ etcd_dist.noProxyEnv ∗
      "%Haufit" ∷ ⌜authRecordsFit⌝ ∗
      "%Hbuq" ∷ ⌜apply.backendUnderQuota⌝ ∗
      "%Hdisk" ∷ ⌜storage.diskOk⌝ ∗
      "%Hmmap" ∷ ⌜storage.openMmapOk cfg⌝ ∗
      -- (premises to axioms, 2026-11-24: `rnLoggerZapOk`, `rnTimeoutDetectorOk` gone, now `newRaftNode`'s callees' trust-boundary specs)
      "#Hcci" ∷ context.isClosedchanInit }}
    (App (Val (@! NewServer)) (Val #cfg))
  {{ (srv : Loc) (err : GoInterface), RET (PairV #srv #err);
      -- (T4, 2026-11-24, lead's decision) raft's crash token of the vacancy `NewServer` arms
      -- (`nodeVacant_arm`), for this generation's own next crash
      (∃ x, nodeCrashTok γ.cl id x) ∗
      -- (D-T7-2, 2026-11-25, approved on #50) the snapshot directory's crash token (the image's
      -- `snapDirKeep`; the server keeps the handle), for the same next crash
      srvSnapKeep γ id cfg.DataDir' ∗
      ((⌜srv = null ∧ err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      ⌜err = GoInterface.nil⌝ ∗ threadTok ∗
        ∃ (γn : NetNames GF) (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
          (γrn : RNNames GF) (b : GoInterface) (γk : GName) (τ : SrvTr GF) (at₀ : w64),
          -- (dist) the member's network names, with the in-process network's payload and directory
          ⌜γn.N = srvNet γ ∧ γn.dir = dir ∧ envAgree E E₀ ∧ E.authOn = false⌝ ∗
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
          srvStop.keep srv cfg E γrn γk) }}

end spec

end EtcdGrove
end Perennial
