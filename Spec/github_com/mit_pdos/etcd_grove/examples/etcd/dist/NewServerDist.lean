/- Lean-first (no Rocq counterpart).

`etcdserver.NewServer(cfg)` on a member machine of a distributed deployment (interim trust boundary until phase 7
S5 across machines; `notes/etcd-dist-plan.md`, "Interim transport"): `NewServer.specG` with the in-process raft
network replaced by the peer addresses. The axiom is `Proof/.../etcd/dist/NewServerDist.lean`.

**What changes from `NewServer.specG`** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean`; nothing
else, the rest is its text verbatim):
* the network's names `γn` are no binder: the post gives them (`∃ γn`, with `γn.N = srvNet γ` and `γn.dir = dir`,
  what the premise fixed before), as `StartMember_dist.spec` (`putgetk`) does;
* `netHttpOk γn id` (the in-process streams' registry, every other member's host registered with raft's protocol
  through the single-process `http.reserve`) is replaced by `httpAddrAt a` (`S5Interim.lean`: the deployment's
  start set `a` to etcd's peer protocols) for every other peer's address `a` in the directory;
* `noProxyEnv` (this process has no HTTP proxy variable set; the program's check, `os.Getenv.specEnv`) is added.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S5Interim

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewServer(cfg)` on a member machine** (see the file header), in the auth mode `on` and the compaction
mode `cmp`. -/
abbrev NewServer.specG_dist [π : Net.NetProtoGS] (on cmp : Bool) : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft)
    (id : w64) (ctxs : List (List w8)) (ρ : ReqNames) (E₀ : apply.AEnv GF) (N : Nat)
    (Φs : w64 → w64 → List w8 → GName → IProp GF)
    -- the URL directory (the raft network's names `γn` are the post's: the network across machines is the
    -- peer addresses', `httpAddrAt`)
    (dir : w64 → List GoString)
    -- (2026-10-26, D22 J2, R-loc) the member's snapshot directory's names (`SrvRaft.snapLoc`;
    -- raft's `RaftNames.reSnapLoc` until 2026-10-27)
    (γd : GName)
    -- (2026-11-04, the lease-expiry plan's Part C) the cluster's lease mode, the caller's choice
    (m : lease.Mode),
  -- the read names: at the cluster's raft names, the start log empty, the start index `0`; the
  -- cluster static, as raft's static mode until 2026-10-27 (the conf-change policy then, now the
  -- KV invariant's `ccLogOk`); the KV's start values, its certificate map the store's
  -- (2026-10-30, the repair: raft's one mode; until then the cluster static, `γ.dyn = false`)
  ρ.rd.raft = ⟨γ, [], W64 0⟩ →
  -- (2026-10-30, the repair, P9) the cluster's conf entries decided by the server's rule
  -- (`srvClusterBoot_alloc`'s; what `rnEnvOk` asks of the raft node's environment)
  γ.rule = srvRule (W64 0) γ.boot →
  -- (auth-lease S4, 2026-11-16, L1 option 1) in the cluster's no-snapshot mode,
  -- `SnapshotCatchUpEntries` at least `2^48`, the receipts' bound below (the log compacted at index
  -- `1` only)
  (clusterNoSnap γ.cl → 2 ^ 48 ≤ uint.Z cfg.SnapshotCatchUpEntries') →
  ρ.rd.kv.c0 = W64 0 → ρ.rd.kv.ch0 = apply.alarmChain on false false →
  ρ.rd.kv.log0 = [[], []] →
  -- (M2's apply side, item 14') the KV names' compaction mode the stand-in's
  ρ.rd.kv.cmp = cmp →
  -- the configuration (`mvcc.New`'s premise on the batch limit: unit N1, 2026-10-17;
  -- `nonissues/etcd-compaction-negative-batch-limit.md`)
  -- (sweep repairs 1, R1-2: the logger, until then `cfg.Logger' ≠ null` here, is the precondition's
  -- `zapLoggerOk cfg.Logger'`)
  mvcc.batchLimitOk cfg.CompactionBatchLimit' →
  -- (2026-10-30, `notes/keylen.md`) the request limit (`MaxRequestBytes`) below the clients'
  -- model's key bound, with the gRPC overhead (`v3rpc.etcdMaxRequestBytesOk`): a scope
  -- restriction, the code accepts any limit; etcd's default (1.5 MiB) meets it
  v3rpc.etcdMaxRequestBytesOk (uint.nat cfg.MaxRequestBytes') →
  -- (2026-10-31, `issues/etcd-txn-nested-depth-apply-panic.md`) the transaction budget
  -- (`MaxTxnOps`) within protobuf's recursion limit (`v3rpc.maxTxnOpsOk`: at most 4999): a scope
  -- restriction, the code accepts any budget and from 5000 on one nested transaction panics every
  -- member's apply; etcd's default (128) meets it
  v3rpc.maxTxnOpsOk (sint.Z cfg.MaxTxnOps') →
  -- the auto-compactor's configuration against the KV's compaction mode and the cluster's retention
  -- (the compactor's slot, `v3compactor.bootCfg`: off in either mode, or on in compaction mode in
  -- revision or periodic mode; K1 of `notes/k8s-compactor-plan.md`, 2026-11-04, the user's approval;
  -- until then inline, the compactor on exactly in compaction mode)
  v3compactor.bootCfg cfg.AutoCompactionMode' cfg.AutoCompactionRetention' cmp ρ.rd.kv.cret →
  -- compaction with auth off (M2's scope; a coupling of the auth mode and the KV's)
  (cmp = true → on = false) →
  -- the stand-in's mode the server's (`envAgree`'s `E.γ.cm = E.cmp` reads it off the post)
  E₀.cmp = cmp →
  -- (R8, 2026-11-07) the stand-in's KV witness the server's at the read names (`srvKVInvsM`'s
  -- `E.Nx = kvNxM on ρ.rd`, `srvApi.kvNx` per mode, which `envAgree`'s `E.Nx = E₀.Nx` reads off the post)
  E₀.Nx = srvApi.kvNx ρ.rd on →
  -- the logic's thread bound (D17: the adequacy theorem's `T`, its caller's choice; J8a-6,
  -- 2026-11-01, the user's decision: `2 ^ 28` (until then `2 ^ 31`), the transport's pool of `lgMu`
  -- reader slots, a thread pool, having `2 ^ 28` of them; the backend-auth-split stage, 2026-11-02:
  -- written `backend.rdPoolN`, the backend's pool of readers being as large)
  threadBound GF ≤ backend.rdPoolN →
  -- the time-receipt bound (D19b: the adequacy theorem's step bound `N`, its caller's choice):
  -- the id generator issues fewer than `2 ^ 48` ids; the apply thread takes at most `N` of the
  -- `N + 7` write tokens `bootstrap` gives (the write budget `srvWTPool`)
  receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-10-30, the repair: snapshots allowed, the user's decision) no run-length premise (until
  -- then `receiptBound ≤ SnapshotCatchUpEntries + 1`, which kept the compaction at index `1`)
  -- (D19b stage 5) the bootstrap log (one conf change per initial peer) shorter than `2 ^ 60`:
  -- with the receipts, raft's indices fit `MemoryStorage.Append`'s `2 ^ 61` (`rnLogFits`)
  γ.boot.length ≤ 2 ^ 60 →
  -- (D21e (A), stage M4) the member's prefix in the cluster's claims is its member id's
  -- (`NewGenerator`'s `uint16(id) << 48`), and the claimers' facts at it are the server's
  -- (`srvFloorFact`, unit V2)
  ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) → Φs ρ.ids.pfx = srvFloorFact E₀ →
  (∃ p : Loc, p ≠ null ∧ cfg.ServerFeatureGate' = interface.mkOk
    (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #p) →
  -- (2026-10-24, rafthttp stage 6d) the network's directory well formed
  netDirOk dir →
  -- (2026-10-27, D22 J-T, W8) the member's configured peer URLs its directory URLs (what its
  -- transport sends in `X-PeerURLs`)
  peerURLsDir dir id U.peer →
  -- (2026-11-03, the final whole-`bootOk` review's S2 and M2; slots of the slot convention,
  -- `notes/spec-first-plan.md`) the raft node's condition on the configuration (a positive
  -- heartbeat, a scope restriction: `raftNode.bootCfg`), and the transport's on its directory, of
  -- raft's peers (the members it names exactly raft's, at most `peersMax`: `rafthttp.bootCfg`, a
  -- coupling the transport owns)
  raftNode.bootCfg cfg → rafthttp.bootCfg dir γ.vs →
  -- (the auth plan's E2i) with auth on, the simple token provider with a positive TTL that fits
  -- `time.Duration(cfg.TokenTTL) * time.Second`
  (on = true → cfg.AuthToken' = go!"simple" ∧ 0 < uint.Z cfg.TokenTTL' ∧
    uint.Z cfg.TokenTTL' < 2 ^ 32) →
  -- (2026-11-04, the lease-expiry plan's Part C; the slot convention) the lease subsystem's boot
  -- premise at the mode `m` (`lease.bootCfg`, `LeaseApi.lean`): the KV names' grant flag the mode's,
  -- in a granting cluster no lease expiring, in either auth mode (auth-lease S3c, 2026-11-15: until
  -- then with auth on no lease granted, lease-grant 2.13) (and
  -- until the lease-expiry plan's S2–S4, 2026-11-05, the open cases, `srvGrantOpen`; lease-grant
  -- D2); until 2026-11-12 also the lessor's checkpointer's effects (the opaque `ckptEffectsOk`,
  -- `NewLessor`'s premise; D14e, unit N4), deleted: no checkpointer is installed (`Hlcp`), so it
  -- covered no call
  lease.bootCfg (GF := GF) ρ.rd.kv.lm m on →
  -- (2026-11-03, the whole-`bootOk` review, A and C) what `bootstrap`'s contract asks: the
  -- configurations it covers (`bootCfgOk`, `bootCfgFresh`: a mappable quota, a batch
  -- limit the backend's model admits, no bootstrap defragmentation, raft's timing, a new cluster, no
  -- discovery service, valid UTF-8 member names; scope restrictions, the code accepts more) and a
  -- write budget past `bootstrap`'s own write-backs (`bootWB`)
  bootCfgOk cfg → bootCfgFresh cfg U → N + 7 + bootWB ≤ backend.wbInit →
  -- (2026-10-27) the `MemoryStorage` registry the cluster's storage model's (`srvStor γ`)
  letI : MemStorReg GF := ⟨γ.reg⟩
  {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      -- (2026-11-02, the backend-auth-split stage) the constructing thread's token, given back:
      -- for the pooled readers of the next stage
      "Htok" ∷ threadTok ∗
      "#Hfg" ∷ isFeatureGate cfg.ServerFeatureGate' ∗
      -- (stage B3, 2026-11-12) the lease checkpointer off: `NewServer` installs none, so `le.cp`
      -- stays nil (`NewLessor.spec`, `lease.lessor.Renew.spec`); `NewDefaultServerFeatureGate` gives it
      "#Hlcp" ∷ featureIs cfg.ServerFeatureGate' go!"LeaseCheckpoint" false ∗
      -- `bootstrap`'s contract (D13b)
      -- (M2's item 15, stage B3) at `N` write tokens in both modes (until then `N + N` in
      -- compaction mode, `N` more for the compaction's own stock, `srvCmpStock`)
      "#Hboot" ∷ bootstrapContract cfg U γ id ctxs N dir ∗
      -- (sweep repairs 1, R1-2, L4) the configured logger a zap logger (what `bootstrap`'s contract
      -- takes; until then `cfg.Logger' ≠ null`, which a zero `&zap.Logger{}` meets)
      "#Hzlg" ∷ zapLoggerOk cfg.Logger' ∗
      -- (sweep repairs 1, R1-4b, B4) `ETCD_VERIFY` off for the run, from program start (what
      -- `bootstrap`'s contract and the snapshot path's `OpenSnapshotBackend` take)
      "#Hvoff" ∷ envVerifyOff ∗
      -- (D19r (B), (F)) what `bootstrap` takes: the configuration's URLs, read-only, and the
      -- storage registry's authority, empty (the caller allocates it)
      "#Hcfgro" ∷ bootCfgRO cfg U ∗ "Hrauth" ∷ memStorRegAuth (∅ : GMap Loc MemStorNamesRec) ∗
      -- (2026-11-03, the WAL's API, change 6; its slot) the member's WAL directory fresh: a first start
      "Hwdf" ∷ wal.bootRes cfg ∗
      -- the cluster's (the node API's allocation, 2026-10-27): this node's boot token, of the
      -- peers `γ.vs` with the contexts `ctxs`, with (2026-11-01, durability layer 4) its durable
      -- state at `RaftState.init` and its vacant id (`StartNode`'s), and the server's raft invariant
      "Hnboot" ∷ (nodeBoot γ.cl srvClusterN γ.vs ctxs id ∗ raftState γ.cl id RaftState.init ∗
        nodeVacant γ.cl id) ∗
      "#Hsrl" ∷ srvRaftLogInv ρ.rd.raft ∗
      -- (D21e (A), stage M4) the cluster's resources, allocated once (`srvClusterBoot_alloc`):
      -- the claims (with the reserved id `0`, D19c), the proposals' mint, the read contexts;
      -- and the member's share: its prefix's entry and slots (`idShare`), `2 ^ 48` of raft's read
      -- credits (`srvMemberBoot_alloc`)
      -- (R2c, 2026-11-02) by incarnation key: the cluster's claims at the server's facts' family,
      -- the member's key registering its store's index (the claim facts' parameter)
      "#Hidc" ∷ idClusterInv ρ.ids.issued ρ.ids.cnt ρ.ids.wn ρ.ids.fs ρ.ids.gen srvFloorFacts ∗
      "#Hpfxi" ∷ idPfxInv ρ.ids.gen ρ.ids.pfx ∗
      "#Hidk" ∷ idKeyFactAt ρ.ids.fs ρ.ids.key E₀.γs.slog ∗ "#HNZ0" ∷ idNoZero ρ.ids ∗
      "#Hpmint" ∷ srvPropMint ρ.rd.raft ρ.ids ∗ "#Hrdctx" ∷ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
      -- (2026-10-30, the repair: no read credits, raft's `ReadIndex` takes none)
      "Hids" ∷ idShare ρ.ids ∗
      -- (linkv-txn stage B1, 2026-10-20) the member's entry of the registries' map, for `start`
      "Hwtok" ∷ idWaitTok ρ.ids ∗
      -- the names chosen before the call (D13a), fresh
      -- (strict M1, 2026-11-06, the draft's `newServerStoreFreshA`) the server's names of the
      -- store's state fresh (until then mvcc's `idxFresh E₀.γ.idx`), and the KV certificates' map
      -- the read names' (until then the store's, `ρ.rd.kv.cok = E₀.γ.cok`)
      "Hkvs" ∷ srvApi.newServerStoreFreshA E₀.γs ∗
      "Hcok" ∷ ghostMapAuth ρ.rd.kv.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      "Hrev" ∷ ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
      "Hrd" ∷ srvReadNamesFreshNK ρ.rd ∗
      -- the KV invariant at the bootstrap log (D19g (a): allocated with raft's ghost state,
      -- whose standing update `noopAu` it gives, `srvRaftBoot_alloc`)
      "#Hkvinv" ∷ kvInvM on ρ.rd.raft ρ.rd.kv srvAuthSt0 ∗
      -- (D21 M2, 2026-10-19) the raft network, whose payload is the server's (`srvNet`) and
      -- directory `bootstrap`'s (until then the named premise `transportEffectsOk`); (2026-10-24,
      -- rafthttp stage 6d) its HTTP side ready (until then the member's slot, `netSlot γn id`)
      -- (dist) in place of the in-process network's HTTP side (`netHttpOk γn id`, `γn.N = srvNet γ`,
      -- `γn.dir = dir`): every other peer's address in the directory set to etcd's peer protocols (the start's
      -- `http_addr_set`), and no HTTP proxy in this process (the program's check, `noProxyEnv`)
      "#Hpeers" ∷ (□ ∀ (pid : w64) (a : GoString), ⌜pid ∈ γ.vs ∧ pid ≠ id ∧ go!"http://" ++ a ∈ dir pid⌝ -∗
        etcd_dist.httpAddrAt (Gg := hG.goose_globalGS) a) ∗
      "#Hnoproxy" ∷ etcd_dist.noProxyEnv ∗
      -- (2026-10-26, D22 J2, R-loc) the member's snapshot directory, empty, at the names the
      -- cluster gives the member (raft's `RaftNames.reSnapLoc` until 2026-10-27; until then `NewServer` allocated it,
      -- `snapDir_alloc`; 2026-10-27: at the server's `SrvRaft.snapLoc`). This is the ghost map's
      -- authority only; the directory itself (no `.snap.db` file yet, no writer but the server's
      -- snapshotters) is `bootOk`'s `Hsdo` (`snap.snapDirOwn`, restart S6a M1), which names this map
      -- in the directory's invariant (`snapDir_init`); `snapDir_alloc` is deleted.
      "%Hsloc" ∷ ⌜γ.snapLoc id = some γd⌝ ∗ "Hsdir" ∷ ghostMapAuth γd 1 (∅ : GMap w64 Unit) ∗
      -- the named premises of the constructors' axioms (D14e, unit N4): the auth store's record
      -- bound (until 2026-11-12 also the lessor's checkpointer's effects, through `lease.bootCfg`)
      "%Haufit" ∷ ⌜authRecordsFit⌝ ∗
      "%Hbuq" ∷ ⌜apply.backendUnderQuota⌝ ∗
      -- (D22 S-j2, 2026-10-20; an environment assumption the user approved) bbolt's `Open`
      -- succeeds on the database files the server opens after its start (`storage.OpenBackend`'s
      -- axiom: its goroutine panics otherwise), for `applySnapshot`'s snapshot backend; kept by
      -- the server's snapshot path once S-j wires it in (today nothing opens one)
      "%Hdisk" ∷ ⌜storage.diskOk⌝ ∗
      -- (2026-10-29, the `axiom` skill's `notes/axiom-review/openbackend.md`; the user's decision)
      -- the configuration's quota is one bbolt can map (`storage.openMmapOk`: `OpenBackend`'s
      -- goroutine panics otherwise, `nonissues/etcd-quota-backend-bytes-mmap-panic.md`), for the same
      -- snapshot backend
      "%Hmmap" ∷ ⌜storage.openMmapOk cfg⌝ ∗
      -- `NodeStartSpec`'s trust-boundary premises
      "#Hzap" ∷ rnLoggerZapOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
      "#Hns" ∷ rnNewStorageOk ∗
      -- the packages' init facts `start` needs
      "#Hcci" ∷ context.isClosedchanInit }}
    (App (Val (@! NewServer)) (Val #cfg))
  {{ (srv : Loc) (err : GoInterface), RET (PairV #srv #err);
      (⌜srv = null ∧ err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      ⌜err = GoInterface.nil⌝ ∗ threadTok ∗
        ∃ (γn : NetNames GF) (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
          (γrn : RNNames GF) (b : GoInterface) (γk : GName) (τ : SrvTr GF),
          -- (the auth plan's E3zb, 2026-10-28) with auth on, the mode `.on γa` (`Start.spec`'s at `.on γa`)
          -- (dist) the member's network names, with the in-process network's payload and directory
          ⌜γn.N = srvNet γ ∧ γn.dir = dir ∧ envAgree E E₀ ∧ E.authOn = on ∧ (on = true → ∃ γa, E.authMode = .on γa)⌝ ∗
          -- (per-type stage B2, 2026-11-11, r5 §4.2) the raw serving stocks: the revocation's built
          -- part, the gRPC run pool's store tokens with `bemu` slots
          srvServeStock srv E ∗
          srvWatchBuilt srv E ∗
          -- (D22 J1b, 2026-11-01, the user's decision) the KV's closer and the backend file's
          -- directory entry are in the built part (`srvSnapBoot`'s `srvSnapRes`)
          srvBuiltG on srv γA ci TM E ρ ρ.rd (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) id (srvTrKey γn γk) (srvTrStopK γk))
            γrn b (W64 0)
            (W64 0) (bootKVOf on) N ∗
          -- (D17d, 2026-10-18) `run`'s snapshot contract, from the storage's snapshot token
          srvBuildGap srv γrn ρ.rd.cursor (W64 0) (W64 0) ∗
          -- (D19g (b), 2026-10-18) what serving needs: `v3rpc.Server`'s configuration fields and
          -- watchable store, the progress interval's field, `v3rpc.Server`'s `bemu` slot and
          -- `Start`'s two `lgMu` slots (until per-type stage B3, 2026-11-11, also 64 request slots:
          -- the gRPC runs borrow the run pools, `srvRunPool`)
          srvServeBuilt srv E cfg ∗
          -- (D19i part 2) the storage version monitor's backend access
          srvSVRes srv E ∗
          -- (audit B4a, D19m) the hash and downgrade monitors' configuration fields and
          -- `monitorDowngrade`'s `lgMu` reader slot
          srvMonitorCfg srv cfg ∗
          -- (2026-10-23) the right to close `readych`, for `publishV3`
          srvReadyCloser srv E ∗
          -- (D21 M5, 2026-10-19) the server is member `id` of the network `γn`, its transport
          -- started there: what `RaftHandler` takes, to serve the member's raft handler;
          -- (2026-10-24, rafthttp stage 6d) a reader's token of the transport (`CutPeer`,
          -- `MendPeer`) and what each request the handler serves borrows (`http.Serve`)
          srvNetMember γn srv id τ ∗ srvTrTok γn τ ∗
          ([∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ) ∗
          -- (until per-type stage B3, 2026-11-11, also 64 of the store's reader tokens for the
          -- watch service, `srvWatchReaders`: the watch loops borrow the run pool)
          -- (2026-11-04, the lease-expiry plan's Part C; the slot convention) the lease
          -- subsystem's part (`lease.srvInv`, `LeaseApi.lean`): (until auth-lease S3c, 2026-11-15,
          -- with auth on its lessor finding no lease, E3zb) the peers' round tripper and the lessor's reader side (K7),
          -- the lessor's reader pool (the lease-src plan); until then four conjuncts here
          lease.srvInv on srv E m ∗
          -- (2026-11-05, the lease-expiry plan's E3 (c) stage 2) the lease-TTL row's raft part at
          -- the peers (`leaseTTLRowR`, `LeaseRead.lean`): the member id, the node `StartNode` made
          -- (a first start), every committed configuration the boot's
          leaseTTLRowR srv γ.vs ∗
          -- (authkv's Main, 2026-10-30) the TLS fallback's configuration field, the
          -- configuration's (`srvTLSId_false` refutes the fallback when it is `false`), and with
          -- auth on the auth store's cost field (`BcryptCost()`'s) and (C1's A4, 2026-10-31) its
          -- `Authenticate` side at the server's reader resource (`srvAuthStoreOn`)
          srvCfgFieldAddr srv go!"ClientCertAuthEnabled" ↦□ cfg.ClientCertAuthEnabled' ∗
          □ (⌜on = true⌝ → srvAuthStoreOn srv E.RD) ∗
          -- (the restart plan's R2b-3d; 2026-11-05, the stop's slot, `StopApi.lean`: until then
          -- inline, `srvStopKeep`, `srvTrKeyOf`, the auth-off `srvCleanupOwn`) what the server's stop
          -- needs of the construction
          srvStop.keep srv cfg E γrn γk }}

end spec

end EtcdGrove
end Perennial

end
