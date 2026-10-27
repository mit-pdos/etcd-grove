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
  `srvRaftBoot_alloc`, `NewServerAlloc.lean`). **Since stage M4 of D21 (2026-10-19) the cluster's
  resources are allocated once for the cluster and the member takes its share**
  (`srvClusterBoot_alloc`, `srvMemberBoot_alloc`): the claims of request ids (`idClusterInv`, one
  map for the cluster keyed by the full id, D21e (A), with the claimers' facts `Φs` per prefix, the
  server's at its own; the reserved id `0`, `idNoZero`), the proposals' mint (`srvPropMint`) and
  the read contexts (`srvRdCtxInv`), persistent; and the member's prefix's entry with its slots
  (`idShare`) and `2 ^ 48` of raft's read credits. Until then `NewServer` took the fresh-token
  authorities, raft's whole read budget and fresh generator names, and required the member id's 16
  low bits not `0` (now the allocation's pure premise, with the prefixes distinct).
* **The names chosen before the call** (D13a): the request path's names `ρ` (the read names at the cluster's raft names, the start log empty and the start index `0`,
  fresh, but the KV state's variable, `srvReadNamesFreshNK`), the store's index names and certificate map and the revisions' map (fresh), which the
  stand-in environment `E₀` carries (the construction's apply environment agrees with it,
  `envAgree`).
* The start `bootKV` at the consistent index `0` (the workload clause `clusterWorkloadOk`, a
  premise until D19c, D13c, is proved, `clusterWorkloadOk_of`; its residual size bound
  `clusterLogBound`, a premise until D19c's move, 2026-10-18, is gone: the apply thread checks the
  size clauses at the log it meets, small by the store's time receipts); the member id's 16 low
  bits not `0` (since M4 the cluster's allocation's premise) and the conf-change policy
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
  server's raft environment `srvEr`; `Stop` of a started node, `rnStopOkStarted`, D19r (A):
  until then of every location, false of Go), the configuration's logger and feature gate (a
  `*featuregate.featureGate`, for `addFeatureGateMetrics`'s type assertion), the packages' init
  facts `start` needs (`context`'s `closedchan`; since D19r (C), (D) the raft status's mutex and
  `pkg/wait`'s `closec` come from `etcdserver`'s and `pkg/wait`'s facts).
* (D19r (B), (F), 2026-10-18) what `bootstrap` takes: the configuration's URLs read-only
  (`bootCfgRO cfg U`) and the storage registry's authority, empty (`memStorRegAuth ∅`), which the
  caller allocates; `bootstrap`'s new `MemoryStorage` joins it.
* (D21 M2, 2026-10-19) **the raft network** (`rafthttp/Net.lean`): a network whose payload is the
  server's messages' bundle (`srvNet`) and whose URL directory is `bootstrap`'s (`dir`: the
  members' records name their own URLs), which `rafthttp.Transport.Start` takes with the server's
  inbound methods (`srv_netRaftOk`: `Process`, `IsIDRemoved`, the two reports). (2026-10-24,
  rafthttp stage 6d) The network's HTTP side ready (`netHttpOk`: every other member's hosts
  registered with the raft protocol) and its directory well formed (`netDirOk`); each peer `AddPeer` adds
  borrows eight of `lgMu`'s reader slots, each request the member's raft handler serves one (with
  one of the transport's reader tokens), `httpProcSlots` of them. (Until stage 6d the member's
  slot `netSlot γn id`, and `2 ^ 29` of `lgMu`'s reader slots for the transport's axiom; until D21
  M2 the named premise `transportEffectsOk`, opaque.)

* (D22 S-j2, 2026-10-20; approved by the user, `notes/decisions.md`, "D22's environment assumptions
  approved") `storage.dbOpensOk`: bbolt's `Open` succeeds on the files the server opens after its
  start, which the snapshot path's `OpenBackend` needs; and, in `bootstrap`'s contract (`bootOk`'s
  `Hpath`), the backend file's directory entry, which `NewServer` returns for that path.

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
(D21 M5, 2026-10-19) The server's membership in the network (`srvNetMember γn srv id τ`: what its
inbound path reads and its transport `τ`, frozen, every other member added as a peer), which
`RaftHandler` takes to give the member's raft handler, for serving it on the member's peer URL;
(2026-10-24, rafthttp stage 6d) one of the transport's reader tokens (`srvTrTok`, for
`CutPeer`/`MendPeer`) and `httpProcSlots` copies of what each request the handler serves borrows
(`srvServeRes`, for `http.Serve`). The raft loop's key to the transport's `Send` (`srvTrKey`,
`srvEr`'s `S`) is in the built part.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServe
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWatchBuilt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStorageVersion
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvMonitors
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn

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

/-- **`NewServer(cfg)`** (see the file header). -/
abbrev NewServer.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft)
    (id : w64) (ctxs : List (List w8)) (ρ : ReqNames) (E₀ : apply.AEnv GF) (N : Nat)
    (Φs : w64 → w64 → List w8 → GName → IProp GF)
    -- (D21 M2, 2026-10-19) the raft network and its URL directory
    (γn : NetNames GF) (dir : w64 → List GoString)
    -- (2026-10-26, D22 J2, R-loc) the member's snapshot directory's names (`SrvRaft.snapLoc`;
    -- raft's `RaftNames.reSnapLoc` until 2026-10-27)
    (γd : GName),
  -- the read names: at the cluster's raft names, the start log empty, the start index `0`; the
  -- cluster static, as raft's static mode until 2026-10-27 (the conf-change policy then, now the
  -- KV invariant's `ccLogOk`); the KV's start values, its certificate map the store's
  ρ.rd.raft = ⟨γ, [], W64 0⟩ → γ.dyn = false →
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
  -- (2026-10-19, D21 M3, D21 M0's run bound) at most `SnapshotCatchUpEntries + 1` (`5000`, etcd's
  -- default, for `0`; `start`'s), so the apply thread, one write token per entry, compacts raft's
  -- log at index `1` only (`compactRaftLog`), which raft's no-snapshot mode needs
  receiptBound GF ≤ uint.Z (if cfg.SnapshotCatchUpEntries' = W64 0 then W64 5000
    else cfg.SnapshotCatchUpEntries') + 1 →
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
  -- (2026-10-27) the `MemoryStorage` registry the cluster's storage model's (`srvStor γ`)
  letI : MemStorReg GF := ⟨γ.reg⟩
  {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "#Hfg" ∷ isFeatureGate cfg.ServerFeatureGate' ∗
      -- `bootstrap`'s contract (D13b)
      "#Hboot" ∷ bootstrapContract cfg U γ id ctxs N dir ∗
      -- (D19r (B), (F)) what `bootstrap` takes: the configuration's URLs, read-only, and the
      -- storage registry's authority, empty (the caller allocates it)
      "#Hcfgro" ∷ bootCfgRO cfg U ∗ "Hrauth" ∷ memStorRegAuth (∅ : GMap Loc MemStorNamesRec) ∗
      -- the cluster's (the node API's allocation, 2026-10-27): this node's boot token, of the
      -- peers `γ.vs` with the contexts `ctxs`, and the server's raft invariant
      "Hnboot" ∷ (if γ.dyn then Draft.nodeDynamicBoot γ.cl srvClusterN γ.vs ctxs id
        else Draft.nodeBoot γ.cl srvClusterN γ.vs ctxs id) ∗
      "#Hsrl" ∷ srvRaftLogInv ρ.rd.raft ∗
      -- (D21e (A), stage M4) the cluster's resources, allocated once (`srvClusterBoot_alloc`):
      -- the claims (with the reserved id `0`, D19c), the proposals' mint, the read contexts;
      -- and the member's share: its prefix's entry and slots (`idShare`), `2 ^ 48` of raft's read
      -- credits (`srvMemberBoot_alloc`)
      "#Hidc" ∷ idClusterInv ρ.ids.issued ρ.ids.cnt Φs ∗ "#HNZ0" ∷ idNoZero ρ.ids ∗
      "#Hpmint" ∷ srvPropMint ρ.rd.raft ρ.ids ∗ "#Hrdctx" ∷ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
      "Hids" ∷ idShare ρ.ids ∗ "HrdCred" ∷ Draft.readCredits γ.cl (2 ^ 48) ∗
      -- (linkv-txn stage B1, 2026-10-20) the member's entry of the registries' map, for `start`
      "Hwtok" ∷ idWaitTok ρ.ids ∗
      -- the names chosen before the call (D13a), fresh
      "Hidx" ∷ mvcc.idxFresh E₀.γ.idx ∗
      "Hcok" ∷ ghostMapAuth E₀.γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      "Hrev" ∷ ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
      "Hrd" ∷ srvReadNamesFreshNK ρ.rd ∗
      -- the KV invariant at the bootstrap log (D19g (a): allocated with raft's ghost state,
      -- whose standing update `noopAu` it gives, `srvRaftBoot_alloc`)
      "#Hkvinv" ∷ kvInv ρ.rd.raft ρ.rd.kv ∗
      -- (D21 M2, 2026-10-19) the raft network, whose payload is the server's (`srvNet`) and
      -- directory `bootstrap`'s (until then the named premise `transportEffectsOk`); (2026-10-24,
      -- rafthttp stage 6d) its HTTP side ready (until then the member's slot, `netSlot γn id`)
      "#Hnet" ∷ netHttpOk γn id ∗ "%Hγn" ∷ ⌜γn.N = srvNet γ ∧ γn.dir = dir⌝ ∗
      -- (2026-10-26, D22 J2, R-loc) the member's snapshot directory, empty, at the names the
      -- cluster gives the member (raft's `RaftNames.reSnapLoc` until 2026-10-27; until then `NewServer` allocated it,
      -- `snapDir_alloc`; 2026-10-27: at the server's `SrvRaft.snapLoc`)
      "%Hsloc" ∷ ⌜γ.snapLoc id = some γd⌝ ∗ "Hsdir" ∷ ghostMapAuth γd 1 (∅ : GMap w64 Unit) ∗
      -- the named premises of the constructors' axioms (D14e, unit N4): the lessor's
      -- checkpointer's effects and the auth store's record bound
      "%Hckok" ∷ ⌜ckptEffectsOk⌝ ∗ "%Haufit" ∷ ⌜authRecordsFit⌝ ∗
      "%Hbuq" ∷ ⌜apply.backendUnderQuota⌝ ∗
      -- (D22 S-j2, 2026-10-20; an environment assumption the user approved) bbolt's `Open`
      -- succeeds on the database files the server opens after its start (`storage.OpenBackend`'s
      -- axiom: its goroutine panics otherwise), for `applySnapshot`'s snapshot backend; kept by
      -- the server's snapshot path once S-j wires it in (today nothing opens one)
      "%Hdbo" ∷ ⌜storage.dbOpensOk⌝ ∗
      -- `NodeStartSpec`'s trust-boundary premises
      "#Hzap" ∷ rnLoggerZapOk ∗ "#Hsetlg" ∷ rnSetLoggerOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
      "#Htkok" ∷ rnTickerOk (srvEr ρ E₀ (W64 0) (W64 0) bootKV id iprop(True)) ∗
      "#Hns" ∷ rnNewStorageOk ∗
      "#Hstop" ∷ rnStopOkStarted ∗
      -- the packages' init facts `start` needs
      "#Hcci" ∷ context.isClosedchanInit }}
    (App (Val (@! NewServer)) (Val #cfg))
  {{ (srv : Loc) (err : GoInterface), RET (PairV #srv #err);
      ⌜srv = null ∧ err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗
        ∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
          (γrn : RNNames) (b : GoInterface) (γk : GName) (τ : SrvTr GF),
          ⌜envAgree E E₀ ∧ E.authOn = false⌝ ∗ srvWatchBuilt srv E ∗
          -- (D22 S-g, D22d (A)) the KV's closer, kept for the snapshot path's `Restore`
          srvKVCloser srv E ∗
          -- (D22 S-j2, 2026-10-20) the backend file's directory entry (`bootOk`'s), kept for
          -- `applySnapshot`'s `OpenSnapshotBackend`
          backend.pathOwn (config.backendPathOf cfg.DataDir') ∗
          srvBuilt srv γA ci TM E ρ ρ.rd (srvEr ρ E₀ (W64 0) (W64 0) bootKV id (srvTrKey γn γk))
            γrn b (W64 0)
            (W64 0) bootKV N ∗
          -- (D17d, 2026-10-18) `run`'s snapshot contract, from the storage's snapshot token
          srvBuildGap srv γrn (W64 0) (W64 0) ∗
          -- (D19g (b), 2026-10-18) what serving needs: `v3rpc.Server`'s configuration fields and
          -- watchable store, the progress interval's field, and the request slots
          srvServeBuilt srv E cfg 64 ∗
          -- (D19i part 2) the storage version monitor's backend access
          srvSVRes srv E ∗
          -- (audit B4a, D19m) the hash and downgrade monitors' configuration fields and
          -- `monitorDowngrade`'s `lgMu` reader slot
          srvMonitorCfg srv cfg ∗
          -- (2026-10-23) the right to close `readych`, for `publishV3`
          srvReadyCloser srv ∗
          -- (D21 M5, 2026-10-19) the server is member `id` of the network `γn`, its transport
          -- started there: what `RaftHandler` takes, to serve the member's raft handler;
          -- (2026-10-24, rafthttp stage 6d) a reader's token of the transport (`CutPeer`,
          -- `MendPeer`) and what each request the handler serves borrows (`http.Serve`)
          srvNetMember γn srv id τ ∗ srvTrTok γn τ ∗
          ([∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ) ∗
          -- (2026-10-20, watchkv) 64 reader slots of the watchable store, for the watch
          -- service's run slots (`v3rpc.watchRunSlot`)
          srvWatchReaders srv E 64 }}

/-- **`NewServer(cfg)` with auth on or off** (the auth plan's E2i, 2026-10-26; see the file header):
as `NewServer.spec` (its mode off, `NewServer.spec_of_specM`), the start's chain with the auth
layer enabled when `on` (`(bootKVOf on)Of`), with auth on the configuration's token provider the simple
one with a positive TTL, and the apply environment's auth `on`. With auth on, the server's proof
(`NewServer.wp_proofM`) takes the auth store's construction as the contract `authSrvTP true`
(`AuthSrv.lean`: D22's named premise `authSchemaSrv`). (The auth plan's E2w, 2026-10-26) The KV
invariant is the mode's (`kvInvM on`: `kvInvOn` from the store's start state `srvAuthSt0` at
`on = true`), as are the raft environment (`srvErM on`: the committed logs' shapes the mode's) and
the built part (`srvBuiltG on`), `ServerOn.lean`; at `on = false` each is today's by definition.
Until E2w the spec took `kvInv`, whose start chain has auth off, so at `on = true` its precondition
was unsatisfiable (`KVChainOff.lean`). -/
abbrev NewServer.specM (on : Bool) : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft)
    (id : w64) (ctxs : List (List w8)) (ρ : ReqNames) (E₀ : apply.AEnv GF) (N : Nat)
    (Φs : w64 → w64 → List w8 → GName → IProp GF)
    -- (D21 M2, 2026-10-19) the raft network and its URL directory
    (γn : NetNames GF) (dir : w64 → List GoString)
    -- (2026-10-26, D22 J2, R-loc) the member's snapshot directory's names (`SrvRaft.snapLoc`;
    -- raft's `RaftNames.reSnapLoc` until 2026-10-27)
    (γd : GName),
  -- the read names: at the cluster's raft names, the start log empty, the start index `0`; the
  -- cluster static, as raft's static mode until 2026-10-27 (the conf-change policy then, now the
  -- KV invariant's `ccLogOk`); the KV's start values, its certificate map the store's
  ρ.rd.raft = ⟨γ, [], W64 0⟩ → γ.dyn = false →
  ρ.rd.kv.c0 = W64 0 → ρ.rd.kv.ch0 = apply.alarmChain on false false →
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
  -- (2026-10-19, D21 M3, D21 M0's run bound) at most `SnapshotCatchUpEntries + 1` (`5000`, etcd's
  -- default, for `0`; `start`'s), so the apply thread, one write token per entry, compacts raft's
  -- log at index `1` only (`compactRaftLog`), which raft's no-snapshot mode needs
  receiptBound GF ≤ uint.Z (if cfg.SnapshotCatchUpEntries' = W64 0 then W64 5000
    else cfg.SnapshotCatchUpEntries') + 1 →
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
  -- (the auth plan's E2i) with auth on, the simple token provider with a positive TTL that fits
  -- `time.Duration(cfg.TokenTTL) * time.Second`
  (on = true → cfg.AuthToken' = go!"simple" ∧ 0 < uint.Z cfg.TokenTTL' ∧
    uint.Z cfg.TokenTTL' < 2 ^ 32) →
  -- (2026-10-27) the `MemoryStorage` registry the cluster's storage model's (`srvStor γ`)
  letI : MemStorReg GF := ⟨γ.reg⟩
  {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "#Hfg" ∷ isFeatureGate cfg.ServerFeatureGate' ∗
      -- `bootstrap`'s contract (D13b)
      "#Hboot" ∷ bootstrapContract cfg U γ id ctxs N dir ∗
      -- (D19r (B), (F)) what `bootstrap` takes: the configuration's URLs, read-only, and the
      -- storage registry's authority, empty (the caller allocates it)
      "#Hcfgro" ∷ bootCfgRO cfg U ∗ "Hrauth" ∷ memStorRegAuth (∅ : GMap Loc MemStorNamesRec) ∗
      -- the cluster's (the node API's allocation, 2026-10-27): this node's boot token, of the
      -- peers `γ.vs` with the contexts `ctxs`, and the server's raft invariant
      "Hnboot" ∷ (if γ.dyn then Draft.nodeDynamicBoot γ.cl srvClusterN γ.vs ctxs id
        else Draft.nodeBoot γ.cl srvClusterN γ.vs ctxs id) ∗
      "#Hsrl" ∷ srvRaftLogInv ρ.rd.raft ∗
      -- (D21e (A), stage M4) the cluster's resources, allocated once (`srvClusterBoot_alloc`):
      -- the claims (with the reserved id `0`, D19c), the proposals' mint, the read contexts;
      -- and the member's share: its prefix's entry and slots (`idShare`), `2 ^ 48` of raft's read
      -- credits (`srvMemberBoot_alloc`)
      "#Hidc" ∷ idClusterInv ρ.ids.issued ρ.ids.cnt Φs ∗ "#HNZ0" ∷ idNoZero ρ.ids ∗
      "#Hpmint" ∷ srvPropMint ρ.rd.raft ρ.ids ∗ "#Hrdctx" ∷ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
      "Hids" ∷ idShare ρ.ids ∗ "HrdCred" ∷ Draft.readCredits γ.cl (2 ^ 48) ∗
      -- (linkv-txn stage B1, 2026-10-20) the member's entry of the registries' map, for `start`
      "Hwtok" ∷ idWaitTok ρ.ids ∗
      -- the names chosen before the call (D13a), fresh
      "Hidx" ∷ mvcc.idxFresh E₀.γ.idx ∗
      "Hcok" ∷ ghostMapAuth E₀.γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      "Hrev" ∷ ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
      "Hrd" ∷ srvReadNamesFreshNK ρ.rd ∗
      -- the KV invariant at the bootstrap log (D19g (a): allocated with raft's ghost state,
      -- whose standing update `noopAu` it gives, `srvRaftBoot_alloc`)
      "#Hkvinv" ∷ kvInvM on ρ.rd.raft ρ.rd.kv srvAuthSt0 ∗
      -- (D21 M2, 2026-10-19) the raft network, whose payload is the server's (`srvNet`) and
      -- directory `bootstrap`'s (until then the named premise `transportEffectsOk`); (2026-10-24,
      -- rafthttp stage 6d) its HTTP side ready (until then the member's slot, `netSlot γn id`)
      "#Hnet" ∷ netHttpOk γn id ∗ "%Hγn" ∷ ⌜γn.N = srvNet γ ∧ γn.dir = dir⌝ ∗
      -- (2026-10-26, D22 J2, R-loc) the member's snapshot directory, empty, at the names the
      -- cluster gives the member (raft's `RaftNames.reSnapLoc` until 2026-10-27; until then `NewServer` allocated it,
      -- `snapDir_alloc`; 2026-10-27: at the server's `SrvRaft.snapLoc`)
      "%Hsloc" ∷ ⌜γ.snapLoc id = some γd⌝ ∗ "Hsdir" ∷ ghostMapAuth γd 1 (∅ : GMap w64 Unit) ∗
      -- the named premises of the constructors' axioms (D14e, unit N4): the lessor's
      -- checkpointer's effects and the auth store's record bound
      "%Hckok" ∷ ⌜ckptEffectsOk⌝ ∗ "%Haufit" ∷ ⌜authRecordsFit⌝ ∗
      "%Hbuq" ∷ ⌜apply.backendUnderQuota⌝ ∗
      -- (D22 S-j2, 2026-10-20; an environment assumption the user approved) bbolt's `Open`
      -- succeeds on the database files the server opens after its start (`storage.OpenBackend`'s
      -- axiom: its goroutine panics otherwise), for `applySnapshot`'s snapshot backend; kept by
      -- the server's snapshot path once S-j wires it in (today nothing opens one)
      "%Hdbo" ∷ ⌜storage.dbOpensOk⌝ ∗
      -- `NodeStartSpec`'s trust-boundary premises
      "#Hzap" ∷ rnLoggerZapOk ∗ "#Hsetlg" ∷ rnSetLoggerOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
      "#Htkok" ∷ rnTickerOk (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) id iprop(True)) ∗
      "#Hns" ∷ rnNewStorageOk ∗
      "#Hstop" ∷ rnStopOkStarted ∗
      -- the packages' init facts `start` needs
      "#Hcci" ∷ context.isClosedchanInit }}
    (App (Val (@! NewServer)) (Val #cfg))
  {{ (srv : Loc) (err : GoInterface), RET (PairV #srv #err);
      ⌜srv = null ∧ err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗
        ∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
          (γrn : RNNames) (b : GoInterface) (γk : GName) (τ : SrvTr GF),
          ⌜envAgree E E₀ ∧ E.authOn = on⌝ ∗ srvWatchBuilt srv E ∗
          -- (D22 S-g, D22d (A)) the KV's closer, kept for the snapshot path's `Restore`
          srvKVCloser srv E ∗
          -- (D22 S-j2, 2026-10-20) the backend file's directory entry (`bootOk`'s), kept for
          -- `applySnapshot`'s `OpenSnapshotBackend`
          backend.pathOwn (config.backendPathOf cfg.DataDir') ∗
          srvBuiltG on srv γA ci TM E ρ ρ.rd (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) id (srvTrKey γn γk))
            γrn b (W64 0)
            (W64 0) (bootKVOf on) N ∗
          -- (D17d, 2026-10-18) `run`'s snapshot contract, from the storage's snapshot token
          srvBuildGap srv γrn (W64 0) (W64 0) ∗
          -- (D19g (b), 2026-10-18) what serving needs: `v3rpc.Server`'s configuration fields and
          -- watchable store, the progress interval's field, and the request slots
          srvServeBuilt srv E cfg 64 ∗
          -- (D19i part 2) the storage version monitor's backend access
          srvSVRes srv E ∗
          -- (audit B4a, D19m) the hash and downgrade monitors' configuration fields and
          -- `monitorDowngrade`'s `lgMu` reader slot
          srvMonitorCfg srv cfg ∗
          -- (2026-10-23) the right to close `readych`, for `publishV3`
          srvReadyCloser srv ∗
          -- (D21 M5, 2026-10-19) the server is member `id` of the network `γn`, its transport
          -- started there: what `RaftHandler` takes, to serve the member's raft handler;
          -- (2026-10-24, rafthttp stage 6d) a reader's token of the transport (`CutPeer`,
          -- `MendPeer`) and what each request the handler serves borrows (`http.Serve`)
          srvNetMember γn srv id τ ∗ srvTrTok γn τ ∗
          ([∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ) ∗
          -- (2026-10-20, watchkv) 64 reader slots of the watchable store, for the watch
          -- service's run slots (`v3rpc.watchRunSlot`)
          srvWatchReaders srv E 64 }}

end spec

end EtcdGrove
end Perennial
