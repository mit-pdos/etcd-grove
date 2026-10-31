/-
**M2, the apply side: the drafted trusted statements** (`notes/m2-apply-plan.md`). Imported by
nothing; no `axiom`, no `sorry`; nothing switched. Generated from today's texts
(`NewServer.lean`, `EtcdServer__Compact.lean`), each change marked `(M2, the apply side, Draft)`:

The switch is stated in place (the user's Q6 (a), 2026-10-30): these texts name the definitions
the switch keeps (`isServerReq`, `isServerRead`, `srvBuilt`, ...) and are read under the redefined
ones (item 1's `dispatchOk`, item 5's `kvInv γ γk := kvInvD γ γk γk.cmp`, item 19's ties
`srvReqFieldsAtD`/`srvKVInvsD`), as at the switch.

- `NewServer.specD` (deferred by Q4): `NewServer.spec` merged with `NewServer.specCompact` (one statement, the mode
  the configuration's: `E₀.cmp = decide (retention ≠ 0)`), the KV invariant in the cluster's mode
  (`kvInvD`), the KV's closer by the mode (`srvKVCloserM … (-1)`, the storage side's draft, with
  the inner store's right: `start` splits it, `srvKVCloserM_split`).
- `EtcdServer.Compact.specD`: over the general `isServerReq` and `isServerRead` (the compaction
  family's `isServerReqC` gone) in compaction mode; their KV invariants are the mode's through
  item 19's ties.
- **The closer without the right** (`srvKVCloserW`, review round 1's F-6): what `start` keeps for
  the snapshot path once the right has gone to the apply thread (A2), the one the snapshot track's
  `restorePre_of_applyM` takes; `srvKVCloserM_split` (proved): the closer by the mode at `c` is
  `srvKVCloserW` and `apply.cmpRight E c`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Compact
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.M2ApplyDraft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.M2StorageDraftRestore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section closer
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The KV's closer without the compaction right** (review round 1's F-6; A2: the right lives
with the apply thread, `apply.cmpOwn`): off, today's `srvKVCloser`; on, the watchable store's own
parts of `mvcc.wsCloserR` (its stop channel's close and its waiter), without the inner store's
right. What `start` keeps after splitting `NewServer`'s `srvKVCloserM srv E (-1)`, and what the
snapshot track's `restorePre_of_applyM` takes beside `apply.cmpOwn` (the collaborator's draft,
item 17). -/
def srvKVCloserW (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  if mvcc.kbCmpM E.γ.kb then
    iprop(∃ wsl : Loc,
      srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
      ∃ stc : Loc, wsl.[go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore, go!"stopc"] ↦□ stc ∗
        mvcc.stopCloser stc ∗ mvcc.wsWaiter wsl)
  else srvKVCloser s E

/-- **`start`'s split** (G5, review round 1's F-6): the closer by the mode at `c` (at least `-1`)
is the closer without the right and the apply thread's compaction right at `c`; and back (for the
server's `Stop` path, or a restore that hands the right back). -/
theorem srvKVCloserM_split (s : Loc) (E : apply.AEnv GF) (c : Int) :
    srvKVCloserM (GF := GF) s E c ∗ ⌜-1 ≤ c⌝ ⊣⊢ srvKVCloserW s E ∗ apply.cmpRight E c := by
  unfold srvKVCloserM srvKVCloserW apply.cmpRight
  by_cases h : mvcc.kbCmpM E.γ.kb
  · simp only [h, ↓reduceIte]
    constructor
    · iintro ⟨⟨%wsl, #Hkv, Hcl⟩, %hc⟩
      icases (mvcc.wsCloserR_iff wsl E.s E.γ c).1 $$ Hcl with ⟨%stc, #Hstc, Hsc, Hw, Hr⟩
      iframe Hr
      isplitl [Hsc Hw]
      · iexists wsl
        iframe Hkv
        iexists stc
        iframe Hstc Hsc Hw
      · ipureintro; exact hc
    · iintro ⟨⟨%wsl, #Hkv, %stc, #Hstc, Hsc, Hw⟩, Hr, %hc⟩
      isplitl [Hsc Hw Hr]
      · iexists wsl
        iframe Hkv
        iapply (mvcc.wsCloserR_iff wsl E.s E.γ c).2
        iexists stc
        iframe Hstc Hsc Hw Hr
      · ipureintro; exact hc
  · simp only [h, ↓reduceIte]
    constructor
    · iintro ⟨⟨Hcl, %hc⟩, -⟩
      iframe Hcl
      ipureintro; exact hc
    · iintro ⟨Hcl, %hc⟩
      iframe Hcl
      isplitr
      · ipureintro; exact hc
      · ipureintro; omega

end closer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Draft of `NewServer.spec`, merged with `specCompact`** (see the file header). -/
abbrev NewServer.specD : Prop :=
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
  -- (2026-10-30, the repair: raft's one mode; until then the cluster static, `γ.dyn = false`)
  ρ.rd.raft = ⟨γ, [], W64 0⟩ →
  -- (2026-10-30, the repair, P9) the cluster's conf entries decided by the server's rule
  -- (`srvClusterBoot_alloc`'s; what `rnEnvOk` asks of the raft node's environment)
  γ.rule = srvRule (W64 0) γ.boot →
  ρ.rd.kv.c0 = W64 0 → ρ.rd.kv.ch0 = apply.alarmChain false false false →
  ρ.rd.kv.log0 = [[], []] → ρ.rd.kv.cok = E₀.γ.cok →
  -- the configuration (`mvcc.New`'s premise on the batch limit: unit N1, 2026-10-17;
  -- `issues/etcd-compaction-negative-batch-limit.md`)
  cfg.Logger' ≠ null → mvcc.batchLimitOk cfg.CompactionBatchLimit' →
  -- (M2, the apply side, Draft) the compactor off, or on in revision mode at a positive retention
  -- (M2's scope: no periodic mode, which needs the clock's trust boundary); the stand-in's mode
  -- the configuration's (`E₀.cmp`: the store built at `cm := retention ≠ 0`, `envAgree`'s
  -- `E.γ.cm = E.cmp` reads it off the post); the KV invariant's mode the member's (one for the
  -- cluster: the field `ρ.rd.kv.cmp`, in place since stage 4a)
  (cfg.AutoCompactionRetention' = 0 ∨
    (cfg.AutoCompactionMode' = go!"revision" ∧ 0 < sint.Z cfg.AutoCompactionRetention')) →
  E₀.cmp = decide (cfg.AutoCompactionRetention' ≠ 0) → ρ.rd.kv.cmp = E₀.cmp →
  -- the logic's thread bound (D17: the adequacy theorem's `T`, its caller's choice)
  threadBound GF ≤ 2 ^ 31 →
  -- the time-receipt bound (D19b: the adequacy theorem's step bound `N`, its caller's choice):
  -- the id generator issues fewer than `2 ^ 48` ids; the apply thread takes at most `N` of the
  -- `N + 7` write tokens `bootstrap` gives (`start`'s `srvWTPool`)
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
      "Hnboot" ∷ nodeBoot γ.cl srvClusterN γ.vs ctxs id ∗
      "#Hsrl" ∷ srvRaftLogInv ρ.rd.raft ∗
      -- (D21e (A), stage M4) the cluster's resources, allocated once (`srvClusterBoot_alloc`):
      -- the claims (with the reserved id `0`, D19c), the proposals' mint, the read contexts;
      -- and the member's share: its prefix's entry and slots (`idShare`), `2 ^ 48` of raft's read
      -- credits (`srvMemberBoot_alloc`)
      "#Hidc" ∷ idClusterInv ρ.ids.issued ρ.ids.cnt Φs ∗ "#HNZ0" ∷ idNoZero ρ.ids ∗
      "#Hpmint" ∷ srvPropMint ρ.rd.raft ρ.ids ∗ "#Hrdctx" ∷ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
      -- (2026-10-30, the repair: no read credits, raft's `ReadIndex` takes none)
      "Hids" ∷ idShare ρ.ids ∗
      -- (linkv-txn stage B1, 2026-10-20) the member's entry of the registries' map, for `start`
      "Hwtok" ∷ idWaitTok ρ.ids ∗
      -- the names chosen before the call (D13a), fresh
      "Hidx" ∷ mvcc.idxFresh E₀.γ.idx ∗
      "Hcok" ∷ ghostMapAuth E₀.γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      "Hrev" ∷ ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
      "Hrd" ∷ srvReadNamesFreshNK ρ.rd ∗
      -- the KV invariant at the bootstrap log (D19g (a): allocated with raft's ghost state,
      -- whose standing update `noopAu` it gives, `srvRaftBoot_alloc`)
      -- (M2, the apply side, Draft; review round 4's R4-1) in the member's mode: at the switch
      -- `kvInv ρ.rd.raft ρ.rd.kv` with the premise `ρ.rd.kv.cmp = E₀.cmp` (the post's ties,
      -- item 19, need it; the interim `NewServer.spec`/`specCompact`/`specM` take it too)
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
      -- (2026-10-29, the `axiom` skill's `notes/axiom-review/openbackend.md`; the user's decision)
      -- the configuration's quota is one bbolt can map (`storage.openMmapOk`: `OpenBackend`'s
      -- goroutine panics otherwise, `issues/etcd-quota-backend-bytes-mmap-panic.md`), for the same
      -- snapshot backend
      "%Hmmap" ∷ ⌜storage.openMmapOk cfg⌝ ∗
      -- `NodeStartSpec`'s trust-boundary premises
      "#Hzap" ∷ rnLoggerZapOk ∗ "#Hsetlg" ∷ rnSetLoggerOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
      "#Htkok" ∷ rnTickerOk (srvEr ρ E₀ (W64 0) (W64 0) bootKV id iprop(True)) ∗
      "#Hns" ∷ rnNewStorageOk ∗
      -- the packages' init facts `start` needs
      "#Hcci" ∷ context.isClosedchanInit }}
    (App (Val (@! NewServer)) (Val #cfg))
  {{ (srv : Loc) (err : GoInterface), RET (PairV #srv #err);
      ⌜srv = null ∧ err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗
        ∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
          (γrn : RNNames) (b : GoInterface) (γk : GName) (τ : SrvTr GF),
          ⌜envAgree E E₀ ∧ E.authOn = false⌝ ∗ srvWatchBuilt srv E ∗
          -- (D22 S-g, D22d (A)) the KV's closer, kept for the snapshot path's `Restore`; (M2, the
          -- apply side, Draft) by the mode, at the store's compaction revision `-1`
          -- (`srvKVCloserM`, the storage side's D22 draft: on, the watchable store's own parts and
          -- the inner store's restorable right, `srvKVCloserM_of_new` after the last error return;
          -- `start` splits off the right for the apply thread, `srvKVCloserM_split`: review round
          -- 1's F-6)
          srvKVCloserM srv E (-1) ∗
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

/-- **Draft of `EtcdServer.Compact.spec`** over the one family (see the file header). -/
abbrev EtcdServer.Compact.specD : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (r : Int),
  -- (M2, the storage side, 2026-10-30: M2's scope restriction, the user's Q7 (a), the approval's
  -- item 35) a revision past `0`
  1 ≤ r →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      -- (M2, the apply side, Draft: one family) the general request path's server (its KV
      -- invariant the server's mode's: item 19's tie in `srvReqFieldsAt`, review rounds 1-3's
      -- F-3/N-2/R3-2), in compaction mode: M2's scope (review round 2's S-6). Go serves a client's `Compact` RPC with the
      -- auto-compactor off too; such a server's invariant admits no compaction entry, so a client
      -- compaction at an off server stays outside the model (the compactor pilot's scope: other
      -- compactions are not in the workload) until a later stage puts every server in compaction
      -- mode
      isServerReq s E ρ ∗ ⌜E.cmp = true⌝ ∗ -- (review round 5's F5-2) the readers' names the request path's (`ρ.rd`: the proposal's
      -- `cmpReach ρ.kv r` from the certificates `isServerRead` reaches; `start`'s `isServer`
      -- gives both at the same names)
      isServerRead s E ρ.rd ∗ srvLeadTimeReader s ∗ srvLgReader s ∗ E.RD ∗
      mvcc.storeReaderC E.s E.γ ∗ idCred ρ.ids 1 ∗
      context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx none ∗ srvRevLb E.γ r ∗
      compactReqIs p r }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Compact"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗
      srvLgReader s ∗ E.RD ∗ mvcc.storeReaderC E.s E.γ ∗ compactOutIs E resp err }}

end spec

end EtcdGrove
end Perennial
