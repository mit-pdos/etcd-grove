/-
**The examples' shared start (`examples/lib/etcdstart`): its vocabulary** (2026-10-22, D33). Lean-first (no
Rocq counterpart). What putget's, linkv's, linkvtxn's, watchkv's, cachekv's (one member) and
putget3's, linkv3's, linkv3p's (three members) `Main`s and `startMember`s said each in their own
`Defs.lean`/`Alloc.lean`, once, with what differed among them (the member's name, its addresses, the
cluster's map, token and members) as parameters; each example's named premises (`premises`) stay its
own, at its configuration, and give these (`bootPremise_of`-style conversions in its `Main`'s proof).

**The configuration** (`cfgOk`): the scalar fields `newServer` sets for member `name` of a new
cluster with token `token`: data directory `name.etcd`, raft's clock `100` ms and `10` ticks.

**`bootstrap`'s contract** (`bootPremise`): at every server raft names of the cluster `ps` (static,
the bootstrap log; 2026-10-27, the server port: until then raft's names, with raft's no-snapshot and
no-transfer modes and the conf-change policy `ccOk ps`), at the peers' contexts `ctxs`, for a
configuration with those fields and URLs `U` meeting `Uok` (one member's `urls1`, a three-member
cluster's `urls3`: the member's peer and client URLs, the initial cluster's map of the shape the
caller builds, the initial URLs by name), at the bound `N` and the directory `dir`.

**The premises the members share** (`commonPremises`): the raft wrapper's trust-boundary contracts,
`Stop` of a started node, and the deployment's `runsNoRequireLeader`.

**A member built and started** (`memberBuilt`: `newServer`'s success, what `Start` takes;
`memberUp`: `Start`'s, what serving it needs) and **what `NewServer` takes of the ghost state**
(`memberBoot`, at the stand-in apply environment `env₀`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Start
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvStreamInterceptor
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap
public import Proof.net.InvNet
public import Spec.google_golang_org.grpc.Server__Serve
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvAuthServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLease
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheck
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The bootstrap log's conf changes, for the cluster `ps`** (2026-10-27, the server port; until
then the conf-change policy `ccOk ps`, raft's `reCCOk`): each entry's bytes are a `ConfChange` of id
`0` that the server's `applyConfChange` takes (`ccBootOk`: an `AddNode` of a member of `ps`, its
context that member), what `srvClusterBoot_alloc` takes of the bootstrap log. -/
def bootCCOk (ps : List w64) (bootLog : List EntryM) : Prop :=
  ∀ e ∈ bootLog, ccIdOf e.Data' = W64 0 ∧ ccBootOk (GMap.listToSet ps) e.Data'

/-- A URL `http://<host>`. -/
def httpURL (host : GoString) : _root_.Perennial.net.url.URL :=
  { Scheme' := go!"http", Opaque' := [], User' := null, Host' := host, Path' := [], Fragment' := [],
    RawQuery' := [], RawPath' := [], RawFragment' := [], ForceQuery' := false, OmitHost' := false }

/-- **`[http://host]` is the member's directory URLs** (D22 J-T, W8: `NewServer`'s
`peerURLsDir` premise, from a well-formed directory holding `http://host` for the member). -/
theorem peerURLsDir_httpURL (dir : w64 → List GoString) (id : w64) (host : GoString)
    (hd : netDirOk dir) (hm : go!"http://" ++ host ∈ dir id) :
    peerURLsDir dir id [httpURL host] := by
  refine ⟨by simp, fun u hu => ?_⟩
  rw [List.mem_singleton.1 hu]
  have hpl := (hd.2.2 id _ hm).2
  rw [List.drop_left' (by rfl)] at hpl
  obtain ⟨hne, hb⟩ := types.plainHostPort_noEscape host hpl
  have he : stringToGoString "" = [] := by simp [stringToGoString]
  exact ⟨⟨rfl, he.symm, rfl, he.symm, he.symm, he.symm, he.symm, rfl, rfl, he.symm, hne, hb⟩, hm⟩

/-- **The URLs of a one-member cluster's member `name`** (`StartServer`'s): its peer URLs
`[http://peerAddr]`, its client URLs `[http://client]`, the initial cluster's map `{name ↦ _}` and
the member's initial URLs its peer URLs. -/
def urls1 (name peerAddr client : GoString) (U : BootURLs) : Prop :=
  U.peer = [httpURL peerAddr] ∧ U.client = [httpURL client] ∧
    (∃ sl : GoSlice, U.initMap = GMap.insert name sl ∅) ∧ U.initURLs name = [httpURL peerAddr]

/-- **The URLs of a three-member cluster's member** (`StartMember`'s, `NewMember`'s): its peer URLs
`[http://peerAddr]`, its client URLs `[http://client]`, the initial cluster's map (the members'
names `n₁ n₂ n₃` to their peer URL slices) and the initial URLs by name `iu`. -/
def urls3 (n₁ n₂ n₃ : GoString) (iu : GoString → List _root_.Perennial.net.url.URL)
    (peerAddr client : GoString) (U : BootURLs) : Prop :=
  U.peer = [httpURL peerAddr] ∧ U.client = [httpURL client] ∧
    (∃ sl₁ sl₂ sl₃ : GoSlice,
      U.initMap = GMap.insert n₃ sl₃ (GMap.insert n₂ sl₂ (GMap.insert n₁ sl₁ ∅))) ∧
    U.initURLs = iu

/-- **A map's keys all valid UTF-8** (2026-11-02, the backend-auth-split stage: `bootPremise`'s
condition on the initial cluster's map, Q8), for the empty map. -/
theorem utf8Keys_empty : ∀ k, ((∅ : GMap GoString GoSlice).lookup k).isSome → utf8Valid k := by
  intro k h; simp at h

/-- **A map's keys all valid UTF-8**, kept by inserting a valid key (2026-11-02, the
backend-auth-split stage). -/
theorem utf8Keys_insert (M : GMap GoString GoSlice) (n : GoString) (sl : GoSlice)
    (hn : utf8Valid n) (hM : ∀ k, (M.lookup k).isSome → utf8Valid k) :
    ∀ k, ((GMap.insert n sl M).lookup k).isSome → utf8Valid k := by
  intro k h
  rcases (GMap.lookup_insert_is_Some M n k sl).1 h with rfl | ⟨-, h'⟩
  · exact hn
  · exact hM k h'

/-- **`bootstrap`'s configuration conditions at either start** (`bootCfgOk`; 2026-11-03, the
whole-`bootOk` review, C) from the fields a configuration literal sets: a logger, the default quota,
batch limit and bootstrap defragmentation (zero), raft's `10` ticks (2026-11-03, the boot premises:
the clock no longer `bootCfgOk`'s; `raftNode.bootCfg_of` takes it). -/
theorem bootCfgOk_of (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (hlg : cfg.Logger' ≠ null) (hq : cfg.QuotaBackendBytes' = W64 0)
    (hbl : cfg.BackendBatchLimit' = W64 0)
    (hdf : cfg.BootstrapDefragThresholdMegabytes' = W64 0)
    (het : cfg.ElectionTicks' = W64 10) : bootCfgOk cfg := by
  have hl : storage.openLimit cfg = W64 10000 := by unfold storage.openLimit; rw [if_pos hbl]
  refine ⟨hlg, storage.openMmapOk_of_quota_zero cfg hq, ?_, ?_, hdf, ?_⟩
  · rw [hl]; decide
  · rw [hl]; decide
  · rw [het]; decide

/-- The zero discovery configuration has no endpoints (`ShouldDiscover` is false). -/
theorem discoveryZero_len :
    (zero_val go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery.DiscoveryConfig).ConfigSpec'.Endpoints'.len =
      W64 0 := rfl

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `newServer` passes to `NewServer`**, by its scalar fields (its pointers --
the logger, the feature gate, the URLs, read through `bootCfgRO` -- are the caller's allocations):
member `name` of a new cluster with token `token`, data directory `name.etcd`, raft's clock `100`
ms and `10` ticks. -/
def cfgOk (token name : GoString) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = name ∧ cfg.DataDir' = name ++ go!".etcd" ∧
    cfg.InitialClusterToken' = token ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`bootstrap`'s contract for member `name`** (id `id`) of the cluster `ps` with token `token`,
at every server raft names of the cluster (its peers `ps`, static, its bootstrap log `bootLog`; at
the storage registry they name), for its configuration and URLs meeting `Uok`, at the peers'
contexts `ctxs`, the bound `N` and the directory `dir` (see the file header). (2026-11-03, the
whole-`bootOk` review, C: the initial cluster's member names valid UTF-8, a conjunct here since
2026-11-02, Q8, moved into the contract's precondition, `bootCfgFresh`, with the other
configuration conditions `bootstrap` needs.) -/
def bootPremise (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64) :
    IProp GF :=
  iprop(□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
      ⌜cfgOk token name cfg ∧ Uok U ∧
        γ.vs = ps ∧ γ.rule = srvRule (W64 0) bootLog ∧ γ.boot = bootLog⌝ -∗
      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N dir)

instance bootPremise_persistent (N : Nat) (ps : List w64) (bootLog : List EntryM)
    (ctxs : List (List w8)) (dir : w64 → List GoString) (token name : GoString)
    (Uok : BootURLs → Prop) (id : w64) :
    Persistent (bootPremise (GF := GF) N ps bootLog ctxs dir token name Uok id) := by
  unfold bootPremise; infer_instance

/-- **`bootPremise` from an example's own form of it** (its `premises`' clause, at its configuration
predicate `cfgOk'` and URLs predicate `Uok'`): this one asks less, when the shared start's
configuration meets the example's (`Hc`) and its URLs too (`Hu`). -/
theorem bootPremise_of (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64)
    (cfgOk' : go_etcd_io.etcd.server.v3.config.ServerConfig → Prop) (Uok' : BootURLs → Prop)
    (Hc : ∀ cfg, cfgOk token name cfg → cfgOk' cfg) (Hu : ∀ U, Uok U → Uok' U) :
    (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
      ⌜cfgOk' cfg ∧ Uok' U ∧ γ.vs = ps ∧ γ.rule = srvRule (W64 0) bootLog ∧ γ.boot = bootLog⌝ -∗
      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N dir) ⊢
      bootPremise (GF := GF) N ps bootLog ctxs dir token name Uok id := by
  iintro #H
  iunfold bootPremise
  imodintro
  iintro %cfg %U %γ %Hp
  obtain ⟨hc, hu, h1, h2, h3⟩ := Hp
  iapply H
  ipureintro
  exact ⟨Hc cfg hc, Hu U hu, h1, h2, h3⟩

/-- **The premises shared by the members** (see the file header). -/
def commonPremises : IProp GF :=
  iprop(rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    v3rpc.runsNoRequireLeader)

instance commonPremises_persistent : Persistent (commonPremises (GF := GF)) := by
  unfold commonPremises; infer_instance

/-- **The stand-in apply environment** (`NewServer.spec`'s `E₀`): the store's index names, its
certificate map and the revisions' map, and (M2, the storage side, review round 2's N1) the member's
compaction mode (`cmp`, `false` by default); `envAgree` reads nothing else. -/
def env₀ (idx : mvcc.IdxNames) (cok rev : GName) (cmp : Bool := false) : apply.AEnv GF :=
  { s := null,
    γ := { idx := idx, bucket := 0, clog := 0, leases := 0, revs := 0, hook := 0, hookFn := 0,
           kb := none, cmeta := 0, fin := 0, sch := ⟨0, 0, 0⟩, cok := cok, watchQ := false },
    P := iprop(True), f := #(), RD := iprop(True), γrev := rev, authMode := .off,
    FS := iprop(True), ciC := fun _ _ => True, RO := fun _ => iprop(True), RW := iprop(True),
    γbe := 0, cmp := cmp }

theorem env₀_cmp (idx : mvcc.IdxNames) (cok rev : GName) (cmp : Bool) :
    (env₀ (GF := GF) idx cok rev cmp).cmp = cmp := rfl

/-- **What member `id`'s `NewServer` takes of the ghost state** (its pure facts, the cluster's
resources at its names, its share): `NewServer.spec`'s precondition but the network's and the
premises'; and (M2, the storage side, review round 2's N1, the approval's item 12) the member's
compaction mode `cmp` (default `false`), recorded as the stand-in's (`E₀.cmp = cmp`); (the
lease-expiry plan's X2, 2026-11-04, the user's (a)) the member's lease mode `m` (default `none`), the
mode of its lease subsystem's sealed premise (`lease.runCfg`), which each example picks. -/
def memberBoot (γ : SrvRaft) (ctxs : List (List w8))
    (ρ : ReqNames) (E₀ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64)
    (cmp : Bool := false) (m : lease.Mode := .none) : IProp GF :=
  iprop(⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧
      ρ.rd.kv.c0 = W64 0 ∧ ρ.rd.kv.ch0 = apply.alarmChain false false false ∧
      ρ.rd.kv.log0 = [[], []] ∧ ρ.rd.kv.cok = E₀.γ.cok ∧
      ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) ∧ Φs ρ.ids.pfx = srvFloorFact E₀ ∧ E₀.cmp = cmp ∧
      ρ.rd.kv.cmp = cmp ∧
      -- (2026-11-02, the lease-grant plan's D2) `NewServer`'s premise on a cluster that grants
      -- leases (the open cases, `srvGrantOpen`): `alloc1`'s names grant none; (2026-11-04, the
      -- lease-expiry plan's Part C) as the lease subsystem's sealed premise, (X2) at the mode `m`
      lease.runCfg (GF := GF) ρ.rd.kv.lm m⌝ ∗
    -- (2026-10-27, the server port) the node API's boot token of the member and the server's raft
    -- invariant (until then raft's ghost state, its committed bootstrap log and the term budget)
    (nodeBoot γ.cl srvClusterN γ.vs ctxs id ∗ raftState γ.cl id RaftState.init ∗
      nodeVacant γ.cl id) ∗ srvRaftLogInv ρ.rd.raft ∗
    idClusterInv ρ.ids.issued ρ.ids.cnt ρ.ids.wn ρ.ids.fs srvFloorFacts ∗
    idKeyFactAt ρ.ids.fs ρ.ids.key E₀.γ.idx ∗ idNoZero ρ.ids ∗
    srvPropMint ρ.rd.raft ρ.ids ∗ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
    idShare ρ.ids ∗ idWaitTok ρ.ids ∗
    mvcc.idxFresh E₀.γ.idx ∗
    ghostMapAuth E₀.γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
    ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
    srvReadNamesFreshNK ρ.rd ∗ kvInv ρ.rd.raft ρ.rd.kv ∗
    -- (2026-10-27, the server port) the member's storage registry, empty, at the names' (`SrvRaft.reg`;
    -- until then `newServer` allocated it): a member's `bootstrap` joins its own
    ghostMapAuth γ.reg 1 (∅ : GMap Loc MemStorNamesRec) ∗
    -- (2026-10-26, D22 J2, R-loc) the member's snapshot directory, empty, at the names the
    -- cluster gives it (`SrvRaft.snapLoc`, `NewServer`'s)
    ∃ γd : GName, ⌜γ.snapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit))

/-- **The member's compaction mode, read off its boot bundle** (M2, the storage side, N1: what a
`Main` keeps before `newServer` takes the bundle; `newServer` gives it to `NewServer.spec`'s
premise). -/
theorem memberBoot_cmp (γ : SrvRaft) (ctxs : List (List w8)) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64) (cmp : Bool) (m : lease.Mode := .none) :
    memberBoot γ ctxs ρ E₀ Φs id cmp m ⊢ ⌜E₀.cmp = cmp⌝ ∗ memberBoot γ ctxs ρ E₀ Φs id cmp m := by
  iintro H
  iunfold memberBoot at H
  icases H with ⟨%Hρ, Hr⟩
  isplitr
  · ipureintro; exact Hρ.2.2.2.2.2.2.2.1
  iunfold memberBoot
  isplitr
  · ipureintro; exact Hρ
  iexact Hr

/-- **The lease subsystem's part of the built server, at the lease mode `m`** (persistent; the
closed lease example, 2026-11-02, `notes/lease-ex-plan.md`): (the lease-expiry plan's X2,
2026-11-04, the user's (a)) `NewServer`'s `lease.srvInv` at `m`, at some auth mode; until then its
reader side only (`srvLessorRd`, `lessorRdPool`), which the served lease reads take
(`raftLeaseRead_server`, `srvLeaseRd_lessorRd`), and which the monotone mode's grant takes whole
(`v3rpc.lessorGrantOkL_server`). -/
def srvLeaseRd (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) : IProp GF :=
  iprop(∃ on : Bool, lease.srvInv on s E m)

instance srvLeaseRd_persistent (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    Persistent (srvLeaseRd (GF := GF) s E m) := by
  unfold srvLeaseRd; infer_instance

/-- **The lessor's reader side, from `srvLeaseRd`** (what it was until X2). -/
theorem srvLeaseRd_lessorRd (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    srvLeaseRd (GF := GF) s E m ⊢ srvLessorRd s E.γ.leases ∗ lease.lessorRdPool E.γ.leases := by
  unfold srvLeaseRd
  iintro ⟨%on, #H⟩
  iapply lease.srvInv_lessorRd on s E m $$ H

/-- **A member built** (`newServer`'s success): the server `s` built by `NewServer` with the
request names `ρ` at an apply environment `E` agreeing with the stand-in `E₀`, auth off, from a
configuration `cfg` with the logger `lg`, no tracer options and no progress-notify interval:
`isServerBuilt` (from `NewServer`'s `srvBuilt` and `srvBuildGap`, at the bound `N`), what `Start` takes besides (the storage version monitor's backend access, the
monitors off, `lgMu`'s reader slot of the downgrade monitor), and what `NewServer` left for serving
(`srvServeBuilt`, the watchable store's readers) and for the member's place in the network `γn`
(`srvNetMember`, with its transport `τ`; 2026-10-24, rafthttp stage 6d: the raft loop's key to the
transport's `Send`, `srvTrKey`, under `γk`, one of the transport's reader tokens, `srvTrTok`, and
what `http.Serve`'s request goroutines borrow, `srvServeRes`, until the peer address is served:
`served`). (2026-11-02, the restart plan) The apply thread's starting state `ai₀ at₀ c₀ x₀`, a
first start's (`0` and the boot store) unless given: a restarted member's (`Restart.lean`). (The
lease-expiry plan's X2, 2026-11-04) The lease subsystem at the member's lease mode `m` (default
`none`; `memberBoot`'s). (2026-11-04, the restart plan's R2b-3d) And what `NewServer` kept for the
stop (its slot, `srvStop.keep`) at the raft wrapper's names, the configuration, the apply
environment and the transport key's name, which `Start` hands `run` (2026-11-05, R2c-3: until then a
parameter `K`, `True` unless given, and `memberBuiltS` the member with the slot). -/
def memberBuilt (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (N : Nat) (served : Bool) (ai₀ at₀ c₀ : w64 := W64 0)
    (x₀ : apply.ApplyKV := bootKV) (m : lease.Mode := .none) :
    IProp GF :=
  iprop(∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
      (γrn : RNNames) (b : GoInterface) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
      (γk : GName) (τ : SrvTr GF),
    ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0⌝ ∗
    srvWatchBuilt s E ∗
    isServerBuilt s γA ci TM E ρ ρ.rd (srvEr ρ E₀ ai₀ c₀ x₀ id (srvTrKey γn γk) (srvTrStopK γk))
      γrn b ai₀ at₀ c₀ x₀ N ∗
    srvServeBuilt s E cfg 64 ∗ srvSVRes s E ∗ srvMonitorsOff s ∗ srvLgReader s ∗
    srvReadyCloser s ∗ srvNetMember γn s id τ ∗ srvTrTok γn τ ∗
    (if served then True else [∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ) ∗
    srvWatchReaders s E 64 ∗ srvLeaseRd s E m ∗ srvStop.keep s cfg E γrn γk)

/-- **What the partitioner takes of a member** (2026-10-24, rafthttp stage 6d): its place in the
network (`srvNetMember`, with its transport `τ`) and one of its transport's reader tokens
(`srvTrTok`), which `CutPeer` and `MendPeer` borrow. -/
def srvPeerCtl (γn : NetNames GF) (s : Loc) (id : w64) : IProp GF :=
  iprop(∃ τ : SrvTr GF, srvNetMember γn s id τ ∗ srvTrTok γn τ)

/-- **A member started** (`Start`'s success from `memberBuilt`): the server `s` started with its
request names `ρ` (the wait registry's `γw`) at an apply environment `E` agreeing with the stand-in
`E₀`, auth off, built from a configuration `cfg` with the logger `lg`, no tracer options and no
progress-notify interval; what `Start` returns (the request and read views, the `GoAttach`
resources with the thread token, a `lgMu` reader slot, the read loop's readers) and what
`NewServer` left for serving (`srvServeBuilt`'s resources, two of its `lgMu` slots spent on
`Start`; the watchable store's readers), and its place in the network `γn`; (the lease-expiry
plan's X2, 2026-11-04) the lease subsystem at the member's lease mode `m` (default `none`);
(2026-11-05, the restart plan's R2c-4) and `Start`'s right to stop the server (`srvStopRight`, at
`E`, the member id `id` and the configuration's data directory), at the environment of the
serving stocks a stop request hands back. -/
def memberUp (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (m : lease.Mode := .none) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName),
    ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0⌝ ∗
    isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvGoRes s ∗ srvLgReader s ∗
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      srvReadReader s ρ.rd) ∗
    srvWatchBuilt s E ∗ srvServeFacts s E cfg ∗
    srvBemuReader s ∗
    ([∗list] _x ∈ List.replicate 64 (), srvLeadTimeReader s) ∗
    ([∗list] _x ∈ List.replicate (64 - 2) (), srvLgReader s) ∗
    ([∗list] _x ∈ List.replicate 64 (), E.RD) ∗
    ([∗list] _x ∈ List.replicate 64 (), mvcc.storeReader E.s E.γ) ∗
    ([∗list] _x ∈ List.replicate 64 (), srvBemuReader s) ∗
    srvPeerCtl γn s id ∗ srvWatchReaders s E 64 ∗ srvLeaseRd s E m ∗
    (∃ dd : GoString, srvStopRight s E ρ.rd.raft.raft ρ id dd))

/-- **A started member that will not serve, split for its stop** (R2c review F4, 2026-11-06): the
request view and the `GoAttach` resources (what `AppliedIndex()` and the goroutines need), and what a
stop request takes of it: the right to stop it (`srvStopRight`) at its apply environment `E`, which
has auth off and `E₀`'s compaction mode, with its unused serving stocks (`srvStopReaders`). The rest
of `memberUp` (its serving stocks' other parts) is dropped. -/
theorem memberUp_stop (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (m : lease.Mode) :
    memberUp (GF := GF) s ρ E₀ lg γn id m ⊢
      (∃ (E : apply.AEnv GF) (γw : GName), isServerReq s E { ρ with wait := γw } ∗ srvGoRes s) ∗
      ∃ (E : apply.AEnv GF) (dd : GoString), srvStopRight s E ρ.rd.raft.raft ρ id dd ∗
        ⌜E.authOn = false ∧ E.cmp = E₀.cmp⌝ ∗ srvStopReaders E := by
  iintro Hup
  iunfold memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, -, Hgo, -, -, -, -, -, -, -, -, Hsts, -, -, HWR, -,
    %dd, Hr⟩
  isplitl [Hgo]
  · iexists E, γw
    iframe Hreq Hgo
  iexists E, dd
  iframe Hr
  isplitr
  · ipureintro; exact ⟨HEc.2.1, HEc.1.2.2.2.1⟩
  iapply srvStopReaders_intro s E
  iframe Hsts HWR

/-- **The Lease service `v3rpc.Server` registered** (persistent; the closed lease example,
2026-11-02): its unary methods among the registrations `regs` (`leaseRegs`), on the
`*quotaLeaseServer` `ql` over the `*LeaseServer` `pl` of the server `s`, its header at the KV answers
`A` (`v3rpc.Server`'s post). -/
def grpcLeaseUp (s : Loc) (A : v3rpc.KVAns GF) (regs : List (GoString × val × GoInterface)) :
    IProp GF :=
  iprop(∃ (ql pl : Loc) (lcid lmid : w64), ⌜∀ x ∈ v3rpc.leaseRegs ql, x ∈ regs⌝ ∗
    v3rpc.quotaLeaseServerAt ql
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #pl⟩ s ∗
    v3rpc.leaseServerAt pl s A lcid lmid)

instance grpcLeaseUp_persistent (s : Loc) (A : v3rpc.KVAns GF)
    (regs : List (GoString × val × GoInterface)) : Persistent (grpcLeaseUp (GF := GF) s A regs) := by
  unfold grpcLeaseUp; infer_instance

/-- **What `v3rpc.Server` and `Listen` return** (the ghost step's input): the gRPC server `gs`
being built with etcd's interceptor chains and services (`v3rpc.Server.spec`'s postcondition, at
the configuration `C` `grpcCfgOk_of_started_w` gives: the KV answers of the server's views at
`E`, `ρ`, `γr`; the watch server's state `R` at `E`; 64 of the watchable store's readers), the
server's resources back, and the listener `lis` at `addr`. -/
def grpcUp (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (gs : Loc)
    (lis : GoInterface) (addr : GoString) (cid mid : w64) (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(∃ (C : v3rpc.GrpcCfg GF) (q p pw : Loc) (il im iu ims is : GoFunc) (svcs : List GoString)
      (regs sregs : List (GoString × val × GoInterface)),
    ⌜C.A = v3rpc.srvKVAns s E ρ γr (W64 0) [] .none ∧ C.E = E ∧
      (∀ x ∈ v3rpc.kvRegs q, x ∈ regs) ∧ v3rpc.watchSReg pw ∈ sregs ∧
      R.s = s ∧ R.E = E ∧ R.wsl = C.wsl ∧ R.γ = C.γ⌝ ∗
    v3rpc.grpcCfgOk s C ∗
    grpcSrvNew gs [il, im, iu] [ims, is] svcs regs sregs ∗
    v3rpc.quotaKVServerAt q
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
    v3rpc.kvServerIs p s C.A cid mid C.n ∗
    v3rpc.isWatchServer pw R ∗
    (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk il (srvLgReader s) Q) ∗
    (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk im iprop(True) Q) ∗
    srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
    srvStreamInterceptorOk ims iprop(True) ∗ srvStreamInterceptorOk is iprop(True) ∗
    srvLgReader s ∗ srvBemuReader s ∗ srvGoRes s ∗
    ([∗list] _x ∈ List.replicate 64 (), mvcc.watchReader C.wsl E.s C.γ) ∗
    netListenerAt lis addr ∗ grpcLeaseUp s C.A regs)

/-- **What member `id`'s `NewServer` takes of the ghost state, with auth on** (the auth plan's
E3zb, 2026-10-28; `memberBoot`'s, `NewServer.specM true`'s): the start chain with the auth layer
enabled and the KV invariant in the mode `on` from the auth store's start state (`kvInvM true`, at
`srvAuthSt0`). -/
def memberBootOn (γ : SrvRaft) (ctxs : List (List w8))
    (ρ : ReqNames) (E₀ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64)
    (cmp : Bool := false) : IProp GF :=
  iprop(⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧
      ρ.rd.kv.c0 = W64 0 ∧ ρ.rd.kv.ch0 = apply.alarmChain true false false ∧
      ρ.rd.kv.log0 = [[], []] ∧ ρ.rd.kv.cok = E₀.γ.cok ∧
      ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) ∧ Φs ρ.ids.pfx = srvFloorFact E₀ ∧ E₀.cmp = cmp ∧
      ρ.rd.kv.cmp = cmp ∧
      -- (2026-11-02, the lease-grant plan's D2) `NewServer`'s premise on a cluster that grants
      -- leases (the open cases, `srvGrantOpen`): `alloc1`'s names grant none; (2026-11-04, the
      -- lease-expiry plan's Part C) as the lease subsystem's sealed premise at some mode
      (∃ m : lease.Mode, lease.runCfg (GF := GF) ρ.rd.kv.lm m) ∧
      -- (the lease-grant stage, 2.13) `NewServer.specM true`'s: auth on grants none
      ρ.rd.kv.lg = false⌝ ∗
    (nodeBoot γ.cl srvClusterN γ.vs ctxs id ∗ raftState γ.cl id RaftState.init ∗
      nodeVacant γ.cl id) ∗ srvRaftLogInv ρ.rd.raft ∗
    idClusterInv ρ.ids.issued ρ.ids.cnt ρ.ids.wn ρ.ids.fs srvFloorFacts ∗
    idKeyFactAt ρ.ids.fs ρ.ids.key E₀.γ.idx ∗ idNoZero ρ.ids ∗
    srvPropMint ρ.rd.raft ρ.ids ∗ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
    idShare ρ.ids ∗ idWaitTok ρ.ids ∗
    mvcc.idxFresh E₀.γ.idx ∗
    ghostMapAuth E₀.γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
    ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
    srvReadNamesFreshNK ρ.rd ∗ kvInvM true ρ.rd.raft ρ.rd.kv srvAuthSt0 ∗
    ghostMapAuth γ.reg 1 (∅ : GMap Loc MemStorNamesRec) ∗
    ∃ γd : GName, ⌜γ.snapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit))

/-- **The member's compaction mode, read off its boot bundle with auth on** (`memberBoot_cmp`'s). -/
theorem memberBootOn_cmp (γ : SrvRaft) (ctxs : List (List w8)) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64) (cmp : Bool) :
    memberBootOn γ ctxs ρ E₀ Φs id cmp ⊢ ⌜E₀.cmp = cmp⌝ ∗ memberBootOn γ ctxs ρ E₀ Φs id cmp := by
  iintro H
  iunfold memberBootOn at H
  icases H with ⟨%Hρ, Hr⟩
  isplitr
  · ipureintro; exact Hρ.2.2.2.2.2.2.2.1
  iunfold memberBootOn
  isplitr
  · ipureintro; exact Hρ
  iexact Hr

/-- **A member started with auth on** (the auth plan's E3zb, 2026-10-28; `memberUp`'s, from
`NewServer.specM true` and `Start.spec` at `.on γa`): at an apply environment in the mode `.on γa`, the
request and read views in the mode (`isServerReqM true`, `isServerReadM true`) and the store's range
check at a reader's lower bound (`srvAuthLb`), what `Serve.spec` takes at `E.authOn`; otherwise as `memberUp`. -/
def memberUpOn (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName),
    ⌜envAgree E E₀ ∧ E.authMode = .on γa ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0⌝ ∗
    isServerReqM true s E { ρ with wait := γw } ∗ isServerReadM true s E ρ.rd ∗ srvAuthLb s E ∗
    srvGoRes s ∗ srvLgReader s ∗
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      srvReadReader s ρ.rd) ∗
    srvWatchBuilt s E ∗ srvServeFacts s E cfg ∗
    srvBemuReader s ∗
    ([∗list] _x ∈ List.replicate 64 (), srvLeadTimeReader s) ∗
    ([∗list] _x ∈ List.replicate (64 - 2) (), srvLgReader s) ∗
    ([∗list] _x ∈ List.replicate 64 (), E.RD) ∗
    ([∗list] _x ∈ List.replicate 64 (), mvcc.storeReader E.s E.γ) ∗
    ([∗list] _x ∈ List.replicate 64 (), srvBemuReader s) ∗
    srvPeerCtl γn s id ∗ srvWatchReaders s E 64 ∗
    -- (authkv's Main, 2026-10-30) the TLS fallback off (`ClientCertAuthEnabled` the
    -- configuration's `false`, `srvTLSId_false`) and the auth store's cost field (`BcryptCost()`'s)
    -- and (C1's A4, 2026-10-31) its `Authenticate` side (`srvAuthStoreOn`)
    □ (srvTLSId s -∗ False) ∗ srvAuthStoreOn s E.RD)

/-- **What `v3rpc.Server` and `Listen` return, with auth on** (the auth plan's E3zb; `grpcUp`'s): at
the KV answers with auth on (`srvKVAnsOn … 0 none`), and with the Auth service's registrations on
the `*AuthServer` `pa` over the server (`authRegs`, `authServerIs`). -/
def grpcUpOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (gs : Loc)
    (lis : GoInterface) (addr : GoString) (cid mid : w64) (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(∃ (C : v3rpc.GrpcCfg GF) (q p pw pa : Loc) (il im iu ims is : GoFunc)
      (svcs : List GoString) (regs sregs : List (GoString × val × GoInterface)),
    ⌜C.A = v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none ∧ C.E = E ∧
      (∀ x ∈ v3rpc.kvRegs q, x ∈ regs) ∧ (∀ x ∈ v3rpc.authRegs pa, x ∈ regs) ∧
      v3rpc.watchSReg pw ∈ sregs ∧ R.s = s ∧ R.E = E ∧ R.wsl = C.wsl ∧ R.γ = C.γ⌝ ∗
    v3rpc.grpcCfgOk s C ∗
    grpcSrvNew gs [il, im, iu] [ims, is] svcs regs sregs ∗
    v3rpc.quotaKVServerAt q
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
    v3rpc.kvServerIs p s C.A cid mid C.n ∗
    v3rpc.authServerIs pa s ∗
    v3rpc.isWatchServer pw R ∗
    (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk il (srvLgReader s) Q) ∗
    (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk im iprop(True) Q) ∗
    srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
    srvStreamInterceptorOk ims iprop(True) ∗ srvStreamInterceptorOk is iprop(True) ∗
    srvLgReader s ∗ srvBemuReader s ∗ srvGoRes s ∗
    ([∗list] _x ∈ List.replicate 64 (), mvcc.watchReader C.wsl E.s C.γ) ∗
    netListenerAt lis addr)


/-- **What `v3rpc.Server` and `Listen` return, in the auth mode `on`** (the auth component's stage 5;
`grpcUp`'s and `grpcUpOn`'s, what `Serve.spec` gives the caller's ghost step): at the KV answers in
the mode (`srvKVAnsM on … 0 none`), with the Auth service's registrations and the Lease service's
(`grpcLeaseUp`). `grpcUpM_false` and `grpcUpM_true` give `grpcUp` and `grpcUpOn`. -/
def grpcUpM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (gs : Loc)
    (lis : GoInterface) (addr : GoString) (cid mid : w64) (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(∃ (C : v3rpc.GrpcCfg GF) (q p pw pa : Loc) (il im iu ims is : GoFunc)
      (svcs : List GoString) (regs sregs : List (GoString × val × GoInterface)),
    ⌜C.A = v3rpc.srvKVAnsM on s E ρ γr (W64 0) [] .none 0 none ∧ C.E = E ∧
      (∀ x ∈ v3rpc.kvRegs q, x ∈ regs) ∧ (∀ x ∈ v3rpc.authRegs pa, x ∈ regs) ∧
      v3rpc.watchSReg pw ∈ sregs ∧ R.s = s ∧ R.E = E ∧ R.wsl = C.wsl ∧ R.γ = C.γ⌝ ∗
    v3rpc.grpcCfgOk s C ∗
    grpcSrvNew gs [il, im, iu] [ims, is] svcs regs sregs ∗
    v3rpc.quotaKVServerAt q
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
    v3rpc.kvServerIs p s C.A cid mid C.n ∗
    v3rpc.authServerIs pa s ∗
    v3rpc.isWatchServer pw R ∗
    (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk il (srvLgReader s) Q) ∗
    (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk im iprop(True) Q) ∗
    srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
    srvStreamInterceptorOk ims iprop(True) ∗ srvStreamInterceptorOk is iprop(True) ∗
    srvLgReader s ∗ srvBemuReader s ∗ srvGoRes s ∗
    ([∗list] _x ∈ List.replicate 64 (), mvcc.watchReader C.wsl E.s C.γ) ∗
    netListenerAt lis addr ∗ grpcLeaseUp s C.A regs)

open Iris.ProofMode in
/-- **`grpcUpM` with auth off is `grpcUp`** (a bridge): the configuration, the `*kvServer` and the
Lease service moved to the off answers (`grpcCfgOk_A`, `kvServerIs_mono`, `leaseServerAt_revR`,
through `raftKV_srvKVAnsM_false`); the Auth service dropped. -/
theorem grpcUpM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (gs : Loc)
    (lis : GoInterface) (addr : GoString) (cid mid : w64) (R : v3rpc.WSrv GF) :
    grpcUpM false s E ρ γr gs lis addr cid mid R ⊢ grpcUp s E ρ γr gs lis addr cid mid R := by
  iintro H
  iunfold grpcUpM at H
  icases H with ⟨%C, %q, %p, %pw, %pa, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC, #Hc,
    Hn, #Hq, #Hk, -, #Hw, #Hil, #Him, #Hiu, #Hims, #His, Hlg, Hbe, Hgo, Hrds, Hlis, #Hlu⟩
  obtain ⟨hA, hE, hkv, -, hw, h6, h7, h8, h9⟩ := HC
  have hk : v3rpc.raftKV s C.A ⊢ v3rpc.raftKV s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) := by
    rw [hA]; exact v3rpc.raftKV_srvKVAnsM_false s E ρ γr (W64 0) [] .none
  have hR : C.A.revR = (v3rpc.srvKVAns (GF := GF) s E ρ γr (W64 0) [] .none).revR := by
    rw [hA]; rfl
  iunfold grpcUp
  iexists { C with A := v3rpc.srvKVAns s E ρ γr (W64 0) [] .none }, q, p, pw, il, im, iu, ims, is,
    svcs, regs, sregs
  isplitr
  · ipureintro; exact ⟨rfl, hE, hkv, hw, h6, h7, h8, h9⟩
  isplitr
  · iapply v3rpc.grpcCfgOk_A s C _ hk $$ Hc
  ihave #Hk' := v3rpc.kvServerIs_mono p s C.A _ cid mid C.n hR hk $$ Hk
  iframe; iframe #
  have hl : ∀ pl lcid lmid, v3rpc.leaseServerAt (GF := GF) pl s C.A lcid lmid =
      v3rpc.leaseServerAt pl s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) lcid lmid :=
    fun pl lcid lmid => v3rpc.leaseServerAt_revR pl s _ _ lcid lmid hR
  unfold grpcLeaseUp
  simp only [hl]
  iexact Hlu

open Iris.ProofMode in
/-- **`grpcUpM` with auth on is `grpcUpOn`** (a bridge): the configuration and the `*kvServer`
moved to the on answers (through `raftKV_srvKVAnsM_true`); the Lease service dropped. -/
theorem grpcUpM_true (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (gs : Loc)
    (lis : GoInterface) (addr : GoString) (cid mid : w64) (R : v3rpc.WSrv GF) :
    grpcUpM true s E ρ γr gs lis addr cid mid R ⊢ grpcUpOn s E ρ γr gs lis addr cid mid R := by
  iintro H
  iunfold grpcUpM at H
  icases H with ⟨%C, %q, %p, %pw, %pa, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC, #Hc,
    Hn, #Hq, #Hk, #Has, #Hw, #Hil, #Him, #Hiu, #Hims, #His, Hlg, Hbe, Hgo, Hrds, Hlis, -⟩
  obtain ⟨hA, hE, hkv, hau, hw, h6, h7, h8, h9⟩ := HC
  have hk : v3rpc.raftKV s C.A ⊢
      v3rpc.raftKV s (v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none) := by
    rw [hA]; exact v3rpc.raftKV_srvKVAnsM_true s E ρ γr (W64 0) [] .none 0 none
  have hR : C.A.revR = (v3rpc.srvKVAnsOn (GF := GF) s E ρ γr (W64 0) [] .none 0 none).revR := by
    rw [hA]; rfl
  iunfold grpcUpOn
  iexists { C with A := v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none }, q, p, pw, pa, il, im,
    iu, ims, is, svcs, regs, sregs
  isplitr
  · ipureintro; exact ⟨rfl, hE, hkv, hau, hw, h6, h7, h8, h9⟩
  isplitr
  · iapply v3rpc.grpcCfgOk_A s C _ hk $$ Hc
  ihave #Hk' := v3rpc.kvServerIs_mono p s C.A _ cid mid C.n hR hk $$ Hk
  iframe; iframe #


open Iris.ProofMode in
/-- **An auth-off server's views in its mode** (what `Serve.spec` takes of an auth-off member,
`memberUp`'s): auth off, the mode not `.any`, the views at `E.authOn` and the store's range check
(`srvAuthLb_off`). -/
theorem serveViews_off (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServerReq s E ρ ∗ isServerRead s E γr ⊢
      ⌜E.authOn = false ∧ E.authMode ≠ .any⌝ ∗ isServerReqM E.authOn s E ρ ∗
        isServerReadM E.authOn s E γr ∗ srvAuthLb s E := by
  iintro ⟨#Hq, #Hd⟩
  ihave %hon := isServerReq_authOn s E ρ $$ Hq
  ihave #Hlb := srvAuthLb_off s E ρ $$ Hq
  have hM : E.authMode = .off := by
    unfold apply.AEnv.authOn at hon
    cases hM : E.authMode <;> simp_all [auth.AuthMode.isOn]
  rw [hon, isServerReqM_false, isServerReadM_false]
  iframe #
  ipureintro; exact ⟨rfl, by rw [hM]; simp⟩

end defs

end etcdstart
end EtcdGrove
end Perennial
