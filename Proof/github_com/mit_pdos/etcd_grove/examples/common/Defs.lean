/-
**The examples' shared start (`examples/common`): its vocabulary** (2026-10-22, D33). Lean-first (no
Rocq counterpart). What putget's, linkv's, linkvtxn's, watchkv's, cachekv's (one member) and
putget3's, linkv3's, linkv3p's (three members) `Main`s and `startMember`s said each in their own
`Defs.lean`/`Alloc.lean`, once, with what differed among them (the member's name, its addresses, the
cluster's map, token and members) as parameters; each example's named premises (`premises`) stay its
own, at its configuration, and give these (`bootPremise_of`-style conversions in its `Main`'s proof).

**The configuration** (`cfgOk`): the scalar fields `newServer` sets for member `name` of a new
cluster with token `token`: data directory `name.etcd`, raft's clock `100` ms and `10` ticks.

**`bootstrap`'s contract** (`bootPremise`): at every storage registry and raft names of the cluster
`ps` (static, no-snapshot mode, the bootstrap log, the conf-change policy `ccOk ps`), for a
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
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [ext : FfiSyntax]

/-- **The server's conf-change policy for the cluster `ps`** (`srvCCPolicy`'s clauses, D19c): a v1
conf change, a `ConfChange` encoding of id `0`, which changes nothing of the configuration. -/
def ccOk (ps : List w64) : w32 → List w8 → Prop := fun ty d =>
  ty = W32 1 ∧ isConfChangeEncoding d ∧ ccIdOf d = W64 0 ∧ ccBootOk (GMap.listToSet ps) d

/-- A URL `http://<host>`. -/
def httpURL (host : GoString) : _root_.Perennial.net.url.URL :=
  { Scheme' := go!"http", Opaque' := [], User' := null, Host' := host, Path' := [], Fragment' := [],
    RawQuery' := [], RawPath' := [], RawFragment' := [], ForceQuery' := false, OmitHost' := false }

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

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
at every storage registry and raft names of the cluster, for its configuration and URLs meeting
`Uok`, at the bound `N`, the bootstrap log and the directory `dir` (see the file header). -/
def bootPremise (N : Nat) (ps : List w64) (bootLog : List EntryM) (dir : w64 → List GoString)
    (token name : GoString) (Uok : BootURLs → Prop) (id : w64) : IProp GF :=
  iprop(□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
        (γ : RaftNames),
      ⌜cfgOk token name cfg ∧ Uok U ∧ γ.reCfg = GMap.listToSet ps ∧
        γ.reDyn = none ∧ γ.reCCOk = ccOk ps ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧
        γ.reNoXfer = true⌝ -∗
      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N dir)

instance bootPremise_persistent (N : Nat) (ps : List w64) (bootLog : List EntryM)
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64) :
    Persistent (bootPremise (GF := GF) N ps bootLog dir token name Uok id) := by
  unfold bootPremise; infer_instance

/-- **`bootPremise` from an example's own form of it** (its `premises`' clause, at its configuration
predicate `cfgOk'`, URLs predicate `Uok'` and conf-change policy `cc'`): this one asks less, when
the shared start's configuration meets the example's (`Hc`), its URLs too (`Hu`), and the policies
are one. -/
theorem bootPremise_of (N : Nat) (ps : List w64) (bootLog : List EntryM)
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64)
    (cfgOk' : go_etcd_io.etcd.server.v3.config.ServerConfig → Prop) (Uok' : BootURLs → Prop)
    (cc' : w32 → List w8 → Prop)
    (Hc : ∀ cfg, cfgOk token name cfg → cfgOk' cfg) (Hu : ∀ U, Uok U → Uok' U)
    (Hcc : cc' = ccOk ps) :
    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
        (γ : RaftNames),
      ⌜cfgOk' cfg ∧ Uok' U ∧ γ.reCfg = GMap.listToSet ps ∧
        γ.reDyn = none ∧ γ.reCCOk = cc' ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧
        γ.reNoXfer = true⌝ -∗
      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N dir) ⊢
      bootPremise (GF := GF) N ps bootLog dir token name Uok id := by
  iintro #H
  iunfold bootPremise
  imodintro
  iintro %reg %cfg %U %γ %Hp
  obtain ⟨hc, hu, h1, h2, h3, h4, h5, h6⟩ := Hp
  iapply H
  ipureintro
  exact ⟨Hc cfg hc, Hu U hu, h1, h2, by rw [Hcc]; exact h3, h4, h5, h6⟩

/-- **The premises shared by the members** (see the file header). -/
def commonPremises : IProp GF :=
  iprop(rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
    rnStopOkStarted ∗ v3rpc.runsNoRequireLeader)

instance commonPremises_persistent : Persistent (commonPremises (GF := GF)) := by
  unfold commonPremises; infer_instance

/-- **The stand-in apply environment** (`NewServer.spec`'s `E₀`): the store's index names, its
certificate map and the revisions' map; `envAgree` reads nothing else. -/
def env₀ (idx : mvcc.IdxNames) (cok rev : GName) : apply.AEnv GF :=
  { s := null,
    γ := { idx := idx, bucket := 0, clog := 0, leases := 0, revs := 0, hook := 0, hookFn := 0,
           kb := none, cmeta := 0, fin := 0, sch := ⟨0, 0⟩, cok := cok, watchQ := false },
    P := iprop(True), f := #(), RD := iprop(True), γrev := rev, authMode := .off,
    FS := iprop(True), ciC := fun _ => True, RO := fun _ => iprop(True), RW := iprop(True),
    γbe := 0 }

/-- **What member `id`'s `NewServer` takes of the ghost state** (its pure facts, the cluster's
resources at its names, its share): `NewServer.spec`'s precondition but the network's and the
premises'. -/
def memberBoot (W : SrvWorkload) (γ : RaftNames) (bud : BudgetNames) (bootLog : List EntryM)
    (ρ : ReqNames) (E₀ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64) :
    IProp GF :=
  iprop(⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧ srvCCPolicy ρ.rd.raft ∧
      ρ.rd.kv.c0 = W64 0 ∧ ρ.rd.kv.ch0 = apply.alarmChain false false false ∧
      ρ.rd.kv.log0 = [[], []] ∧ ρ.rd.kv.cok = E₀.γ.cok ∧ ρ.rd.kv.wl = W ∧
      ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) ∧ Φs ρ.ids.pfx = srvFloorFact E₀⌝ ∗
    ownRaftGhost γ id (bootPState bootLog) ∗ isCommitted γ bootLog ∗ raftCommitInv γ ∗
    inv budgetN (budgetInv bud) ∗ termLB bud (W64 1) ∗
    idClusterInv ρ.ids.issued ρ.ids.cnt Φs ∗ idNoZero ρ.ids ∗
    srvPropMint ρ.rd.raft ρ.ids ∗ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
    idShare ρ.ids ∗ rdCred γ (2 ^ 48) ∗ idWaitTok ρ.ids ∗
    mvcc.idxFresh E₀.γ.idx ∗
    ghostMapAuth E₀.γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
    ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
    srvReadNamesFreshNK ρ.rd ∗ kvInv ρ.rd.raft ρ.rd.kv ∗
    -- (2026-10-26, D22 J2, R-loc) the member's snapshot directory, empty, at the names raft's
    -- names give it (`RaftNames.reSnapLoc`, `NewServer`'s)
    ∃ γd : GName, ⌜γ.reSnapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit))

/-- **A member built** (`newServer`'s success): the server `s` built by `NewServer` with the
request names `ρ` at an apply environment `E` agreeing with the stand-in `E₀`, auth off, from a
configuration `cfg` with the logger `lg`, no tracer options and no progress-notify interval:
`isServerBuilt` (from `NewServer`'s `srvBuilt` and `srvBuildGap`, at the bound `N` and the term
budget `bud`), what `Start` takes besides (the storage version monitor's backend access, the
monitors off, `lgMu`'s reader slot of the downgrade monitor), and what `NewServer` left for serving
(`srvServeBuilt`, the watchable store's readers) and for the member's place in the network `γn`
(`srvNetMember`, with its transport `τ`; 2026-10-24, rafthttp stage 6d: the raft loop's key to the
transport's `Send`, `srvTrKey`, under `γk`, one of the transport's reader tokens, `srvTrTok`, and
what `http.Serve`'s request goroutines borrow, `srvServeRes`, until the peer address is served:
`served`). -/
def memberBuilt (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (N : Nat) (bud : BudgetNames) (served : Bool) : IProp GF :=
  iprop(∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
      (γrn : RNNames) (b : GoInterface) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
      (γk : GName) (τ : SrvTr GF),
    ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0⌝ ∗
    srvWatchBuilt s E ∗
    isServerBuilt s γA ci TM E ρ ρ.rd (srvEr ρ E₀ (W64 0) (W64 0) bootKV bud id (srvTrKey γn γk))
      γrn b (W64 0)
      (W64 0) (W64 0) bootKV N ∗
    srvServeBuilt s E cfg 64 ∗ srvSVRes s E ∗ srvMonitorsOff s ∗ srvLgReader s ∗
    srvReadyCloser s ∗ srvNetMember γn s id τ ∗ srvTrTok γn τ ∗
    (if served then True else [∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ) ∗
    srvWatchReaders s E 64)

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
`Start`; the watchable store's readers), and its place in the network `γn`. -/
def memberUp (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName),
    ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0⌝ ∗
    isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvGoRes s ∗ srvLgReader s ∗
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      srvReadReader s ρ.rd) ∗
    srvWatchBuilt s E ∗ srvServeFacts s E cfg ∗
    srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦ cfg.WatchProgressNotifyInterval' ∗
    srvBemuReader s ∗
    ([∗list] _x ∈ List.replicate 64 (), srvLeadTimeReader s) ∗
    ([∗list] _x ∈ List.replicate (64 - 2) (), srvLgReader s) ∗
    ([∗list] _x ∈ List.replicate 64 (), E.RD) ∗
    ([∗list] _x ∈ List.replicate 64 (), mvcc.storeReader E.s E.γ) ∗
    ([∗list] _x ∈ List.replicate 64 (), srvBemuReader s) ∗
    srvPeerCtl γn s id ∗ srvWatchReaders s E 64)

/-- **What `v3rpc.Server` and `Listen` return** (the ghost step's input): the gRPC server `gs`
being built with etcd's interceptor chains and services (`v3rpc.Server.spec`'s postcondition, at
the configuration `C` `grpcCfgOk_of_started_w` gives: the KV answers of the server's views at
`E`, `ρ`, `γr`; the watch server's state `R` at `E`; 64 of the watchable store's readers), the
server's resources back, and the listener `lis` at `addr`. -/
def grpcUp (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (gs : Loc)
    (lis : GoInterface) (addr : GoString) (cid mid : w64) (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(∃ (C : v3rpc.GrpcCfg GF) (q p pw : Loc) (il im iu ims is : GoFunc) (svcs : List GoString)
      (regs sregs : List (GoString × val × GoInterface)) (d' : w64),
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
    srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦ d' ∗
    ([∗list] _x ∈ List.replicate 64 (), mvcc.watchReader C.wsl E.s C.γ) ∗
    netListenerAt lis addr)

end defs

end common
end EtcdGrove
end Perennial
