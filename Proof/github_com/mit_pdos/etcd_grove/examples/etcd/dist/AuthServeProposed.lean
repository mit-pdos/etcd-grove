/-
**PROPOSED texts of `Serve_dist` and `NewServer_dist` for auth on** (F7, `notes/etcd-dist-f7.md`, "Lifting
`Hauth` and `Serve_dist`'s `Γ.auth = false`"; #50, the lead's approval 2026-11-26T01:29:52Z). Lean-first.

PROPOSALS ONLY: definitions, no axiom, no proof, no `sorry`; nothing imports this file. The current axioms
(`Serve_dist.wp_proof`, `NewServer.wp_specG_dist`, their Spec files `ServeDist.lean`, `NewServerDist.lean`)
are unchanged. Each proposal replaces its current text only after a fresh `axiom`-skill re-review
(`notes/etcd-dist-f7-reviews.md`), in step S2 (with P-A1 and P-L1). The member's auth names are the view's
`Γ.au mid` (`DistView.au`; until the reviews of 2026-11-26 a free binder `A`, `notes/axiom-review/f7-{a,c}.md`).

`MemberLessor.lean` (F2's P-L1, `etcdstart.memberUpL`) is a copy of `etcd-safe-f2`'s file, identical, so that
the proposed Serve below states the lessor part with F2's text; it merges cleanly with F2's branch.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ServeDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewServerDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.MemberLessor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Net go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **`γa`'s fresh authorities, which P-A1 moves from `NewServer` to the start** (one per name of
`auth.AuthNames`, each at the value the server's boot allocates today). Today they are allocated inside
`NewServer` (its post's `∃ γa`): the history and its companions by `auth.authBoot_alloc` /
`auth.authHist_alloc` (`auth/Boot.lean`, `auth/Model.lean`), inside `NewAuthStore`'s boot proof
(`auth.newAuthStore_boot`, `auth_store_boot_on` in `etcdserver/Results.lean`); the token names by the
simple provider (`newTokenProviderSimple.lean`: `γf` an empty map, `γt` by `auth.tokAlloc γf`); the
readiness cell `γy` by `srvTpInv_alloc` (`InvStart.lean`). With P-A1 the start allocates them per member
(as `clusterAllocN` does the KV names) and hands them over:
* `hist`: the history's whole authority at the boot state `[bootState]` (`authHist_alloc` at
  `hs := [bootState]`; split into `authHist`'s three quarters and `authHistRev`'s quarter, `authHist_full`);
* `cur`: the latest state's ghost variable, whole, at `bootState` (`authHist_alloc` splits it in halves);
* `tok`: the issued tokens' authority, none issued (`auth.tokAuth γa.tok γa.fresh ∅`, `tokAlloc`);
* `fresh`: the issue rights' authority, none minted (`authFreshInit (.on γa)`);
* `pub`: the published index's authority at `0` (`auth.authPubAuth γa 0`);
* `fen`, `fca`: the `enabled` field's and the permission cache's ghost variables, at `false` and
  `(null, 0)`;
* `cap`: the cap's authority at `[bootState, bump bootState]` (`auth.capAuth`; its lower bound
  `capLb` follows from it);
* `bk`: the current backend's ghost variable, unset (any value), whole;
* `succ`: the succession token;
* `rdt`: the readers' tickets' authority, none out (`ownTokAuth γa.rdt 0`);
* `rdy`: the readiness cell's mono-nat authority at `0`, whole (`srvTpInv_alloc`'s; `NewServer` keeps a
  half and puts the other in the readiness invariant, which names the server's location).
Not here: the simple provider's token keeper map (`γk`, a ghost map of `Loc`s, not an `AuthNames`
field: the provider's own, allocated in `NewServer` as now) and the backend's names (`d.γB`, the
member's backend, allocated by `NewServer`'s backend construction). -/
def authNamesFreshD (γa : auth.AuthNames) : IProp GF :=
  iprop(monoListAuthOwn γa.hist 1 [auth.bootState] ∗
    ghostVar γa.cur 1 auth.bootState ∗
    auth.tokAuth γa.tok γa.fresh ∅ ∗
    authFreshInit (.on γa) ∗
    auth.authPubAuth γa 0 ∗
    ghostVar γa.fen 1 false ∗
    ghostVar γa.fca 1 ((null : Loc), 0) ∗
    auth.capAuth γa [auth.bootState, auth.bump auth.bootState] ∗
    (∃ γ0 : GName × GName × GName, ghostVar γa.bk 1 γ0) ∗
    token γa.succ ∗
    ownTokAuth γa.rdt 0 ∗
    monoNatAuthOwn γa.rdy 1 0)

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **PROPOSED `NewServer.specG_dist` for P-A1** (with auth on, the auth names `γa` the caller's and
`E.authMode = .on γa` in the post, in place of `∃ γa`). Otherwise the current text verbatim, its comments
dropped (read them in `NewServerDist.lean`); the two changes are marked `(F7, P-A1: PROPOSED)`. P-L1's
lessor binder joins in the same change (F2's). -/
abbrev NewServer.specG_dist_proposed [π : Net.NetProtoGS] (on cmp : Bool) : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft)
    (id : w64) (ctxs : List (List w8)) (ρ : ReqNames) (E₀ : apply.AEnv GF) (N : Nat)
    (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (dir : w64 → List GoString)
    (γd : GName)
    (m : lease.Mode)
    -- (F7, P-A1: PROPOSED) the member's auth names, the caller's (the start's per-member allocation)
    (γa : auth.AuthNames),
  ρ.rd.raft = ⟨γ, [], W64 0⟩ →
  γ.rule = srvRule (W64 0) γ.boot →
  (clusterNoSnap γ.cl → 2 ^ 48 ≤ uint.Z cfg.SnapshotCatchUpEntries') →
  ρ.rd.kv.c0 = W64 0 → ρ.rd.kv.ch0 = apply.alarmChain on false false →
  ρ.rd.kv.log0 = [[], []] →
  ρ.rd.kv.cmp = cmp →
  mvcc.batchLimitOk cfg.CompactionBatchLimit' →
  v3rpc.etcdMaxRequestBytesOk (uint.nat cfg.MaxRequestBytes') →
  v3rpc.maxTxnOpsOk (sint.Z cfg.MaxTxnOps') →
  v3compactor.bootCfg cfg.AutoCompactionMode' cfg.AutoCompactionRetention' cmp ρ.rd.kv.cret →
  (cmp = true → on = false) →
  E₀.cmp = cmp →
  E₀.Nx = srvApi.kvNx ρ.rd on →
  threadBound GF ≤ backend.rdPoolN →
  receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.boot.length ≤ 2 ^ 60 →
  ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) → Φs ρ.ids.pfx = srvFloorFact E₀ →
  (∃ p : Loc, p ≠ null ∧ cfg.ServerFeatureGate' = interface.mkOk
    (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #p) →
  netDirOk dir →
  peerURLsDir dir id U.peer →
  raftNode.bootCfg cfg → rafthttp.bootCfg dir γ.vs →
  (on = true → cfg.AuthToken' = go!"simple" ∧ 0 < uint.Z cfg.TokenTTL' ∧
    uint.Z cfg.TokenTTL' < 2 ^ 32) →
  lease.bootCfg (GF := GF) ρ.rd.kv.lm m on →
  bootCfgOk cfg → bootCfgFresh cfg U → N + 7 + bootWB ≤ backend.wbInit →
  letI : MemStorReg GF := ⟨γ.reg⟩
  {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Htok" ∷ threadTok ∗
      "#Hfg" ∷ isFeatureGate cfg.ServerFeatureGate' ∗
      "#Hlcp" ∷ featureIs cfg.ServerFeatureGate' go!"LeaseCheckpoint" false ∗
      "#Hboot" ∷ bootstrapContract cfg U γ id ctxs N dir ∗
      "#Hzlg" ∷ zapLoggerOk cfg.Logger' ∗
      "#Hvoff" ∷ ⌜EtcdVerifyOff⌝ ∗
      "#Hcfgro" ∷ bootCfgRO cfg U ∗ "Hrauth" ∷ memStorRegAuth (∅ : GMap Loc MemStorNamesRec) ∗
      "Hwdf" ∷ wal.bootRes cfg ∗
      "Hnboot" ∷ (nodeBoot γ.cl srvClusterN γ.vs ctxs id ∗ raftState γ.cl id RaftState.init ∗
        nodeVacant γ.cl id) ∗
      "#Hsrl" ∷ srvRaftLogInv ρ.rd.raft ∗
      "#Hidc" ∷ idClusterInv ρ.ids.issued ρ.ids.cnt ρ.ids.wn ρ.ids.fs ρ.ids.gen srvFloorFacts ∗
      "#Hpfxi" ∷ idPfxInv ρ.ids.gen ρ.ids.pfx ∗
      "#Hidk" ∷ idKeyFactAt ρ.ids.fs ρ.ids.key E₀.γs.slog ∗ "#HNZ0" ∷ idNoZero ρ.ids ∗
      "#Hpmint" ∷ srvPropMint ρ.rd.raft ρ.ids ∗ "#Hrdctx" ∷ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
      "Hids" ∷ idShare ρ.ids ∗
      "Hwtok" ∷ idWaitTok ρ.ids ∗
      "Hkvs" ∷ srvApi.newServerStoreFreshA E₀.γs ∗
      "Hcok" ∷ ghostMapAuth ρ.rd.kv.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      "Hrev" ∷ ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
      "Hrd" ∷ srvReadNamesFreshNK ρ.rd ∗
      "#Hkvinv" ∷ kvInvM on ρ.rd.raft ρ.rd.kv srvAuthSt0 ∗
      "#Hpeers" ∷ (□ ∀ (pid : w64) (a : GoString), ⌜pid ∈ γ.vs ∧ pid ≠ id ∧ go!"http://" ++ a ∈ dir pid⌝ -∗
        etcd_dist.httpAddrAt (Gg := hG.goose_globalGS) γ pid a) ∗
      "#Hnoproxy" ∷ etcd_dist.noProxyEnv ∗
      "%Hsloc" ∷ ⌜γ.snapLoc id = some γd⌝ ∗ "Hsdir" ∷ ghostMapAuth γd 1 (∅ : GMap w64 Unit) ∗
      "%Haufit" ∷ ⌜authRecordsFit⌝ ∗
      "%Hbuq" ∷ ⌜apply.backendUnderQuota⌝ ∗
      "%Hdisk" ∷ ⌜storage.diskOk⌝ ∗
      "%Hmmap" ∷ ⌜storage.openMmapOk cfg⌝ ∗
      "#Hcci" ∷ context.isClosedchanInit ∗
      -- (F7, P-A1: PROPOSED) with auth on, `γa`'s fresh authorities, the caller's
      "Hγa" ∷ (if on then authNamesFreshD γa else iprop(True)) }}
    (App (Val (@! NewServer)) (Val #cfg))
  {{ (srv : Loc) (err : GoInterface), RET (PairV #srv #err);
      (⌜srv = null ∧ err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      ⌜err = GoInterface.nil⌝ ∗ threadTok ∗
        ∃ (γn : NetNames GF) (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
          (γrn : RNNames GF) (b : GoInterface) (γk : GName) (τ : SrvTr GF),
          ⌜γn.N = srvNet γ ∧ γn.dir = dir ∧ envAgree E E₀ ∧ E.authOn = on ∧ (on = true → E.authMode = .on γa)⌝ ∗
          srvServeStock srv E ∗
          srvWatchBuilt srv E ∗
          srvBuiltG on srv γA ci TM E ρ ρ.rd (srvErM on ρ E₀ (W64 0) (W64 0) (bootKVOf on) id (srvTrKey γn γk) (srvTrStopK γk))
            γrn b (W64 0)
            (W64 0) (bootKVOf on) N ∗
          srvBuildGap srv γrn ρ.rd.cursor (W64 0) (W64 0) ∗
          srvServeBuilt srv E cfg ∗
          srvSVRes srv E ∗
          srvMonitorCfg srv cfg ∗
          srvReadyCloser srv E ∗
          srvNetMember γn srv id τ ∗ srvTrTok γn τ ∗
          ([∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ) ∗
          lease.srvInv on srv E m ∗
          leaseTTLRowR srv γ.vs ∗
          srvCfgFieldAddr srv go!"ClientCertAuthEnabled" ↦□ cfg.ClientCertAuthEnabled' ∗
          □ (⌜on = true⌝ → srvAuthStoreOn srv E.RD) ∗
          srvStop.keep srv cfg E γrn γk }}

end spec

namespace etcdstart

section defsL
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`memberUpOn` with the lessor at `γl`** (PROPOSED, F7 review C's F2, 2026-11-26; F2's `memberUpL`
with auth on): `memberUpOn`'s body verbatim, at the lease mode `m`, and `mvcc.api.mvccLeases E.γ = γl` for its
environment `E` (the name the lessor was made at: F2's `NewServer.specG_dist_proposed`, P-L1). -/
def memberUpOnL (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames) (m : lease.Mode) (γl : GName) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName),
    ⌜envAgree E E₀ ∧ E.authMode = .on γa ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0 ∧ mvcc.api.mvccLeases E.γ = γl⌝ ∗
    srvServeStock s E ∗ srvRunReadStock s ρ.rd ∗
    isServerReqM true s E { ρ with wait := γw } ∗ isServerReadM true s E ρ.rd ∗ srvAuthLb s E ∗
    srvGoRes s ∗ srvLgReader s ∗
    ([∗list] _x ∈ List.replicate memberReadN (), srvReadReader s ρ.rd) ∗
    srvWatchBuilt s E ∗ srvServeFacts s E cfg ∗
    srvBemuReader s ∗
    srvPeerCtl γn s id ∗
    □ (srvTLSId s -∗ False) ∗ srvAuthStoreOn s E.RD ∗
    srvLeaseRd s E m)

end defsL

end etcdstart

namespace etcd_dist

section spec2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **PROPOSED `Serve_dist.spec` for auth on, with P-L1's lessor** (the current text with three changes):
* the pure premise `kvCongr ρ.rd.kv Γ.kv ∧ Γ.auth = false` becomes `kvCongr ρ.rd.kv Γ.kv ∧ (Γ.auth = false ∨
  ρ.rd.kv.hist = Γ.kv.hist)` (`kvCongr` leaves `hist` out; with auth on every member's history is the
  cluster's, `kvCongrOn`);
* the member's serving resources are, with auth on, `etcdstart.memberUpOnL … (Γ.au mid) Γ.kv.lm (Γ.ls mid)`
  (`memberUpOn`'s, its `E.authMode = .on (Γ.au mid)`: the member's auth names the view's), and with auth off
  F2's `etcdstart.memberUpL … Γ.kv.lm (Γ.ls mid)` (`memberUp`'s);
* in both, the member's lessor is at the view's name `Γ.ls mid` and its lease subsystem at the view's mode
  `Γ.kv.lm` (P-L1, F2's `Serve_dist.spec_proposed` on `etcd-safe-f2`, reviewed with this one).
Why (F7 reviews A and C, 2026-11-26): address facts are minted for any `Γ` (`etcdAddr_set`), so without these
premises a start could publish a `Γ` whose `au`/`ls` names it allocated and owns, and refute every auth-on and
lease axiom's success arm. With them, `Γ.au mid` and `Γ.ls mid` are the serving member's real names, held
through the member's exclusive resources (`NewServer`'s fresh authorities, P-A1's `authNamesFreshD` and
P-L1's lessor), so two members cannot share them and the drafts' distinct-names premises (kept here too)
are redundant. `etcdSvc`'s intended interpretation then says that an auth-on member's entries are the
`etcd*SpecOn` handlers at `T := False` (no TLS identity: `ClientCertAuthEnabled` false in `deployment`'s
configuration). -/
abbrev Serve_dist_proposed.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)]
    [π : NetProtoGS] (s : Loc) (a : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (mid : w64) (Γ : DistView),
  -- (F7: PROPOSED) distinct auth names per member (the lease review's form; redundant given the tie below)
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗
      ⌜v3rpc.ServerMethodSets ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ srvLevels (GF := GF) ∧
        kvCongr ρ.rd.kv Γ.kv ∧ (Γ.auth = false ∨ ρ.rd.kv.hist = Γ.kv.hist)⌝ ∗
      -- (F7 + F2's P-L1: PROPOSED) the member's auth names `Γ.au mid`, its lessor `Γ.ls mid`, its lease
      -- mode `Γ.kv.lm`
      (if Γ.auth then etcdstart.memberUpOnL s ρ E₀ lg γn mid (Γ.au mid) Γ.kv.lm (Γ.ls mid)
        else etcdstart.memberUpL s ρ E₀ lg γn mid Γ.kv.lm (Γ.ls mid)) ∗
      etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve)) (Val #s))
      (Val #a))
  {{ (err : GoInterface), RET #err; True }}

end spec2

end etcd_dist

end EtcdGrove
end Perennial
