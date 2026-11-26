/-
**PROPOSED texts of `Serve_dist` and `NewServer_dist` for auth on** (F7, `notes/etcd-dist-f7.md`, "Lifting
`Hauth` and `Serve_dist`'s `Γ.auth = false`"; #50, the lead's approval 2026-11-26T01:29:52Z). Lean-first.

PROPOSALS ONLY: definitions, no axiom, no proof, no `sorry`; nothing imports this file. The current axioms
(`Serve_dist.wp_proof`, `NewServer.wp_specG_dist`, their Spec files `ServeDist.lean`, `NewServerDist.lean`)
are unchanged. Each proposal replaces its current text only after a fresh `axiom`-skill re-review
(`notes/etcd-dist-f7-reviews.md`), in step S2 (with P-A1 and P-L1). `A : w64 → auth.AuthNames` stands for
`Γ.au` until `DistView` gains it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ServeDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewServerDist

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

/-- **PLACEHOLDER: `γa`'s fresh authorities, which P-A1 moves from `NewServer` to the start.** Today
`NewAuthStore` allocates the auth names inside the server (`NewServer`'s post's `∃ γa`); with P-A1 the
start allocates them per member (as `clusterAllocN` does the KV names) and hands `NewServer` their
authorities. Only the token rights' authority (`authFreshInit (.on γa)`, the one a store construction
hands to the server, `authApplyResPre`) is named here; S2 lists the rest from `NewAuthStore`'s
allocation (the history, the current state, the tokens, the publication, `fen`, `fca`, `cap`, the
backend's names). A review must treat this conjunct as incomplete. -/
def authNamesFreshD (γa : auth.AuthNames) : IProp GF :=
  authFreshInit (.on γa)

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

namespace etcd_dist

section spec2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **PROPOSED `Serve_dist.spec` for auth on** (the current text with two changes): the pure premise
`kvCongr ρ.rd.kv Γ.kv ∧ Γ.auth = false` becomes `kvCongr ρ.rd.kv Γ.kv ∧ (Γ.auth = false ∨ ρ.rd.kv.hist =
Γ.kv.hist)` (`kvCongr` leaves `hist` out; with auth on every member's history is the cluster's,
`kvCongrOn`), and the member's serving resources are `etcdstart.memberUpOn … (A mid)` with auth on (its
`E.authMode = .on (A mid)`: the member's auth names the view's) and `etcdstart.memberUp` with auth off, as
now. `etcdSvc`'s intended interpretation then says that an auth-on member's entries are the
`etcd*SpecOn` handlers at `T := False` (no TLS identity: `ClientCertAuthEnabled` false in `deployment`'s
configuration). The lease mode stays the default (`.none`), as now; P-L1 sets it. -/
abbrev Serve_dist_proposed.spec (A : w64 → auth.AuthNames) : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)]
    [π : NetProtoGS] (s : Loc) (a : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (mid : w64) (Γ : DistView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗
      ⌜v3rpc.ServerMethodSets ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ srvLevels (GF := GF) ∧
        kvCongr ρ.rd.kv Γ.kv ∧ (Γ.auth = false ∨ ρ.rd.kv.hist = Γ.kv.hist)⌝ ∗
      (if Γ.auth then etcdstart.memberUpOn s ρ E₀ lg γn mid (A mid)
        else etcdstart.memberUp s ρ E₀ lg γn mid) ∗
      etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve)) (Val #s))
      (Val #a))
  {{ (err : GoInterface), RET #err; True }}

end spec2

end etcd_dist

end EtcdGrove
end Perennial
