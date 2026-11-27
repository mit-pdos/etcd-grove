/-
**A restart's `NewServer` at one image** (etcd-dist D6, T4, 2026-11-24; `notes/etcd-dist-d6.md` §4):
the hinge between the graceful restart's `NewServer.specR` and the crash restart's `NewServer.specC`.

`NewServer.specRAt` is `NewServer.specR` with `bootstrap`'s restart contract (`bootstrapRestartContract`,
over every image) replaced by its instance at the image's witnesses `σ i A D M` (`bootstrapAtR`): the
only use `NewServer.wp_proofRG` makes of the contract. Both contracts give that instance:

* the graceful one directly (`bootstrapAtR_of_restart`), so `specR` follows (`NewServer.specR_of_RAt`);
* the crash one (`bootstrapCrashContract`) at an image whose records meet the WAL's read facts
  (`bootstrapAtR_of_crash`, its first case), which the crash image carries (`wal.crashImageR`).

With the crash image turned into the graceful one when it is one (`srvCrashImageAt_disk`: the backend's
index at or below the WAL's commit and at or above its snapshot and the bootstrap log, the stored
`confState` the index's; the vacancy armed, `wal.stopImage` from `wal.crashImageR`), `specRAt` gives
`specC` in that case (`NewServer.wp_proofC`). The other cases (the backend ahead of the WAL's commit,
T10's weakened rows) are not instances of the graceful proof: see the proof file.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServerR
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServerCrash

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **`bootstrap`'s restart contract at one image** (`bootstrapRestartContract`'s body at the image's
witnesses `σ i L D M`). -/
def bootstrapAtR (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (id : w64) (N : Nat) (dir : w64 → List GoString) (σ : StorContents) (i : w64)
    (L : List EntryModel) (D : backend.Data) (M : GMap Loc MemStorNamesRec) : IProp GF :=
  iprop(□ (⌜σ.b ≤ uint.nat i ∧ uint.nat i ≤ σ.commit ∧ γ.cl.bootLen ≤ uint.nat i ∧
      bootCfgOk cfg ∧ cfg.ForceNewCluster' = false ∧ cfg.DedicatedWALDir' = srvWalDirOf cfg.DataDir' ∧
      storage.dbOpensOk ∧
      N + 7 + bootWB ≤ backend.wbInit ∧
      (∀ f, ((restModel (W64 0) γ.boot L).mem.lookup f).map apply.MemberM.peerURLs =
        ((memBoot γ.boot).lookup f).map apply.MemberM.peerURLs) ∧
      clusterVerLogOk L⌝ -∗
    (∃ (γk : KVNames) (A : List EntryModel) (u : Bool),
      ⌜γk.c0 = W64 0 ∧ imageRestAt γk γ.boot i L D ∧ imageStOk (kvModel γk A) (crevOf γk A)⌝ ∗
      mvcc.api.mvccImage D (kvModel γk A) (crevOf γk A) u) -∗
    {{ zapLoggerOk cfg.Logger' ∗
        (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
        ⌜EtcdVerifyOff⌝ ∗
        bootCfgRO cfg U ∗ memStorRegAuth M ∗
        srvFilesC cfg.DataDir' id σ D }}
      (App (Val (@! bootstrap)) (Val #cfg))
    {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
        ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ bootOkR cfg γ id N dir σ i L D M b }}))

instance bootstrapAtR_persistent (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (id : w64) (N : Nat) (dir : w64 → List GoString) (σ : StorContents) (i : w64)
    (L : List EntryModel) (D : backend.Data) (M : GMap Loc MemStorNamesRec) :
    Persistent (bootstrapAtR (GF := GF) cfg U γ id N dir σ i L D M) := by
  unfold bootstrapAtR; infer_instance

/-- `bootstrap`'s restart contract is persistent (as `bootstrapContract`; moved here from
`NewServerR.lean`). -/
instance bootstrapRestartContract_persistent (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (U : BootURLs) (γ : SrvRaft) (id : w64) (N : Nat) (dir : w64 → List GoString) :
    Persistent (bootstrapRestartContract (GF := GF) cfg U γ id N dir) := by
  unfold bootstrapRestartContract; infer_instance

/-- `bootstrap`'s crash contract is persistent. -/
instance bootstrapCrashContract_persistent (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (U : BootURLs) (γ : SrvRaft) (id : w64) (N : Nat) (dir : w64 → List GoString) :
    Persistent (bootstrapCrashContract (GF := GF) cfg U γ id N dir) := by
  unfold bootstrapCrashContract; infer_instance

/-- The graceful contract at an image. -/
theorem bootstrapAtR_of_restart (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (id : w64) (N : Nat) (dir : w64 → List GoString) (σ : StorContents) (i : w64)
    (L : List EntryModel) (D : backend.Data) (M : GMap Loc MemStorNamesRec) :
    bootstrapRestartContract (GF := GF) cfg U γ id N dir ⊢ bootstrapAtR cfg U γ id N dir σ i L D M := by
  unfold bootstrapRestartContract bootstrapAtR
  iintro #H
  imodintro
  iintro %Hp Hs
  ihave Hc := H $$ %σ %i %L %D %M [] [Hs]
  · ipureintro; exact Hp
  · iexact Hs
  iexact Hc

/-- The crash contract at an image whose records meet the WAL's read facts (the restart contract's
`i ≤ σ.commit` puts the bootstrap log, below the index, below the commit: the crash contract's
`γ.cl.bootLen ≤ σ.commit`, C-I2's restatement). -/
theorem bootstrapAtR_of_crash (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (id : w64) (N : Nat) (dir : w64 → List GoString) (σ : StorContents) (i : w64)
    (L : List EntryModel) (D : backend.Data) (M : GMap Loc MemStorNamesRec) (hw : walReadFacts σ) :
    bootstrapCrashContract (GF := GF) cfg U γ id N dir ⊢ bootstrapAtR cfg U γ id N dir σ i L D M := by
  unfold bootstrapCrashContract bootstrapAtR
  iintro ⟨#H, -⟩
  imodintro
  iintro %Hp Hs
  ihave Hc := H $$ %σ %i %L %D %M [] [Hs]
  · ipureintro; exact ⟨Hp.1, hw, Nat.le_trans Hp.2.2.1 Hp.2.1, Hp.2.2.2⟩
  · iexact Hs
  iexact Hc

end boot

section image
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A crash image that is a graceful one** (and its records meet the WAL's read facts): with the
backend's index at or below the WAL's commit, at or above its snapshot (`snapRowB2`'s first case) and the
bootstrap log, the stored `confState` the index's (`confRowW`'s first case; its second case, a `confState`
one conf change ahead, is the same one: (T10s3b B8) both configurations are recorded over the committed
log, `confAt_committed`, so both are the boot one under the server's raft-log invariant,
`srv_confAt_eq_simple`), the vacancy armed
(`nodeVacant_arm`: its crash token returned, for `specC`'s post; and the snapshot directory's crash
token, `srvSnapKeep`, D-T7-2: the graceful image keeps only the handle), the WAL's slot `wal.stopImage` from
`wal.crashImageR`; the rest is the same. Otherwise the crash image is returned with the reason (T10's
restatement, 2026-11-25, weakened those rows). -/
theorem srvCrashImageAt_disk (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString) (S : RaftState)
    (σ : StorContents) (i : w64) (A : List EntryModel) (D : backend.Data) (m : Membership)
    (M : GMap Loc MemStorNamesRec) (E : CoPset) (hC : ↑srvConfN ⊆ E) (hL : ↑srvLogN ⊆ E) :
    srvRaftLogInv (GF := GF) ⟨γ, [], W64 0⟩ ∗ srvCrashImageAt (GF := GF) γ ρ id dd S σ i A D m M ⊢
      |={E}=> (srvDiskImageAt γ ρ id dd S σ i A D m M ∗ ⌜walReadFacts σ⌝ ∗
        (∃ x, nodeCrashTok γ.cl id x) ∗ srvSnapKeep γ id dd) ∨
      (srvCrashImageAt γ ρ id dd S σ i A D m M ∗
        ⌜¬ (uint.nat i ≤ σ.commit ∧ σ.b ≤ uint.nat i ∧ γ.cl.bootLen ≤ uint.nat i)⌝) := by
  by_cases hg : uint.nat i ≤ σ.commit ∧ σ.b ≤ uint.nat i ∧ γ.cl.bootLen ≤ uint.nat i
  rotate_left
  · iintro ⟨-, Himg⟩
    imodintro
    iright
    iframe Himg
    ipureintro; exact hg
  obtain ⟨hc, hb, hbl⟩ := hg
  unfold srvCrashImageAt srvDiskImageAt wal.crashImageR snapRowB2
  iintro ⟨#Hsrl, Hvac, HrS, %Hρ, #HA, %Himp, Hmv, #Hconf, Hcrow, ⟨%Hw, #Hcert, Hl⟩, Hreg, Hfiles,
    ⟨%γd, %γm, %c, %Hsl, Hrow, Hsdi, Hmn⟩⟩
  -- (T10s3b B8) the stored `confState` is the index's in both cases of `confRowW`: the configurations
  -- at `i` and `i + 1` are both the boot one
  ihave Hcs : |={E}=> ⌜∀ cs, v3ConfStateIs D cs → confStateIs cs m⌝ $$ [Hcrow]
  · iunfold confRowW at Hcrow
    icases Hcrow with (%H | ⟨%m', #Hm', %H⟩)
    · imodintro; ipureintro; exact H
    icases confAt_committed γ.cl (uint.nat i) m $$ Hconf with ⟨%l, #Hl1, %Hl1⟩
    icases confAt_committed γ.cl (uint.nat i + 1) m' $$ Hm' with ⟨%l', #Hl2, %Hl2⟩
    imod srv_confAt_eq_simple ⟨γ, [], W64 0⟩ l (uint.nat i) m Hl1 E hC hL $$ [$Hsrl $Hl1 $Hconf] with %Hm
    imod srv_confAt_eq_simple ⟨γ, [], W64 0⟩ l' (uint.nat i + 1) m' Hl2 E hC hL $$ [$Hsrl $Hl2 $Hm']
      with %Hm2
    imodintro; ipureintro
    rw [Hm, ← Hm2]; exact H
  imod Hcs with %hcs
  icases Hrow with (%Hrow | ⟨%j, %Hj, -, -⟩)
  rotate_left
  · iexfalso; ipureintro; omega
  icases snapDirKeep_handle _ _ _ _ $$ Hsdi with ⟨#Hsdh, Hsdi⟩
  imod nodeVacant_arm γ.cl id E $$ Hvac with ⟨%x, Hvac, Hct⟩
  ihave Hws := wal.stopImage_intro γ.cl S σ i Hw.1 hb hc $$ [Hcert Hl]
  · iframe Hcert Hl
  imodintro
  ileft
  isplitl [Hvac HrS Hmv Hws Hreg Hfiles Hmn]
  · iframe Hvac HrS HA Hmv Hconf Hws Hreg Hfiles
    isplitr
    · ipureintro; exact Hρ
    isplitr
    · ipureintro; exact Himp
    isplitr
    · ipureintro; exact hbl
    isplitr
    · ipureintro; exact hcs
    iexists γd, γm, c
    iframe Hsdh Hmn
    ipureintro; exact ⟨Hsl, Hrow.2⟩
  isplitr
  · ipureintro; exact Hw.2
  isplitl [Hct]
  · iexists x
    iexact Hct
  iunfold srvSnapKeep
  iexists γd, γm
  iframe Hsdi
  ipureintro; exact Hsl

end image

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewServer(cfg)` at a restart, `bootstrap`'s contract at the image** (see the file header):
`NewServer.specR` with `#HbootR` the contract's instance at the image's witnesses (`bootstrapAtR`). -/
abbrev NewServer.specRAt : Prop :=
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
  -- what the restart contract covers: no forced new cluster, the WAL in the data directory's
  -- dedicated WAL directory (wal-link P2)
  bootCfgOk cfg → cfg.ForceNewCluster' = false → cfg.DedicatedWALDir' = srvWalDirOf cfg.DataDir' →
  N + 7 + bootWB ≤ backend.wbInit →
  letI : MemStorReg GF := ⟨γ.reg⟩
  {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Htok" ∷ threadTok ∗
      "#Hfg" ∷ isFeatureGate cfg.ServerFeatureGate' ∗
      "#Hlcp" ∷ featureIs cfg.ServerFeatureGate' go!"LeaseCheckpoint" false ∗
      -- `bootstrap`'s contract on the stopped member's data directory
      "#HbootR" ∷ bootstrapAtR cfg U γ id N dir σ i A D M ∗
      "#Hzlg" ∷ zapLoggerOk cfg.Logger' ∗
      "#Hvoff" ∷ ⌜EtcdVerifyOff⌝ ∗
      "#Hcfgro" ∷ bootCfgRO cfg U ∗
      -- the stopped member's image, in the configuration's data directory
      "Himg" ∷ srvDiskImageAt γ ρo id cfg.DataDir' S σ i A D mb M ∗
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
      -- (premises to axioms, 2026-11-24: `rnLoggerZapOk`, `rnTimeoutDetectorOk` gone, now `newRaftNode`'s callees' trust-boundary specs)
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

/-- **The graceful restart's spec from `specRAt`**: the restart contract's instance at the image. -/
theorem NewServer.specR_of_RAt (h : NewServer.specRAt (GF := GF) (hG := hG)) :
    NewServer.specR (GF := GF) (hG := hG) := by
  intro cfg U γ id ρ ρo E₀ N Φs γn dir m S σ i A D mb M HρRaft HrN Hrule Hnsm Hc0 Hch0 Hlog0 Hkcmp Hcbl
    Hmrb Hmto Hcb Hcmp0 HNx0 Hbnd Hrb HrbN Hboot Hpfx HΦs Hfgp Hdirok HpU HfU HfC Hrnc Hdirs Hlbc Hbco Hfnc
    Hdwd Hbwb
  letI : MemStorReg GF := ⟨γ.reg⟩
  have h' := h cfg U γ id ρ ρo E₀ N Φs γn dir m S σ i A D mb M HρRaft HrN Hrule Hnsm Hc0 Hch0 Hlog0
    Hkcmp Hcbl Hmrb Hmto Hcb Hcmp0 HNx0 Hbnd Hrb HrbN Hboot Hpfx HΦs Hfgp Hdirok HpU HfU HfC Hrnc Hdirs Hlbc
    Hbco Hfnc Hdwd Hbwb
  iintro %Φ Hpre HΦ
  iNamed Hpre
  ihave #HbootA := bootstrapAtR_of_restart cfg U γ id N dir σ i A D M $$ HbootR
  iapply h' $$ [-HΦ] HΦ
  iframe
  iframe %Hγn
  iframe %Haufit
  iframe %Hbuq
  iframe %Hdisk
  iframe %Hmmap
  iframe #

end spec

end EtcdGrove
end Perennial
