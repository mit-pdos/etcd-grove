/- Lean-first (no Rocq counterpart).

# `etcd/all`: the single-process closed etcd theorem over the operational semantics, from `Main`'s triple

`etcd_adequate_of` (`notes/etcd-unified-scope.md` §3.2; `Results.lean` applies it to
`etcd_all.wp_Main` as `etcd_safe_single_process`; over the net extension since 2026-11-23,
`notes/single-process-restore.md`): every real execution of
`etcdProgram k₁ clients ops n₁ nw nops n₂ cnw cnops k₂ k₃ k₄ k₅` (`TopLevelDefs.lean`: the package's
initialization, then `MainChecked` with the five member counts, the three workloads and the two
schedules' lengths) from a fresh state with one thread and a network with no connection, of `n` steps
along which fewer than `2 ^ 28` threads are live, with `n + 1 ≤ 2 ^ 48`: if the main thread has
finished, its result is `#()`; no thread is stuck; no thread has ended in a panic.

It follows from `etcd_adequate_members_below`, in two cases (the pure-premises plan's P4, 2026-11-24:
the counts' and workloads' ranges are `MainChecked`'s check, no longer premises). When the parameters
are in range (`etcd_all.paramsOk`), with the eleven clusters' members (`etcdStarts`), their bridges
(`etcdBridges`), the program's addresses `etcdAddrs` and data directories `etcdDirs`, whose
distinctness is `Disjoint.lean`'s (for counts in range: out of range the addresses may collide). When
they are not, with no member, address or directory: `MainChecked` returns without starting any. The
proof of the body: `etcdall`'s `wp_initialize'` and `MainChecked`'s triple, here a hypothesis
(`hMain`), so that this module does not import the eleven drivers' linked results (split from
`AdequacyLinked.lean`).

Its premises are `etcd_robust_single_process.spec`'s (`Spec/.../examples/etcd/all/TopLevelRobustness.lean`) at one `n`;
`Hlow` (the condition of idutil's trusted model) is not used by the proof and is stated in
`Results.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AdequacyMembers
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Disjoint
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NetExts
public import Proof.runtime.Start
public import Proof.runtime.Threads

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem etcdFsSemOk etcdFsNoErr

/-! ## The ghost-state bundle -/

/-- The universal camera at slot 0. -/
def etcdGF_allG : AllG etcdGF := ⟨⟨0, rfl⟩⟩

instance etcdGF_gooseGpreS : GooseGpreS etcdGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨etcdGF_allG⟩, ⟨etcdGF_allG⟩, ⟨etcdGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := etcdGF_allG

/-- iris-lean's camera of non-atomic invariants, at slot 11: the instance porcupine's results
take. -/
instance etcdGF_naInvG : NaInvG etcdGF := ⟨⟨11, rfl⟩⟩

/-! ## The closed theorem -/

/-- The IDs the program's packages register (their metric names' label-free descriptor IDs and
`v3rpc`'s server metrics' IDs, in `regQs`' order; computed with xxhash64, and checked by the kernel in
`etcd_regQsOk`; prom-registry, route (b), 2026-11-23). -/
def etcdRegKeys : List w64 :=
  [0x12ecdedc778f3f77, 0x6ac118629bed5903, 0x4aa04489ac2b734b, 0x4ab58b8498228b63,
   0x31b044d75943f6dd, 0x5a080044ea5fdf1a, 0x958bb1c4f0e3d61, 0xd537c2a29197bfe6,
   0x38df0bda13eced78, 0xc5eca1b74fabe814, 0x714bc8e301bc1919, 0x7c09ff7fdc8bd9e2,
   0xca706d4e58b535eb, 0x7eaca73262315545, 0xcfa3e07e6efd0dda, 0x94a3ca5582a08ac8,
   0xf4dff1e237623d2, 0x9a0496b0ef986279, 0x6c3eea8e7dbd9701, 0x1c4edd07e42b3902,
   0xa41ef058a0a6b2e, 0x1ac7b57ed76461ba, 0xe6d60bdb6ca2ca2f, 0xe233596477e3f822,
   0xf4109d5f6085f482, 0x8d957e41d1d11d17, 0x1f7b18004d0507ca, 0x9e66b7f695a88383,
   0x606eb6c3266940a1, 0xccb7c98c879ff20c, 0xdca4bc9464724b6, 0xce41c40aa2166e13,
   0xe7cd4a7e1ce001f2, 0x6c80ca5a0a06a60f, 0xc415d620f8a840b3, 0xc174f386755af284,
   0x8e2ca5829b1415ca, 0xf76aa9ea6954a561, 0x79460c68f240b0ab, 0x50db1f551c79b595,
   0x84b7397632eb946f, 0x2b3902ff335816f9, 0x6a15a11de7b828c4, 0x342d1ac3e8fccf46,
   0x8652a92ef6ff21a5, 0x79b607416929bc6b, 0xb617c6d2d636f8d3, 0x8cdefdfd7fbe0f89,
   0x4d5dbff2abdff296, 0x2f589e3e7676603c, 0x7d293418f489e89, 0x1cf0310f1f3cbc4d,
   0xaf13cf18762e0410, 0xab20cb33e635a4d3, 0x4ea7aecf35604fe8, 0xdfccb0d5dbf98fee,
   0x1329a594e50076ed, 0xe21d9196734675f, 0x4f14727af435217b, 0x93f9374046090575,
   0x1f18f72ac56b959b, 0xb99f16de319e8327, 0x6f040a217f98b36f, 0x6e59011109180671,
   0x11c28b1620be2404, 0x7454d00abfa5eebd, 0x3990ae2951922721, 0xc6dbc11e1f9070ed,
   0xee70855f50c035a7, 0xe022592a562465ef, 0xc59e341e500edbf0, 0x4ff1a721c3c867d0,
   0xddb5f8a18722005e, 0x37b32b97f7de5f, 0x9c06bb0ca40cbda8, 0x23dbdcaf102f1686,
   0x1de4f1c3b13fe482, 0xe4ccc50c7daf4c9c, 0x9b8a677c6e6c1ef8, 0x7133d22463246355,
   0xaa607cdd4f5c0a9a, 0xb0bfadd1258d120e, 0xe5bc0e939f7dd45d, 0x35c8acd42298ce6b]

/-- **The registering packages' IDs can have their rights** (prom-registry, route (b)): pairwise
distinct, none a built-in's, no name a built-in's. Decided by the kernel once, over the IDs as literals
(`etcdRegKeys`; `mvccfull_regQsOk`). -/
theorem etcd_regQsOk : prometheus.regQsOk github_com.mit_pdos.etcd_grove.examples.etcd.all.regQs :=
  prometheus.regQsOk_of_keys _ etcdRegKeys (by decide +kernel) (by decide +kernel) (by decide +kernel)

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **The one closed etcd theorem, over the operational semantics, from `MainChecked`'s triple** (see
the file header). -/
theorem etcd_adequate_of [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [log.NewModel] [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (hMain : ∀ hG : HeapGS .hasLC etcdGF,
      etcd_all.MainChecked.spec (GF := etcdGF) (hG := etcdHeapAt hG lctx))
    (Hctx : ∀ hG : HeapGS .hasLC etcdGF, ContextReadErrs (GF := etcdGF) (hG := etcdHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC etcdGF, ContextErrsClient (GF := etcdGF) (hG := etcdHeapAt hG lctx))
    -- KV: txnlinfaultsN's cluster, `k₁` members
    (k₁ : w64) (ids₁ ps₁ : List w64) (ctxs₁ : List (List w8))
    (boot₁ : List LogEntry) (Hlen₁ : ids₁.length = uint.nat k₁)
    (Hbf₁ : etcd_txnlinfaultsN.BootFacts ids₁ ps₁ ctxs₁ boot₁)
    -- KV: partition's cluster (three members)
    (pid₁ pid₂ pid₃ : w64) (psP : List w64) (ctxsP : List (List w8)) (bootP : List LogEntry)
    (HbfP : etcd_partition.BootFacts pid₁ pid₂ pid₃ psP ctxsP bootP)
    -- KV: compactwatch's, compacted's and cache's one-member clusters
    (cwId : w64) (ctxsCW : List (List w8)) (bootCW : List LogEntry)
    (HbfCW : etcd_compactwatch.BootFacts cwId ctxsCW bootCW)
    (cId : w64) (ctxsC : List (List w8)) (bootC : List LogEntry)
    (HbfC : etcd_compacted.BootFacts cId ctxsC bootC)
    (kvId : w64) (ctxsK : List (List w8)) (bootK : List LogEntry)
    (HbfK : etcd_putget.BootFacts kvId ctxsK bootK)
    -- Auth: authN's cluster, `k₂` members, and authlease's, `k₃` (their ids apart in 15 bits)
    (k₂ : w64) (ids₂ ps₂ : List w64) (ctxs₂ : List (List w8))
    (boot₂ : List LogEntry) (Hlen₂ : ids₂.length = uint.nat k₂)
    (Hbf₂ : etcd_putgetN.BootFacts ids₂ ps₂ ctxs₂ boot₂)
    (k₃ : w64) (ids₃ ps₃ : List w64) (ctxs₃ : List (List w8))
    (boot₃ : List LogEntry) (Hlen₃ : ids₃.length = uint.nat k₃)
    (Hbf₃ : etcd_putgetN.BootFacts ids₃ ps₃ ctxs₃ boot₃) (Hap : leaseIdsApart ids₃)
    -- Lease: leaseN's cluster, `k₄` members, and leasecatchup's (three members)
    (k₄ : w64) (ids₄ ps₄ : List w64) (ctxs₄ : List (List w8))
    (boot₄ : List LogEntry) (Hlen₄ : ids₄.length = uint.nat k₄)
    (Hbf₄ : etcd_putgetN.BootFacts ids₄ ps₄ ctxs₄ boot₄)
    (lid₁ lid₂ lid₃ : w64) (psL : List w64) (ctxsL : List (List w8)) (bootL : List LogEntry)
    (HbfL : cluster3.BootFacts lid₁ lid₂ lid₃ psL ctxsL bootL)
    -- Restart: restartN's cluster, `k₅` members, and restart1's one member
    (k₅ : w64) (ids₅ ps₅ : List w64) (ctxs₅ : List (List w8))
    (boot₅ : List LogEntry) (Hlen₅ : ids₅.length = uint.nat k₅)
    (Hbf₅ : etcd_restartN.BootFacts ids₅ ps₅ ctxs₅ boot₅)
    (rId : w64) (ctxsR : List (List w8)) (bootR : List LogEntry)
    (HbfR : etcd_restart1.BootFacts rId ctxsR bootR)
    -- the server's workload and environment
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- peers answer `/leases/internal` as etcd's handler does or not with 200; no lease expires in the run
    (Hlp : leasePeersOk) (Hlne : lease.leasesNoExpiry)
    -- txnlinfaultsN's workload and its schedule's length; partition's; cache's workload
    (clients ops n₁ nw nops n₂ cnw cnops : w64)
    -- the program's addresses, data directories and environment
    (HAs : addrsUnclaimed (etcdProgram k₁ clients ops n₁ nw nops n₂ cnw cnops k₂ k₃ k₄ k₅)
      (etcdProgAddrs k₁ k₂ k₃ k₄ k₅))
    (HDs : dataDirsAbsent (etcdProgram k₁ clients ops n₁ nw nops n₂ cnw cnops k₂ k₃ k₄ k₅)
      (etcdProgDirs k₁ k₂ k₃ k₄ k₅))
    (HEnv : verifyEnvOff (etcdProgram k₁ clients ops n₁ nw nops n₂ cnw cnops k₂ k₃ k₄ k₅))
    (n : Nat)
    (Hprem₁ : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_txnlinfaultsN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₁) n ids₁
          ps₁ ctxs₁ boot₁)
    (HpremP : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_partition.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n pid₁ pid₂ pid₃ psP ctxsP
          bootP)
    (HpremCW : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_compactwatch.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n cwId ctxsCW bootCW)
    (HpremC : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_compacted.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n cId ctxsC bootC)
    (HpremK : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_cache.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n kvId ctxsK bootK)
    (Hprem₂ : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_authN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₂) n ids₂ ps₂ ctxs₂
          boot₂)
    (Hprem₃ : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_authlease.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₃) n ids₃ ps₃
          ctxs₃ boot₃)
    (Hprem₄ : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_leaseN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₄) n ids₄ ps₄
          ctxs₄ boot₄)
    (HpremL : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ cluster3.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) etcd_leasecatchup.clusterCfg n
          lid₁ lid₂ lid₃ psL ctxsL bootL)
    (Hprem₅ : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_restartN.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₅) n ids₅ ps₅
          ctxs₅ boot₅)
    (HpremR : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_restart1.premises (GF := etcdGF) (hG := etcdHeapAt hG lctx) n rId ctxsR bootR)
    (σ : state) (g : GlobalState) (Hg : extsInitGlobal g)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world)
      (etcdProgDirs k₁ k₂ k₃ k₄ k₅))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNstepsBelow (2 ^ 28) n
      ([etcdProgram k₁ clients ops n₁ nw nops n₂ cnw cnops k₂ k₃ k₄ k₅], ((σ, g) : CfgState))
      κs (t2, σ2))
    (Hn : n + 1 ≤ 2 ^ 48) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  by_cases hok : etcd_all.paramsOk k₁ clients ops nw nops cnw cnops k₂ k₃ k₄ k₅
  · -- in range: the eleven clusters' members, bridges, addresses and data directories
    obtain ⟨h1, h2, -, -, -, -, -, -, -, -, -, -, -, -, h21, h22, h31, h32, h41, h42, h51, h52⟩ :=
      id hok
    have hk₁ : uint.nat k₁ ≤ 1000 := by word
    have hk₂ : uint.nat k₂ ≤ 1000 := by word
    have hk₃ : uint.nat k₃ ≤ 1000 := by word
    have hk₄ : uint.nat k₄ ≤ 1000 := by word
    have hk₅ : uint.nat k₅ ≤ 1000 := by word
    have hc : etcdCountsOk k₁ k₂ k₃ k₄ k₅ := by unfold etcdCountsOk; and_intros <;> word
    unfold etcdProgAddrs at HAs
    unfold etcdProgDirs at HDs HWal
    rw [if_pos hc] at HAs HDs HWal
    refine etcd_adequate_members_below (GF := etcdGF) (hbody := rfl) (HWal := HWal) (hn := by omega)
      (hmsL := etcd_all.etcdStarts_names_len _ _ _ _ _)
      (hAsLit := etcd_all.etcdAddrs_lit _ _ _ _ _ hk₁ hk₂ hk₃ hk₄ hk₅)
      (hAsOk := etcd_all.etcdAddrs_ok _ _ _ _ _ hk₁ hk₂ hk₃ hk₄ hk₅)
      (HEnv := HEnv) github_com.mit_pdos.etcd_grove.examples.etcd.all.initialize'
      (App (App (App (App (App (App (App (App (App (App (App (App (App
        (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked))
        (Val #k₁)) (Val #clients)) (Val #ops)) (Val #n₁))
        (Val #nw)) (Val #nops)) (Val #n₂)) (Val #cnw)) (Val #cnops))
        (Val #k₂)) (Val #k₃)) (Val #k₄)) (Val #k₅))
      (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm)
      (etcdAddrs (uint.nat k₁) (uint.nat k₂) (uint.nat k₃) (uint.nat k₄) (uint.nat k₅))
      (etcd_all.etcdAddrs_nodup _ _ _ _ _ hk₁ hk₂ hk₃ hk₄ hk₅)
      (etcdDirs (uint.nat k₁) (uint.nat k₂) (uint.nat k₃) (uint.nat k₄) (uint.nat k₅))
      (etcd_all.etcdDirs_nodup _ _ _ _ _ hk₁ hk₂ hk₃ hk₄ hk₅)
      (etcd_all.etcdStarts (uint.nat k₁) (uint.nat k₂) (uint.nat k₃) (uint.nat k₄) (uint.nat k₅))
      (etcd_all.etcdBridges (uint.nat k₁))
      (etcd_all.etcdAddrs_perm _ _ _ _ _) (etcd_all.etcdDirs_perm _ _ _ _ _)
      σ g ⟨trivial, trivial, Hg.2.2.1, trivial⟩ ⟨trivial, Hfs, trivial, trivial⟩ Hlctx Hinit Hthreads
      github_com.mit_pdos.etcd_grove.examples.etcd.all.regQs etcd_regQsOk HAs HDs
      (2 ^ 28) n κs t2 σ2 Hsteps' fun hG HN HT => ?_
    intro _
    letI : HeapGS .hasLC etcdGF := etcdHeapAt hG lctx
    haveI := Hctx hG
    haveI := Hcec hG
    unfold progOk
    refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.etcd.all.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.etcd.all.getIsPkgInit_wf, ?_⟩
    ihave #Hp1 := Hprem₁ hG
    ihave #HpP := HpremP hG
    ihave #HpCW := HpremCW hG
    ihave #HpC := HpremC hG
    ihave #HpK := HpremK hG
    ihave #Hp2 := Hprem₂ hG
    ihave #Hp3 := Hprem₃ hG
    ihave #Hp4 := Hprem₄ hG
    ihave #HpL := HpremL hG
    ihave #Hp5 := Hprem₅ hG
    ihave #HpR := HpremR hG
    iintro #Hinit Htok ⟨Hms, Hbs⟩
    unfold etcd_all.etcdStarts etcd_all.etcdBridges
    icases Hms with ⟨⟨⟨⟨⟨⟨⟨⟨Hms1, HmsP⟩, HmsKV⟩, Hms2⟩, Hms3⟩, Hms4⟩, HmsL⟩, Hms5⟩, HmsR⟩
    icases Hbs with ⟨⟨Hbs1, HbsP⟩, HbsL⟩
    ihave HresP : cluster3.startRes (GF := etcdGF) etcd_partition.clusterCfg $$ [HmsP HbsP]
    · iapply cluster3.startRes_intro; iframe
    ihave HresL : cluster3.startRes (GF := etcdGF) etcd_leasecatchup.clusterCfg $$ [HmsL HbsL]
    · iapply cluster3.startRes_intro; iframe
    icases BigSepL.bigSepL_cons.1 $$ HmsKV with ⟨HresCW, HmsKV⟩
    icases BigSepL.bigSepL_cons.1 $$ HmsKV with ⟨HresC, HmsKV⟩
    icases BigSepL.bigSepL_cons.1 $$ HmsKV with ⟨HresK, -⟩
    icases BigSepL.bigSepL_cons.1 $$ HmsR with ⟨HresR, -⟩
    unfold etcd_txnlinfaultsN.startAddrs etcd_authN.startAddrs etcd_authlease.startAddrs
      etcd_leaseN.startAddrs etcd_restartN.startAddrs
    simp only [BigSepL.bigSepL_map]
    haveI : ThreadBoundLe etcdGF (2 ^ 28) := ⟨by rw [HT]; word⟩
    haveI : ReceiptBoundLe etcdGF (2 ^ 48) := ⟨by rw [HN]; omega⟩
    haveI : ReceiptBoundLe etcdGF (n + 1) := ⟨by rw [HN]; omega⟩
    have hM := hMain hG n k₁ ids₁ ps₁ ctxs₁ boot₁ pid₁ pid₂ pid₃ psP ctxsP bootP cwId ctxsCW bootCW
      cId ctxsC bootC kvId ctxsK bootK k₂ ids₂ ps₂ ctxs₂ boot₂ k₃ ids₃ ps₃ ctxs₃ boot₃
      k₄ ids₄ ps₄ ctxs₄ boot₄ lid₁ lid₂ lid₃ psL ctxsL bootL k₅ ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR
      clients ops n₁ nw nops n₂ cnw cnops (srvLevels_of_max HT)
      Hlen₁ Hbf₁ HbfP HbfCW HbfC HbfK Hlen₂ Hbf₂ Hlen₃ Hbf₃ Hap Hlen₄ Hbf₄ HbfL Hlen₅ Hbf₅ HbfR
      (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hrf Hdbo Hlp Hlne inferInstance
      EtcdGrove.rpctypesEtcdError_asTarget
    wp_apply hM $$ [Hms1 Hbs1 HresP HresCW HresC HresK Hms2 Hms3 Hms4 HresL Hms5 HresR Htok]
    · iframe; (try iframe #)
      iintro -
      iunfold etcd_all.startBundle
      iframe
    ipureintro
    rfl
  · -- out of range: `MainChecked` returns at once; no member, address or data directory
    refine etcd_adequate_members_below (GF := etcdGF) (hbody := rfl) (hn := by omega)
      (HWal := fun d hd => by cases hd) (hmsL := fun m hm => by cases hm)
      (hAsLit := fun a ha => by cases ha) (hAsOk := fun a ha => by cases ha)
      (HEnv := HEnv) github_com.mit_pdos.etcd_grove.examples.etcd.all.initialize'
      (App (App (App (App (App (App (App (App (App (App (App (App (App
        (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked))
        (Val #k₁)) (Val #clients)) (Val #ops)) (Val #n₁))
        (Val #nw)) (Val #nops)) (Val #n₂)) (Val #cnw)) (Val #cnops))
        (Val #k₂)) (Val #k₃)) (Val #k₄)) (Val #k₅))
      (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm)
      [] List.nodup_nil [] List.nodup_nil [] [] (List.Perm.refl _) (List.Perm.refl _)
      σ g ⟨trivial, trivial, Hg.2.2.1, trivial⟩ ⟨trivial, Hfs, trivial, trivial⟩ Hlctx Hinit Hthreads
      github_com.mit_pdos.etcd_grove.examples.etcd.all.regQs etcd_regQsOk
      (fun a ha => by cases ha) ⟨fun d hd => (by cases hd), List.Pairwise.nil⟩
      (2 ^ 28) n κs t2 σ2 Hsteps' fun hG HN HT => ?_
    intro _
    letI : HeapGS .hasLC etcdGF := etcdHeapAt hG lctx
    haveI := Hctx hG
    haveI := Hcec hG
    unfold progOk
    refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.etcd.all.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.etcd.all.getIsPkgInit_wf, ?_⟩
    ihave #Hp1 := Hprem₁ hG
    ihave #HpP := HpremP hG
    ihave #HpCW := HpremCW hG
    ihave #HpC := HpremC hG
    ihave #HpK := HpremK hG
    ihave #Hp2 := Hprem₂ hG
    ihave #Hp3 := Hprem₃ hG
    ihave #Hp4 := Hprem₄ hG
    ihave #HpL := HpremL hG
    ihave #Hp5 := Hprem₅ hG
    ihave #HpR := HpremR hG
    iintro #Hinit Htok -
    haveI : ThreadBoundLe etcdGF (2 ^ 28) := ⟨by rw [HT]; word⟩
    haveI : ReceiptBoundLe etcdGF (2 ^ 48) := ⟨by rw [HN]; omega⟩
    haveI : ReceiptBoundLe etcdGF (n + 1) := ⟨by rw [HN]; omega⟩
    have hM := hMain hG n k₁ ids₁ ps₁ ctxs₁ boot₁ pid₁ pid₂ pid₃ psP ctxsP bootP cwId ctxsCW bootCW
      cId ctxsC bootC kvId ctxsK bootK k₂ ids₂ ps₂ ctxs₂ boot₂ k₃ ids₃ ps₃ ctxs₃ boot₃
      k₄ ids₄ ps₄ ctxs₄ boot₄ lid₁ lid₂ lid₃ psL ctxsL bootL k₅ ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR
      clients ops n₁ nw nops n₂ cnw cnops (srvLevels_of_max HT)
      Hlen₁ Hbf₁ HbfP HbfCW HbfC HbfK Hlen₂ Hbf₂ Hlen₃ Hbf₃ Hap Hlen₄ Hbf₄ HbfL Hlen₅ Hbf₅ HbfR
      (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hrf Hdbo Hlp Hlne inferInstance
      EtcdGrove.rpctypesEtcdError_asTarget
    wp_apply hM $$ [Htok]
    · iframe; (try iframe #)
      iintro %h
      exact (hok h).elim
    ipureintro
    rfl

end adequacy

end EtcdGrove
end Perennial
