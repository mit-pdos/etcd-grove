/- Lean-first (no Rocq counterpart).

# `etcd/all`: the single-process closed etcd theorem over the operational semantics, from `Main`'s triple

`etcd_adequate_of` (`notes/etcd-unified-scope.md` §3.2; `Results.lean` applies it to
`etcd_all.wp_MainChecked` as `etcd_restart_safe_single_process`; over the net extension since 2026-11-23,
`notes/single-process-restore.md`): every real execution of
`etcdProgram k₅` (`TopLevelDefs.lean`: the package's initialization, then `MainChecked` with restartN's
member count) from a fresh state with one thread and a network with no connection, of `n` steps
along which fewer than `2 ^ 28` threads are live, with `n + 1 ≤ 2 ^ 48`: if the main thread has
finished, its result is `#()`; no thread is stuck; no thread has ended in a panic.

It follows from `etcd_adequate_members_below`, in two cases (the pure-premises plan's P4, 2026-11-24:
the count's range is `MainChecked`'s check, no longer a premise). When the parameter is in range
(`etcd_all.paramsOk`), with the two clusters' members (`etcdStarts`), no bridge (`etcdBridges`), the
program's addresses `etcdAddrs` and data directories `etcdDirs`, whose distinctness is
`Disjoint.lean`'s. When it is not, with no member, address or directory: `MainChecked` returns without
starting any. The proof of the body: `etcdall`'s `wp_initialize'` and `MainChecked`'s triple, here a
hypothesis (`hMain`), so that this module does not import the drivers' linked results (split from
`AdequacyLinked.lean`).

Its premises are `etcd_restart_robust_single_process.spec`'s (`Spec/.../examples/etcd/all/TopLevelRobustness.lean`) at one `n`;
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.bootstrapOne
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.bootstrapRestart

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
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    (hMain : ∀ hG : HeapGS .hasLC etcdGF,
      etcd_all.MainChecked.spec (GF := etcdGF) (hG := etcdHeapAt hG lctx))
    -- restartN's cluster, `k₅` members, and restart1's one member
    (k₅ : w64) (ids₅ ps₅ : List w64) (ctxs₅ : List (List w8))
    (boot₅ : List LogEntry) (Hlen₅ : ids₅.length = uint.nat k₅)
    (Hbf₅ : etcd_restartN.BootFacts ids₅ ps₅ ctxs₅ boot₅)
    (rId : w64) (ctxsR : List (List w8)) (bootR : List LogEntry)
    (HbfR : etcd_restart1.BootFacts rId ctxsR bootR)
    -- `bootstrap`'s values Go's
    (Hbg₅ : etcd_restartN.BootGoN (uint.nat k₅) ids₅ ps₅ ctxs₅)
    (HbgR : etcd_restart1.BootGo rId ctxsR bootR)
    -- the server's workload and environment
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    -- the program's addresses, data directories and environment
    (HAs : addrsUnclaimed (etcdProgram k₅) (etcdProgAddrs k₅))
    (HDs : dataDirsAbsent (etcdProgram k₅) (etcdProgDirs k₅))
    (HEnv : EtcdVerifyOff) (Hfips : crypto.fips140.GodebugFips140Off)
    (n : Nat)
    (Hprem₅ : ∀ hG : HeapGS .hasLC etcdGF,
      ⊢ etcd_restartN.bootPremises (GF := etcdGF) (hG := etcdHeapAt hG lctx) (uint.nat k₅) n ids₅ ps₅
          ctxs₅ boot₅)
    (σ : state) (g : GlobalState) (Hg : extsInitGlobal g)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (etcdProgDirs k₅))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNstepsBelow (2 ^ 28) n ([etcdProgram k₅], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 1 ≤ 2 ^ 48) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  by_cases hok : etcd_all.paramsOk k₅
  · -- in range: the two clusters' members, addresses and data directories
    obtain ⟨h51, h52⟩ := id hok
    have hk₅ : uint.nat k₅ ≤ 1000 := by word
    have hc : etcdCountsOk k₅ := by unfold etcdCountsOk; and_intros <;> word
    unfold etcdProgAddrs at HAs
    unfold etcdProgDirs at HDs HWal
    rw [if_pos hc] at HAs HDs HWal
    refine etcd_adequate_members_below (GF := etcdGF) (hbody := rfl) (HWal := HWal) (hn := by omega)
      (hmsL := etcd_all.etcdStarts_names_len _)
      (hAsLit := etcd_all.etcdAddrs_lit _ hk₅)
      (hAsOk := etcd_all.etcdAddrs_ok _ hk₅)
      (HEnv := HEnv) github_com.mit_pdos.etcd_grove.examples.etcd.all.initialize'
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked)) (Val #k₅))
      (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm)
      (etcdAddrs (uint.nat k₅)) (etcd_all.etcdAddrs_nodup _ hk₅)
      (etcdDirs (uint.nat k₅)) (etcd_all.etcdDirs_nodup _ hk₅)
      (etcd_all.etcdStarts (uint.nat k₅)) etcd_all.etcdBridges
      (etcd_all.etcdAddrs_perm _) (etcd_all.etcdDirs_perm _)
      σ g ⟨trivial, trivial, Hg.2.2.1, trivial⟩ ⟨trivial, Hfs, trivial, trivial⟩ Hlctx Hinit Hthreads
      github_com.mit_pdos.etcd_grove.examples.etcd.all.regQs etcd_regQsOk HAs HDs
      (2 ^ 28) n κs t2 σ2 Hsteps' fun hG HN HT => ?_
    intro _
    letI : HeapGS .hasLC etcdGF := etcdHeapAt hG lctx
    unfold progOk
    refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.etcd.all.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.etcd.all.getIsPkgInit_wf, ?_⟩
    haveI : ThreadBoundLe etcdGF (2 ^ 28) := ⟨by rw [HT]; word⟩
    haveI : ThreadBoundLe etcdGF (2 ^ 29) := ⟨by rw [HT]; word⟩
    haveI : ReceiptBoundLe etcdGF (2 ^ 48) := ⟨by rw [HN]; omega⟩
    haveI : ReceiptBoundLe etcdGF (2 ^ 60) := ⟨by rw [HN]; omega⟩
    haveI : ReceiptBoundLe etcdGF (n + 1) := ⟨by rw [HN]; omega⟩
    ihave #Hbp5 := Hprem₅ hG
    iintro #Hinit Htok ⟨Hms, -⟩
    -- (premises to axioms, 2026-11-27) the restart contracts and restart1's first-start contract from the
    -- interim bootstrap axioms (until then in the premises `Hprem₅`, `HpremR`)
    ihave #Hsrvpkg : isPkgInit (PROP := IProp etcdGF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
    · iPkgInit
    ihave #Hp5 := etcd_restartN.premises_of_specRestart (fun [_] => _root_.Perennial.EtcdGrove.bootstrap.wp_proofRestart)
      (uint.nat k₅) n ids₅ ps₅ ctxs₅ boot₅ Hfips Hbf₅ Hbg₅
      (by rw [etcdstart.membersOf_length, Hlen₅]) $$ Hsrvpkg Hbp5
    ihave #HpR := etcd_restart1.premises_of_specs (fun [_] => _root_.Perennial.EtcdGrove.bootstrap.wp_proofOne)
      (fun [_] => _root_.Perennial.EtcdGrove.bootstrap.wp_proofRestart) n rId ctxsR bootR Hfips HbgR $$ Hsrvpkg
    unfold etcd_all.etcdStarts
    icases Hms with ⟨Hms5, HmsR⟩
    icases BigSepL.bigSepL_cons.1 $$ HmsR with ⟨HresR, -⟩
    unfold etcd_restartN.startAddrs
    simp only [BigSepL.bigSepL_map]
    have hM := hMain hG n k₅ ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR (srvLevels_of_max HT)
      Hlen₅ Hbf₅ HbfR (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hdbo
    wp_apply hM $$ [Hms5 HresR Htok]
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
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked)) (Val #k₅))
      (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm)
      [] List.nodup_nil [] List.nodup_nil [] [] (List.Perm.refl _) (List.Perm.refl _)
      σ g ⟨trivial, trivial, Hg.2.2.1, trivial⟩ ⟨trivial, Hfs, trivial, trivial⟩ Hlctx Hinit Hthreads
      github_com.mit_pdos.etcd_grove.examples.etcd.all.regQs etcd_regQsOk
      (fun a ha => by cases ha) ⟨fun d hd => (by cases hd), List.Pairwise.nil⟩
      (2 ^ 28) n κs t2 σ2 Hsteps' fun hG HN HT => ?_
    intro _
    letI : HeapGS .hasLC etcdGF := etcdHeapAt hG lctx
    unfold progOk
    refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.etcd.all.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.etcd.all.getIsPkgInit_wf, ?_⟩
    haveI : ThreadBoundLe etcdGF (2 ^ 28) := ⟨by rw [HT]; word⟩
    haveI : ThreadBoundLe etcdGF (2 ^ 29) := ⟨by rw [HT]; word⟩
    haveI : ReceiptBoundLe etcdGF (2 ^ 48) := ⟨by rw [HN]; omega⟩
    haveI : ReceiptBoundLe etcdGF (2 ^ 60) := ⟨by rw [HN]; omega⟩
    haveI : ReceiptBoundLe etcdGF (n + 1) := ⟨by rw [HN]; omega⟩
    ihave #Hbp5 := Hprem₅ hG
    iintro #Hinit Htok -
    -- (premises to axioms, 2026-11-27) the restart contracts and restart1's first-start contract from the
    -- interim bootstrap axioms (until then in the premises `Hprem₅`, `HpremR`)
    ihave #Hsrvpkg : isPkgInit (PROP := IProp etcdGF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
    · iPkgInit
    ihave #Hp5 := etcd_restartN.premises_of_specRestart (fun [_] => _root_.Perennial.EtcdGrove.bootstrap.wp_proofRestart)
      (uint.nat k₅) n ids₅ ps₅ ctxs₅ boot₅ Hfips Hbf₅ Hbg₅
      (by rw [etcdstart.membersOf_length, Hlen₅]) $$ Hsrvpkg Hbp5
    ihave #HpR := etcd_restart1.premises_of_specs (fun [_] => _root_.Perennial.EtcdGrove.bootstrap.wp_proofOne)
      (fun [_] => _root_.Perennial.EtcdGrove.bootstrap.wp_proofRestart) n rId ctxsR bootR Hfips HbgR $$ Hsrvpkg
    have hM := hMain hG n k₅ ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR (srvLevels_of_max HT)
      Hlen₅ Hbf₅ HbfR (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hdbo
    wp_apply hM $$ [Htok]
    · iframe; (try iframe #)
      iintro %h
      exact (hok h).elim
    ipureintro
    rfl

end adequacy

end EtcdGrove
end Perennial
