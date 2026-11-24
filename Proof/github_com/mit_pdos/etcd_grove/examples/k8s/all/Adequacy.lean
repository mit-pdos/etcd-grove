/- Lean-first (no Rocq counterpart).

# `k8s/all`: the one closed Kubernetes theorem over the operational semantics

`k8s_adequate` (`notes/k8s-unified-scope.md`, §3.3; restated as `k8s_safe_single_process` in `Results.lean`): every
real execution of `k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂` (`TopLevelDefs.lean`: the
package's initialization, then `MainChecked` with the two member counts, the workload and the two
schedules' lengths) from a fresh
state with one thread, of `n` steps: if the main thread has finished, its result is `#()`; no thread is
stuck; no thread has ended in a panic (no porcupine check of the store's history fails, no API
server's compactor check fails).

It follows from `etcd_adequate_alloc_members` with the members of both clusters (the store cluster's
`k8s_etcd3N.startAddrs k₁`, then the compactor cluster's `k8s_compactorN.startAddrs k₂`), their
bridges, the program's addresses `k8sAddrs k₁ k₂` and data directories `k8sDirs k₁ k₂`, whose
distinctness is `Disjoint.lean`'s; the compactor registry is allocated before the program's proof is
chosen, as the compactor driver's retired closed theorems did, and `Main` receives its claims'
authority with no endpoint claimed. The proof of the body: `k8sall`'s `wp_initialize'` and
`k8s_all.wp_MainChecked` (`MainLinked.lean`). (The pure-premises plan's P5, 2026-11-24) In two cases:
the member counts and the workload in range (`k8s_all.paramsOk`, `MainChecked`'s check), as above;
out of range, with no member, address or directory, `MainChecked` returning at once (out of range the
addresses may collide, `Disjoint.lean`'s facts being for counts in range).

Its premises are the two retired partition theorems' (`k8s_etcd3_partition_adequate`,
`k8s_compactor_partition_adequate`), once where they coincide; `Hlow` (`k8s_safe_single_process`'s, the condition of
idutil's trusted model) is not used by the proof and is stated in `Results.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AdequacyMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.Disjoint
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.TopLevelDefs
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
def k8sGF_allG : AllG k8sGF := ⟨⟨0, rfl⟩⟩

instance k8sGF_gooseGpreS : GooseGpreS k8sGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨k8sGF_allG⟩, ⟨k8sGF_allG⟩, ⟨k8sGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := k8sGF_allG

/-- iris-lean's camera of non-atomic invariants, at slot 11: the instance porcupine's results
take. -/
instance k8sGF_naInvG : NaInvG k8sGF := ⟨⟨11, rfl⟩⟩

/-! ## The closed theorem -/

/-- The IDs the program's packages register (their metric names' label-free descriptor IDs and
`v3rpc`'s server metrics' IDs, in `regQs`' order; computed with xxhash64, and checked by the kernel in
`k8s_regQsOk`; prom-registry, route (b), 2026-11-23). -/
def k8sRegKeys : List w64 :=
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
(`k8sRegKeys`; `mvccfull_regQsOk`). -/
theorem k8s_regQsOk : prometheus.regQsOk github_com.mit_pdos.etcd_grove.examples.k8s.all.regQs :=
  prometheus.regQsOk_of_keys _ k8sRegKeys (by decide +kernel) (by decide +kernel) (by decide +kernel)

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **`k8s_adequate` along executions with fewer than `2 ^ 28` live threads** (2026-11-22, as
`etcd/all`'s `etcd_adequate_of` since 2026-11-20): the same conclusion for every execution of `n`
steps, `n + 1 ≤ 2 ^ 48` (the receipt bound of the server's request ids; until 2026-11-22 `n + 12 ≤ 2 ^ 40`, the backend's write-back budget), along which fewer than
`2 ^ 28` threads are ever live at once (`RealNstepsBelow`, through
`etcd_adequate_alloc_members_below`): the thread bound is a premise on the execution, not a
consequence of its length. -/
theorem k8s_adequate_below [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC k8sGF, ContextReadErrs (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8sGF, ContextErrsClient (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hafter : ∀ hG : HeapGS .hasLC k8sGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    -- the store's cluster: `k₁` members
    (k₁ : w64) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (Hlen : ids.length = uint.nat k₁)
    (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    -- the compactor's cluster: `k₂` members
    (k₂ : w64) (ids' : List w64) (ps' : List w64)
    (ctxs' : List (List w8)) (boot' : List LogEntry) (Hlen' : ids'.length = uint.nat k₂)
    (Hbf' : k8s_compactorN.BootFacts ids' ps' ctxs' boot')
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- the store's workload and the two schedules' lengths (any values: `MainChecked` checks them)
    (clients ops watchers wops n₁ n₂ : w64)
    (HAs : addrsUnclaimed (k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂)
      (k8sProgAddrs k₁ k₂))
    (HDs : dataDirsAbsent (k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂)
      (k8sProgDirs k₁ k₂))
    (HEnv : verifyEnvOff (k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂))
    (n : Nat)
    (Hprem₁ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_etcd3N.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) (uint.nat k₁) n ids ps ctxs boot)
    (Hprem₂ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_compactorN.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) (uint.nat k₂) n ids' ps'
          ctxs' boot')
    (σ : state) (g : GlobalState) (Hg : extsInitGlobal g) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (k8sProgDirs k₁ k₂))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNstepsBelow (2 ^ 28) n ([k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂],
      ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 1 ≤ 2 ^ 48) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  by_cases hok : k8s_all.paramsOk k₁ clients ops watchers wops k₂
  · -- in range: both clusters' members, bridges, addresses and data directories
    obtain ⟨h1, h2, h21, h22, -, -, -, -, -, -⟩ := id hok
    have hk₁ : uint.nat k₁ ≤ 1000 := by word
    have hk₂ : uint.nat k₂ ≤ 1000 := by word
    have hc : k8sCountsOk k₁ k₂ := by unfold k8sCountsOk; and_intros <;> word
    unfold k8sProgAddrs at HAs
    unfold k8sProgDirs at HDs HWal
    rw [if_pos hc] at HAs HDs HWal
    refine etcd_adequate_alloc_members_below (GF := k8sGF) (hbody := rfl) (HWal := HWal)
      (hn := by omega)
      (hmsL := fun m hm => (List.mem_append.1 hm).elim
        (k8s_etcd3N.startAddrs_names_len (uint.nat k₁) m)
        (k8s_compactorN.startAddrs_names_len (uint.nat k₂) m))
      (hAsLit := k8s_all.k8sAddrs_lit _ _ hk₁ hk₂) (hAsOk := k8s_all.k8sAddrs_ok _ _ hk₁ hk₂)
      (HEnv := HEnv)
      github_com.mit_pdos.etcd_grove.examples.k8s.all.initialize'
      (App (App (App (App (App (App (App (App
        (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.all.MainChecked))
        (Val #k₁)) (Val #clients)) (Val #ops)) (Val #watchers)) (Val #wops)) (Val #n₁))
        (Val #k₂)) (Val #n₂))
      (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm)
      (k8sAddrs (uint.nat k₁) (uint.nat k₂)) (k8s_all.k8sAddrs_nodup _ _ hk₁ hk₂)
      (k8sDirs (uint.nat k₁) (uint.nat k₂)) (k8s_all.k8sDirs_nodup _ _ hk₁ hk₂)
      (k8s_etcd3N.startAddrs (uint.nat k₁) ++ k8s_compactorN.startAddrs (uint.nat k₂))
      (k8s_etcd3N.bridges (uint.nat k₁) ++ k8s_compactorN.bridges (uint.nat k₂))
      (k8s_all.k8sAddrs_perm _ _) (k8s_all.k8sDirs_perm _ _)
      σ g ⟨trivial, trivial, Hg.2.2.1, trivial⟩ ⟨trivial, Hfs, trivial, trivial⟩ Hlctx Hinit Hthreads
      github_com.mit_pdos.etcd_grove.examples.k8s.all.regQs k8s_regQsOk HAs HDs
      (2 ^ 28) n κs t2 σ2 Hsteps' fun hG HN HT => ?_
    intro _
    letI : HeapGS .hasLC k8sGF := k8sHeapAt hG lctx
    -- the compactor registry, allocated before the program's proof is chosen (as the compactor
    -- driver's retired closed theorems): `Main` receives the claims' authority, no endpoint claimed
    refine ⟨GName, fun γ => EtcdGrove.k8s.regAuth (reg := ⟨γ⟩) (∅ : GMap GoString GName),
      EtcdGrove.k8s.regAuth_alloc, fun γ => ?_⟩
    letI : EtcdGrove.k8s.CompactorRegistry := ⟨γ⟩
    haveI := Hctx hG
    haveI := Hcec hG
    unfold progOk
    refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.k8s.all.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.k8s.all.getIsPkgInit_wf, ?_⟩
    ihave #Hp1 := Hprem₁ hG
    ihave #Hp2 := Hprem₂ hG
    iintro #Hinit Htok ⟨⟨Hms, Hbs⟩, Hreg⟩
    icases Hms with ⟨Hms1, Hms2⟩
    icases Hbs with ⟨Hbs1, Hbs2⟩
    unfold k8s_etcd3N.startAddrs k8s_compactorN.startAddrs
    rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
    haveI : ThreadBoundLe k8sGF (2 ^ 28) := ⟨by rw [HT]; word⟩
    haveI : ReceiptBoundLe k8sGF (2 ^ 48) := ⟨by rw [HN]; omega⟩
    haveI : ReceiptBoundLe k8sGF (n + 1) := ⟨by rw [HN]; omega⟩
    have hM := k8s_all.wp_MainChecked (GF := k8sGF) (Hafter hG) k₁ n ids ps ctxs boot k₂ ids' ps'
      ctxs' boot' clients ops watchers wops n₁ n₂ (srvLevels_of_max HT) Hlen Hbf Hlen' Hbf'
      (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hrf Hdbo inferInstance
      EtcdGrove.rpctypesEtcdError_asTarget k8s_etcd3.storageErrTyOk_holds k8s_etcd3.objTyOk_holds
    wp_apply hM $$ [Hms1 Hbs1 Hms2 Hbs2 Htok Hreg]
    · iframe; (try iframe #)
      iintro -
      iunfold k8s_all.startBundle
      iframe
    ipureintro
    rfl
  · -- out of range: `MainChecked` returns at once; no member, address or data directory
    refine etcd_adequate_alloc_members_below (GF := k8sGF) (hbody := rfl) (hn := by omega)
      (HWal := fun d hd => by cases hd) (hmsL := fun m hm => by cases hm)
      (hAsLit := fun a ha => by cases ha) (hAsOk := fun a ha => by cases ha)
      (HEnv := HEnv)
      github_com.mit_pdos.etcd_grove.examples.k8s.all.initialize'
      (App (App (App (App (App (App (App (App
        (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.all.MainChecked))
        (Val #k₁)) (Val #clients)) (Val #ops)) (Val #watchers)) (Val #wops)) (Val #n₁))
        (Val #k₂)) (Val #n₂))
      (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm)
      [] List.nodup_nil [] List.nodup_nil [] [] (List.Perm.refl _) (List.Perm.refl _)
      σ g ⟨trivial, trivial, Hg.2.2.1, trivial⟩ ⟨trivial, Hfs, trivial, trivial⟩ Hlctx Hinit Hthreads
      github_com.mit_pdos.etcd_grove.examples.k8s.all.regQs k8s_regQsOk
      (fun a ha => by cases ha) ⟨fun d hd => (by cases hd), List.Pairwise.nil⟩
      (2 ^ 28) n κs t2 σ2 Hsteps' fun hG HN HT => ?_
    intro _
    letI : HeapGS .hasLC k8sGF := k8sHeapAt hG lctx
    refine ⟨GName, fun γ => EtcdGrove.k8s.regAuth (reg := ⟨γ⟩) (∅ : GMap GoString GName),
      EtcdGrove.k8s.regAuth_alloc, fun γ => ?_⟩
    letI : EtcdGrove.k8s.CompactorRegistry := ⟨γ⟩
    haveI := Hctx hG
    haveI := Hcec hG
    unfold progOk
    refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.k8s.all.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.k8s.all.getIsPkgInit_wf, ?_⟩
    ihave #Hp1 := Hprem₁ hG
    ihave #Hp2 := Hprem₂ hG
    iintro #Hinit Htok ⟨-, Hreg⟩
    haveI : ThreadBoundLe k8sGF (2 ^ 28) := ⟨by rw [HT]; word⟩
    haveI : ReceiptBoundLe k8sGF (2 ^ 48) := ⟨by rw [HN]; omega⟩
    haveI : ReceiptBoundLe k8sGF (n + 1) := ⟨by rw [HN]; omega⟩
    have hM := k8s_all.wp_MainChecked (GF := k8sGF) (Hafter hG) k₁ n ids ps ctxs boot k₂ ids' ps'
      ctxs' boot' clients ops watchers wops n₁ n₂ (srvLevels_of_max HT) Hlen Hbf Hlen' Hbf'
      (by unfold bootWB backend.wbInit; omega) Haf Hbuq Hrf Hdbo inferInstance
      EtcdGrove.rpctypesEtcdError_asTarget k8s_etcd3.storageErrTyOk_holds k8s_etcd3.objTyOk_holds
    wp_apply hM $$ [Htok Hreg]
    · iframe; (try iframe #)
      iintro %h
      exact (hok h).elim
    ipureintro
    rfl

/-- **The one closed Kubernetes theorem, over the operational semantics** (see the file header):
every real execution of `k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂` from a fresh state
with one thread, of `n` steps: if the main thread has finished, its result is `#()`; no thread is stuck; no
thread has ended in a panic. -/
theorem k8s_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC k8sGF, ContextReadErrs (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8sGF, ContextErrsClient (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    (Hafter : ∀ hG : HeapGS .hasLC k8sGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8sGF) (hG := k8sHeapAt hG lctx))
    -- the store's cluster: `k₁` members
    (k₁ : w64) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (Hlen : ids.length = uint.nat k₁)
    (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    -- the compactor's cluster: `k₂` members
    (k₂ : w64) (ids' : List w64) (ps' : List w64)
    (ctxs' : List (List w8)) (boot' : List LogEntry) (Hlen' : ids'.length = uint.nat k₂)
    (Hbf' : k8s_compactorN.BootFacts ids' ps' ctxs' boot')
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- the store's workload and the two schedules' lengths (any values: `MainChecked` checks them)
    (clients ops watchers wops n₁ n₂ : w64)
    (HAs : addrsUnclaimed (k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂)
      (k8sProgAddrs k₁ k₂))
    (HDs : dataDirsAbsent (k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂)
      (k8sProgDirs k₁ k₂))
    (HEnv : verifyEnvOff (k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂))
    (n : Nat)
    (Hprem₁ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_etcd3N.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) (uint.nat k₁) n ids ps ctxs boot)
    (Hprem₂ : ∀ hG : HeapGS .hasLC k8sGF,
      ⊢ k8s_compactorN.premises (GF := k8sGF) (hG := k8sHeapAt hG lctx) (uint.nat k₂) n ids' ps'
          ctxs' boot')
    (σ : state) (g : GlobalState) (Hg : extsInitGlobal g) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (k8sProgDirs k₁ k₂))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([k8sProgram k₁ clients ops watchers wops n₁ k₂ n₂],
      ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  k8s_adequate_below Hctx Hcec Hafter k₁ ids ps ctxs boot Hlen Hbf k₂ ids' ps' ctxs' boot' Hlen' Hbf'
    Haf Hbuq Hrf Hdbo clients ops watchers wops n₁ n₂ HAs HDs HEnv n Hprem₁ Hprem₂ σ g Hg Hfs HWal
    Hlctx Hinit Hthreads κs t2 σ2 ((RealNstepsBelow.of_one Hsteps' Hthreads).mono (by omega)) (by omega)

end adequacy

end EtcdGrove
end Perennial
