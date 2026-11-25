/- Lean-first (no Rocq counterpart).

# mvcc's randomized tester's closed theorem (2026-11-08)

A closed theorem about the operational semantics of `mvccrand`'s program (`examples/mvccrand`): the
package's initialization (which initializes its import closure: mvcc, the lessor, the backend,
zap, ...) followed by `Main()` -- a backend in the fresh file `mvccrand.db`, the lessor and the
store over it as etcd's server makes them, the writer's 1000 random operations, 4 readers and a
watch stream's registrar and receiver running concurrently, every result of mvcc checked against
the tester's model (a failed check panics), then the store, the lessor and the backend closed --
started from a fresh state (no package initialized, one thread): for every real execution of `n`
steps, the main thread's result, if it has one, is `#()`, no thread is stuck, and no thread has
ended in a panic. So no check of the tester fails, in any interleaving, within the executions it
covers.

**What it covers: each prefix of fewer than `2 ^ 28` steps** (as `mvccfull_adequate`, finding
mvcc-r3-1, round 3, 2026-11-11). The execution's length is bounded by the hypothesis
`n + 2 ≤ 2 ^ 28` (the thread bound). The theorem says no check fails in the first `2 ^ 28 - 2`
steps of any interleaving, and nothing about later steps. Whether a complete run of `Main` fits
under the bound has not been measured; `mvccfull`'s does not.

(S3e, 2026-11-17) **The program is `Run` of `Main`'s configuration with the file at an absolute
path** `r/mvccrand.db`, `r` a root of the file system's model: `Main`'s `mvccrand.db` is relative,
and the file extension gives meaning only to paths in its roots' trees (a step on any other path is
stuck, `GooseLang/Ext/Fs/Impl.lean`), which the backend's file now is (bbolt's proved `Open`, over the
file extension). Until then the theorem was about `Main()` over the trivial extension, where
bbolt's `Open`'s file operations are stuck too (the backend's file was an axiom, `fileHolds`).

(P3 of the pure-premise plan, 2026-11-24) **The program is `MainAt(r)`**, which checks `r` itself:
it returns without running unless `r` fits (`dirFits`, `Fs.DirFits r`) and nothing is at
`r/mvccrand.db` (`absent`: `os.Lstat` and `errors.Is(err, os.ErrNotExist)`), then runs `Run` of `Main`'s
configuration there. Until then `Fs.DirFits r` and the name's absence were hypotheses (`Hrfit`,
`Habs`); the proof now gets the root's claim from the tree at start (`start_rootClaim`), whatever
its names hold, and `MainAt`'s proof makes the fresh file from what `absent` found.

It follows from `goose_adequacy_start` (`Proof/runtime/Start.lean`: Perennial's `goose_adequacy`
whose WP proof also receives program start's rights, here `ETCD_VERIFY` off) over the etcd
examples' extensions (`etcdstart/FsExts.lean`: the request ids' record and the Linux file extension,
whose steps do not fail on files, `etcdSQ`) and a ghost-state bundle `mvccrandGF`, the fresh file
from the tree at start (`start_rootClaim`, `Proof/runtime/StartFiles.lean`: the claim on the root
`r`'s names, for `MainAt` to check), from `mvccrand`'s `wp_initialize'` (`Init.lean`, over the program's
package table `PkgTable.lean`) and `mvccrand.wp_Run` (`Link.lean`).

**Its hypotheses** (S3e: no longer `dbOpenOk` and `dbCloseOk`, bbolt's `Open` and `Close` not
failing, the user's decision of 2026-11-08: the semantics' steps do not fail on files, `etcdSQ`, and
the backend's `Open_kv`/`DB.Close_kv` are theorems with no error case; the two are `True` now):
* pure facts of the program's environment: `EtcdVerifyOff` (`ETCD_VERIFY` off) and the
  execution's length (prom-registry, route (b), 2026-11-22: no longer `namesUnclaimed` of
  `mvccrandNames`: the proof allocates the registration rights of the packages' metric IDs itself,
  `mvccrand_regQsOk`, and the default registry is client_golang's real code)
  (`n + 2 ≤ 2 ^ 28`: the thread bound, and with `N = n + 1` the receipt bound `2 ^ 48`;
  `mvccrand_adequate_below` takes the thread bound `T ≤ 2 ^ 28` along the execution instead, and
  only `n + 1 ≤ 2 ^ 48`);
* the semantics: `go.Semantics`, the package assumptions (`mvccrand`'s, mvcc's, the server's,
  the cache's) and (S3e) the `os` structs' field facts (`TrustedCode/os.lean`); the file extension's
  steps restricted by `etcdSQ` (no I/O error, no `flock`/`mmap`/`munmap` error, on any file);
* (S3e) the file extension's initial state: `FsInit` (the files as on disk), `r` a root (`j0` its
  directory) (until P3, 2026-11-24, also with no entry `mvccrand.db`, and `Fs.DirFits r`: `MainAt`
  checks both; until S3e the axiomatized `dbFilesAbsent`);
* (sortslice2, 2026-11-25) no longer, at every ghost-state instance, `sort.Slice`'s spec
  (`Spec/sort/Slice.lean`, deleted: unbounded, probably unprovable, `notes/specs-only/ledger.md`): the
  writer's `genLease` sorts with `slices.Sort`, proved. (Premise fixes 5, 2026-11-10) Until
  then also the store's key-count premise `keySized` (the backend's read states hold fewer than
  `2 ^ 62` keys), now proved (`mvcc.keySized_all`, from bbolt's address-space bound
  `backend.rtxSnap_size`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Results
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.runtime.StartFiles
public import Proof.runtime.Threads
public import Robustness.Statement
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.InitLinked

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

/-! ## The ghost-state bundle -/

/-- The universal camera at slot 0. -/
def mvccrandGF_allG : AllG mvccrandGF := ⟨⟨0, rfl⟩⟩

instance mvccrandGF_gooseGpreS : GooseGpreS mvccrandGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨mvccrandGF_allG⟩, ⟨mvccrandGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := mvccrandGF_allG

/-! ## The closed theorem -/

/-- The IDs the program's packages register (auth's, the lessor's, the backend's and mvcc's metric
names' label-free descriptor IDs, in `regQs`' order; computed with cespare/xxhash v2.3.0, and checked by
the kernel in `mvccrand_regQsOk`). -/
def mvccrandRegKeys : List w64 :=
  [0x12ecdedc778f3f77, 0x79b607416929bc6b, 0xb617c6d2d636f8d3, 0x8cdefdfd7fbe0f89,
   0x4d5dbff2abdff296, 0x7d293418f489e89, 0x1cf0310f1f3cbc4d, 0xaf13cf18762e0410,
   0xab20cb33e635a4d3, 0x4ea7aecf35604fe8, 0xdfccb0d5dbf98fee, 0x1329a594e50076ed,
   0xe21d9196734675f, 0x4f14727af435217b, 0x93f9374046090575, 0x1f18f72ac56b959b,
   0xb99f16de319e8327, 0x6f040a217f98b36f, 0x6e59011109180671, 0x11c28b1620be2404,
   0x7454d00abfa5eebd, 0x3990ae2951922721, 0xc6dbc11e1f9070ed, 0xee70855f50c035a7,
   0xe022592a562465ef, 0xc59e341e500edbf0, 0x4ff1a721c3c867d0, 0xddb5f8a18722005e,
   0x37b32b97f7de5f, 0x9c06bb0ca40cbda8, 0x23dbdcaf102f1686, 0x1de4f1c3b13fe482,
   0xe4ccc50c7daf4c9c, 0x9b8a677c6e6c1ef8, 0x7133d22463246355, 0xaa607cdd4f5c0a9a]

/-- **The registering packages' IDs can have their rights** (prom-registry, route (b)): pairwise
distinct, none a built-in's, no name a built-in's. Decided by the kernel once, here, over the IDs as
literals (`mvccrandRegKeys`: the kernel hashes each name once; deciding `regQsOk` directly rehashes the names
for every pair `Nodup` compares, and ran out of memory: 21 GB). -/
theorem mvccrand_regQsOk :
    prometheus.regQsOk github_com.mit_pdos.etcd_grove.examples.mvccrand.regQs :=
  prometheus.regQsOk_of_keys _ mvccrandRegKeys (by decide +kernel) (by decide +kernel) (by decide +kernel)

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **`mvccrand_adequate` along executions with fewer than `T ≤ 2 ^ 28` live threads**: the
same conclusion for every execution of `n` steps, `n + 1 ≤ 2 ^ 48` (the receipt bound the
proof needs), along which fewer than `T` threads are ever live at once (`RealNstepsBelow`): the
thread bound is a premise on the execution, not a consequence of its length
(`goose_adequacy_start`). -/
theorem mvccrand_adequate_below [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
    [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (r : GoString)
    (HEnv : EtcdVerifyOff)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (j0 : Fs.Ino)
    (Hr : (r, j0) ∈ (extLocal Fs.fsExt σ.world).fs.roots)
    (Hthreads : σ.threads = 1)
    (T : Nat) (HT28 : T ≤ 2 ^ 28)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([mvccrandProgram r], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 1 ≤ 2 ^ 48) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_adequacy_start (GF := mvccrandGF) (n + 1) T (mvccrandProgram r) σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) ⟨trivial, trivial, trivial⟩
    ⟨trivial, Hfs, trivial⟩ [] [] List.nodup_nil List.nodup_nil
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
    ?_ n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads
  intro hG HN HT HL
  obtain ⟨G, ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC mvccrandGF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs, th, cr⟩⟩
  -- the hypotheses at this instance (`heapWith` of it, definitionally)
  unfold IsInit at Hinit
  rw [Hinit]
  haveI : ThreadBoundLe mvccrandGF (2 ^ 28) := ⟨by rw [HT]; omega⟩
  haveI : ReceiptBoundLe mvccrandGF (2 ^ 48) := ⟨by rw [HN]; omega⟩
  iintro - Hl Hgs Htok Hrights
  iclear Hrights
  ihave #Hvoff : ⌜EtcdVerifyOff⌝ $$ []
  · ipureintro; exact HEnv
  -- (prom-registry, route (b)) the run's registration rights: a fresh ghost map of its packages' IDs,
  -- the run's registry name
  imod (prometheus.regKeys_alloc (GF := mvccrandGF) _ mvccrand_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS mvccrandGF := ⟨γreg⟩
  ihave Hregs := prometheus.idToks_regsFree (GF := mvccrandGF) _ $$ Hregs
  have Hst : extsLocalStart (GF := mvccrandGF) σ.world ⊢
      Fs.osStart (Fs.gooseOsGS (L := (inferInstance : HeapGS .hasLC mvccrandGF).goose_localGS))
        (extLocal Fs.fsExt σ.world) :=
    sep_elim_right.trans sep_elim_left
  ihave Hown := (ownInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.mvccrand.getIsPkgInit (GF := mvccrandGF))) $$ Hgs
  iapply start_rootClaim (extLocal Fs.fsExt σ.world) Hfs r j0 Hr _ _ $$ [Hl]
  · iapply Hst $$ Hl
  iintro Hroot
  unfold mvccrandProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.mvccrand.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.mvccrand.getIsPkgInit_wf) $$ [Hown Hregs] as ⟨-, #Hpkg⟩
  · iframe Hown Hregs
  wp_apply (mvccrand.wp_MainAt r) $$ [Hroot Htok]
  · iframe Hroot Htok Hvoff
  (try wp_auto)
  ipureintro
  rfl

/-- **mvcc's randomized tester passes** (see the file header): every real execution of
`mvccrandProgram r` from a fresh state with one thread, `r` a root of its file system (P3,
2026-11-24: no longer also with no entry `mvccrand.db` and fitting, which `MainAt` checks), of `n` steps: if the main thread has finished, its result is `#()` (`Run` returned:
every check of mvcc passed); no thread is stuck; no thread has ended in a panic. -/
theorem mvccrand_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
    [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (r : GoString)
    (HEnv : EtcdVerifyOff)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (j0 : Fs.Ino)
    (Hr : (r, j0) ∈ (extLocal Fs.fsExt σ.world).fs.roots)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([mvccrandProgram r], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  mvccrand_adequate_below r HEnv σ g Hlctx Hinit Hfs j0 Hr Hthreads (n + 2)
    (by omega) n κs t2 σ2 (RealNstepsBelow.of_one Hsteps Hthreads) (by omega)

end adequacy

#print axioms mvccrand_adequate
#print axioms mvccrand_adequate_below

end EtcdGrove
end Perennial
