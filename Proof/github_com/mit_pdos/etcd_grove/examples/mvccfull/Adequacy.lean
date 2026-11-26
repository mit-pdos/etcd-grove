/- Lean-first (no Rocq counterpart).

# mvcc's full tester's closed theorem (2026-11-10)

A closed theorem about the operational semantics of `mvccfull`'s program (`examples/mvccfull`): the
package's initialization (which initializes its import closure: mvcc, the lessor, the backend,
zap, ...) followed by `Main()` -- `Run(MainConfig("mvccfull"))`: two members (a leader and a
follower), each a backend in a fresh file, a lessor and a store over it as etcd's server makes them,
the writer's 12000 log steps (puts, deletes, transactions, lease grants and revokes, compactions,
snapshot installs into fresh builder stores, clean restarts), 2 readers per member and 2 watch
streams per member running concurrently, every result of mvcc checked against the tester's model
(a failed check panics), then each member's streams drained and closed, its store closed, reopened
and read in full, and closed -- started from a fresh state (no package initialized, one thread):
for every real execution of `n` steps, the main thread's result, if it has one, is `#()`, no thread
is stuck, and no thread has ended in a panic. So no check of the tester fails, in any
interleaving, within the executions it covers.

**What it covers: each prefix of fewer than `2 ^ 28` steps** (finding mvcc-r3-1, round 3,
2026-11-11). The execution's length is bounded by the hypothesis `n + 2 ≤ 2 ^ 28` (the thread
bound), and a full-size run of `Main` (12000 writer steps, with readers and watch streams on two
members, each over a bbolt-backed store) takes more steps than that. The theorem therefore says no
check fails in the first `2 ^ 28 - 2` steps of any interleaving. It says nothing about a run's later
steps, and in particular it does not say that a complete run of `Main` returns.

(S3e, 2026-11-17) **The program is `Run(MainConfig(r/mvccfull))`**, `Main`'s run with its files in
a root `r` of the file system's model (`Main`'s prefix `mvccfull` is relative, and the file extension
gives meaning only to paths in its roots' trees; until then the theorem was about `Main()` over the
trivial extension, where bbolt's file operations are stuck). As `mvccrand_adequate`
(`examples/mvccrand/Adequacy.lean`): from `goose_adequacy_start` (`Proof/runtime/Start.lean`) over
the etcd examples' extensions with the no-file-error semantics (`etcdstart/FsExts.lean`), the fresh
files from the tree at start (`start_fileHolds`, `Proof/runtime/StartFiles.lean`), a ghost-state
bundle `mvccfullGF`, `mvccfull`'s `wp_initialize'` (`Init.lean`, over the
program's package table `PkgTable.lean`) and `mvccfull.wp_Main` (`Link.lean`; `Results.lean`'s
`mvccfull_Main`). The program's fresh files are `FilePaths(MainConfig("mvccfull"))`
(`filePathsM`: the members' two and one per possible snapshot install, `Ops = 12000`), distinct
(`filePaths_main_nodup`).

(P3 of the pure-premise plan, 2026-11-24) **The program is `MainAt(r)`**, which checks `r` itself: it
returns without running unless `r` fits (`dirFits`, `Fs.DirFits r`) and nothing is at any of those
paths (`absent` of each: `os.Lstat` and `errors.Is(err, os.ErrNotExist)`), then runs
`Run(MainConfig(r/mvccfull))`. Until then `Fs.DirFits r` and the names' absence were hypotheses
(`Hrfit`, `Habs`); the proof now gets the root's claim from the tree at start (`start_rootClaim`), and
`MainAt`'s proof makes the fresh files from what `absent` found (the names' facts in `FileNames.lean`).

**Its hypotheses** are mvccrand's, but `sort.Slice.spec` (`mvccfull.wp_Main` takes no hypothesis:
the tester's lease checks compare the lessor's list against the model's without sorting it):
* pure facts of the program's environment: `EtcdVerifyOff` (`ETCD_VERIFY` off) and the execution's
  length (prom-registry, route (b), 2026-11-22: no longer `namesUnclaimed` of `mvccfullMetricNames`:
  the proof allocates the registration rights of the packages' metric IDs itself, `mvccfull_regQsOk`)
  (`n + 2 ≤ 2 ^ 28`: the thread bound, and with `N = n + 1` the receipt bound `2 ^ 48`;
  `mvccfull_adequate_below` takes the thread bound `T ≤ 2 ^ 28` along the execution instead, and
  only `n + 1 ≤ 2 ^ 48`);
* the semantics: `go.Semantics`, the package assumptions (`mvccfull`'s, mvcc's, the server's,
  the cache's) and (S3e) the `os` structs' field facts; the file extension's steps restricted by
  `etcdSQ` (no file I/O error);
* (S3e) the file extension's initial state: `FsInit`, `r` a root (`j0` its directory) (until P3,
  2026-11-24, also with no entry at any of `Main`'s file names, `mvccfullNames`, and `Fs.DirFits r`:
  `MainAt` checks both; until S3e the axiomatized `dbFilesAbsent`).
Nothing beyond mvccrand's. (Until premise fixes 5, 2026-11-10, also the store's key-count premise
`keySized` at every ghost-state instance; now proved, `mvcc.keySized_all`, from bbolt's address-space
bound `backend.rtxSnap_size`.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.runtime.StartFiles
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.FileNames

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

/-- The functors (as `putgetGF`): the universal camera (`AllG`) at slot 0, then invariants, later
credits, GooseLang's heap, prophecies and package state. Every other slot is the unit functor. -/
def mvccfullGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0. -/
def mvccfullGF_allG : AllG mvccfullGF := ⟨⟨0, rfl⟩⟩

instance mvccfullGF_gooseGpreS : GooseGpreS mvccfullGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨mvccfullGF_allG⟩, ⟨mvccfullGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := mvccfullGF_allG

/-! ## The closed theorem -/

/-- The IDs the program's packages register (auth's, the lessor's, the backend's and mvcc's metric
names' label-free descriptor IDs, in `regQs`' order; computed with cespare/xxhash v2.3.0, and checked by
the kernel in `mvccfull_regQsOk`). -/
def mvccfullRegKeys : List w64 :=
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
literals (`mvccfullRegKeys`: the kernel hashes each name once; deciding `regQsOk` directly rehashes the names
for every pair `Nodup` compares, and ran out of memory: 21 GB). -/
theorem mvccfull_regQsOk :
    prometheus.regQsOk github_com.mit_pdos.etcd_grove.examples.mvccfull.regQs :=
  prometheus.regQsOk_of_keys _ mvccfullRegKeys (by decide +kernel) (by decide +kernel) (by decide +kernel)

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **`mvccfull_adequate` along executions with fewer than `T ≤ 2 ^ 28` live threads**: the
same conclusion for every execution of `n` steps, `n + 1 ≤ 2 ^ 48` (the receipt bound the proof
needs), along which fewer than `T` threads are ever live at once (`RealNstepsBelow`): the thread
bound is a premise on the execution, not a consequence of its length (`goose_adequacy_start`). -/
theorem mvccfull_adequate_below [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
    [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    (r : GoString)
    (HEnv : EtcdVerifyOff)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (j0 : Fs.Ino)
    (Hr : (r, j0) ∈ (extLocal Fs.fsExt σ.world).fs.roots)
    (Hthreads : σ.threads = 1)
    (T : Nat) (HT28 : T ≤ 2 ^ 28)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([mvccfullProgram r], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 1 ≤ 2 ^ 48) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_adequacy_start (GF := mvccfullGF) (n + 1) T (mvccfullProgram r) σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) ⟨trivial, trivial, trivial⟩
    ⟨trivial, Hfs, trivial⟩ [] [] List.nodup_nil List.nodup_nil
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
    ?_ n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads
  intro hG HN HT HL
  obtain ⟨G, ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC mvccfullGF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs, th, cr⟩⟩
  unfold IsInit at Hinit
  rw [Hinit]
  haveI : ThreadBoundLe mvccfullGF (2 ^ 28) := ⟨by rw [HT]; omega⟩
  haveI : ReceiptBoundLe mvccfullGF (2 ^ 48) := ⟨by rw [HN]; omega⟩
  iintro - Hl Hgs Htok Hrights
  iclear Hrights
  ihave #Hvoff : ⌜EtcdVerifyOff⌝ $$ []
  · ipureintro; exact HEnv
  -- (prom-registry, route (b)) the run's registration rights: a fresh ghost map of its packages' IDs,
  -- the run's registry name
  imod (prometheus.regKeys_alloc (GF := mvccfullGF) _ mvccfull_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS mvccfullGF := ⟨γreg⟩
  ihave Hregs := prometheus.idToks_regsFree (GF := mvccfullGF) _ $$ Hregs
  have Hst : extsLocalStart (GF := mvccfullGF) σ.world ⊢
      Fs.osStart (Fs.gooseOsGS (L := (inferInstance : HeapGS .hasLC mvccfullGF).goose_localGS))
        (extLocal Fs.fsExt σ.world) :=
    sep_elim_right.trans sep_elim_left
  ihave Hown := (ownInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.mvccfull.getIsPkgInit (GF := mvccfullGF))) $$ Hgs
  iapply start_rootClaim (extLocal Fs.fsExt σ.world) Hfs r j0 Hr _ _ $$ [Hl]
  · iapply Hst $$ Hl
  iintro Hroot
  unfold mvccfullProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.mvccfull.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.mvccfull.getIsPkgInit_wf) $$ [Hown Hregs] as ⟨-, #Hpkg⟩
  · iframe Hown Hregs
  wp_apply (mvccfull.wp_MainAt r) $$ [Hroot Htok]
  · iframe Hroot Htok Hvoff
  (try wp_auto)
  ipureintro
  rfl

/-- **mvcc's full tester passes** (see the file header): every real execution of
`mvccfullProgram r` from a fresh state with one thread, whose file system's root `r` has none of
`Main`'s file names, of `n` steps: if the main thread has finished, its result is `#()` (`Run`
returned: every check of mvcc passed); no thread is stuck; no thread has ended in a panic. -/
theorem mvccfull_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
    [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    (r : GoString)
    (HEnv : EtcdVerifyOff)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (j0 : Fs.Ino)
    (Hr : (r, j0) ∈ (extLocal Fs.fsExt σ.world).fs.roots)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([mvccfullProgram r], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  mvccfull_adequate_below r HEnv σ g Hlctx Hinit Hfs j0 Hr Hthreads (n + 2) (by omega)
    n κs t2 σ2 (RealNstepsBelow.of_one Hsteps Hthreads) (by omega)

end adequacy

#print axioms mvccfull_adequate
#print axioms mvccfull_adequate_below

end EtcdGrove
end Perennial
