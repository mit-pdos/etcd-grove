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
interleaving.

As `mvccrand_adequate` (`examples/mvccrand/Adequacy.lean`; `notes/decisions.md`, "mvccrand's closed
theorem"): from `goose_adequacy_start_files` (`Proof/runtime/Start.lean`), with the trivial
extension and a ghost-state bundle `mvccfullGF`, `mvccfull`'s `wp_initialize'` (`Init.lean`, over the
program's package table `PkgTable.lean`) and `mvccfull.wp_Main` (`Link.lean`; `Results.lean`'s
`mvccfull_Main`). The program's fresh files are `FilePaths(MainConfig("mvccfull"))`
(`filePathsM`: the members' two and one per possible snapshot install, `Ops = 12000`), distinct
(`filePaths_main_nodup`).

**Its hypotheses** are mvccrand's, but `sort.Slice.spec` (`mvccfull.wp_Main` takes no hypothesis:
the tester's lease checks compare the lessor's list against the model's without sorting it):
* pure facts of the program's environment: `dbOpenOk` and `dbCloseOk` (bbolt's `Open` and `Close`
  do not fail for the environment's reasons), `dbFilesAbsent` of `Main`'s files (absent at start,
  touched only by the backend) and `verifyEnvOff` (`ETCD_VERIFY` unset), and the execution's length
  (`n + 2 ≤ 2 ^ 28`: the thread bound, and with `N = n + 1` the receipt bound `2 ^ 38`);
* a pure fact of the lessor's configuration: `ckptEffectsOk` (`lease.NewLessor`'s);
* the semantics: `go.Semantics` and the package assumptions (`mvccfull`'s, mvcc's, the server's,
  the cache's);
* at every ghost-state instance: the store's key-count premise `keySized` (`etcdStorage_open.law`'s:
  the backend's read states hold fewer than `2 ^ 62` keys, a genuine assumption, persistent).
Nothing beyond mvccrand's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Proof.runtime.Start
public import Proof.runtime.Threads

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

/-! ## The program's files -/

namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull

theorem decDigits_ne_nil (n : Nat) (h : n ≠ 0) : decDigits n ≠ [] := by
  rw [decDigits_pos n h]; simp

/-- `n`'s decimal digits determine `n` (for `n ≠ 0`). -/
theorem decDigits_inj : ∀ (a b : Nat), a ≠ 0 → b ≠ 0 → decDigits a = decDigits b → a = b := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b ha hb he
    rw [decDigits_pos a ha, decDigits_pos b hb] at he
    obtain ⟨h1, h2⟩ := List.append_inj' he rfl
    simp only [List.cons.injEq, and_true] at h2
    have hd : a % 10 = b % 10 := by
      have := congrArg (fun w : w8 => uint.Z w) h2
      have ha10 := Nat.mod_lt a (by decide : 10 > 0)
      have hb10 := Nat.mod_lt b (by decide : 10 > 0)
      word
    by_cases ha' : a / 10 = 0
    · by_cases hb' : b / 10 = 0
      · omega
      · exfalso; rw [ha', decDigits_zero] at h1
        exact decDigits_ne_nil _ hb' h1.symm
    · by_cases hb' : b / 10 = 0
      · exfalso; rw [hb', decDigits_zero] at h1
        exact decDigits_ne_nil _ ha' h1
      · have := ih (a / 10) (by omega) (b / 10) ha' hb' h1
        omega

theorem decDigits_one (n : Nat) (h : n ≠ 0) (x : w8) (he : decDigits n = [x]) :
    n < 10 ∧ x = W8 (48 + n % 10 : Nat) := by
  rw [decDigits_pos n h] at he
  by_cases h' : n / 10 = 0
  · rw [h', decDigits_zero] at he
    simp only [List.nil_append, List.cons.injEq, and_true] at he
    exact ⟨by omega, he.symm⟩
  · exfalso
    have hl := congrArg List.length he
    have hne : (decDigits (n / 10)).length ≠ 0 := by
      have := decDigits_ne_nil _ h'; simpa using this
    simp only [List.length_append, List.length_singleton] at hl
    omega

/-- `itoa` is injective. -/
theorem itoaM_inj (a b : Nat) (he : itoaM a = itoaM b) : a = b := by
  unfold itoaM at he
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · omega
  · simp only [ha, hb, ↓reduceIte] at he
    obtain ⟨h1, h2⟩ := decDigits_one b hb _ he.symm
    have := congrArg (fun w : w8 => uint.Z w) h2
    simp at this; word
  · simp only [ha, hb, ↓reduceIte] at he
    obtain ⟨h1, h2⟩ := decDigits_one a ha _ he
    have := congrArg (fun w : w8 => uint.Z w) h2
    simp at this; word
  · simp only [ha, hb, ↓reduceIte] at he
    exact decDigits_inj a b ha hb he

theorem buildPathM_inj (a b : Nat) (h : buildPathM go!"mvccfull" a = buildPathM go!"mvccfull" b) :
    a = b := by
  unfold buildPathM at h
  simp only [List.append_assoc, List.append_cancel_left_eq, List.append_cancel_right_eq] at h
  exact itoaM_inj a b h

theorem buildPathM_ne0 (n : Nat) : buildPathM go!"mvccfull" n ≠ memberPathM go!"mvccfull" 0 := by
  unfold buildPathM memberPathM
  simp [itoaM]

theorem buildPathM_ne1 (n : Nat) : buildPathM go!"mvccfull" n ≠ memberPathM go!"mvccfull" 1 := by
  unfold buildPathM memberPathM
  simp [itoaM, decDigits_pos 1 (by decide), decDigits_zero]

/-- **`Main`'s files are distinct** (`goose_adequacy_start_files`' `Fs.Nodup`): the members'
`mvccfull-0.db`, `mvccfull-1.db` and the builders' `mvccfull-b<n>.db`. -/
theorem filePaths_main_nodup [GooseExts] [GoGlobalContext] (mx : Mix) : (filePathsM (mainConfigM go!"mvccfull" mx)).Nodup := by
  unfold filePathsM
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · simp [memberPathM, itoaM, decDigits_pos 1 (by decide), decDigits_zero]
  · exact List.pairwise_map.2 ((List.nodup_range' (s := 1) (n := sint.nat (W64 12000))).imp fun h e => h (buildPathM_inj _ _ e))
  · intro x hx y hy hxy
    subst hxy
    simp only [List.mem_map] at hy
    obtain ⟨n, -, rfl⟩ := hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h
    · exact buildPathM_ne0 n h
    · exact buildPathM_ne1 n h

end mvccfull

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
  goosePreGExts := (⟨mvccfullGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := mvccfullGF_allG

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The program: `mvccfull`'s initialization, then `Main()`. -/
def mvccfullProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.mvccfull.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.Main) #()

/-- **mvcc's full tester passes** (see the file header): every real execution of
`mvccfullProgram` from a fresh state with one thread, of `n` steps: if the main thread has
finished, its result is `#()` (`Main` returned: every check of mvcc passed); no thread is stuck;
no thread has ended in a panic. -/
theorem mvccfull_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
    [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    (Hks : ∀ hG : HeapGS .hasLC mvccfullGF,
      ⊢ (□ ∀ (γB : backend.BNames) (P : backend.BParams) (b : Loc),
          mvcc.keySized (GF := mvccfullGF) (hG := heapWith hG lctx) γB P b : IProp mvccfullGF))
    (Hck : ckptEffectsOk) (Hdbo : backend.dbOpenOk) (Hdbc : backend.dbCloseOk)
    (HFs : dbFilesAbsent mvccfullProgram
      (mvccfull.filePathsM (mvccfull.mainConfigM go!"mvccfull"
        (zeroValDef : github_com.mit_pdos.etcd_grove.examples.mvccfull.Mix))))
    (HEnv : verifyEnvOff mvccfullProgram)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([mvccfullProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  apply adequate_of_unrecovered
  refine goose_adequacy_start_files (GF := mvccfullGF) (n + 1) (n + 2) mvccfullProgram σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) ⟨trivial, trivial⟩
    ⟨trivial, trivial⟩ [] [] [] _ List.nodup_nil List.nodup_nil List.nodup_nil
    (mvccfull.filePaths_main_nodup _)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
    HFs HEnv ?_ n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG HN HT HL
  obtain ⟨G, ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC mvccfullGF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs, th, cr⟩⟩
  -- the hypothesis at this instance (`heapWith` of it, definitionally)
  have Hks' : ⊢ (□ ∀ (γB : backend.BNames) (P : backend.BParams) (b : Loc),
      mvcc.keySized (GF := mvccfullGF) γB P b : IProp mvccfullGF) := Hks _
  unfold IsInit at Hinit
  rw [Hinit]
  haveI : ThreadBoundLe mvccfullGF (2 ^ 28) := ⟨by rw [HT]; omega⟩
  haveI : ReceiptBoundLe mvccfullGF (2 ^ 38) := ⟨by rw [HN]; omega⟩
  ihave #Hks := Hks'
  iintro - - Hgs Htok Hrights Hfiles
  iunfold startRights at Hrights
  icases Hrights with ⟨-, -, -, -, #Hvoff⟩
  ihave Hown := (ownInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.mvccfull.getIsPkgInit (GF := mvccfullGF))) $$ Hgs
  imodintro
  unfold mvccfullProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.mvccfull.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.mvccfull.getIsPkgInit_wf) $$ Hown as ⟨-, #Hpkg⟩
  wp_apply (mvccfull.wp_Main Hck Hdbo Hdbc) $$ [Hfiles Htok]
  · iframe Hfiles Htok Hvoff Hks
  ipureintro
  rfl

end adequacy

#print axioms mvccfull_adequate

end EtcdGrove
end Perennial
