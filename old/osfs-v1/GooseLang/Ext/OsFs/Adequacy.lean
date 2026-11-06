/-
Adequacy, plain and with crashes, for a program whose only extension is the Linux file extension
(`[osFsExt]`, `osFsExts`).

* The initial state of the extension is an `OsInit` state: no fd, change or mapping, and every
  file at an allowed path as on disk (the environment assumptions of `Impl.lean`'s header are
  what make a real node's files such a state).
* The program's proof gets the invariant of the mapped cells (`osInv`, allocated here from the
  start resources) and every file, whole, as on disk (`osFileStart`: its `OsMeta` and its bytes,
  all clean).
* With crashes (`osFs_crash_adequacy`, `goose_crash_adequacy` for `[osFsExt]`), each generation's
  ghost state is new (`Crash.lean`): the proof of a generation guarantees the precondition of the
  next from the new generation's `osInv` and `crashRest old new []`, from which `osCrash_take`
  takes the new files, each related to the old generation's view of it (the bytes it knew clean
  are kept).
-/
module

public import GooseLang.Ext.OsFs.Crash

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The extensions of a program with Linux files: that extension alone. -/
@[reducible] def osFsExts : GooseExts := ⟨[osFsExt]⟩

attribute [local instance] osFsExts

@[reducible] def osFsExtsSemantics : GooseSemantics := ⟨(osFs_semantics, ⟨⟩)⟩

@[reducible] def osFsExtsInterp : GooseInterp := ⟨(os_interp, ⟨⟩)⟩

attribute [local instance] osFsExtsSemantics osFsExtsInterp

@[reducible] def osFsExtsCrashInterp : GooseCrashInterp := ⟨(os_crash_interp, ⟨⟩)⟩

attribute [local instance] osFsExtsCrashInterp

set_option linter.defProp false in
@[reducible] def osFsExts_hasOsFs : HasExt osFsExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] osFsExts_hasOsFs

/-- Ghost state for a program with Linux files: one slot for each camera that `GooseGpreS` needs
for `[osFsExt]` (the extension needs only the universal camera, `AllG`, at slot 0), so that a
client's adequacy theorem need not assume any. -/
noncomputable def osFsGF : BundledGFunctors := fun
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)), inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

noncomputable instance osFsGpreS : GooseGpreS osFsGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨allGOfSlot 0 rfl⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The start resources of `[osFsExt]`: the invariant of the mapped cells, and every file. -/
theorem osFs_start [hG : HeapGS .hasLC GF] (σ : state) :
    ⊢ extsLocalStart (GF := GF) σ.world ={⊤}=∗
      osInv (L := hG.goose_localGS) ∗
      [∗map] p ↦ fo ∈ (extLocal osFsExt σ.world).files, osFileStart (L := hG.goose_localGS) p fo := by
  have Hl : extsLocalStart (GF := GF) σ.world ⊢
      osStart (gooseOsGS (L := hG.goose_localGS)) (extLocal osFsExt σ.world) :=
    sep_elim_left
  iintro Hs
  icases Hl $$ Hs with Hs
  icases osStart_files _ _ $$ Hs with ⟨Hfs, Hv⟩
  imod osInv_alloc (L := hG.goose_localGS) ⊤ $$ Hv with #Hinv
  imodintro
  iframe Hinv
  iapply BigSepM.bigSepM_mono (fun {p fo} _ => (fileStart_eq (L := hG.goose_localGS) p fo).1) $$ Hfs

/-- **Adequacy for a program with Linux files** (`goose_adequacy` for `[osFsExt]`), from an
initial state whose files are as on disk (`OsInit`): if the WP of `e` is proved, under any
instantiation of the ghost state with receipt bound `N` and thread bound `T`, from the invariant
of the mapped cells, every file (whole, all of it clean), the initial package state and the main
thread's token, then in every real execution of `e` of `n < N` steps from one thread, along which
fewer than `T` threads are live: the main thread's result, if any, satisfies `φ`; no thread is
stuck; no thread has an unrecovered panic. -/
theorem osFs_adequacy [hPre : GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state)
    (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ osInv (L := hG.goose_localGS) -∗
        ([∗map] p ↦ fo ∈ (extLocal osFsExt σ.world).files,
          osFileStart (L := hG.goose_localGS) p fo) -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_adequacy (GF := GF) N T e σ g φ hφ ⟨trivial, trivial⟩ ⟨Hinit, trivial⟩ ?_
    n κs t2 σ2 Hsteps Hbound Hthreads Hlive
  intro hG HN HT Hlctx
  iintro _ Hs Hgs Htok
  imod osFs_start σ $$ Hs with ⟨#Hinv, Hfs⟩
  iapply Hwp HN HT Hlctx $$ Hinv Hfs Hgs Htok

/-- **Crash adequacy for a program with Linux files** (`goose_crash_adequacy` for `[osFsExt]`):
the boot program `e` runs at the start and after every crash. The precondition `P` holds of the
first generation, from the invariant of its mapped cells, every initial file (whole, all of it
clean) and the initial package state; every generation proves the WP of `e` from `P` and the
main thread's token, and guarantees `P` of the next generation `L'` after it crashes, from its
`crashed`, `L'`'s invariant of the mapped cells, the files after the crash (`crashRest`, from
which `osCrash_take` takes each file, related to what the old generation knew of it) and `L'`'s
package state of a restarted program. -/
theorem osFs_crash_adequacy [hPre : GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state)
    (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (P : ∀ [GooseGlobalGS .hasLC GF], GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ osInv (L := hG.goose_localGS) -∗
        ([∗map] p ↦ fo ∈ (extLocal osFsExt σ.world).files,
          osFileStart (L := hG.goose_localGS) p fo) -∗
        ownGoState σ.goState.packageState ={⊤}=∗ P hG.goose_localGS)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          osInv (L := L') -∗
          crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) [] -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P L')
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps e n ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow e T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_crash_adequacy (GF := GF) N T e σ g φ hφ ⟨trivial, trivial⟩ ⟨Hinit, trivial⟩ P
    ?_ ?_ n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · intro hG HN HT Hlctx
    iintro _ Hs Hgs
    imod osFs_start σ $$ Hs with ⟨#Hinv, Hfs⟩
    iapply Hstart HN HT Hlctx $$ Hinv Hfs Hgs
  · intro hG HN HT Hlctx
    iintro HP Htok
    imod Hwp HN HT Hlctx $$ HP Htok with ⟨Hwp, Hcrash⟩
    imodintro
    iframe Hwp
    iintro %L' Hcr Hcs Hgs
    have Hc : extsCrashStart (GF := GF) hG.goose_localGS L' ⊢
        osCrashStart (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) :=
      sep_elim_left
    icases Hc $$ Hcs with Hcs
    unfold osCrashStart
    icases Hcs with ⟨Hv, Hr⟩
    imod osInv_alloc (L := L') ⊤ $$ Hv with #Hinv
    iapply Hcrash $$ %L' Hcr Hinv Hr Hgs

end adequacy

end Perennial
