/-
Adequacy, plain and with crashes, for a program whose only extension is the Linux file extension
(`[fsExt]`, `fsExts`). Untrusted.

* The initial state of the extension is an `FsInit` state: no process state, nothing logged, every
  file named and on disk (the environment assumptions of `Impl.lean`'s header are what make a real
  node's files such a state).
* The program's proof gets the invariant of the mapped cells (`osInv`, allocated here from the
  start resources), every file, whole, as on disk (`osFileStart`: its `OsMeta` and its bytes, each
  durable), and the tree's history, whole, with nothing logged (`osTree 1 R (treeDur, [])`).
* With crashes (`fs_crash_adequacy`; `fsQ_crash_adequacy` under a premise `Q` on crashes), each
  generation's ghost state is new (`CrashTok.lean`): the proof of a generation guarantees the
  precondition of the next from the new generation's `osInv` and `crashRest Q old new [] false V'`
  for some new history `V'`, from which `osCrash_take_runs_keep` (and `osCrash_take_tok_keep`)
  takes the files and `osTreeCrash_take` the tree, each related to what the old generation knew.
-/
module

public import GooseLang.Ext.Fs.CrashTok
public import GooseLang.Ext.Fs.SemCongr

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The extensions of a program with Linux files: that extension alone. -/
@[reducible] def fsExts : GooseExts := ⟨[fsExt]⟩

attribute [local instance] fsExts

@[reducible] def fsExtsSemantics : GooseSemantics := ⟨(fs_semantics, ⟨⟩)⟩

@[reducible] def fsExtsInterp : GooseInterp := ⟨(fs_interp, ⟨⟩)⟩

attribute [local instance] fsExtsSemantics fsExtsInterp

@[reducible] def fsExtsCrashInterp : GooseCrashInterp := ⟨(fs_crash_interp, ⟨⟩)⟩

attribute [local instance] fsExtsCrashInterp

set_option linter.defProp false in
@[reducible] def fsExts_hasFs : HasExt fsExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] fsExts_hasFs

/-- Ghost state for a program with Linux files: one slot for each camera that `GooseGpreS` needs
for `[fsExt]` (the extension needs only the universal camera, `AllG`, at slot 0), so that a client's
adequacy theorem need not assume any. -/
noncomputable def fsGF : BundledGFunctors := fun
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)), inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

noncomputable instance fsGpreS : GooseGpreS fsGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨allGOfSlot 0 rfl⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

/-! ## The first generation's start -/

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The start resources of `[fsExt]`: the invariant of the mapped cells, every file, and the
tree's history. -/
theorem fs_start [hG : HeapGS .hasLC GF] (σ : state) (h : FsInit (extLocal fsExt σ.world)) :
    ⊢ extsLocalStart (GF := GF) σ.world ={⊤}=∗
      osInv (L := hG.goose_localGS) ∗
      ([∗map] i ↦ f ∈ (extLocal fsExt σ.world).fs.files, osFileStart (L := hG.goose_localGS) i f) ∗
      osTree (L := hG.goose_localGS) (DFrac.own 1) (extLocal fsExt σ.world).fs.roots
        ((extLocal fsExt σ.world).fs.treeDur, []) := by
  have Hl : extsLocalStart (GF := GF) σ.world ⊢
      osStart (gooseOsGS (L := hG.goose_localGS)) (extLocal fsExt σ.world) :=
    sep_elim_left
  have hdisk : ∀ i f, (extLocal fsExt σ.world).fs.files !! i = some f →
      ∃ img sz, f = OsFile.ofDisk img sz := fun i f hf => (h.2.2.2.2.2.2.1 i f hf).2
  iintro Hs
  icases Hl $$ Hs with Hs
  unfold osStart osStartF treeStart bytesMap metaMap
  icases Hs with ⟨⟨Hb, Hm, Hv⟩, Hd⟩
  ihave Hfs := start_files (gooseOsGS (L := hG.goose_localGS)) hdisk $$ [Hb Hm]
  · iframe
  imod osInv_alloc (L := hG.goose_localGS) ⊤ $$ Hv with #Hinv
  imodintro
  iframe Hinv
  isplitl [Hfs]
  · iapply BigSepM.bigSepM_mono (fun {i f} _ =>
      (fileStart_eq (L := hG.goose_localGS) i f).1) $$ Hfs
  · unfold osTree; iexact Hd

/-- **Adequacy for a program with Linux files** (`goose_adequacy` for `[fsExt]`), from an initial
state whose files are as on disk (`FsInit`). -/
theorem fs_adequacy [hPre : GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state)
    (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinit : FsInit (extLocal fsExt σ.world))
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ osInv (L := hG.goose_localGS) -∗
        ([∗map] i ↦ f ∈ (extLocal fsExt σ.world).fs.files,
          osFileStart (L := hG.goose_localGS) i f) -∗
        osTree (L := hG.goose_localGS) (DFrac.own 1) (extLocal fsExt σ.world).fs.roots
          ((extLocal fsExt σ.world).fs.treeDur, []) -∗
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
  imod fs_start σ Hinit $$ Hs with ⟨#Hinv, Hfs, Hd⟩
  iapply Hwp HN HT Hlctx $$ Hinv Hfs Hd Hgs Htok

/-- **Crash adequacy for a program with Linux files** (`goose_crash_adequacy` for `[fsExt]`): the
boot program `e` runs at the start and after every crash (of the machine, or of the process alone).
The precondition `P` holds of the first generation, from the invariant of its mapped cells, every
initial file (whole, every byte durable), the tree's history and the initial package state; every
generation proves the WP of `e` from `P` and the main thread's token, and guarantees `P` of the next
generation `L'` after it crashes, from its `crashed`, `L'`'s invariant of the mapped cells, the
restart's resources (`crashRest`, for some new history `V'`) and `L'`'s package state. -/
theorem fs_crash_adequacy [hPre : GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state)
    (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinit : FsInit (extLocal fsExt σ.world))
    (P : ∀ [GooseGlobalGS .hasLC GF], GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ osInv (L := hG.goose_localGS) -∗
        ([∗map] i ↦ f ∈ (extLocal fsExt σ.world).fs.files,
          osFileStart (L := hG.goose_localGS) i f) -∗
        osTree (L := hG.goose_localGS) (DFrac.own 1) (extLocal fsExt σ.world).fs.roots
          ((extLocal fsExt σ.world).fs.treeDur, []) -∗
        ownGoState σ.goState.packageState ={⊤}=∗ P hG.goose_localGS)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗
        ∀ (L' : GooseLocalGS GF) (V' : Hist), crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          osInv (L := L') -∗
          crashRest (fun _ _ => True) (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L'))
            [] false V' -∗
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
    imod fs_start σ Hinit $$ Hs with ⟨#Hinv, Hfs, Hd⟩
    iapply Hstart HN HT Hlctx $$ Hinv Hfs Hd Hgs
  · intro hG HN HT Hlctx
    iintro HP Htok
    imod Hwp HN HT Hlctx $$ HP Htok with ⟨Hwp, Hcrash⟩
    imodintro
    iframe Hwp
    iintro %L' Hcr Hcs Hgs
    have Hc : extsCrashStart (GF := GF) hG.goose_localGS L' ⊢
        osCrashStart (fun _ _ => True) (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) :=
      sep_elim_left
    icases Hc $$ Hcs with Hcs
    unfold osCrashStart
    icases Hcs with ⟨Hv, %V', Hr⟩
    imod osInv_alloc (L := L') ⊤ $$ Hv with #Hinv
    iapply Hcrash $$ %L' %V' Hcr Hinv Hr Hgs

end adequacy

/-! ## Crash adequacy under a premise on crashes -/

/-- The semantics of a program with Linux files, crashes restricted by the premise `Q`. -/
@[reducible] def fsExtsSemanticsWith (Q : OsState → OsState → Prop) :
    @GooseSemantics fsExts := @GooseSemantics.mk fsExts (fsSemWith Q, ⟨⟩)

@[reducible] def fsExtsCrashInterpWith (Q : OsState → OsState → Prop) :
    @GooseCrashInterp fsExts (fsExtsSemanticsWith Q) fsExtsInterp :=
  @GooseCrashInterp.mk fsExts (fsExtsSemanticsWith Q) fsExtsInterp (fs_crash_interpQ Q, ⟨⟩)

section adequacyQ
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The extension's steps are the same in both semantics. -/
theorem fsWith_extStep_iff (Q : OsState → OsState → Prop) (ext op : String) (v : val)
    (σg : CfgState) (e' : Expr) (σg' : CfgState) :
    @extStep fsExts fsExtsSemantics _ ext op v σg e' σg' ↔
      @extStep fsExts (fsExtsSemanticsWith Q) _ ext op v σg e' σg' := by
  unfold extStep
  refine exists_congr fun E => exists_congr fun h => ?_
  generalize ExtIn.ofNamed h = m
  change ExtIn E [fsExt] at m
  cases m with
  | here => exact Iff.rfl
  | there m => cases m

/-- **Crash adequacy for a program with Linux files, under a premise `Q` on crashes**: as
`fs_crash_adequacy`, for executions of the semantics whose crash relation is `OsCrash ∧ Q`
(`fsExtsSemanticsWith Q`). The proof of each generation is in the terms of the extension's own
semantics (`fsExtsSemantics`, which its specs are for), and after a crash gets `crashRest Q`: the
files and the tree, with the crashed state and the premise (`CrashSeenR`). -/
theorem fsQ_crash_adequacy (Q : OsState → OsState → Prop) [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinit : FsInit (extLocal fsExt σ.world))
    (P : ∀ [GooseGlobalGS .hasLC GF], GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ osInv (L := hG.goose_localGS) -∗
        ([∗map] i ↦ f ∈ (extLocal fsExt σ.world).fs.files,
          osFileStart (L := hG.goose_localGS) i f) -∗
        osTree (L := hG.goose_localGS) (DFrac.own 1) (extLocal fsExt σ.world).fs.roots
          ((extLocal fsExt σ.world).fs.treeDur, []) -∗
        ownGoState σ.goState.packageState ={⊤}=∗ P hG.goose_localGS)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗
        ∀ (L' : GooseLocalGS GF) (V' : Hist), crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          osInv (L := L') -∗
          crashRest Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) [] false V' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P L')
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : @RealCrashNsteps fsExts (fsExtsSemanticsWith Q) _ e n
      ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : @RealCrashThreadsBelow fsExts (fsExtsSemanticsWith Q) _ e T n
      ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧
      (∀ e2, e2 ∈ t2 → @RealNotStuck fsExts (fsExtsSemanticsWith Q) _ e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine @goose_crash_adequacy fsExts fsExtsInterp (fsExtsSemanticsWith Q) _
    (fsExtsCrashInterpWith Q) GF hPre N T e σ g φ hφ ⟨trivial, trivial⟩ ⟨Hinit, trivial⟩ P
    ?_ ?_ n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · intro hG HN HT Hlctx
    iintro _ Hs Hgs
    imod fs_start σ Hinit $$ Hs with ⟨#Hinv, Hfs, Hd⟩
    iapply Hstart HN HT Hlctx $$ Hinv Hfs Hd Hgs
  · intro hG HN HT Hlctx
    have hw := wp_sem_congr (hlc := .hasLC) (GF := GF) (Sa := fsExtsSemantics)
      (Sb := fsExtsSemanticsWith Q) (fsWith_extStep_iff Q) Stuckness.NotStuck ⊤ e
      (fun v => iprop(⌜φ v⌝))
    iintro HP Htok
    imod Hwp HN HT Hlctx $$ HP Htok with ⟨Hwp, Hcrash⟩
    imodintro
    isplitl [Hwp]
    · rw [← hw]; iexact Hwp
    iintro %L' Hcr Hcs Hgs
    have Hc : @extsCrashStart fsExts (fsExtsSemanticsWith Q) fsExtsInterp
        (fsExtsCrashInterpWith Q) GF hG.goose_localGS L' ⊢
        osCrashStart Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) := by
      unfold extsCrashStart Exts.crashStart; exact sep_elim_left
    icases Hc $$ Hcs with Hcs
    unfold osCrashStart
    icases Hcs with ⟨Hv, %V', Hr⟩
    imod osInv_alloc (L := L') ⊤ $$ Hv with #Hinv
    iapply Hcrash $$ %L' %V' Hcr Hinv Hr Hgs

end adequacyQ

end Fs
end Perennial

end
