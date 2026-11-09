/-
Crash adequacy for a program with Linux files under premises on its executions: on the extension's
steps (`SQ`) and on crashes (`Q`), `fsSemWithS SQ Q` (`FilteredSem.lean`). The proof of the program
is over the restricted semantics, which the specs hold over when `SQ` keeps a step (`FsSemOk`,
`fsSemWithS_ok`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.Adequacy
public import GooseLang.Ext.Fs.FilteredSem

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

attribute [local instance] fsExts fsExtsInterp

/-! ## Crash adequacy under premises on steps and crashes -/

/-- The semantics of a program with Linux files, steps restricted by `SQ` and crashes by `Q`. -/
@[reducible] def fsExtsSemanticsWithS (SQ : StepPrem) (Q : OsState → OsState → Prop) :
    @GooseSemantics fsExts := @GooseSemantics.mk fsExts (fsSemWithS SQ Q, ⟨⟩)

@[reducible] def fsExtsCrashInterpWithS (SQ : StepPrem) (Q : OsState → OsState → Prop) :
    @GooseCrashInterp fsExts (fsExtsSemanticsWithS SQ Q) fsExtsInterp :=
  @GooseCrashInterp.mk fsExts (fsExtsSemanticsWithS SQ Q) fsExtsInterp (fs_crash_interpS SQ Q, ⟨⟩)

set_option linter.defProp false in
/-- The program's extension is the file extension, with the restricted semantics: the specs, stated
over a semantics with `FsSemOk` (`fsSemWithS_ok`), apply to it. -/
@[reducible] def fsExtsWithS_hasFs (SQ : StepPrem) (Q : OsState → OsState → Prop) :
    letI := fsExtsSemanticsWithS SQ Q; letI := fsSemWithS SQ Q; HasExt fsExt :=
  letI := fsExtsSemanticsWithS SQ Q; letI := fsSemWithS SQ Q
  { registered := rfl, sem_eq := rfl, interp_eq := rfl }

section adequacySQ
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The start resources of `[fsExt]`, as `fs_start`, for the restricted semantics. -/
theorem fs_startS (SQ : StepPrem) (Q : OsState → OsState → Prop) (hk : StepKeeps SQ)
    [hG : HeapGS .hasLC GF] :
    letI := fsExtsSemanticsWithS SQ Q; letI := fsSemWithS SQ Q; letI := fsExtsWithS_hasFs SQ Q
    ∀ (σ : state) (_ : FsInit (extLocal fsExt σ.world)), (⊢ extsLocalStart (GF := GF) σ.world ={⊤}=∗
      osInv (L := hG.goose_localGS) ∗
      ([∗map] i ↦ f ∈ (extLocal fsExt σ.world).fs.files, osFileStart (L := hG.goose_localGS) i f) ∗
      osTree (L := hG.goose_localGS) (DFrac.own 1) (extLocal fsExt σ.world).fs.roots
        ((extLocal fsExt σ.world).fs.treeDur, [])) := by
  letI := fsExtsSemanticsWithS SQ Q; letI := fsSemWithS SQ Q; letI := fsExtsWithS_hasFs SQ Q
  haveI : FsSemOk := fsSemWithS_ok SQ Q hk
  intro σ h
  have Hl : extsLocalStart (GF := GF) σ.world ⊢
      osStart (gooseOsGS (L := hG.goose_localGS)) (extLocal fsExt σ.world) :=
    sep_elim_left
  have hdisk : ∀ i f, (extLocal fsExt σ.world).fs.files !! i = some f →
      ∃ vs sz kp, f = OsFile.ofDisk vs sz kp := fun i f hf => (h.2.2.2.2.2.2.1 i f hf).2
  iintro Hs
  icases Hl $$ Hs with Hs
  unfold osStart osStartF treeStart
  icases Hs with ⟨⟨Hb, Hm, Hv⟩, Hd⟩
  rw [bytesMap_init h, metaMap_init h]
  ihave Hfs := start_filesG (gooseOsGS (L := hG.goose_localGS)) _ $$ [Hb Hm]
  · iframe
  imod osInv_alloc (L := hG.goose_localGS) ⊤ $$ Hv with #Hinv
  imodintro
  iframe Hinv
  isplitl [Hfs]
  · iapply BigSepM.bigSepM_mono (fun {i f} hf => by
      obtain ⟨vs, sz, kp, rfl⟩ := hdisk i f hf
      exact (osFileStartG_ofDisk (L := hG.goose_localGS) i vs sz kp).1) $$ Hfs
  · unfold osTree; iexact Hd


/-- **Crash adequacy for a program with Linux files, under a premise `SQ` on steps and `Q` on
crashes**: as `fsQ_crash_adequacy`, for executions of the semantics whose steps are `FsStep ∧ SQ`
and whose crashes are `OsCrash ∧ Q` (`fsExtsSemanticsWithS SQ Q`). The proof of each generation is
in the terms of that semantics (the specs hold over it when `SQ` keeps a step, `fsSemWithS_ok`), and
after a crash gets `crashRest Q`. With `SQ` true of every step, the executions are
`fsQ_crash_adequacy`'s. -/
theorem fsSQ_crash_adequacy (SQ : StepPrem) (Q : OsState → OsState → Prop) (hk : StepKeeps SQ)
    [hPre : GooseGpreS GF] :
    letI := fsExtsSemanticsWithS SQ Q; letI := fsSemWithS SQ Q
    letI := fsExtsWithS_hasFs SQ Q
    ∀ (N T : Nat) (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (hφ : ∀ p, ¬ φ (PanicV p))
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
    (Hsteps : @RealCrashNsteps fsExts (fsExtsSemanticsWithS SQ Q) _ e n
      ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : @RealCrashThreadsBelow fsExts (fsExtsSemanticsWithS SQ Q) _ e T n
      ([e], ((σ, g) : CfgState))),
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧
      (∀ e2, e2 ∈ t2 → @RealNotStuck fsExts (fsExtsSemanticsWithS SQ Q) _ e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  letI := fsExtsSemanticsWithS SQ Q; letI := fsSemWithS SQ Q; letI := fsExtsWithS_hasFs SQ Q
  haveI : FsSemOk := fsSemWithS_ok SQ Q hk
  intro N T e σ g φ hφ Hinit P Hstart Hwp n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  refine @goose_crash_adequacy fsExts fsExtsInterp (fsExtsSemanticsWithS SQ Q) _
    (fsExtsCrashInterpWithS SQ Q) GF hPre N T e σ g φ hφ ⟨trivial, trivial⟩ ⟨Hinit, trivial⟩ P
    ?_ ?_ n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · intro hG HN HT Hlctx
    iintro _ Hs Hgs
    imod fs_startS SQ Q hk σ Hinit $$ Hs with ⟨#Hinv, Hfs, Hd⟩
    iapply Hstart HN HT Hlctx $$ Hinv Hfs Hd Hgs
  · intro hG HN HT Hlctx
    iintro HP Htok
    imod Hwp HN HT Hlctx $$ HP Htok with ⟨Hwp, Hcrash⟩
    imodintro
    iframe Hwp
    iintro %L' Hcr Hcs Hgs
    have Hc : @extsCrashStart fsExts (fsExtsSemanticsWithS SQ Q) fsExtsInterp
        (fsExtsCrashInterpWithS SQ Q) GF hG.goose_localGS L' ⊢
        osCrashStart Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) := by
      unfold extsCrashStart Exts.crashStart; exact sep_elim_left
    icases Hc $$ Hcs with Hcs
    unfold osCrashStart
    icases Hcs with ⟨Hv, %V', Hr⟩
    imod osInv_alloc (L := L') ⊤ $$ Hv with #Hinv
    iapply Hcrash $$ %L' %V' Hcr Hinv Hr Hgs

end adequacySQ

end Fs
end Perennial

end
