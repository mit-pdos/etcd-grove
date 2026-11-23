/-
**Crash adequacy, every generation switched to the shared mode before its WP** (wal-safe, 2026-11-21;
`notes/wal-units/tester.md`, twelfth session): `fsSQ_crash_adequacyShared`. The executions, the
semantics `fsExtsSemanticsWithS SQ Q` and the conclusion are `fsSQ_crash_adequacy`'s. The difference is
in what a generation's proof is given: the shared mode's resources (`osShared R V`, for the
generation's whole tree `V`) before its WP is made, never the legacy tree. The switch is made by this
theorem's proof at the start of every generation, the first and each one after a crash, with
`treeCtx_switchG` and `osSwitchKit_open` on the extension's local interpretation. That interpretation
is given by `goose_crash_adequacy_acc` (`CrashAdequacyAcc.lean`, the local copy of Perennial's
`goose_crash_adequacy` with access to it at each generation's start). So a generation's crash frame
can already hold whatever its proof allocated in the shared mode: no window exists before the switch.

The client gives:
- `Hstart`: its precondition `P L V` of the first generation, at the disk's tree;
- `Hwp`: from `P L V` and `osShared R V`, the WP and the crash frame. The frame turns the crash's
  `crashRest` (tree untaken) into the next generation's tree, whole, and its `P`.
`fsSQ_crash_adequacy` and its clients are untouched. Untrusted.
-/
module

public import GooseLang.Ext.Fs.AdequacyS
public import GooseLang.Ext.Fs.TreeSharedKit
public import GooseLang.Ext.Fs.CrashAdequacyAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

attribute [local instance] fsExts fsExtsInterp

section adequacyShared
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- **Crash adequacy, every generation in the shared mode from its start** (see the file header). `R`
is the roots. -/
theorem fsSQ_crash_adequacyShared (SQ : StepPrem) (Q : OsState → OsState → Prop) (hk : StepKeeps SQ)
    [hPre : GooseGpreS GF] :
    letI := fsExtsSemanticsWithS SQ Q; letI := fsSemWithS SQ Q
    letI := fsExtsWithS_hasFs SQ Q
    ∀ (N T : Nat) (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinit : FsInit (extLocal fsExt σ.world))
    (P : ∀ [GooseGlobalGS .hasLC GF], GooseLocalGS GF → Hist → IProp GF)
    (Hstart : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ osInv (L := hG.goose_localGS) -∗
        ([∗map] i ↦ f ∈ (extLocal fsExt σ.world).fs.files,
          osFileStart (L := hG.goose_localGS) i f) -∗
        ownGoState σ.goState.packageState ={⊤}=∗
        P hG.goose_localGS ((extLocal fsExt σ.world).fs.treeDur, []))
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ∀ V : Hist,
      ⊢ osInv (L := hG.goose_localGS) -∗ P hG.goose_localGS V -∗
        osShared (L := hG.goose_localGS) (extLocal fsExt σ.world).fs.roots V -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗
        ∀ (L' : GooseLocalGS GF) (V' : Hist), crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          osInv (L := L') -∗
          crashRest Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) [] false V' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗
          ∃ V'' : Hist, osTree (L := L') (DFrac.own 1) (extLocal fsExt σ.world).fs.roots V'' ∗
            P L' V'')
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
  obtain ⟨R, hRdef⟩ : ∃ R, (extLocal fsExt σ.world).fs.roots = R := ⟨_, rfl⟩
  rw [hRdef] at Hwp
  -- a generation's precondition: the extension's invariant, the whole tree and the client's `P`
  let P' : ∀ [GooseGlobalGS .hasLC GF], GooseLocalGS GF → IProp GF := fun L =>
    iprop(osInv (L := L) ∗ ∃ V : Hist, osTree (L := L) (DFrac.own 1) R V ∗ P L V)
  refine @goose_crash_adequacy_acc fsExts fsExtsInterp (fsExtsSemanticsWithS SQ Q) _
    (fsExtsCrashInterpWithS SQ Q) GF hPre N T e σ g φ hφ ⟨trivial, trivial⟩ ⟨Hinit, trivial⟩ P'
    ?_ ?_ n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · intro hG HN HT Hlctx
    iintro _ Hs Hgs
    imod fs_startS SQ Q hk σ Hinit $$ Hs with ⟨#Hinv, Hfs, Hd⟩
    imod Hstart HN HT Hlctx $$ Hinv Hfs Hgs with HP
    imodintro
    dsimp only [P']
    iframe Hinv
    iexists _
    rw [hRdef]
    iframe
  · intro hG HN HT Hlctx
    dsimp only [P']
    iintro ⟨#Hinv, %V, Hh, HP⟩ Htok %w Hext
    -- the switch, on the extension's local interpretation
    icases HasExt.localCtx_acc (X := fsExt) _ $$ Hext with ⟨Hl, Hlclose⟩
    icases (os_local_ctx_eq (L := hG.goose_localGS) _).mp $$ Hl with Hl
    unfold osCtx
    icases Hl with ⟨HF, Ht, Hof⟩
    iunfold osTree at Hh
    imod treeCtx_switchG (gooseOsGS (L := hG.goose_localGS)) _ R V $$ Hh Ht with ⟨Ht, Hkit, -⟩
    imod osSwitchKit_open (L := hG.goose_localGS) R V ⊤ $$ Hkit with Hsh
    ihave Hl : osCtx (gooseOsGS (L := hG.goose_localGS)) _ $$ [HF Ht Hof]
    · unfold osCtx; iframe
    ihave Hl := (os_local_ctx_eq (L := hG.goose_localGS) _).mpr $$ Hl
    ihave Hext := Hlclose $$ Hl
    rw [ExtIn.set_get]
    iframe Hext
    unfold osShared
    icases Hsh with ⟨#Hsi, Hsh⟩
    imod Hwp HN HT Hlctx V $$ Hinv HP [Hsh] Htok with ⟨Hw, Hcc⟩
    · unfold osShared; iframe Hsi Hsh
    imodintro
    iframe Hw
    iintro %L' Hcr Hcs Hgs
    have Hc : @extsCrashStart fsExts (fsExtsSemanticsWithS SQ Q) fsExtsInterp
        (fsExtsCrashInterpWithS SQ Q) GF hG.goose_localGS L' ⊢
        osCrashStart Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) := by
      unfold extsCrashStart Exts.crashStart; exact sep_elim_left
    icases Hc $$ Hcs with Hcs
    unfold osCrashStart
    icases Hcs with ⟨Hv, %V', Hr⟩
    imod osInv_alloc (L := L') ⊤ $$ Hv with #Hinv'
    imod Hcc $$ %L' %V' Hcr Hinv' Hr Hgs with ⟨%V'', Hh', HP'⟩
    imodintro
    iframe Hinv'
    iexists V''
    iframe

end adequacyShared

end Fs
end Perennial

end
