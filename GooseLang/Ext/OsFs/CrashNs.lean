/-
Crash adequacy with the namespace (`notes/walfs-ext-plan.md`): the crash interpretation
`os_crash_interpN` is `os_crash_interpT`'s (`CrashTok.lean`), and hands the restarted boot program
the namespace's too: every directory of the new generation, whole, with what a crash left of it,
related to the old generation's ghost entries (`nsCrashRest`: the new entries are a crash outcome
of the old, `DirG.CrashTo`), and the in-flight flag, unset. `osNsCrash_take` is how a boot program
uses it. Untrusted.
-/
module

public import GooseLang.Ext.OsFs.CrashTok
public import GooseLang.Ext.OsFs.NsSpecs3

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## The pure relation across a crash -/

theorem take_min_length' (l : List NsOp) (k : Nat) :
    l.take (min k l.length) = l.take k := by
  rw [← List.take_take, List.take_length]

/-- **A crash leaves a prefix of the history**: the namespace after it is some prefix of the
operations logged since boot replayed on the namespace the generation booted with. -/
theorem nsCrash_hist {st st' : OsState} {V : NsMap × List NsOp} {Γdf} (hc : NsCoh st V Γdf)
    (hcr : NsCrash st st') : ∃ n, n ≤ V.2.length ∧ st'.ns = nsReplay (V.2.take n) V.1 := by
  obtain ⟨-, -, -, -, -, ⟨n, hn, hns⟩, -⟩ := hcr
  obtain ⟨h1, h2, h3⟩ := hc.hist
  generalize hcd : V.2.length - st.nsLog.length = c at h2 h3
  refine ⟨c + min n st.nsLog.length, by omega, ?_⟩
  rw [hns, h3, ← nsReplay_append, ← h2, List.take_add, take_min_length']

/-! ## The crash interpretation -/

section crash
variable {GF : BundledGFunctors}

/-- The namespace's part of the restart: the old generation's history, and the new generation's,
whole, on the namespace the crash left, a prefix of the old history replayed. -/
def nsCrashRest (hL hL' : OsGS GF) : IProp GF :=
  iprop(∃ (V : NsMap × List NsOp) (ns' : NsMap), gAuth hL hL.γd (histMap V) ∗
    gElem hL' hL'.γd () (DFrac.own 1) (ns', ([] : List NsOp)) ∗
    ⌜∃ n, n ≤ V.2.length ∧ ns' = nsReplay (V.2.take n) V.1⌝)

/-- The restart's resources: `osCrashStartT`'s, the namespace's, and the new in-flight flag. -/
def osCrashStartN (hL hL' : OsGS GF) : IProp GF :=
  iprop(osCrashStartT hL hL' ∗ nsCrashRest hL hL' ∗
    ([∗map] k ↦ b ∈ busyMap false, gElem hL' hL'.γz k (DFrac.own 1) b))

theorem osStartF_files (hL : OsGS GF) (st : OsState) :
    osStartF hL st ⊢ ([∗map] p ↦ fo ∈ st.files, fileStart hL p fo) ∗
      gVar hL (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0) := by
  unfold osStartF
  rw [bytesMap_eq, metaMap_eq]
  iintro ⟨Hb, Hm, Hv⟩
  iframe Hv
  iapply start_files hL st.files; iframe

/-- `os_local_crashT`, with the namespace's part. -/
theorem os_local_crashN (hPre : OsGpreS GF) (hL : OsGS GF) (st st' : OsState)
    (hc : OsCrash st st') :
    ⊢@{IProp GF} osCtx hL st ==∗ ∃ hL' : OsGS GF, osCtx hL' st' ∗ osCrashStartN hL hL' := by
  unfold osCtx osCtxF nsCtx
  iintro ⟨⟨%Γb, %Γm, %Γf, %Γt, %hwc, Hab, Ham, -, HAt, Htok, -⟩, ⟨%Γd, %Γdf, %hns, HAd, -, -, -⟩⟩
  obtain ⟨hinit, hrel⟩ := osCrash_rel hwc.2 hns.1 hc
  have hhist := nsCrash_hist hns.2 hc.2
  imod os_local_init hPre st' hinit with ⟨%hL', Hctx, Hst⟩
  unfold osCtx osCtxF nsCtx
  unfold osStart
  icases Hst with ⟨Hst, Hns⟩
  icases osStartF_files hL' st' $$ Hst with ⟨Hfs, Hv⟩
  unfold nsStart
  icases Hns with ⟨Hds, Hz⟩
  imodintro
  iexists hL'
  iframe Hctx
  unfold osCrashStartN osCrashStartT crashRestT crashRest nsCrashRest
  iframe Hv Hz
  isplitl [Hab Ham Hfs HAt Htok]
  · isplitl [Hab Ham Hfs]
    · iexists Γb, Γm, st'.files
      iframe Hab Ham Hfs
      ipureintro; exact hrel
    · iexists st, Γt
      iframe
  · iexists Γd, st'.ns
    iframe HAd Hds
    ipureintro; exact hhist

/-- The crash interpretation of the Linux file extension with the namespace. -/
@[reducible] def os_crash_interpN : ExtCrashInterp osFsExt where
  crashStart hL hL' := osCrashStartN hL hL'
  local_crash _ hPre hL st st' hc := os_local_crashN hPre hL st st' hc

end crash

/-! ## In a generation's terms -/

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **The history after a crash**: from (a fraction of) the old generation's history `W`, the new
generation's, whole, on a prefix of `W` replayed (nothing logged on it yet). The old fraction is
given back. -/
theorem osNsCrash_takeAll (L L' : GooseLocalGS GF) (dq : DFrac) (W : NsMap × List NsOp) :
    ⊢ nsCrashRest (gooseOsGS (L := L)) (gooseOsGS (L := L')) -∗ osNsAll (L := L) dq W -∗
      ∃ n, ⌜n ≤ W.2.length⌝ ∗
        osNsAll (L := L') (DFrac.own 1) (nsReplay (W.2.take n) W.1, ([] : List NsOp)) ∗
        osNsAll (L := L) dq W := by
  unfold nsCrashRest
  iintro ⟨%V, %ns', HA, Hn, %hrel⟩ Hh
  icases osNsAll_auth (L := L) V W dq $$ HA Hh with %h
  subst h
  obtain ⟨n, hn, rfl⟩ := hrel
  iexists n
  iframe Hh
  isplitr
  · ipureintro; exact hn
  unfold osNsAll; iexact Hn

/-- **A directory after a crash**: from (a fraction of) the old generation's view `g` of `d`, the
new generation's, whole, with nothing since a commit, its entries a crash outcome of `g`. -/
theorem osNsCrash_take (L L' : GooseLocalGS GF) (d : GoString) (dq : DFrac) (g : DirG) :
    ⊢ nsCrashRest (gooseOsGS (L := L)) (gooseOsGS (L := L')) -∗ osDir (L := L) d dq g -∗
      ∃ g', ⌜g'.pend = [] ∧ g.CrashTo g'.dur⌝ ∗ osDir (L := L') d (DFrac.own 1) g' ∗
        osDir (L := L) d dq g := by
  iintro Hr Hd
  unfold osDir
  icases Hd with ⟨%W, Hh, %hg⟩
  obtain ⟨rfl, hall⟩ := hg
  icases osNsCrash_takeAll L L' dq W $$ Hr Hh with ⟨%n, %hn, Hn, Hh⟩
  iexists ⟨entsOf (nsReplay (W.2.take n) W.1) d, []⟩
  isplitr
  · ipureintro; exact ⟨rfl, dview_crashTo W.1 W.2 d n⟩
  isplitl [Hn]
  · iexists (nsReplay (W.2.take n) W.1, ([] : List NsOp))
    iframe Hn
    ipureintro
    refine ⟨rfl, fun m => ?_⟩
    show nsReplay (([] : List NsOp).take m) _ !! d = _
    simp only [List.take_nil]
    exact hall n
  · iexists W; iframe Hh; ipureintro; exact ⟨rfl, hall⟩

/-- The in-flight flag of the new generation, from the restart's. -/
theorem osNsBusy_start [L : GooseLocalGS GF] :
    ([∗map] k ↦ b ∈ busyMap false, gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γz k
      (DFrac.own 1) b) ⊢ osNsBusy (L := L) false := by
  unfold busyMap osNsBusy
  exact (BigSepM.bigSepM_singleton (M := GMap Unit)
    (Φ := fun (k : Unit) (b : Bool) =>
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γz k (DFrac.own 1) b)).1

end gen

/-! ## Crash adequacy with the namespace -/

attribute [local instance] osFsExts osFsExtsSemantics osFsExtsInterp osFsExts_hasOsFs

@[reducible] def osFsExtsCrashInterpN : GooseCrashInterp := ⟨(os_crash_interpN, ⟨⟩)⟩

attribute [local instance] osFsExtsCrashInterpN

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The start resources of `[osFsExt]` with the namespace: the invariant of the mapped cells,
every file, every directory and the in-flight flag. -/
theorem osFs_startN [hG : HeapGS .hasLC GF] (σ : state) :
    ⊢ extsLocalStart (GF := GF) σ.world ={⊤}=∗
      osInv (L := hG.goose_localGS) ∗
      ([∗map] p ↦ fo ∈ (extLocal osFsExt σ.world).files, osFileStart (L := hG.goose_localGS) p fo) ∗
      osNsAll (L := hG.goose_localGS) (DFrac.own 1) ((extLocal osFsExt σ.world).ns, ([] : List NsOp)) ∗
      osNsBusy (L := hG.goose_localGS) false := by
  have Hl : extsLocalStart (GF := GF) σ.world ⊢
      osStart (gooseOsGS (L := hG.goose_localGS)) (extLocal osFsExt σ.world) :=
    sep_elim_left
  iintro Hs
  icases Hl $$ Hs with Hs
  unfold osStart
  icases Hs with ⟨Hs, Hns⟩
  icases osStartF_files _ _ $$ Hs with ⟨Hfs, Hv⟩
  unfold nsStart
  icases Hns with ⟨Hds, Hz⟩
  imod osInv_alloc (L := hG.goose_localGS) ⊤ $$ Hv with #Hinv
  imodintro
  iframe Hinv
  isplitl [Hfs]
  · iapply BigSepM.bigSepM_mono (fun {p fo} _ => (fileStart_eq (L := hG.goose_localGS) p fo).1) $$ Hfs
  isplitl [Hds]
  · unfold osNsAll; iexact Hds
  · iapply osNsBusy_start (L := hG.goose_localGS) $$ Hz

/-- **Crash adequacy for a program with Linux files and a namespace**, as `osFs_crash_adequacyT`,
with the crash interpretation `os_crash_interpN`: the first generation gets every directory too,
and after a crash, the proof of a generation gets `crashRestT` and `nsCrashRest`, from which it
takes the files and the directories, and the in-flight flag. -/
theorem osFs_crash_adequacyN [hPre : GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state)
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
        osNsAll (L := hG.goose_localGS) (DFrac.own 1) ((extLocal osFsExt σ.world).ns, ([] : List NsOp)) -∗
        osNsBusy (L := hG.goose_localGS) false -∗
        ownGoState σ.goState.packageState ={⊤}=∗ P hG.goose_localGS)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          osInv (L := L') -∗
          crashRestT (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) [] -∗
          nsCrashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) -∗
          osNsBusy (L := L') false -∗
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
    imod osFs_startN σ $$ Hs with ⟨#Hinv, Hfs, Hds, Hz⟩
    iapply Hstart HN HT Hlctx $$ Hinv Hfs Hds Hz Hgs
  · intro hG HN HT Hlctx
    iintro HP Htok
    imod Hwp HN HT Hlctx $$ HP Htok with ⟨Hwp, Hcrash⟩
    imodintro
    iframe Hwp
    iintro %L' Hcr Hcs Hgs
    have Hc : extsCrashStart (GF := GF) hG.goose_localGS L' ⊢
        osCrashStartN (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) :=
      sep_elim_left
    icases Hc $$ Hcs with Hcs
    unfold osCrashStartN osCrashStartT
    icases Hcs with ⟨⟨Hv, Hr⟩, Hn, Hz⟩
    imod osInv_alloc (L := L') ⊤ $$ Hv with #Hinv
    iapply Hcrash $$ %L' Hcr Hinv Hr Hn [Hz] Hgs
    iapply osNsBusy_start (L := L') $$ Hz

end adequacy


end Perennial

