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

/-- A file operation changes no path's being a directory. -/
theorem fileOp_dir {m : NsMap} {o : NsOp} (h : FileOp m o) (e : GoString) :
    (o.apply m !! e = some .dir) ↔ (m !! e = some .dir) := by
  cases o with
  | create p k =>
    obtain ⟨hn, -, -⟩ := h
    show (<[p := OsNode.file k]> m) !! e = _ ↔ _
    by_cases he : p = e
    · subst he; rw [GMap.lookup_insert, hn]; simp
    · rw [GMap.lookup_insert_ne _ _ he]
  | remove p =>
    obtain ⟨k, hf⟩ := h
    show (GMap.delete p m) !! e = _ ↔ _
    by_cases he : p = e
    · subst he; rw [GMap.lookup_delete, hf]; simp
    · rw [GMap.lookup_delete_ne _ he]
  | rename s t =>
    obtain ⟨⟨k, hf⟩, ht, -⟩ := h
    have happ : (NsOp.rename s t).apply m = <[t := .file k]> (GMap.delete s m) := by
      simp only [NsOp.apply, hf]
    rw [happ]
    show (<[t := OsNode.file k]> (GMap.delete s m)) !! e = _ ↔ _
    by_cases h1 : t = e
    · subst h1; rw [GMap.lookup_insert]
      constructor
      · intro h; cases h
      · intro h; exact absurd h ht
    · rw [GMap.lookup_insert_ne _ _ h1]
      by_cases h2 : s = e
      · subst h2; rw [GMap.lookup_delete, hf]; simp
      · rw [GMap.lookup_delete_ne _ h2]
  | mkdir p => exact h.elim

/-- Every prefix of the log replayed has the directories of the durable namespace. -/
theorem replay_dirs {st : OsState} {Γd Γdf} (hc : NsCoh st Γd Γdf) :
    ∀ n, n ≤ st.nsLog.length → ∀ e,
      (nsReplay (st.nsLog.take n) st.nsDur !! e = some .dir) ↔ (st.nsDur !! e = some .dir) := by
  intro n
  induction n with
  | zero => intro _ e; simp [nsReplay]
  | succ n ih =>
    intro hn e
    rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some]
    rw [nsReplay_snoc, fileOp_dir (hc.ops n (by omega)) e]
    exact ih (by omega) e

/-- After a crash, every directory the old ghost state knew has an entry that is a crash outcome
of the old one. -/
theorem nsCrash_dirs {st st' : OsState} {Γd Γdf} (hw : NsWf st) (hc : NsCoh st Γd Γdf)
    (hcr : NsCrash st st') :
    ∀ d g, Γd !! d = some g → dirMap st' !! d = some ⟨entsOf st'.ns d, []⟩ ∧
      g.CrashTo (entsOf st'.ns d) := by
  obtain ⟨-, -, -, -, -, ⟨n, hn, hns⟩, -⟩ := hcr
  intro d g hg
  have hdir : st.ns !! d = some .dir := (hc.dirs d).1 (by rw [hg]; rfl)
  have hdur : st.nsDur !! d = some .dir := by
    have := (replay_dirs hc st.nsLog.length (Nat.le_refl _) d).1
    rw [List.take_length, ← hw.replay] at this
    exact this hdir
  have hdir' : st'.ns !! d = some .dir := by rw [hns]; exact (replay_dirs hc n hn d).2 hdur
  refine ⟨by rw [dirMap_lookup, if_pos hdir'], ?_⟩
  rw [hns]; exact hc.hist d g hg n hn

/-! ## The crash interpretation -/

section crash
variable {GF : BundledGFunctors}

/-- The namespace's part of the restart: the old generation's directories' ghost entries and the
new generation's directories (those not yet taken), each a crash outcome of the old (`D`: the
directories taken). -/
def nsCrashRest (hL hL' : OsGS GF) (D : List GoString) : IProp GF :=
  iprop(∃ (Γd Dirs : GMap GoString DirG), gAuth hL hL.γd Γd ∗
    ([∗map] d ↦ g' ∈ Dirs, gElem hL' hL'.γd d (DFrac.own 1) g') ∗
    ⌜∀ d g, Γd !! d = some g → d ∉ D → ∃ g', Dirs !! d = some g' ∧ g'.pend = [] ∧ g.CrashTo g'.dur⌝)

/-- The restart's resources: `osCrashStartT`'s, the namespace's, and the new in-flight flag. -/
def osCrashStartN (hL hL' : OsGS GF) : IProp GF :=
  iprop(osCrashStartT hL hL' ∗ nsCrashRest hL hL' [] ∗
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
  have hdirs := nsCrash_dirs hns.1 hns.2 hc.2
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
  · iexists Γd, (dirMap st')
    iframe HAd Hds
    ipureintro
    intro d g hg _
    obtain ⟨h1, h2⟩ := hdirs d g hg
    exact ⟨_, h1, rfl, h2⟩

/-- The crash interpretation of the Linux file extension with the namespace. -/
@[reducible] def os_crash_interpN : ExtCrashInterp osFsExt where
  crashStart hL hL' := osCrashStartN hL hL'
  local_crash _ hPre hL st st' hc := os_local_crashN hPre hL st st' hc

end crash

/-! ## In a generation's terms -/

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **A directory after a crash**: from (a fraction of) the old generation's ghost entry `g` of
`d`, the new generation's, whole, with no change since a commit, its entries a crash outcome of
`g`. The old fraction is given back. -/
theorem osNsCrash_take (L L' : GooseLocalGS GF) (D : List GoString) (d : GoString) (hd : d ∉ D)
    (dq : DFrac) (g : DirG) :
    ⊢ nsCrashRest (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ osDir (L := L) d dq g -∗
      ∃ g', ⌜g'.pend = [] ∧ g.CrashTo g'.dur⌝ ∗ osDir (L := L') d (DFrac.own 1) g' ∗
        nsCrashRest (gooseOsGS (L := L)) (gooseOsGS (L := L')) (d :: D) ∗ osDir (L := L) d dq g := by
  unfold nsCrashRest osDir
  iintro ⟨%Γd, %Dirs, HAd, Hds, %hrel⟩ Hd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hd with %Hdl
  obtain ⟨g', hg', hp, hcr⟩ := hrel d g Hdl hd
  icases (BigSepM.bigSepM_delete (M := GMap GoString)
    (Φ := fun (d : GoString) (g' : DirG) =>
      gElem (gooseOsGS (L := L')) (gooseOsGS (L := L')).γd d (DFrac.own 1) g') hg').1 $$ Hds
    with ⟨Hg', Hds⟩
  iexists g'
  iframe Hg' Hd
  isplitr
  · ipureintro; exact ⟨hp, hcr⟩
  iexists Γd, (GMap.delete d Dirs)
  iframe HAd Hds
  ipureintro
  intro e ge hge he
  have hed : e ≠ d := fun h => he (h ▸ List.mem_cons_self)
  obtain ⟨g2, h1, h2⟩ := hrel e ge hge (fun h => he (List.mem_cons_of_mem _ h))
  exact ⟨g2, by rw [GMap.lookup_delete_ne _ (Ne.symm hed)]; exact h1, h2⟩

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
      ([∗map] d ↦ g ∈ dirMap (extLocal osFsExt σ.world), osDir (L := hG.goose_localGS) d (DFrac.own 1) g) ∗
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
  · unfold osDir; iexact Hds
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
        ([∗map] d ↦ g ∈ dirMap (extLocal osFsExt σ.world),
          osDir (L := hG.goose_localGS) d (DFrac.own 1) g) -∗
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
          nsCrashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) [] -∗
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

