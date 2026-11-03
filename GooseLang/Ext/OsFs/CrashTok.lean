/-
A crash interpretation of the Linux file extension that keeps the old generation's in-flight
changes (`os_crash_interpT`), and crash adequacy with it (`osFs_crash_adequacyT`).

`os_crash_interp` (`Crash.lean`) gives the restart the old generation's maps of bytes and files
(`crashRest`), from which a file is taken with a fragment of its `OsMeta` (`osCrash_take`). A
change in flight holds such a fragment itself (`tokRes`), all of the `OsMeta` if it may resize the
file (a `pwrite` past the end, a truncate): while it is in flight no invariant can hold any of it,
so a crash proof could not take that file. `os_crash_interpT` keeps the old generation's map of
changes and what they hold (`crashRestT`), so that a crash proof whose invariant holds a change's
token (`osTok`) gets back what the change holds (`crashRestT_tok`). The interpretation is not
trusted: crash adequacy is stated in the extension's terms (`OsCrash`) whatever the ghost state.

`crashRest_take_runs` takes a file with its bytes in any number of runs (`FileCrashedR`), so that
a client holding the bytes around a change in flight keeps what it knows of both sides.
-/
module

public import GooseLang.Ext.OsFs.Adequacy

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Taking a file with its bytes in runs -/

/-- What a crash did to the file at `p`, which the old generation knew as `mo`, with the bytes of
the runs `rs` (each `(off, dq, xs)`, the bytes `xs` from `off` on): `FileCrashed` for every run. -/
def FileCrashedR (mo : Option OsMeta) (rs : List (Nat × DFrac × List (w8 × Bool)))
    (fo : Option OsFile) : Prop :=
  match mo with
  | none => fo = none
  | some m => (fo = none ∧ m.named = false) ∨
      ∃ img, fo = some (OsFile.ofDisk img) ∧ m.lo ≤ img.length ∧ img.length ≤ m.hi ∧
        ∀ r ∈ rs, ∀ k x, r.2.2[k]? = some x → x.2 = true → img[r.1 + k]? = some x.1

theorem fileCrashedR_of_g {Γb : GMap (GoString × Nat) (w8 × Bool)} {p : GoString}
    {mo : Option OsMeta} {fo : Option OsFile} {rs : List (Nat × DFrac × List (w8 × Bool))}
    (h : FileCrashedG Γb p mo fo)
    (hxs : ∀ r ∈ rs, ∀ k (hk : k < r.2.2.length), Γb !! (p, r.1 + k) = some r.2.2[k]) :
    FileCrashedR mo rs fo := by
  cases mo with
  | none => exact h
  | some m =>
    rcases h with h | ⟨img, h1, h2, h3, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨img, h1, h2, h3, fun r hr k x hk hc => ?_⟩
      obtain ⟨hk', hx⟩ := List.getElem?_eq_some_iff.1 hk
      have := hxs r hr k hk'
      rw [hx] at this
      obtain ⟨b, c⟩ := x
      simp only at hc ⊢; subst hc
      exact h4 _ _ this

section files
variable {GF : BundledGFunctors} (hL : OsGS GF)

theorem bytesG_lookup_runs (p : GoString) (Γb : GMap (GoString × Nat) (w8 × Bool)) :
    ∀ rs : List (Nat × DFrac × List (w8 × Bool)),
    ⊢ gAuth hL hL.γb Γb -∗ ([∗list] r ∈ rs, bytesG hL p r.1 r.2.1 r.2.2) -∗
      ⌜∀ r ∈ rs, ∀ k (hk : k < r.2.2.length), Γb !! (p, r.1 + k) = some r.2.2[k]⌝
  | [] => by
    iintro _ _
    ipureintro
    intro r hr; cases hr
  | r :: rs => by
    iintro HA Hrs
    icases BigSepL.bigSepL_cons.1 $$ Hrs with ⟨Hr, Hrs⟩
    icases bytesG_lookup hL p r.1 r.2.1 r.2.2 Γb $$ HA Hr with %h1
    icases bytesG_lookup_runs p Γb rs $$ HA Hrs with %h2
    ipureintro
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | h
    · exact h1
    · exact h2 r' h

/-- `crashRest_take` with the bytes in runs. -/
theorem crashRest_take_runs (hL' : OsGS GF) (D : List GoString) (p : GoString) (hp : p ∉ D)
    (dq : DFrac) (mo : Option OsMeta) (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRest hL hL' D -∗ gElem hL hL.γm p dq mo -∗
      ([∗list] r ∈ rs, bytesG hL p r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR mo rs fo⌝ ∗ fileStart hL' p fo ∗ crashRest hL hL' (p :: D) := by
  unfold crashRest
  iintro ⟨%Γb, %Γm, %F, %hrel, Hab, Ham, Hfs⟩ Hm Hbs
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup_runs hL p Γb rs $$ Hab Hbs with %hxs
  obtain ⟨fo, hF, hfc⟩ := hrel p mo hmo hp
  icases (BigSepM.bigSepM_delete (Φ := fun p fo => fileStart hL' p fo) hF).1 $$ Hfs with ⟨Hf, Hfs⟩
  iexists fo
  iframe Hf
  isplitr
  · ipureintro; exact fileCrashedR_of_g hfc hxs
  iexists Γb, Γm, GMap.delete p F
  iframe Hab Ham Hfs
  ipureintro
  intro q mq hq hqD
  have hqp : q ≠ p := fun h => hqD (h ▸ List.mem_cons_self)
  obtain ⟨fq, h1, h2⟩ := hrel q mq hq (fun h => hqD (List.mem_cons_of_mem _ h))
  exact ⟨fq, by rw [GMap.lookup_delete_ne _ (Ne.symm hqp)]; exact h1, h2⟩

/-- `crashRest_take_runs`, giving back the old generation's resources it looks at (so that an
invariant that held them can be closed again). -/
theorem crashRest_take_runs_keep (hL' : OsGS GF) (D : List GoString) (p : GoString) (hp : p ∉ D)
    (dq : DFrac) (mo : Option OsMeta) (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRest hL hL' D -∗ gElem hL hL.γm p dq mo -∗
      ([∗list] r ∈ rs, bytesG hL p r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR mo rs fo⌝ ∗ fileStart hL' p fo ∗ crashRest hL hL' (p :: D) ∗
        gElem hL hL.γm p dq mo ∗ ([∗list] r ∈ rs, bytesG hL p r.1 r.2.1 r.2.2) := by
  unfold crashRest
  iintro ⟨%Γb, %Γm, %F, %hrel, Hab, Ham, Hfs⟩ Hm Hbs
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup_runs hL p Γb rs $$ Hab Hbs with %hxs
  obtain ⟨fo, hF, hfc⟩ := hrel p mo hmo hp
  icases (BigSepM.bigSepM_delete (Φ := fun p fo => fileStart hL' p fo) hF).1 $$ Hfs with ⟨Hf, Hfs⟩
  iexists fo
  iframe Hf Hm Hbs
  isplitr
  · ipureintro; exact fileCrashedR_of_g hfc hxs
  iexists Γb, Γm, GMap.delete p F
  iframe Hab Ham Hfs
  ipureintro
  intro q mq hq hqD
  have hqp : q ≠ p := fun h => hqD (h ▸ List.mem_cons_self)
  obtain ⟨fq, h1, h2⟩ := hrel q mq hq (fun h => hqD (List.mem_cons_of_mem _ h))
  exact ⟨fq, by rw [GMap.lookup_delete_ne _ (Ne.symm hqp)]; exact h1, h2⟩

end files

/-! ## The crash interpretation -/

section crash
variable {GF : BundledGFunctors}

/-- `crashRest`, and the old generation's map of changes in flight with what they hold. -/
def crashRestT (hL hL' : OsGS GF) (D : List GoString) : IProp GF :=
  iprop(crashRest hL hL' D ∗
    ∃ (st : OsState) (Γt : GMap Nat TokInfo), gAuth hL hL.γt Γt ∗ tokRes hL st Γt)

/-- The restart's resources (`osCrashStart`, with `crashRestT`). -/
def osCrashStartT (hL hL' : OsGS GF) : IProp GF :=
  iprop(gVar hL' (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0) ∗ crashRestT hL hL' [])

theorem crashRestT_take_runs (hL hL' : OsGS GF) (D : List GoString) (p : GoString) (hp : p ∉ D)
    (dq : DFrac) (mo : Option OsMeta) (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRestT hL hL' D -∗ gElem hL hL.γm p dq mo -∗
      ([∗list] r ∈ rs, bytesG hL p r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR mo rs fo⌝ ∗ fileStart hL' p fo ∗ crashRestT hL hL' (p :: D) := by
  unfold crashRestT
  iintro ⟨Hr, Ht⟩ Hm Hbs
  icases crashRest_take_runs hL hL' D p hp dq mo rs $$ Hr Hm Hbs with ⟨%fo, %h, Hf, Hr⟩
  iexists fo
  iframe Hf Hr Ht
  ipureintro; exact h

/-- **A change in flight after a crash**: its token gives back the fragment of the file's
`OsMeta` the change holds. -/
theorem crashRestT_tok (hL hL' : OsGS GF) (D : List GoString) (t : Nat) (ti : TokInfo) :
    ⊢ crashRestT hL hL' D -∗ gElem hL hL.γt t (DFrac.own 1) ti ==∗
      gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗ crashRestT hL hL' D := by
  unfold crashRestT
  iintro ⟨Hr, %st, %Γt, HAt, Htok⟩ Ht
  icases gAuth_lookup hL _ _ _ _ _ $$ HAt Ht with %hti
  imod gAuth_delete hL _ _ _ _ $$ HAt Ht with HAt
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
      bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false)))) hti).1
    $$ Htok with ⟨⟨Hm, -⟩, Htok⟩
  imodintro
  iframe Hm Hr
  iexists st, GMap.delete t Γt
  iframe

theorem crashRestT_take_runs_keep (hL hL' : OsGS GF) (D : List GoString) (p : GoString)
    (hp : p ∉ D) (dq : DFrac) (mo : Option OsMeta) (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRestT hL hL' D -∗ gElem hL hL.γm p dq mo -∗
      ([∗list] r ∈ rs, bytesG hL p r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR mo rs fo⌝ ∗ fileStart hL' p fo ∗ crashRestT hL hL' (p :: D) ∗
        gElem hL hL.γm p dq mo ∗ ([∗list] r ∈ rs, bytesG hL p r.1 r.2.1 r.2.2) := by
  unfold crashRestT
  iintro ⟨Hr, Ht⟩ Hm Hbs
  icases crashRest_take_runs_keep hL hL' D p hp dq mo rs $$ Hr Hm Hbs with ⟨%fo, %h, Hf, Hr, Hm, Hbs⟩
  iexists fo
  iframe Hf Hr Ht Hm Hbs
  ipureintro; exact h

/-- `crashRestT_tok`, lending the fragment instead of taking it: the token is kept. -/
theorem crashRestT_tok_lend (hL hL' : OsGS GF) (D : List GoString) (t : Nat) (ti : TokInfo) :
    ⊢ crashRestT hL hL' D -∗ gElem hL hL.γt t (DFrac.own 1) ti -∗
      gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
      (gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) -∗ crashRestT hL hL' D) ∗
      gElem hL hL.γt t (DFrac.own 1) ti := by
  unfold crashRestT
  iintro ⟨Hr, %st, %Γt, HAt, Htok⟩ Ht
  icases gAuth_lookup hL _ _ _ _ _ $$ HAt Ht with %hti
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
      bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false)))) hti).1
    $$ Htok with ⟨⟨Hm, Hb⟩, Htok⟩
  iframe Hm Ht
  iintro Hm
  iframe Hr
  iexists st, Γt
  iframe HAt
  iapply (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
      bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false)))) hti).2
  iframe

/-- Taking the file a change in flight is on, with the fragment of `OsMeta` the change holds, and
giving back the token. -/
theorem crashRestT_take_tok_keep (hL hL' : OsGS GF) (D : List GoString) (t : Nat) (ti : TokInfo)
    (hp : ti.c.path ∉ D) (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRestT hL hL' D -∗ gElem hL hL.γt t (DFrac.own 1) ti -∗
      ([∗list] r ∈ rs, bytesG hL ti.c.path r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR (some ti.om) rs fo⌝ ∗ fileStart hL' ti.c.path fo ∗
        crashRestT hL hL' (ti.c.path :: D) ∗ gElem hL hL.γt t (DFrac.own 1) ti ∗
        ([∗list] r ∈ rs, bytesG hL ti.c.path r.1 r.2.1 r.2.2) := by
  unfold crashRestT
  iintro ⟨Hr, %st, %Γt, HAt, Htok⟩ Ht Hbs
  icases gAuth_lookup hL _ _ _ _ _ $$ HAt Ht with %hti
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
      bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false)))) hti).1
    $$ Htok with ⟨⟨Hm, Hb⟩, Htok⟩
  icases crashRest_take_runs_keep hL hL' D ti.c.path hp _ _ rs $$ Hr Hm Hbs
    with ⟨%fo, %h, Hf, Hr, Hm, Hbs⟩
  iexists fo
  iframe Hf Hr Ht Hbs
  isplitr
  · ipureintro; exact h
  iexists st, Γt
  iframe HAt
  iapply (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
      bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false)))) hti).2
  iframe

/-- `os_local_crash`, keeping the changes in flight. -/
theorem os_local_crashT (hPre : OsGpreS GF) (hL : OsGS GF) (st st' : OsState)
    (hc : OsCrash st st') :
    ⊢@{IProp GF} osCtx hL st ==∗ ∃ hL' : OsGS GF, osCtx hL' st' ∗ osCrashStartT hL hL' := by
  unfold osCtx
  iintro ⟨%Γb, %Γm, %Γf, %Γt, %hwc, Hab, Ham, -, HAt, Htok, -⟩
  obtain ⟨hinit, hrel⟩ := osCrash_rel hwc.2 hc
  imod os_local_init hPre st' hinit with ⟨%hL', Hctx, Hst⟩
  unfold osCtx
  icases osStart_files hL' st' $$ Hst with ⟨Hfs, Hv⟩
  imodintro
  iexists hL'
  iframe Hctx
  unfold osCrashStartT crashRestT crashRest
  iframe Hv
  isplitl [Hab Ham Hfs]
  · iexists Γb, Γm, st'.files
    iframe Hab Ham Hfs
    ipureintro; exact hrel
  · iexists st, Γt
    iframe

/-- The crash interpretation of the Linux file extension that keeps the changes in flight. -/
@[reducible] def os_crash_interpT : ExtCrashInterp osFsExt where
  crashStart hL hL' := osCrashStartT hL hL'
  local_crash _ hPre hL st st' hc := os_local_crashT hPre hL st st' hc

end crash

/-! ## In a generation's terms -/

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- `crashRestT_take_runs` from the old generation `L` to the new one `L'`. -/
theorem osCrashT_take_runs (L L' : GooseLocalGS GF) (D : List GoString) (p : GoString)
    (hp : p ∉ D) (dq : DFrac) (mo : Option OsMeta) (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ osMeta (L := L) p dq mo -∗
      ([∗list] r ∈ rs, osBytes (L := L) p r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR mo rs fo⌝ ∗ osFileStart (L := L') p fo ∗
        crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) (p :: D) := by
  unfold osMeta osBytes
  iintro Hr Hm Hb
  icases crashRestT_take_runs _ _ D p hp dq mo rs $$ Hr Hm Hb with ⟨%fo, %h, Hf, Hr⟩
  iexists fo
  iframe Hr
  isplitr
  · ipureintro; exact h
  iapply (fileStart_eq (L := L') p fo).1 $$ Hf

/-- `crashRestT_tok` in the generation `L`'s terms. -/
theorem osCrashT_tok (L L' : GooseLocalGS GF) (D : List GoString) (t : Nat) (ti : TokInfo) :
    ⊢ crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ osTok (L := L) t ti ==∗
      osMeta (L := L) ti.c.path (DFrac.own ti.q) (some ti.om) ∗
        crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) D := by
  unfold osMeta osTok
  iintro Hr Ht
  iapply crashRestT_tok $$ Hr Ht

theorem osCrashT_take_runs_keep (L L' : GooseLocalGS GF) (D : List GoString) (p : GoString)
    (hp : p ∉ D) (dq : DFrac) (mo : Option OsMeta) (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ osMeta (L := L) p dq mo -∗
      ([∗list] r ∈ rs, osBytes (L := L) p r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR mo rs fo⌝ ∗ osFileStart (L := L') p fo ∗
        crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) (p :: D) ∗
        osMeta (L := L) p dq mo ∗ ([∗list] r ∈ rs, osBytes (L := L) p r.1 r.2.1 r.2.2) := by
  unfold osMeta osBytes
  iintro Hr Hm Hb
  icases crashRestT_take_runs_keep _ _ D p hp dq mo rs $$ Hr Hm Hb with ⟨%fo, %h, Hf, Hr, Hm, Hb⟩
  iexists fo
  iframe Hr Hm Hb
  isplitr
  · ipureintro; exact h
  iapply (fileStart_eq (L := L') p fo).1 $$ Hf

theorem osCrashT_take_tok_keep (L L' : GooseLocalGS GF) (D : List GoString) (t : Nat)
    (ti : TokInfo) (hp : ti.c.path ∉ D) (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ osTok (L := L) t ti -∗
      ([∗list] r ∈ rs, osBytes (L := L) ti.c.path r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR (some ti.om) rs fo⌝ ∗ osFileStart (L := L') ti.c.path fo ∗
        crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) (ti.c.path :: D) ∗
        osTok (L := L) t ti ∗ ([∗list] r ∈ rs, osBytes (L := L) ti.c.path r.1 r.2.1 r.2.2) := by
  unfold osTok osBytes
  iintro Hr Ht Hb
  icases crashRestT_take_tok_keep _ _ D t ti hp rs $$ Hr Ht Hb with ⟨%fo, %h, Hf, Hr, Ht, Hb⟩
  iexists fo
  iframe Hr Ht Hb
  isplitr
  · ipureintro; exact h
  iapply (fileStart_eq (L := L') _ fo).1 $$ Hf

theorem osCrashT_tok_lend (L L' : GooseLocalGS GF) (D : List GoString) (t : Nat) (ti : TokInfo) :
    ⊢ crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ osTok (L := L) t ti -∗
      osMeta (L := L) ti.c.path (DFrac.own ti.q) (some ti.om) ∗
      (osMeta (L := L) ti.c.path (DFrac.own ti.q) (some ti.om) -∗
        crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) D) ∗
      osTok (L := L) t ti := by
  unfold osMeta osTok
  iintro Hr Ht
  iapply crashRestT_tok_lend $$ Hr Ht

end gen

/-! ## Crash adequacy with the changes in flight -/

attribute [local instance] osFsExts osFsExtsSemantics osFsExtsInterp osFsExts_hasOsFs

@[reducible] def osFsExtsCrashInterpT : GooseCrashInterp := ⟨(os_crash_interpT, ⟨⟩)⟩

attribute [local instance] osFsExtsCrashInterpT

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- **Crash adequacy for a program with Linux files**, as `osFs_crash_adequacy`, with the crash
interpretation `os_crash_interpT`: after a crash, the proof of a generation gets `crashRestT`,
from which it takes the files and the fragments of `OsMeta` its changes in flight held. -/
theorem osFs_crash_adequacyT [hPre : GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state)
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
          crashRestT (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) [] -∗
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
        osCrashStartT (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) :=
      sep_elim_left
    icases Hc $$ Hcs with Hcs
    unfold osCrashStartT
    icases Hcs with ⟨Hv, Hr⟩
    imod osInv_alloc (L := L') ⊤ $$ Hv with #Hinv
    iapply Hcrash $$ %L' Hcr Hinv Hr Hgs

end adequacy

end Perennial
