/-
What the ghost state of the Linux file extension (`Ghost.lean`) does at a crash: the crash
interpretation `os_crash_interp` (`ExtCrashInterp osFsExt`).

* The new generation's ghost state is new (`os_local_init`, from the crashed state, which is an
  `OsInit` state: no fd, change or mapping, every file as on disk).
* `crashStart old new` hands the restarted boot program the new generation's files, one by one
  (`osFileStart`: the file's `OsMeta` and its bytes, whole and clean), with the old generation's
  authoritative maps of bytes and files, and the pure fact (`CrashRel`) relating them: each file
  is kept or, if its name was not durable, may be gone; a kept file's size is within the old
  `OsMeta`'s crash bounds `[m.lo, m.hi]`, and each byte the old generation knew clean is in it,
  with its value. It also holds the new generation's half of the mapped cells' ghost variable,
  from which `osInv_alloc` allocates the new generation's invariant.
* `crashRest_take` (`osCrash_take` in a generation's terms) is how a boot program uses it: from
  the old generation's `osMeta p` and `osBytes p off xs` (say, from an invariant that survived the
  crash), it takes the new generation's file at `p`, and learns that the new file's bytes are
  `xs`'s wherever `xs` said clean.

The facts it rests on are `OsCoh`'s: a byte marked clean is below `sizeLo`, not dirty, not lost,
on disk, and under no change in flight; a file's `OsMeta` bounds its sizes since the last sync
and every in-flight change's target.
-/
module

public import GooseLang.Ext.OsFs.Specs
public import Perennial.GooseLang.CrashAdequacy

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## The pure relation across a crash -/

/-- What a crash did to the file at `p`, which the old generation's ghost state knew as `mo`, with
bytes `Γb`: an allowed path with no file stays so; a file is gone (only if its name was not
durable), or is on disk with a size within the old crash bounds and every byte the old ghost
state knew clean. -/
def FileCrashedG (Γb : GMap (GoString × Nat) (w8 × Bool)) (p : GoString) :
    Option OsMeta → Option OsFile → Prop
  | none, fo => fo = none
  | some m, fo => (fo = none ∧ m.named = false) ∨
      ∃ img, fo = some (OsFile.ofDisk img) ∧ m.lo ≤ img.length ∧ img.length ≤ m.hi ∧
        ∀ i b, Γb !! (p, i) = some (b, true) → img[i]? = some b

/-- The same, as a client sees it: from the old `OsMeta` `mo` and old bytes `xs` from `off` on. -/
def FileCrashed (mo : Option OsMeta) (off : Nat) (xs : List (w8 × Bool)) (fo : Option OsFile) :
    Prop :=
  match mo with
  | none => fo = none
  | some m => (fo = none ∧ m.named = false) ∨
      ∃ img, fo = some (OsFile.ofDisk img) ∧ m.lo ≤ img.length ∧ img.length ≤ m.hi ∧
        ∀ k x, xs[k]? = some x → x.2 = true → img[off + k]? = some x.1

/-- The old generation's maps `Γb`, `Γm` and the new generation's files `F` not yet taken: every
path the old generation knew, except those taken (`D`), has its file in `F`, as `FileCrashedG`
says. -/
def CrashRel (Γb : GMap (GoString × Nat) (w8 × Bool)) (Γm : GMap GoString (Option OsMeta))
    (F : GMap GoString (Option OsFile)) (D : List GoString) : Prop :=
  ∀ p mo, Γm !! p = some mo → p ∉ D → ∃ fo, F !! p = some fo ∧ FileCrashedG Γb p mo fo

theorem fileCrashed_of_g {Γb : GMap (GoString × Nat) (w8 × Bool)} {p : GoString}
    {mo : Option OsMeta} {fo : Option OsFile} {off : Nat} {xs : List (w8 × Bool)}
    (h : FileCrashedG Γb p mo fo) (hxs : ∀ k (hk : k < xs.length), Γb !! (p, off + k) = some xs[k]) :
    FileCrashed mo off xs fo := by
  cases mo with
  | none => exact h
  | some m =>
    rcases h with h | ⟨img, h1, h2, h3, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨img, h1, h2, h3, fun k x hk hc => ?_⟩
      obtain ⟨hk', hx⟩ := List.getElem?_eq_some_iff.1 hk
      have := hxs k hk'
      rw [hx] at this
      obtain ⟨b, c⟩ := x
      simp only at hc ⊢; subst hc
      exact h4 _ _ this

/-- The crash keeps what `OsCoh` says: the crashed state is an initial one, related to the old
ghost maps by `CrashRel`. -/
theorem osCrash_rel {st st' : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt)
    (hc : OsCrash st st') : OsInit st' ∧ CrashRel Γb Γm st'.files [] := by
  obtain ⟨hfd, hin, hmp, hfiles⟩ := hc
  refine ⟨⟨hfd, hin, hmp, fun p f hf => ?_⟩, fun p mo hmo _ => ?_⟩
  · have hp := hfiles p
    revert hp
    rcases st.files !! p with _ | _ | f0
    · intro hp; simp [hp] at hf
    · intro hp; simp [hp] at hf
    · rintro (⟨-, hp⟩ | ⟨img, -, hp⟩)
      · simp [hp] at hf
      · rw [hp] at hf; cases hf; rfl
  · cases mo with
    | none =>
      have hp := hfiles p
      rw [(hcoh.meta_none p).1 hmo] at hp
      exact ⟨none, hp, rfl⟩
    | some m =>
      obtain ⟨f, hf, hok⟩ := hcoh.meta_some p m hmo
      have hp := hfiles p
      rw [hf] at hp
      rcases hp with ⟨hn, hp⟩ | ⟨img, ⟨⟨hlo, hhi⟩, hbytes⟩, hp⟩
      · refine ⟨none, hp, Or.inl ⟨rfl, ?_⟩⟩
        rw [hok.named]; simpa using hn
      · refine ⟨_, hp, Or.inr ⟨img, rfl, ?_, ?_, ?_⟩⟩
        · rcases hlo with h | ⟨t, c, ht, hcp, h⟩
          · exact Nat.le_trans hok.lo h
          · exact Nat.le_trans (hok.targets t c ht hcp).1 h
        · rcases hhi with h | ⟨t, c, ht, hcp, h⟩
          · exact Nat.le_trans h hok.hi
          · exact Nat.le_trans h (hok.targets t c ht hcp).2
        · intro i b hb
          obtain ⟨f', hf', hcur, hclean⟩ := hcoh.bytes p i (b, true) hb
          obtain ⟨⟨hd, hl, hlo', hdur⟩, hnin⟩ := hclean rfl
          rw [file_eq_some] at hf'
          rw [hf] at hf'; cases hf'
          have hsz : st.size p = f.cur.length := size_of_file (file_eq_some.2 hf)
          have hicur : i < f.cur.length := (List.getElem?_eq_some_iff.1 hcur).1
          have hidur : i < f.durable.length := by
            have := hdur.trans hcur; exact (List.getElem?_eq_some_iff.1 this).1
          have hiimg : i < img.length := by
            rcases hlo with h | ⟨t, c, ht, hcp, h⟩
            · omega
            · revert h
              unfold OsChange.target
              rcases hck : c.kind with ⟨off, data⟩ | sz
              · rw [hcp, hsz]; intro h; dsimp only at h; omega
              · intro h
                dsimp only at h
                apply Classical.byContradiction; intro hlt
                apply hnin
                refine ⟨t, c, ht, hcp, ?_⟩
                unfold Affects; rw [hck]; dsimp only; rw [hcp, hsz]; omega
          have := hbytes i hiimg (by simp [hd]) (by simp [hl]) hnin hidur
          rw [List.getElem?_eq_getElem hiimg, this, ← List.getElem?_eq_getElem hidur, hdur, hcur]

/-! ## A generation's files, one by one -/

section files
variable {GF : BundledGFunctors} (hL : OsGS GF)

/-- The start resources of the file `fo` at `p`: its `OsMeta` (as on disk) and its bytes, whole
and clean, or the absence of a file. -/
def fileStart (p : GoString) : Option OsFile → IProp GF
  | none => gElem hL hL.γm p (DFrac.own 1) (none : Option OsMeta)
  | some f => iprop(gElem hL hL.γm p (DFrac.own 1) (some (initMeta f)) ∗
      bytesG hL p 0 (DFrac.own 1) (f.cur.map (·, true)))

theorem fileStart_none (p : GoString) :
    fileStart hL p none ⊣⊢ gElem hL hL.γm p (DFrac.own 1) (none : Option OsMeta) := .rfl

theorem fileStart_some (p : GoString) (f : OsFile) :
    fileStart hL p (some f) ⊣⊢ iprop(gElem hL hL.γm p (DFrac.own 1) (some (initMeta f)) ∗
      bytesG hL p 0 (DFrac.own 1) (f.cur.map (·, true))) := .rfl

theorem bigSepM_insertBytes (p : GoString) :
    ∀ (off : Nat) (ys : List (w8 × Bool)) (m : GMap (GoString × Nat) (w8 × Bool)),
    (∀ k, k < ys.length → m !! (p, off + k) = none) →
    ([∗map] k ↦ x ∈ insertBytes p off ys m, gElem hL hL.γb k (DFrac.own 1) x) ⊢
      bytesG hL p off (DFrac.own 1) ys ∗ [∗map] k ↦ x ∈ m, gElem hL hL.γb k (DFrac.own 1) x
  | off, [], m, _ => by
    simp only [insertBytes]
    iintro H; iframe H; iapply (bytesG_nil hL p off _).2; iempintro
  | off, y :: ys, m, hfree => by
    simp only [insertBytes]
    refine (bigSepM_insertBytes p (off + 1) ys _ (fun k hk => ?_)).trans ?_
    · rw [GMap.lookup_insert_ne _ _ (by simp; omega)]
      rw [show off + 1 + k = off + (k + 1) by omega]; exact hfree (k + 1) (by simp; omega)
    have hm : m !! (p, off) = none := by simpa using hfree 0 (by simp)
    have hins := (BigSepM.bigSepM_insert (Φ := fun k x => gElem hL hL.γb k (DFrac.own 1) x)
      (m := m) (i := (p, off)) (x := y) hm).1
    iintro ⟨H1, H2⟩
    icases hins $$ H2 with ⟨Hy, Hm⟩
    iframe Hm
    iapply (bytesG_cons hL p off _ y ys).2
    iframe

/-- The state with the files `F` and nothing else. -/
abbrev filesState (F : GMap GoString (Option OsFile)) : OsState := ⟨F, ∅, ∅, ∅⟩

theorem bytesMap_eq (st : OsState) : bytesMap st = bytesMap (filesState st.files) := rfl
theorem metaMap_eq (st : OsState) : metaMap st = metaMap (filesState st.files) := rfl

/-- The start resources of `os_interp` (`osStart`'s bytes and files), file by file. -/
theorem start_files : ∀ F : GMap GoString (Option OsFile),
    ([∗map] k ↦ x ∈ bytesMap (filesState F), gElem hL hL.γb k (DFrac.own 1) x) ∗
      ([∗map] p ↦ mo ∈ metaMap (filesState F), gElem hL hL.γm p (DFrac.own 1) mo) ⊢
    [∗map] p ↦ fo ∈ F, fileStart hL p fo := by
  refine GMap.map_ind ?_ ?_
  · have h1 : bytesMap (filesState (∅ : GMap GoString (Option OsFile))) = ∅ :=
      GMap.ext (fun k => by simp [bytesMap, OsState.file])
    have h2 : metaMap (filesState (∅ : GMap GoString (Option OsFile))) = ∅ :=
      GMap.ext (fun k => by simp [metaMap])
    rw [h1, h2]
    iintro -; iapply BigSepM.bigSepM_empty.2; iempintro
  · intro p fo F hp IH
    have hm : metaMap (filesState (<[p := fo]> F)) =
        <[p := fo.map initMeta]> (metaMap (filesState F)) :=
      GMap.ext (fun q => by
        by_cases hq : q = p
        · subst hq; simp [metaMap, GMap.lookup_fmap]
        · simp [metaMap, GMap.lookup_fmap, Ne.symm hq])
    have hmp : metaMap (filesState F) !! p = none := by simp [metaMap, GMap.lookup_fmap, hp]
    have Hins := (BigSepM.bigSepM_insert (Φ := fun p fo => fileStart hL p fo) (m := F) (x := fo)
      hp).2
    refine BIBase.Entails.trans ?_ Hins
    rw [hm]
    have Hmi := (BigSepM.bigSepM_insert (Φ := fun p mo => gElem hL hL.γm p (DFrac.own 1) mo)
      (m := metaMap (filesState F)) (i := p) (x := fo.map initMeta) (by exact hmp)).1
    refine BIBase.Entails.trans (sep_mono_right Hmi) ?_
    cases fo with
    | none =>
      have hb : bytesMap (filesState (<[p := none]> F)) = bytesMap (filesState F) :=
        GMap.ext (fun k => by
          obtain ⟨q, i⟩ := k
          by_cases hq : q = p
          · subst hq; simp [bytesMap, OsState.file, hp]
          · simp [bytesMap, OsState.file, Ne.symm hq])
      rw [hb]
      simp only [Option.map_none]
      iintro ⟨Hb, Hm, Hms⟩
      isplitl [Hm]
      · iapply (fileStart_none hL p).2; iexact Hm
      iapply IH; iframe
    | some f =>
      have hb : bytesMap (filesState (<[p := some f]> F)) =
          insertBytes p 0 (f.cur.map (·, true)) (bytesMap (filesState F)) :=
        GMap.ext (fun k => by
          obtain ⟨q, i⟩ := k
          rw [lookup_insertBytes]
          by_cases hq : q = p
          · subst hq
            simp only [bytesMap, OsState.file, GMap.lookup_insert, Option.bind_some, hp,
              Option.bind_none, _root_.true_and, Nat.zero_le, Nat.zero_add, List.length_map,
              Nat.sub_zero]
            by_cases hi : i < f.cur.length
            · simp [hi]
            · simp [hi]
          · simp [bytesMap, OsState.file, Ne.symm hq, hq])
      rw [hb]
      have Hb := bigSepM_insertBytes hL p 0
        (f.cur.map (·, true)) (bytesMap (filesState F))
        (fun k _ => by simp [bytesMap, OsState.file, hp])
      simp only [Option.map_some]
      iintro ⟨Hb', Hm, Hms⟩
      icases Hb $$ Hb' with ⟨Hb1, Hb2⟩
      isplitl [Hm Hb1]
      · iapply (fileStart_some hL p f).2; iframe
      iapply IH; iframe

/-- The start resources of `os_interp`, file by file, and the half of the cells' view. -/
theorem osStart_files (st : OsState) :
    osStart hL st ⊢ ([∗map] p ↦ fo ∈ st.files, fileStart hL p fo) ∗
      gVar hL (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0) := by
  unfold osStart
  rw [bytesMap_eq, metaMap_eq]
  iintro ⟨Hb, Hm, Hv⟩
  iframe Hv
  iapply start_files hL st.files; iframe

end files

/-! ## The crash interpretation -/

section crash
variable {GF : BundledGFunctors}

/-- What is left of the restart's resources once the files at `D` are taken: the old
generation's maps of bytes and files, and the new generation's files not taken, related by
`CrashRel`. -/
def crashRest (hL hL' : OsGS GF) (D : List GoString) : IProp GF :=
  iprop(∃ (Γb : GMap (GoString × Nat) (w8 × Bool)) (Γm : GMap GoString (Option OsMeta))
      (F : GMap GoString (Option OsFile)),
    ⌜CrashRel Γb Γm F D⌝ ∗ gAuth hL hL.γb Γb ∗ gAuth hL hL.γm Γm ∗
    [∗map] p ↦ fo ∈ F, fileStart hL' p fo)

/-- The restart's resources: the new generation's files, related to the old generation's, and
the new generation's half of the cells' view (for `osInv_alloc`). -/
def osCrashStart (hL hL' : OsGS GF) : IProp GF :=
  iprop(gVar hL' (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0) ∗ crashRest hL hL' [])

/-- **Taking a file after a crash.** From the old generation's `OsMeta` of `p` (any fraction) and
its bytes `xs` from `off` on (any fraction), the new generation's file at `p`, whole: gone (only
if the old name was not durable), or on disk with a size within the old crash bounds and the
bytes of `xs` wherever `xs` said clean. -/
theorem crashRest_take (hL hL' : OsGS GF) (D : List GoString) (p : GoString) (hp : p ∉ D)
    (dq dq' : DFrac) (mo : Option OsMeta) (off : Nat) (xs : List (w8 × Bool)) :
    ⊢ crashRest hL hL' D -∗ gElem hL hL.γm p dq mo -∗ bytesG hL p off dq' xs -∗
      ∃ fo, ⌜FileCrashed mo off xs fo⌝ ∗ fileStart hL' p fo ∗ crashRest hL hL' (p :: D) := by
  unfold crashRest
  iintro ⟨%Γb, %Γm, %F, %hrel, Hab, Ham, Hfs⟩ Hm Hbs
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup hL _ _ _ _ _ $$ Hab Hbs with %hxs
  obtain ⟨fo, hF, hfc⟩ := hrel p mo hmo hp
  icases (BigSepM.bigSepM_delete (Φ := fun p fo => fileStart hL' p fo) hF).1 $$ Hfs with ⟨Hf, Hfs⟩
  iexists fo
  iframe Hf
  isplitr
  · ipureintro; exact fileCrashed_of_g hfc hxs
  iexists Γb, Γm, GMap.delete p F
  iframe Hab Ham Hfs
  ipureintro
  intro q mq hq hqD
  have hqp : q ≠ p := fun h => hqD (h ▸ List.mem_cons_self)
  obtain ⟨fq, h1, h2⟩ := hrel q mq hq (fun h => hqD (List.mem_cons_of_mem _ h))
  exact ⟨fq, by rw [GMap.lookup_delete_ne _ (Ne.symm hqp)]; exact h1, h2⟩

/-- The crash of the extension's ghost state: the new generation's ghost state is allocated from
the crashed state (an initial one), and the restart gets `osCrashStart`. -/
theorem os_local_crash (hPre : OsGpreS GF) (hL : OsGS GF) (st st' : OsState)
    (hc : OsCrash st st') :
    ⊢@{IProp GF} osCtx hL st ==∗ ∃ hL' : OsGS GF, osCtx hL' st' ∗ osCrashStart hL hL' := by
  unfold osCtx
  iintro ⟨%Γb, %Γm, %Γf, %Γt, %hwc, Hab, Ham, -, -, -, -⟩
  obtain ⟨hinit, hrel⟩ := osCrash_rel hwc.2 hc
  imod os_local_init hPre st' hinit with ⟨%hL', Hctx, Hst⟩
  unfold osCtx
  icases osStart_files hL' st' $$ Hst with ⟨Hfs, Hv⟩
  imodintro
  iexists hL'
  iframe Hctx
  unfold osCrashStart crashRest
  iframe Hv
  iexists Γb, Γm, st'.files
  iframe Hab Ham Hfs
  ipureintro; exact hrel

/-- The crash interpretation of the Linux file extension. -/
instance os_crash_interp : ExtCrashInterp osFsExt where
  crashStart hL hL' := osCrashStart hL hL'
  local_crash _ hPre hL st st' hc := os_local_crash hPre hL st st' hc

end crash

/-! ## In a generation's terms -/

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- The new file at `p`, in the generation `L`'s terms: its `OsMeta` as on disk and its bytes,
clean; or no file. -/
def osFileStart [L : GooseLocalGS GF] (p : GoString) : Option OsFile → IProp GF
  | none => osMeta (L := L) p (DFrac.own 1) none
  | some f => iprop(osMeta (L := L) p (DFrac.own 1) (some (initMeta f)) ∗
      osBytes (L := L) p 0 (DFrac.own 1) (f.cur.map (·, true)))

theorem fileStart_eq [L : GooseLocalGS GF] (p : GoString) (fo : Option OsFile) :
    fileStart (gooseOsGS (L := L)) p fo ⊣⊢ osFileStart (L := L) p fo := by
  cases fo <;> exact .rfl

/-- `crashRest_take` from the old generation `L` to the new one `L'`. -/
theorem osCrash_take (L L' : GooseLocalGS GF) (D : List GoString) (p : GoString) (hp : p ∉ D)
    (dq dq' : DFrac) (mo : Option OsMeta) (off : Nat) (xs : List (w8 × Bool)) :
    ⊢ crashRest (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ osMeta (L := L) p dq mo -∗
      osBytes (L := L) p off dq' xs -∗
      ∃ fo, ⌜FileCrashed mo off xs fo⌝ ∗ osFileStart (L := L') p fo ∗
        crashRest (gooseOsGS (L := L)) (gooseOsGS (L := L')) (p :: D) := by
  unfold osMeta osBytes
  iintro Hr Hm Hb
  icases crashRest_take _ _ D p hp dq dq' mo off xs $$ Hr Hm Hb with ⟨%fo, %h, Hf, Hr⟩
  iexists fo
  iframe Hr
  isplitr
  · ipureintro; exact h
  iapply (fileStart_eq (L := L') p fo).1 $$ Hf

end gen

end Perennial
