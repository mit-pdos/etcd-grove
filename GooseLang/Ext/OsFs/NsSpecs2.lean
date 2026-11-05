/-
WP specs of the namespace's operations that change it, and of a directory fd's `fsync` and close
(`NsSpecs.lean` has the resources and the lifting). Untrusted.
-/
module

public import GooseLang.Ext.OsFs.NsSpecs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-! ## Pure facts -/

theorem nsWf_nsFree {st : OsState} (hw : NsWf st) : NsWf st.nsFree :=
  ⟨hw.roots, hw.replay, hw.hist, hw.legacy, hw.dfds, hw.disj⟩

theorem nsCoh_nsFree {st : OsState} {Γd Γdf} (hc : NsCoh st Γd Γdf) : NsCoh st.nsFree Γd Γdf :=
  hc.congr rfl rfl rfl rfl

theorem busyMap_insert (b b' : Bool) : (<[() := b]> (busyMap b')) = busyMap b := by
  apply GMap.ext; intro u; cases u; simp [busyMap]

theorem filesSame_nsFree (st : OsState) : FilesSame st st.nsFree := ⟨rfl, rfl, rfl, rfl⟩

theorem filesSame_nsDo (st : OsState) (o : NsOp) : FilesSame st (st.nsDo o) := ⟨rfl, rfl, rfl, rfl⟩

theorem FilesSame.trans {a b c : OsState} (h1 : FilesSame a b) (h2 : FilesSame b c) :
    FilesSame a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

theorem take_min_length (l : List NsOp) (k : Nat) :
    l.take (min k l.length) = l.take k := by
  rw [← List.take_take, List.take_length]

/-- A commit keeps the namespace's well-formedness... -/
theorem nsWf_nsCommit {st : OsState} (hw : NsWf st) (n : Nat) : NsWf (st.nsCommit n) := by
  refine ⟨hw.roots, ?_, fun m _ => ?_, hw.legacy, hw.dfds, hw.disj⟩
  · show st.ns = nsReplay (st.nsLog.drop n) (nsReplay (st.nsLog.take n) st.nsDur)
    rw [← nsReplay_append, List.take_append_drop]; exact hw.replay
  · simp only [OsState.nsCommit, nsReplay_commit]
    rw [← take_min_length]
    exact hw.hist _ (Nat.min_le_right _ _)

/-- ... and its coherence with the ghost maps: the crash outcomes after it are some before it. -/
theorem nsCoh_nsCommit {st : OsState} {Γd Γdf} (hc : NsCoh st Γd Γdf) (n : Nat) :
    NsCoh (st.nsCommit n) Γd Γdf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  refine ⟨h1, h2, fun d g hg m _ => ?_, fun j hj => ?_, h5, h6, h7⟩
  · simp only [OsState.nsCommit, nsReplay_commit]
    rw [← take_min_length]
    exact h3 d g hg _ (Nat.min_le_right _ _)
  · have hj' : j < (st.nsLog.drop n).length := hj
    simp only [List.length_drop] at hj'
    simp only [OsState.nsCommit, nsReplay_commit, List.getElem_drop]
    exact h4 (n + j) (by omega)

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- The holder of a directory's whole ghost entry knows that no read of it is in progress. -/
theorem rdRes_whole (d : GoString) (g : DirG) (Γdf : GMap w64 (GoString × DirPh)) :
    ⊢ osDir (L := L) d (DFrac.own 1) g -∗ rdRes (gooseOsGS (L := L)) Γdf -∗
      ⌜∀ fd rs g' q, Γdf !! fd ≠ some (d, .reading rs g' q)⌝ ∗ osDir (L := L) d (DFrac.own 1) g ∗
        rdRes (gooseOsGS (L := L)) Γdf := by
  iintro Hd Hrd
  by_cases hall : ∀ fd rs g' q, Γdf !! fd ≠ some (d, .reading rs g' q)
  · iframe; ipureintro; exact hall
  · obtain ⟨fd, h1⟩ := Classical.not_forall.1 hall
    obtain ⟨rs, h2⟩ := Classical.not_forall.1 h1
    obtain ⟨g', h3⟩ := Classical.not_forall.1 h2
    obtain ⟨q, h4⟩ := Classical.not_forall.1 h3
    have hx : Γdf !! fd = some (d, .reading rs g' q) := Classical.not_not.1 h4
    unfold rdRes
    icases BigSepM.bigSepM_lookup (M := GMap w64)
      (Φ := fun (_ : w64) (x : GoString × DirPh) => rdPart (gooseOsGS (L := L)) x) hx $$ Hrd with Hq
    unfold rdPart at *
    unfold osDir
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hd Hq with %Hv
    exact absurd (DFrac.valid_own_op Hv.1) (by simp)

/-- A namespace step that leaves the files alone and changes the namespace to a well-formed,
coherent state: the worlds after it. -/
theorem ns_step_close {st st' : OsState} {Γb Γm Γf Γt} {Γd' : GMap GoString DirG}
    {Γdf : GMap w64 (GoString × DirPh)} {h h' : GMap Loc (NonAtomic val)}
    (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) (hs : FilesSame st st')
    (hr : HeapRendered st st' h h') (hfr : MapsFresh st st' h)
    (hw' : NsWf st') (hc' : NsCoh st' Γd' Γdf) (bz : Bool) (hbz : st'.nsBusy = bz) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt -∗
      tokRes (gooseOsGS (L := L)) st Γt -∗ cellsRes (GF := GF) (cellView st) -∗ naHeapCtx tls h -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd Γd' -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf Γdf -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γz (busyMap bz) -∗
      rdRes (gooseOsGS (L := L)) Γdf ==∗
      osWorld (L := L) st' Γb Γm Γf Γt h' ∗ nsWorld (L := L) st' Γd' Γdf := by
  iintro HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd
  imod osWorld_filesSame hs hr hfr $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact ⟨hwf, hcoh⟩
  imodintro
  iframe Hw
  unfold nsWorld
  rw [hbz]
  iframe
  ipureintro; exact ⟨hw', hc'⟩

/-- `unlink(2)` of the file `b` of the directory `d`, with `d`'s whole ghost entry and the
in-flight flag set: the flag cleared; on success `b` removed; on failure removed or not. -/
theorem wp_osUnlink (d b k : GoString) (g : DirG) (hb : NameOk b)
    (hf : g.now !! b = some (.file k)) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d (DFrac.own 1) g -∗ osNsBusy (L := L) true -∗
      (∀ (e : w64) (g' : DirG),
        ⌜(e = 0 ∧ g' = g.push (.del b)) ∨ (e ≠ 0 ∧ (g' = g ∨ g' = g.push (.del b)))⌝ -∗
        osDir (L := L) d (DFrac.own 1) g' -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Unlink" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hd Hz HΦ
  iapply wp_os_stepN "Unlink" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases rdRes_whole d g Γdf $$ Hd Hrd with ⟨%Hnr, Hd, Hrd⟩
  unfold osDir osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hd with %Hdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hdir : st.ns !! d = some .dir := (hc.dirs d).1 (by rw [Hdl]; rfl)
  have hfile : st.ns !! child d b = some (.file k) := by
    rw [← entsOf_child st.ns d b hb, hc.now d g Hdl]; exact hf
  have hname := hw.nsName_child hdir hb
  have hin := fileOpIn_remove hb hfile
  have hop : FileOp st.ns (.remove (child d b)) := ⟨k, hfile⟩
  -- the states after the step
  have hwe : NsWf (st.nsFree.nsDo (.remove (child d b))) :=
    nsWf_fileOp hw rfl rfl rfl rfl rfl rfl (fun k f h => ⟨f, h⟩) (fun k h => .inl h)
      (shape_remove hw.shape hfile)
      (fun p k' hp => by
        have hp' : (GMap.delete (child d b) st.ns) !! p = some (.file k') := hp
        by_cases hpe : child d b = p
        · subst hpe; rw [GMap.lookup_delete] at hp'; cases hp'
        · rw [GMap.lookup_delete_ne _ hpe] at hp'; exact hw.keys hp')
      hin.dir
  have hce : NsCoh (st.nsFree.nsDo (.remove (child d b))) (<[d := g.push (.del b)]> Γd) Γdf :=
    nsCoh_fileOp hc Hdl Hnr hop hin rfl rfl rfl rfl hw.replay
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  have hs1 : FilesSame st (st.nsFree.nsDo (.remove (child d b))) :=
    hs0.trans (filesSame_nsDo _ _)
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs0 Hag
    exact ⟨_, h, st.nsFree, ⟨child d b, rfl, hname, hb1, .inr ⟨1, by decide, rfl, rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', hv, -, -, hres⟩ := Hst
  cases go.intoVal_inj hv
  imod gAuth_update _ _ _ _ _ false $$ HAz Hz with ⟨HAz, Hz⟩
  rw [busyMap_insert]
  -- the outcomes: removed (success or failure), or not
  have hcases : (st' = st.nsFree.nsDo (.remove (child d b)) ∧
      (e' = Val (#(0 : w64)) ∨ ∃ e : w64, e ≠ 0 ∧ e' = Val (#e))) ∨
      (st' = st.nsFree ∧ ∃ e : w64, e ≠ 0 ∧ e' = Val (#e)) := by
    rcases hres with ⟨-, ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩⟩ | ⟨e, he, rfl, rfl⟩
    · exact .inl ⟨rfl, .inl rfl⟩
    · exact .inr ⟨rfl, e, he, rfl⟩
    · exact .inl ⟨rfl, .inr ⟨e, he, rfl⟩⟩
    · exact .inr ⟨rfl, e, he, rfl⟩
  rcases hcases with ⟨rfl, he⟩ | ⟨rfl, e, he, rfl⟩
  · imod gAuth_update _ _ _ _ _ (g.push (.del b)) $$ HAd Hd with ⟨HAd, Hd⟩
    imod ns_step_close hwf hcoh hs1 Hr Hfr hwe hce false rfl $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf
      HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, (<[d := g.push (.del b)]> Γd), Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    rcases he with rfl | ⟨e, he, rfl⟩
    · iapply wp_value'
      iapply HΦ $$ %0 %_ %(.inl ⟨rfl, rfl⟩) Hd Hz
    · iapply wp_value'
      iapply HΦ $$ %e %_ %(.inr ⟨he, .inr rfl⟩) Hd Hz
  · imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb HAm HAf HAt
      Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, Γd, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %e %_ %(.inr ⟨he, .inl rfl⟩) Hd Hz

/-- `rmdir(2)` of a name of `d` that is no directory, with the in-flight flag set: it fails, the
flag cleared, nothing else changed. -/
theorem wp_osRmdirNotDir (d b : GoString) (dq : DFrac) (g : DirG) (hb : NameOk b)
    (hnd : g.now !! b ≠ some .dir) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d dq g -∗ osNsBusy (L := L) true -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osDir (L := L) d dq g -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rmdir" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hd Hz HΦ
  iapply wp_os_stepN "Rmdir" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  unfold osDir osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hd with %Hdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hdir : st.ns !! d = some .dir := (hc.dirs d).1 (by rw [Hdl]; rfl)
  have hnd' : st.ns !! child d b ≠ some .dir := by
    rw [← entsOf_child st.ns d b hb, hc.now d g Hdl]; exact hnd
  have hname := hw.nsName_child hdir hb
  have hnofd : ∀ fd df, st.dfds !! fd = some df → df.path ≠ child d b := by
    intro fd df hdf he; apply hnd'; rw [← he]; exact hw.dfds fd df hdf
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs0 Hag
    exact ⟨_, h, st.nsFree, ⟨child d b, rfl, hname, hb1, hnofd, .inr ⟨1, by decide, rfl, rfl⟩⟩,
      hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', hv, -, -, -, hres⟩ := Hst
  cases go.intoVal_inj hv
  rcases hres with ⟨⟨hdir', -⟩, -⟩ | ⟨e, he, rfl, rfl⟩
  · exact absurd hdir' hnd'
  imod gAuth_update _ _ _ _ _ false $$ HAz Hz with ⟨HAz, Hz⟩
  rw [busyMap_insert]
  imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb HAm
    HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, Γd, Γdf
  unfold osWorld nsWorld
  iframe Hw Hn
  iapply wp_value'
  iapply HΦ $$ %e %he Hd Hz

/-- `lstat`'s "is it a directory" of a name of `d` that is no directory: `0`. -/
theorem wp_osNsLstatDir (d b : GoString) (dq : DFrac) (g : DirG) (hb : NameOk b)
    (hnd : g.now !! b ≠ some .dir) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d dq g -∗
      (∀ e : w64, osDir (L := L) d dq g -∗ Φ (PairV (#(0 : w64)) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsLstatDir" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hd HΦ
  iapply wp_os_stepN "NsLstatDir" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  unfold osDir
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hd with %Hdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hdir : st.ns !! d = some .dir := (hc.dirs d).1 (by rw [Hdl]; rfl)
  have hnd' : st.ns !! child d b ≠ some .dir := by
    rw [← entsOf_child st.ns d b hb, hc.now d g Hdl]; exact hnd
  have hpath : st.NsPath (child d b) := .inr (hw.nsName_child hdir hb)
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨child d b, 0, 0, rfl, hpath, rfl, .inr rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', isDir, e, hv, -, hst, hres, rfl⟩ := Hst
  subst st'
  cases go.intoVal_inj hv
  have hd0 : isDir = 0 := by
    rcases hres with ⟨h1, -, -⟩ | h0
    · exact absurd h1 hnd'
    · exact h0
  subst hd0
  imod ns_step_close hwf hcoh (filesSame_refl st) Hr Hfr hw hc st.nsBusy rfl $$ HAb HAm HAf HAt
    Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, Γd, Γdf
  unfold osWorld nsWorld
  iframe Hw Hn
  iapply wp_value'
  iapply HΦ $$ %e Hd

/-- `rename(2)` of the file `bs` of `d` to `bt` (nothing or a file), with `d`'s whole ghost entry
and the in-flight flag set: the flag cleared; on success moved; on failure moved or not. -/
theorem wp_osRename (d bs bt k : GoString) (g : DirG) (hbs : NameOk bs) (hbt : NameOk bt)
    (hne : bs ≠ bt) (hf : g.now !! bs = some (.file k)) (ht : g.now !! bt ≠ some .dir)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d (DFrac.own 1) g -∗ osNsBusy (L := L) true -∗
      (∀ (e : w64) (g' : DirG),
        ⌜(e = 0 ∧ g' = g.push (.mv bs bt)) ∨ (e ≠ 0 ∧ (g' = g ∨ g' = g.push (.mv bs bt)))⌝ -∗
        osDir (L := L) d (DFrac.own 1) g' -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rename" (Val (PairV (#(child d bs)) (#(child d bt))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hd Hz HΦ
  iapply wp_os_stepN "Rename" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases rdRes_whole d g Γdf $$ Hd Hrd with ⟨%Hnr, Hd, Hrd⟩
  unfold osDir osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hd with %Hdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hdir : st.ns !! d = some .dir := (hc.dirs d).1 (by rw [Hdl]; rfl)
  have hfile : st.ns !! child d bs = some (.file k) := by
    rw [← entsOf_child st.ns d bs hbs, hc.now d g Hdl]; exact hf
  have ht' : st.ns !! child d bt ≠ some .dir := by
    rw [← entsOf_child st.ns d bt hbt, hc.now d g Hdl]; exact ht
  have hcne : child d bs ≠ child d bt := fun h => hne (List.cons.inj (List.append_cancel_left h)).2
  have hin := fileOpIn_rename hbs hbt hne hfile ht'
  have hop : FileOp st.ns (.rename (child d bs) (child d bt)) :=
    ⟨⟨k, hfile⟩, ht', by rw [parentOf_child' d bs hbs, parentOf_child' d bt hbt],
      ⟨d, parentOf_child' d bs hbs⟩, by rw [baseOf_child' d bt hbt]; exact hbt, hcne⟩
  have hok : RenameOk st (child d bs) (child d bt) := by
    refine ⟨hcne, parentDir_child hdir hbs, parentDir_child hdir hbt, ?_⟩
    rw [hfile]; exact ht'
  have hnofd : ∀ fd df, st.dfds !! fd = some df →
      (st.ns !! child d bs = some .dir → ¬ IsUnder (child d bs) df.path) ∧ df.path ≠ child d bt := by
    intro fd df hdf
    refine ⟨(fun h => by rw [hfile] at h; cases h), fun he => ht' ?_⟩
    rw [← he]; exact hw.dfds fd df hdf
  have happ : (NsOp.rename (child d bs) (child d bt)).apply st.ns =
      <[child d bt := .file k]> (GMap.delete (child d bs) st.ns) := by
    simp only [NsOp.apply, hfile]
  have hwe : NsWf (st.nsFree.nsDo (.rename (child d bs) (child d bt))) := by
    refine nsWf_fileOp hw rfl rfl rfl rfl rfl rfl (fun k f h => ⟨f, h⟩) (fun k h => .inl h) ?_ ?_
      hin.dir
    · rw [happ]
      exact shape_rename hw.shape hdir (hw.dir_form hdir) hbt hfile ht' hcne
    · intro p k' hp
      rw [happ] at hp
      by_cases h1 : child d bt = p
      · subst h1; rw [GMap.lookup_insert] at hp; cases hp; exact hw.keys hfile
      · rw [GMap.lookup_insert_ne _ _ h1] at hp
        by_cases h2 : child d bs = p
        · subst h2; rw [GMap.lookup_delete] at hp; cases hp
        · rw [GMap.lookup_delete_ne _ h2] at hp; exact hw.keys hp
  have hce : NsCoh (st.nsFree.nsDo (.rename (child d bs) (child d bt)))
      (<[d := g.push (.mv bs bt)]> Γd) Γdf :=
    nsCoh_fileOp hc Hdl Hnr hop hin rfl rfl rfl rfl hw.replay
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  have hs1 : FilesSame st (st.nsFree.nsDo (.rename (child d bs) (child d bt))) :=
    hs0.trans (filesSame_nsDo _ _)
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs0 Hag
    exact ⟨_, h, st.nsFree, ⟨child d bs, child d bt, rfl, hw.nsName_child hdir hbs,
      hw.nsName_child hdir hbt, hb1, hnofd, .inr (.inr ⟨1, by decide, rfl, rfl⟩)⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨s', t', hv, -, -, -, -, hres⟩ := Hst
  injection hv with hv1 hv2
  cases go.intoVal_inj hv1; cases go.intoVal_inj hv2
  imod gAuth_update _ _ _ _ _ false $$ HAz Hz with ⟨HAz, Hz⟩
  rw [busyMap_insert]
  have hcases : (st' = st.nsFree.nsDo (.rename (child d bs) (child d bt)) ∧
      (e' = Val (#(0 : w64)) ∨ ∃ e : w64, e ≠ 0 ∧ e' = Val (#e))) ∨
      (st' = st.nsFree ∧ ∃ e : w64, e ≠ 0 ∧ e' = Val (#e)) := by
    rcases hres with ⟨-, ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩⟩ | ⟨heq, -⟩ | ⟨e, he, rfl, rfl⟩
    · exact .inl ⟨rfl, .inl rfl⟩
    · exact .inr ⟨rfl, e, he, rfl⟩
    · exact .inl ⟨rfl, .inr ⟨e, he, rfl⟩⟩
    · exact absurd heq hcne
    · exact .inr ⟨rfl, e, he, rfl⟩
  rcases hcases with ⟨rfl, he⟩ | ⟨rfl, e, he, rfl⟩
  · imod gAuth_update _ _ _ _ _ (g.push (.mv bs bt)) $$ HAd Hd with ⟨HAd, Hd⟩
    imod ns_step_close hwf hcoh hs1 Hr Hfr hwe hce false rfl $$ HAb HAm HAf HAt Htok Hcells Hσ
      HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, (<[d := g.push (.mv bs bt)]> Γd), Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    rcases he with rfl | ⟨e, he, rfl⟩
    · iapply wp_value'
      iapply HΦ $$ %0 %_ %(.inl ⟨rfl, rfl⟩) Hd Hz
    · iapply wp_value'
      iapply HΦ $$ %e %_ %(.inr ⟨he, .inr rfl⟩) Hd Hz
  · imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb HAm
      HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, Γd, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %e %_ %(.inr ⟨he, .inl rfl⟩) Hd Hz

/-- `fsync(2)` of a directory fd: any errno; the namespace's ghost state as it was (a commit only
narrows what a crash may leave). -/
theorem wp_osDirSync (fd : w64) (dq : DFrac) (x : GoString × DirPh) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFd (L := L) fd dq x -∗
      (∀ e : w64, osDirFd (L := L) fd dq x -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "DirSync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_stepN "DirSync" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  unfold osDirFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAdf Hfd with %Hfl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  obtain ⟨df, hdf⟩ : ∃ df, st.dfds !! fd = some df := by
    have := hc.fds fd; rw [Hfl] at this
    cases h0 : st.dfds !! fd with
    | none => rw [h0] at this; cases this
    | some df => exact ⟨df, rfl⟩
  have hs : ∀ n, FilesSame st (st.nsCommit n) := fun n => ⟨rfl, rfl, rfl, rfl⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf (hs _) Hag
    exact ⟨_, h, st.nsCommit (dirCommitLen df.path st.nsLog),
      ⟨fd, df, _, rfl, hdf, Nat.le_refl _, rfl, .inl ⟨rfl, rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', df', n, hv, -, -, rfl, hres⟩ := Hst
  cases go.intoVal_inj hv
  imod ns_step_close hwf hcoh (hs n) Hr Hfr (nsWf_nsCommit hw n) (nsCoh_nsCommit hc n) st.nsBusy rfl
    $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, Γd, Γdf
  unfold osWorld nsWorld
  iframe Hw Hn
  rcases hres with ⟨-, rfl⟩ | ⟨e, -, rfl⟩
  · iapply wp_value'; iapply HΦ $$ %0 Hfd
  · iapply wp_value'; iapply HΦ $$ %e Hfd

/-- What closing a directory fd gives back: the fraction of the directory's ghost entry its read
holds, if it is reading. -/
def rdBack (x : GoString × DirPh) : IProp GF := rdPart (gooseOsGS (L := L)) x

/-- `close(2)` of a directory fd, whole: any errno; the fd gone, and a read's fraction back. -/
theorem wp_osDirClose (fd : w64) (x : GoString × DirPh) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFd (L := L) fd (DFrac.own 1) x -∗
      (∀ e : w64, rdBack (L := L) x -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "DirClose" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_stepN "DirClose" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  unfold osDirFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAdf Hfd with %Hfl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  obtain ⟨df, hdf⟩ : ∃ df, st.dfds !! fd = some df := by
    have := hc.fds fd; rw [Hfl] at this
    cases h0 : st.dfds !! fd with
    | none => rw [h0] at this; cases this
    | some df => exact ⟨df, rfl⟩
  have hs : FilesSame st { st with dfds := GMap.delete fd st.dfds } := ⟨rfl, rfl, rfl, rfl⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs Hag
    exact ⟨_, h, _, ⟨fd, 0, df, rfl, hdf, rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', e, df', hv, -, hst, rfl⟩ := Hst
  cases go.intoVal_inj hv
  -- the fd's part of the reads' fractions, back
  unfold rdRes
  icases (BigSepM.bigSepM_delete (M := GMap w64)
    (Φ := fun (_ : w64) (x : GoString × DirPh) => rdPart (gooseOsGS (L := L)) x) Hfl).1 $$ Hrd
    with ⟨Hx, Hrd⟩
  imod gAuth_delete _ _ _ _ _ $$ HAdf Hfd with HAdf
  have hs' : FilesSame st st' := by rw [hst]; exact hs
  have hw' : NsWf st' := by
    rw [hst]
    refine ⟨hw.roots, hw.replay, hw.hist, hw.legacy, fun fd' df' h' => ?_, fun fd' h' => ?_⟩
    · have : st.dfds !! fd' = some df' := by
        have h'' : (GMap.delete fd st.dfds) !! fd' = some df' := h'
        rw [GMap.lookup_delete_iff] at h''; split at h''
        · cases h''
        · exact h''
      exact hw.dfds fd' df' this
    · show (GMap.delete fd st.dfds) !! fd' = none
      rw [GMap.lookup_delete_iff]; split
      · rfl
      · exact hw.disj fd' h'
  have hc' : NsCoh st' Γd (GMap.delete fd Γdf) := by
    rw [hst]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
    refine ⟨h1, h2, h3, h4, fun fd' => ?_, fun fd' x' df' hx hd => ?_,
      fun fd' d rs g q hx => ?_⟩
    · show ((GMap.delete fd Γdf) !! fd').map (·.1) = ((GMap.delete fd st.dfds) !! fd').map (·.path)
      rw [GMap.lookup_delete_iff, GMap.lookup_delete_iff]; split
      · rfl
      · exact h5 fd'
    · have hx' : Γdf !! fd' = some x' := by
        rw [GMap.lookup_delete_iff] at hx; split at hx
        · cases hx
        · exact hx
      have hd' : st.dfds !! fd' = some df' := by
        have hd'' : (GMap.delete fd st.dfds) !! fd' = some df' := hd
        rw [GMap.lookup_delete_iff] at hd''; split at hd''
        · cases hd''
        · exact hd''
      exact h6 fd' x' df' hx' hd'
    · rw [GMap.lookup_delete_iff] at hx; split at hx
      · cases hx
      · exact h7 fd' d rs g q hx
  ihave Hrd : rdRes (gooseOsGS (L := L)) (GMap.delete fd Γdf) $$ [Hrd]
  · unfold rdRes; iexact Hrd
  imod ns_step_close hwf hcoh hs' Hr Hfr hw' hc' st.nsBusy (by rw [hst]) $$ HAb HAm HAf HAt Htok
    Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, Γd, (GMap.delete fd Γdf)
  unfold osWorld nsWorld rdRes
  iframe Hw Hn
  iapply wp_value'
  iapply HΦ $$ %e
  unfold rdBack; iexact Hx

/-- `unlink(2)` of an absent name of `d`, with the in-flight flag set: it fails, the flag cleared. -/
theorem wp_osUnlinkAbsent (d b : GoString) (dq : DFrac) (g : DirG) (hb : NameOk b)
    (hn : g.now !! b = none) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d dq g -∗ osNsBusy (L := L) true -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osDir (L := L) d dq g -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Unlink" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hd Hz HΦ
  iapply wp_os_stepN "Unlink" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  unfold osDir osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hd with %Hdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hdir : st.ns !! d = some .dir := (hc.dirs d).1 (by rw [Hdl]; rfl)
  have hnone : st.ns !! child d b = none := by
    rw [← entsOf_child st.ns d b hb, hc.now d g Hdl]; exact hn
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs0 Hag
    exact ⟨_, h, st.nsFree, ⟨child d b, rfl, hw.nsName_child hdir hb, hb1,
      .inr ⟨1, by decide, rfl, rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', hv, -, -, hres⟩ := Hst
  cases go.intoVal_inj hv
  rcases hres with ⟨⟨k, hk⟩, -⟩ | ⟨e, he, rfl, rfl⟩
  · rw [hnone] at hk; cases hk
  imod gAuth_update _ _ _ _ _ false $$ HAz Hz with ⟨HAz, Hz⟩
  rw [busyMap_insert]
  imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb HAm
    HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, Γd, Γdf
  unfold osWorld nsWorld
  iframe Hw Hn
  iapply wp_value'
  iapply HΦ $$ %e %he Hd Hz

/-- `rename(2)` of an absent name of `d`, with the in-flight flag set: it fails, the flag
cleared. -/
theorem wp_osRenameAbsent (d bs bt : GoString) (dq : DFrac) (g : DirG) (hbs : NameOk bs)
    (hbt : NameOk bt) (hne : bs ≠ bt) (hn : g.now !! bs = none) (ht : g.now !! bt ≠ some .dir)
    (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d dq g -∗ osNsBusy (L := L) true -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osDir (L := L) d dq g -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rename" (Val (PairV (#(child d bs)) (#(child d bt))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hd Hz HΦ
  iapply wp_os_stepN "Rename" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  unfold osDir osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hd with %Hdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hdir : st.ns !! d = some .dir := (hc.dirs d).1 (by rw [Hdl]; rfl)
  have hnone : st.ns !! child d bs = none := by
    rw [← entsOf_child st.ns d bs hbs, hc.now d g Hdl]; exact hn
  have hcne : child d bs ≠ child d bt := fun h => hne (List.cons.inj (List.append_cancel_left h)).2
  have hnofd : ∀ fd df, st.dfds !! fd = some df →
      (st.ns !! child d bs = some .dir → ¬ IsUnder (child d bs) df.path) ∧ df.path ≠ child d bt := by
    intro fd df hdf
    refine ⟨(fun h => by rw [hnone] at h; cases h), fun he => ?_⟩
    have ht' : st.ns !! child d bt ≠ some .dir := by
      rw [← entsOf_child st.ns d bt hbt, hc.now d g Hdl]; exact ht
    exact ht' (he ▸ hw.dfds fd df hdf)
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs0 Hag
    exact ⟨_, h, st.nsFree, ⟨child d bs, child d bt, rfl, hw.nsName_child hdir hbs,
      hw.nsName_child hdir hbt, hb1, hnofd, .inr (.inr ⟨1, by decide, rfl, rfl⟩)⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨s', t', hv, -, -, -, -, hres⟩ := Hst
  injection hv with hv1 hv2
  cases go.intoVal_inj hv1; cases go.intoVal_inj hv2
  rcases hres with ⟨⟨-, -, -, hok⟩, -⟩ | ⟨heq, -⟩ | ⟨e, he, rfl, rfl⟩
  · rw [hnone] at hok; exact hok.elim
  · exact absurd heq hcne
  imod gAuth_update _ _ _ _ _ false $$ HAz Hz with ⟨HAz, Hz⟩
  rw [busyMap_insert]
  imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb HAm
    HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, Γd, Γdf
  unfold osWorld nsWorld
  iframe Hw Hn
  iapply wp_value'
  iapply HΦ $$ %e %he Hd Hz

end specs

end Perennial
