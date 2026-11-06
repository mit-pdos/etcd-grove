/-
The global specs (`NsSpecsDir.lean`) of `mkdir(2)` and `rmdir(2)`. Untrusted.
-/
module

public import GooseLang.Ext.OsFs.NsSpecsDir

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-! ## Pure facts -/

private theorem mk_isUnder_trans {a b c : GoString} (h1 : IsUnder a b) (h2 : IsUnder b c) :
    IsUnder a c := by
  obtain ⟨r1, rfl, hr1⟩ := (isUnder_iff _ _).1 h1
  obtain ⟨r2, rfl, hr2⟩ := (isUnder_iff _ _).1 h2
  refine (isUnder_iff _ _).2 ⟨r1 ++ r2, by simp, ?_⟩
  rcases hr1 with rfl | ⟨r1', rfl⟩
  · simpa using hr2
  · exact .inr ⟨r1' ++ r2, by simp⟩

private theorem mk_isUnder_len {a b : GoString} (h : IsUnder a b) : a.length ≤ b.length := by
  obtain ⟨r, rfl, -⟩ := (isUnder_iff _ _).1 h
  simp

private theorem mk_canon_len {r p : GoString} (h : CanonBelow r p) : r.length < p.length := by
  obtain ⟨cs, hne, -, rfl⟩ := h
  cases cs with
  | nil => exact absurd rfl hne
  | cons c cs => simp [joinPath]

/-- A name of `d`, `d` a directory or a name in one, is a name the namespace manages. -/
private theorem mk_nsName_below {st : OsState} (hw : NsWf st) {d b : GoString}
    (hd : NsBelowDir st.ns d) (hb : NameOk b) : st.NsName (child d b) := by
  rcases hd with hd | ⟨d0, b0, hb0, rfl, hd0⟩
  · exact hw.nsName_child hd hb
  · obtain ⟨r, hr, hdr⟩ := hw.dir_form hd0
    exact ⟨r, hr, canonBelow_child (.inr (canonBelow_child hdr hb0)) hb⟩

/-- No root is at or under a name of a directory. -/
private theorem mk_root_not_under {st : OsState} (hw : NsWf st) {d b : GoString}
    (hd : st.ns !! d = some .dir) (hb : NameOk b) :
    ∀ r ∈ st.roots, ¬ IsUnder (child d b) r := by
  obtain ⟨r', hr', hdr⟩ := hw.dir_form hd
  have hc : CanonBelow r' (child d b) := canonBelow_child hdr hb
  have hu : IsUnder r' (child d b) := isUnder_of_canonBelow hc
  intro r hr hur
  by_cases hrr : r' = r
  · subst hrr
    have := mk_isUnder_len hur; have := mk_canon_len hc; omega
  · exact (hw.roots.2 r' hr').2 r hr hrr (mk_isUnder_trans hu hur)

/-- Nothing is below an absent name of a directory. -/
private theorem mk_nothing_under {st : OsState} (hw : NsWf st) {d b : GoString}
    (hd : st.ns !! d = some .dir) (hb : NameOk b) (hn : st.ns !! child d b = none) (c : GoString) :
    st.ns !! child (child d b) c = none := by
  cases hx : st.ns !! child (child d b) c with
  | none => rfl
  | some v =>
    exact absurd ((isUnder_iff (child d b) (child (child d b) c)).2 ⟨slashB :: c, by simp [child], .inr ⟨c, rfl⟩⟩)
      (shape_no_under hw.shape hn (mk_root_not_under hw hd hb) _ (by rw [hx]; rfl))

/-- A name below a root's tree: a name of its parent. -/
private theorem mk_canon_parent {r p dd : GoString} (hc : CanonBelow r p)
    (hpar : parentOf p = some dd) : ∃ c, NameOk c ∧ p = child dd c := by
  obtain ⟨cs, hne, hok, rfl⟩ := hc
  obtain ⟨cs', c, rfl⟩ := (List.eq_nil_or_concat cs).resolve_left hne
  have hl : NameOk c := hok _ (by simp)
  rw [List.concat_eq_append, joinPath_snoc] at hpar ⊢
  rw [parentOf_child' _ _ hl] at hpar
  cases hpar
  exact ⟨_, hl, rfl⟩

section shape
variable {R : List GoString} {m : NsMap}

private theorem mk_shape_mkdir {d b : GoString} (hs : NsShape R m) (hd : m !! d = some .dir)
    (hdf : ∃ r ∈ R, d = r ∨ CanonBelow r d) (hb : NameOk b) (hn : m !! child d b = none) :
    NsShape R (<[child d b := .dir]> m) := by
  obtain ⟨hR, hP, hL⟩ := hs
  have hne : ∀ q, m !! q = some .dir → child d b ≠ q := fun q hq h => by
    subst h; rw [hn] at hq; cases hq
  refine ⟨fun r hr => ?_, fun p x hp => ?_, fun p q k' hp hq => ?_⟩
  · rw [GMap.lookup_insert_ne _ _ (hne r (hR r hr))]; exact hR r hr
  · by_cases hpc : child d b = p
    · subst hpc
      obtain ⟨r, hr, hdr⟩ := hdf
      refine .inr ⟨⟨r, hr, canonBelow_child hdr hb⟩, d, parentOf_child' d b hb, ?_⟩
      rw [GMap.lookup_insert_ne _ _ (hne d hd)]; exact hd
    · rw [GMap.lookup_insert_ne _ _ hpc] at hp
      rcases hP p x hp with h | ⟨hc, dd, hdd, hddir⟩
      · exact .inl h
      · exact .inr ⟨hc, dd, hdd, by rw [GMap.lookup_insert_ne _ _ (hne dd hddir)]; exact hddir⟩
  · have hget : ∀ p k', (<[child d b := OsNode.dir]> m) !! p = some (.file k') →
        m !! p = some (.file k') := by
      intro p k' hp
      by_cases hpc : child d b = p
      · subst hpc; rw [GMap.lookup_insert] at hp; cases hp
      · rwa [GMap.lookup_insert_ne _ _ hpc] at hp
    exact hL p q k' (hget p k' hp) (hget q k' hq)

private theorem mk_shape_rmdir {p : GoString} (hs : NsShape R m)
    (hempty : ∀ c, NameOk c → m !! child p c = none) (hnr : ∀ r ∈ R, r ≠ p) :
    NsShape R (GMap.delete p m) := by
  obtain ⟨hR, hP, hL⟩ := hs
  refine ⟨fun r hr => ?_, fun p' x hp' => ?_, fun p1 q1 k' hp1 hq1 => ?_⟩
  · rw [GMap.lookup_delete_ne _ (hnr r hr).symm]; exact hR r hr
  · by_cases hpp : p = p'
    · subst hpp; rw [GMap.lookup_delete] at hp'; cases hp'
    · rw [GMap.lookup_delete_ne _ hpp] at hp'
      rcases hP p' x hp' with h | ⟨⟨r, hr, hc⟩, dd, hdd, hddir⟩
      · exact .inl h
      · refine .inr ⟨⟨r, hr, hc⟩, dd, hdd, ?_⟩
        have hne : p ≠ dd := by
          rintro rfl
          obtain ⟨c, hcok, rfl⟩ := mk_canon_parent hc hdd
          rw [hempty c hcok] at hp'; cases hp'
        rw [GMap.lookup_delete_ne _ hne]; exact hddir
  · by_cases h1 : p = p1
    · subst h1; rw [GMap.lookup_delete] at hp1; cases hp1
    · by_cases h2 : p = q1
      · subst h2; rw [GMap.lookup_delete] at hq1; cases hq1
      · rw [GMap.lookup_delete_ne _ h1] at hp1; rw [GMap.lookup_delete_ne _ h2] at hq1
        exact hL p1 q1 k' hp1 hq1

end shape

/-- With no directory fd open, an operation that keeps the namespace's shape and makes no new file
keeps its well-formedness. -/
private theorem mk_nsWf_dirOp {st : OsState} {o : NsOp} (hw : NsWf st)
    (h0 : ∀ fd, st.dfds !! fd = none) (hshape : NsShape st.roots (o.apply st.ns))
    (hkeys : ∀ p k, o.apply st.ns !! p = some (.file k) → st.ns !! p = some (.file k)) :
    NsWf (st.nsFree.nsDo o) := by
  refine ⟨hw.roots, ?_, fun n hn => ?_, hw.legacy, fun fd df hdf => ?_, fun fd _ => ?_⟩
  · show o.apply st.ns = nsReplay (st.nsLog ++ [o]) st.nsDur
    rw [nsReplay_snoc, ← hw.replay]
  · have hn' : n ≤ st.nsLog.length + 1 := by
      simpa [OsState.nsDo, OsState.nsFree] using hn
    show NsShape st.roots (nsReplay ((st.nsLog ++ [o]).take n) st.nsDur) ∧
      ∀ p k, nsReplay ((st.nsLog ++ [o]).take n) st.nsDur !! p = some (.file k) →
        IsInoKey k ∧ ∃ f, st.files !! k = some (some f)
    by_cases hle : n ≤ st.nsLog.length
    · rw [List.take_append_of_le_length hle]
      exact hw.hist n hle
    · rw [List.take_of_length_le (by simp; omega), nsReplay_snoc, ← hw.replay]
      exact ⟨hshape, fun p k hp => hw.keys (hkeys p k hp)⟩
  · have hdf' : (GMap.fmap (·.note o) st.dfds) !! fd = some df := hdf
    rw [GMap.lookup_fmap, h0] at hdf'; cases hdf'
  · show (GMap.fmap (·.note o) st.dfds) !! fd = none
    rw [GMap.lookup_fmap, h0]; rfl

/-- No directory fd in the ghost state: none in the state. -/
private theorem mk_dfds_none {st : OsState} {V Γdf} (hc : NsCoh st V Γdf) (hnr : NoDirFds Γdf) :
    ∀ fd, st.dfds !! fd = none := by
  intro fd
  have := hc.fds fd
  rw [hnr fd] at this
  cases h : st.dfds !! fd with
  | none => rfl
  | some df => rw [h] at this; cases this

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- `rmdir(2)` of `d/b`, a name the namespace manages, with the whole history and the in-flight
flag set: an empty directory is removed (on a failure, removed or not); or it fails, unchanged. -/
theorem wp_osRmdirG (d b : GoString) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : NsBelowDir (nsReplay V.2 V.1) d) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜(nsReplay V.2 V.1 !! child d b = some .dir ∧
            (∀ c, NameOk c → nsReplay V.2 V.1 !! child (child d b) c = none) ∧
            ((e = 0 ∧ V' = nsPush V (.remove (child d b))) ∨
             (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.remove (child d b)))))) ∨
          (e ≠ 0 ∧ V' = V)⌝ -∗
        osNsAll (L := L) (DFrac.own 1) V' -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rmdir" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  iintro #Hinv HV Hz HΦ
  iapply wp_os_stepN "Rmdir" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases rdRes_none V Γdf $$ HV Hrd with ⟨%Hnr, HV, Hrd⟩
  icases osNsAll_auth _ _ _ $$ HAd HV with %hV
  subst Γd
  unfold osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hns : st.ns = nsReplay V.2 V.1 := ns_eq_replay hw hc
  have hd0 := mk_dfds_none hc Hnr
  have hname : st.NsName (child d b) := mk_nsName_below hw (hns ▸ hd) hb
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  have hs1 : FilesSame st (st.nsFree.nsDo (.remove (child d b))) :=
    hs0.trans (filesSame_nsDo _ _)
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs0 Hag
    exact ⟨_, h, st.nsFree, ⟨child d b, rfl, hname, hb1,
      (fun fd df hdf => by rw [hd0 fd] at hdf; cases hdf), .inr ⟨1, by decide, rfl, rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', hv, -, -, -, hres⟩ := Hst
  cases go.intoVal_inj hv
  imod gAuth_update _ _ _ _ _ false $$ HAz Hz with ⟨HAz, Hz⟩
  rw [busyMap_insert]
  have hcases : (NsEmptyDir st (child d b) ∧ st' = st.nsFree.nsDo (.remove (child d b)) ∧
      (e' = Val (#(0 : w64)) ∨ ∃ e : w64, e ≠ 0 ∧ e' = Val (#e))) ∨
      (st' = st.nsFree ∧ ∃ e : w64, e ≠ 0 ∧ e' = Val (#e)) := by
    rcases hres with ⟨he, ⟨rfl, rfl⟩ | ⟨e, he0, rfl, rfl | rfl⟩⟩ | ⟨e, he, rfl, rfl⟩
    · exact .inl ⟨he, rfl, .inl rfl⟩
    · exact .inr ⟨rfl, e, he0, rfl⟩
    · exact .inl ⟨he, rfl, .inr ⟨e, he0, rfl⟩⟩
    · exact .inr ⟨rfl, e, he, rfl⟩
  rcases hcases with ⟨hemp, rfl, he⟩ | ⟨rfl, e, he, rfl⟩
  · obtain ⟨hpd, hpe⟩ := hemp
    have hempty : ∀ c, NameOk c → st.ns !! child (child d b) c = none := by
      intro c hcok
      cases hx : st.ns !! child (child d b) c with
      | none => rfl
      | some v =>
        exact absurd ⟨hcok, by show (st.ns !! child (child d b) c).isSome; rw [hx]; rfl⟩ (hpe c)
    have hnr : ∀ r ∈ st.roots, r ≠ child d b := by
      intro r hr hre
      obtain ⟨r', hr', hrc⟩ := hname
      have hu := isUnder_of_canonBelow hrc
      by_cases hrr : r' = r
      · subst hrr; have := mk_canon_len hrc; rw [hre] at this; omega
      · exact (hw.roots.2 r' hr').2 r hr hrr (by rw [hre]; exact hu)
    have hwe : NsWf (st.nsFree.nsDo (.remove (child d b))) :=
      mk_nsWf_dirOp hw hd0 (mk_shape_rmdir hw.shape hempty hnr)
        (fun p k' hp => by
          have hp' : (GMap.delete (child d b) st.ns) !! p = some (.file k') := hp
          by_cases hpe : child d b = p
          · subst hpe; rw [GMap.lookup_delete] at hp'; cases hp'
          · rwa [GMap.lookup_delete_ne _ hpe] at hp')
    have hce : NsCoh (st.nsFree.nsDo (.remove (child d b))) (nsPush V (.remove (child d b))) Γdf :=
      nsCoh_log hc Hnr rfl rfl rfl
    have hpure : nsReplay V.2 V.1 !! child d b = some .dir ∧
        (∀ c, NameOk c → nsReplay V.2 V.1 !! child (child d b) c = none) := by
      rw [← hns]; exact ⟨hpd, hempty⟩
    imod osNsAll_update V (nsPush V (.remove (child d b))) V $$ HAd HV with ⟨HAd, HV⟩
    imod ns_step_close hwf hcoh hs1 Hr Hfr hwe hce false rfl $$ HAb HAm HAf HAt Htok Hcells Hσ HAd
      HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, (nsPush V (.remove (child d b))), Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    rcases he with rfl | ⟨e, he, rfl⟩
    · iapply wp_value'
      iapply HΦ $$ %0 %_ %(.inl ⟨hpure.1, hpure.2, .inl ⟨rfl, rfl⟩⟩) HV Hz
    · iapply wp_value'
      iapply HΦ $$ %e %_ %(.inl ⟨hpure.1, hpure.2, .inr ⟨he, .inr rfl⟩⟩) HV Hz
  · imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb HAm
      HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, V, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %e %_ %(.inr ⟨he, rfl⟩) HV Hz

/-- `mkdir(2)` of `d/b`, a name the namespace manages, with the whole history and the in-flight
flag set: where nothing is, in a directory, a new directory (on a failure, made or not); or it
fails, unchanged. -/
theorem wp_osMkdirG (d b : GoString) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : NsBelowDir (nsReplay V.2 V.1) d)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜(nsReplay V.2 V.1 !! child d b = none ∧ nsReplay V.2 V.1 !! d = some .dir ∧
            (∀ c, nsReplay V.2 V.1 !! child (child d b) c = none) ∧
            ((e = 0 ∧ V' = nsPush V (.mkdir (child d b))) ∨
             (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.mkdir (child d b)))))) ∨
          (e ≠ 0 ∧ V' = V)⌝ -∗
        osNsAll (L := L) (DFrac.own 1) V' -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Mkdir" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  iintro #Hinv HV Hz HΦ
  iapply wp_os_stepN "Mkdir" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases rdRes_none V Γdf $$ HV Hrd with ⟨%Hnr, HV, Hrd⟩
  icases osNsAll_auth _ _ _ $$ HAd HV with %hV
  subst Γd
  unfold osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hns : st.ns = nsReplay V.2 V.1 := ns_eq_replay hw hc
  have hd0 := mk_dfds_none hc Hnr
  have hname : st.NsName (child d b) := mk_nsName_below hw (hns ▸ hd) hb
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  have hs1 : FilesSame st (st.nsFree.nsDo (.mkdir (child d b))) :=
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
  have hcases : (st.ns !! child d b = none ∧ st.ParentDir (child d b) ∧
      st' = st.nsFree.nsDo (.mkdir (child d b)) ∧
      (e' = Val (#(0 : w64)) ∨ ∃ e : w64, e ≠ 0 ∧ e' = Val (#e))) ∨
      (st' = st.nsFree ∧ ∃ e : w64, e ≠ 0 ∧ e' = Val (#e)) := by
    rcases hres with ⟨hn, hp, ⟨rfl, rfl⟩ | ⟨e, he0, rfl, rfl | rfl⟩⟩ | ⟨e, he, rfl, rfl⟩
    · exact .inl ⟨hn, hp, rfl, .inl rfl⟩
    · exact .inr ⟨rfl, e, he0, rfl⟩
    · exact .inl ⟨hn, hp, rfl, .inr ⟨e, he0, rfl⟩⟩
    · exact .inr ⟨rfl, e, he, rfl⟩
  rcases hcases with ⟨hn, ⟨dd, hdd, hddir⟩, rfl, he⟩ | ⟨rfl, e, he, rfl⟩
  · rw [parentOf_child' d b hb] at hdd
    cases hdd
    have hwe : NsWf (st.nsFree.nsDo (.mkdir (child d b))) :=
      mk_nsWf_dirOp hw hd0 (mk_shape_mkdir hw.shape hddir (hw.dir_form hddir) hb hn)
        (fun p k' hp => by
          have hp' : (<[child d b := OsNode.dir]> st.ns) !! p = some (.file k') := hp
          by_cases hpe : child d b = p
          · subst hpe; rw [GMap.lookup_insert] at hp'; cases hp'
          · rwa [GMap.lookup_insert_ne _ _ hpe] at hp')
    have hce : NsCoh (st.nsFree.nsDo (.mkdir (child d b))) (nsPush V (.mkdir (child d b))) Γdf :=
      nsCoh_log hc Hnr rfl rfl rfl
    have hpure : nsReplay V.2 V.1 !! child d b = none ∧ nsReplay V.2 V.1 !! d = some .dir ∧
        (∀ c, nsReplay V.2 V.1 !! child (child d b) c = none) := by
      rw [← hns]; exact ⟨hn, hddir, mk_nothing_under hw hddir hb hn⟩
    imod osNsAll_update V (nsPush V (.mkdir (child d b))) V $$ HAd HV with ⟨HAd, HV⟩
    imod ns_step_close hwf hcoh hs1 Hr Hfr hwe hce false rfl $$ HAb HAm HAf HAt Htok Hcells Hσ HAd
      HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, (nsPush V (.mkdir (child d b))), Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    rcases he with rfl | ⟨e, he, rfl⟩
    · iapply wp_value'
      iapply HΦ $$ %0 %_ %(.inl ⟨hpure.1, hpure.2.1, hpure.2.2, .inl ⟨rfl, rfl⟩⟩) HV Hz
    · iapply wp_value'
      iapply HΦ $$ %e %_ %(.inl ⟨hpure.1, hpure.2.1, hpure.2.2, .inr ⟨he, .inr rfl⟩⟩) HV Hz
  · imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb HAm
      HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, V, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %e %_ %(.inr ⟨he, rfl⟩) HV Hz

end specs

end Perennial

end
