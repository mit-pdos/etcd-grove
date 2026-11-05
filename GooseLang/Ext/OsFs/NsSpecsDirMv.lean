/-
The global specs (`NsSpecsDir.lean`) of `rename(2)` of a directory, and of an absent source.
Untrusted.
-/
module

public import GooseLang.Ext.OsFs.NsSpecsDir

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-! ## Paths -/

theorem isUnder_trans {a b c : GoString} (h1 : IsUnder a b) (h2 : IsUnder b c) : IsUnder a c := by
  obtain ⟨r1, rfl, hr1⟩ := (isUnder_iff _ _).1 h1
  obtain ⟨r2, rfl, hr2⟩ := (isUnder_iff _ _).1 h2
  refine (isUnder_iff _ _).2 ⟨r1 ++ r2, by simp, ?_⟩
  rcases hr1 with rfl | ⟨r1', rfl⟩
  · simpa using hr2
  · exact .inr ⟨r1' ++ r2, rfl⟩

theorem isUnder_child' {x d : GoString} (b : GoString) (h : IsUnder x d) : IsUnder x (child d b) :=
  isUnder_trans h ((isUnder_iff _ _).2 ⟨slashB :: b, rfl, .inr ⟨b, rfl⟩⟩)

theorem isUnder_length {a b : GoString} (h : IsUnder a b) : a.length ≤ b.length := by
  obtain ⟨r, rfl, -⟩ := (isUnder_iff _ _).1 h; simp

theorem not_isUnder_child_parent (d b : GoString) : ¬ IsUnder (child d b) d := by
  intro h; have := isUnder_length h; simp at this; omega

theorem canonBelow_length {r p : GoString} (h : CanonBelow r p) : r.length < p.length := by
  obtain ⟨cs, hne, -, rfl⟩ := h
  cases cs with
  | nil => exact absurd rfl hne
  | cons c cs => simp [joinPath]; try omega

theorem canonBelow_snoc_inv {r p : GoString} (h : CanonBelow r p) :
    ∃ dq b, p = child dq b ∧ NameOk b ∧ (dq = r ∨ CanonBelow r dq) := by
  obtain ⟨cs, hne, hcs, rfl⟩ := h
  obtain ⟨cs0, b, rfl⟩ := (List.eq_nil_or_concat cs).resolve_left hne
  rw [List.concat_eq_append] at hcs ⊢
  refine ⟨joinPath r cs0, b, joinPath_snoc r cs0 b, hcs b (by simp), ?_⟩
  by_cases h0 : cs0 = []
  · subst h0; left; simp [joinPath]
  · right; exact ⟨cs0, h0, fun c hc => hcs c (by simp [hc]), rfl⟩

/-- No root is in the tree of a path below a root. -/
theorem root_not_under {R : List GoString} (hR : RootsOk R) {r0 x : GoString} (hr0 : r0 ∈ R)
    (hx : CanonBelow r0 x) {r : GoString} (hr : r ∈ R) : ¬ IsUnder x r := by
  intro h
  have h1 : IsUnder r0 r := isUnder_trans (isUnder_of_canonBelow hx) h
  have hne : r0 ≠ r := by
    intro he; subst he
    have := canonBelow_length hx; have := isUnder_length h; omega
  exact (hR.2 r0 hr0).2 r hr hne h1

theorem child_ne_child {d b b' : GoString} (h : b ≠ b') : child d b ≠ child d b' :=
  fun he => h (List.cons.inj (List.append_cancel_left he)).2

theorem not_isUnder_sibling {d bs bt : GoString} (hbt : NameOk bt) (hne : bs ≠ bt) :
    ¬ IsUnder (child d bs) (child d bt) := by
  intro h
  obtain ⟨r, hr, hr'⟩ := (isUnder_iff _ _).1 h
  have h1 := hr
  simp only [child, List.append_assoc] at h1
  have h2 := List.append_cancel_left h1
  simp only [List.cons_append, List.cons.injEq, _root_.true_and] at h2
  rcases hr' with rfl | ⟨r', rfl⟩
  · simp at h2; exact hne h2.symm
  · exact hbt.2.2.2.1 (by rw [h2]; simp)

/-! ## A directory moved -/

section move
variable {R : List GoString} {m : NsMap} {d bs bt : GoString}

theorem delete_absent {m : NsMap} {t : GoString} (ht : m !! t = none) : GMap.delete t m = m := by
  apply GMap.ext; intro y
  show GMap.delete t m !! y = m !! y
  by_cases h : t = y
  · subst h; rw [GMap.lookup_delete, ht]
  · rw [GMap.lookup_delete_ne _ h]

/-- What `nsMove m s t` binds came from `m`, re-keyed. -/
theorem nsMove_pre {m : NsMap} {s t : GoString} (ht : ∀ x, (m !! x).isSome → ¬ IsUnder t x)
    {y : GoString} {v : OsNode} (h : nsMove m s t !! y = some v) :
    ∃ y0, m !! y0 = some v ∧ rekey s t y0 = y := by
  by_cases hty : IsUnder t y
  · obtain ⟨r, rfl, hr⟩ := (isUnder_iff _ _).1 hty
    rw [nsMove_under ht r hr] at h
    refine ⟨s ++ r, h, ?_⟩
    rw [(rekey_under ((isUnder_iff _ _).2 ⟨r, rfl, hr⟩)).1]; simp
  · by_cases hs : IsUnder s y
    · rw [nsMove_old ht y hs hty] at h; cases h
    · rw [nsMove_other ht y hs hty] at h; exact ⟨y, h, rekey_not_under hs⟩

/-- **The shape kept** by the move of the directory `d/bs` onto `d/bt`, absent. -/
theorem shape_moveDir (hR : RootsOk R) (hsh : NsShape R m) (hd : m !! d = some .dir)
    (hdf : ∃ r ∈ R, d = r ∨ CanonBelow r d) (hbs : NameOk bs) (hbt : NameOk bt)
    (hs : m !! child d bs = some .dir) (htn : m !! child d bt = none) :
    NsShape R (nsMove m (child d bs) (child d bt)) := by
  obtain ⟨r0, hr0, hd0⟩ := hdf
  have hcs : CanonBelow r0 (child d bs) := canonBelow_child hd0 hbs
  have hct : CanonBelow r0 (child d bt) := canonBelow_child hd0 hbt
  have ht' : ∀ x, (m !! x).isSome → ¬ IsUnder (child d bt) x :=
    shape_no_under hsh htn (fun r hr => root_not_under hR hr0 hct hr)
  have hdM : nsMove m (child d bs) (child d bt) !! d = some .dir := by
    rw [nsMove_other ht' d (not_isUnder_child_parent _ _) (not_isUnder_child_parent _ _)]; exact hd
  have htM : nsMove m (child d bs) (child d bt) !! child d bt = some .dir := by
    have := nsMove_under (s := child d bs) ht' [] (.inl rfl)
    simp only [List.append_nil] at this; rw [this, hs]
  refine ⟨fun r hr => ?_, ?_, fun p q k hp hq => ?_⟩
  · rw [nsMove_other ht' r (root_not_under hR hr0 hcs hr) (root_not_under hR hr0 hct hr)]
    exact hsh.1 r hr
  · suffices H : ∀ n p x, p.length ≤ n → nsMove m (child d bs) (child d bt) !! p = some x →
        p ∈ R ∨ ((∃ r ∈ R, CanonBelow r p) ∧
          ∃ dd, parentOf p = some dd ∧ nsMove m (child d bs) (child d bt) !! dd = some .dir) from
      fun p x hp => H p.length p x (Nat.le_refl _) hp
    intro n
    induction n with
    | zero =>
      intro p x hl hp
      obtain ⟨p0, hp0, -⟩ := nsMove_pre ht' hp
      exfalso
      by_cases hty : IsUnder (child d bt) p
      · have := isUnder_length hty; simp at this; omega
      · by_cases hsy : IsUnder (child d bs) p
        · rw [nsMove_old ht' p hsy hty] at hp; cases hp
        · rw [nsMove_other ht' p hsy hty] at hp
          rcases hsh.2.1 p x hp with h | ⟨⟨r, -, hc⟩, -⟩
          · have := hR.2 p h |>.1
            obtain ⟨cs, hne, -, rfl⟩ := this
            cases cs with
            | nil => exact hne rfl
            | cons c cs => simp [joinPath] at hl
          · have := canonBelow_length hc; omega
    | succ n ih =>
      intro p x hl hp
      by_cases hty : IsUnder (child d bt) p
      · obtain ⟨r, rfl, hr⟩ := (isUnder_iff _ _).1 hty
        rcases hr with rfl | ⟨r', rfl⟩
        · right
          simp only [List.append_nil]
          exact ⟨⟨r0, hr0, hct⟩, d, parentOf_child' d bt hbt, hdM⟩
        have hq := nsMove_under (s := child d bs) ht' (slashB :: r') (.inr ⟨r', rfl⟩)
        rw [hp] at hq
        rcases hsh.2.1 _ x hq.symm with hroot | ⟨⟨r1, hr1, hcq⟩, dd, hpd, hdd⟩
        · exact absurd (isUnder_child' r' (.inl rfl)) (root_not_under hR hr0 hcs hroot)
        obtain ⟨dq, b, hqe, hb, -⟩ := canonBelow_snoc_inv hcq
        rw [hqe, parentOf_child' dq b hb] at hpd
        cases hpd
        rcases split_last_slash r' with hns | ⟨a, b', rfl, hb'⟩
        · -- the parent is `d/bs` itself
          have hpq : parentOf (child d bs ++ slashB :: r') = some (child d bs) :=
            parentOf_child _ _ hns
          rw [hqe, parentOf_child' _ b hb] at hpq
          cases hpq
          have hbr : b = r' := (List.cons.inj (List.append_cancel_left hqe.symm)).2
          subst hbr
          right
          exact ⟨⟨r0, hr0, canonBelow_child (.inr hct) hb⟩, child d bt, parentOf_child' _ _ hb, htM⟩
        · -- the parent is below `d/bs`
          have e1 : child d bs ++ slashB :: (a ++ slashB :: b') =
              child (child d bs ++ slashB :: a) b' := by simp [child]
          have hpq : parentOf (child d bs ++ slashB :: (a ++ slashB :: b')) =
              some (child d bs ++ slashB :: a) := by
            rw [e1]; exact parentOf_child _ _ hb'
          rw [hqe, parentOf_child' _ b hb] at hpq
          cases hpq
          have hbb : b = b' := by
            have := hqe.symm; rw [e1] at this
            exact (List.cons.inj (List.append_cancel_left this)).2
          subst hbb
          have e2 : child d bt ++ slashB :: (a ++ slashB :: b) =
              child (child d bt ++ slashB :: a) b := by simp [child]
          have hpdM : nsMove m (child d bs) (child d bt) !! (child d bt ++ slashB :: a) =
              some .dir := by rw [nsMove_under ht' (slashB :: a) (.inr ⟨a, rfl⟩)]; exact hdd
          have hlt : (child d bt ++ slashB :: a).length ≤ n := by
            rw [e2] at hl; simp at hl ⊢; omega
          right
          rw [e2]
          refine ⟨?_, _, parentOf_child' _ _ hb, hpdM⟩
          rcases ih _ _ hlt hpdM with h | ⟨⟨r2, hr2, hc2⟩, -⟩
          · exact ⟨_, h, canonBelow_child (.inl rfl) hb⟩
          · exact ⟨r2, hr2, canonBelow_child (.inr hc2) hb⟩
      · by_cases hsy : IsUnder (child d bs) p
        · rw [nsMove_old ht' p hsy hty] at hp; cases hp
        rw [nsMove_other ht' p hsy hty] at hp
        rcases hsh.2.1 p x hp with h | ⟨⟨r, hr, hc⟩, dd, hpd, hdd⟩
        · exact .inl h
        right
        refine ⟨⟨r, hr, hc⟩, dd, hpd, ?_⟩
        obtain ⟨dq, b, rfl, hb, -⟩ := canonBelow_snoc_inv hc
        rw [parentOf_child' dq b hb] at hpd
        cases hpd
        rw [nsMove_other ht' _ (fun h => hsy (isUnder_child' b h)) (fun h => hty (isUnder_child' b h))]
        exact hdd
  · obtain ⟨p0, hp0, rfl⟩ := nsMove_pre ht' hp
    obtain ⟨q0, hq0, rfl⟩ := nsMove_pre ht' hq
    rw [hsh.2.2 p0 q0 k hp0 hq0]

theorem keys_moveDir {P : GoString → Prop} {s t : GoString}
    (ht' : ∀ x, (m !! x).isSome → ¬ IsUnder t x)
    (hk : ∀ p k, m !! p = some (.file k) → P k) :
    ∀ p k, nsMove m s t !! p = some (.file k) → P k := by
  intro p k hp
  obtain ⟨p0, hp0, -⟩ := nsMove_pre ht' hp
  exact hk p0 k hp0

end move

/-- The well-formedness kept by a namespace operation made with no directory fd open. -/
theorem nsWf_nsDo_free {st : OsState} {o : NsOp} (hw : NsWf st) (hnd : ∀ fd, st.dfds !! fd = none)
    (hshape : NsShape st.roots (o.apply st.ns))
    (hkeys : ∀ p k, o.apply st.ns !! p = some (.file k) →
      IsInoKey k ∧ ∃ f, st.files !! k = some (some f)) :
    NsWf (st.nsFree.nsDo o) := by
  have hlog : (st.nsFree.nsDo o).nsLog = st.nsLog ++ [o] := rfl
  have hns : (st.nsFree.nsDo o).ns = o.apply st.ns := rfl
  have hdur : (st.nsFree.nsDo o).nsDur = st.nsDur := rfl
  have hroots : (st.nsFree.nsDo o).roots = st.roots := rfl
  refine ⟨hroots ▸ hw.roots, ?_, fun n hn => ?_, fun k hk hni r hr' => hw.legacy k hk hni r hr',
    fun fd df hdf => ?_, fun fd hfd => ?_⟩
  · rw [hns, hlog, hdur, nsReplay_snoc, ← hw.replay]
  · rw [hlog] at hn ⊢; rw [hdur, hroots]
    simp only [List.length_append, List.length_singleton] at hn
    by_cases hle : n ≤ st.nsLog.length
    · rw [List.take_append_of_le_length hle]
      exact hw.hist n hle
    · rw [List.take_of_length_le (by simp; omega), nsReplay_snoc, ← hw.replay]
      exact ⟨hshape, hkeys⟩
  · have hdf' : (GMap.fmap (·.note o) st.dfds) !! fd = some df := hdf
    rw [GMap.lookup_fmap, hnd fd] at hdf'; cases hdf'
  · have : (st.nsFree.nsDo o).dfds !! fd = (GMap.fmap (·.note o) st.dfds) !! fd := rfl
    rw [this, GMap.lookup_fmap, hnd fd]; rfl

theorem dfds_none {st : OsState} {V Γdf} (hc : NsCoh st V Γdf) (hnr : NoDirFds Γdf) :
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

/-- `rename(2)` of the directory `d/bs` to `d/bt`, nothing there now, with the whole history and the
in-flight flag set: moved, its tree with it (on a failure, moved or not); what the move leaves,
looked up: the tree under its new place, nothing under the old, the rest as it was. -/
theorem wp_osRenameDirG (d bs bt : GoString) (hbs : NameOk bs) (hbt : NameOk bt) (hne : bs ≠ bt)
    (V : NsMap × List NsOp) (hd : nsReplay V.2 V.1 !! d = some .dir)
    (hs : nsReplay V.2 V.1 !! child d bs = some .dir) (ht : nsReplay V.2 V.1 !! child d bt = none)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜((e = 0 ∧ V' = nsPush V (.rename (child d bs) (child d bt))) ∨
          (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.rename (child d bs) (child d bt))))) ∧
          (∀ r, (r = [] ∨ ∃ r', r = slashB :: r') →
            (NsOp.rename (child d bs) (child d bt)).apply (nsReplay V.2 V.1) !! (child d bt ++ r) =
              nsReplay V.2 V.1 !! (child d bs ++ r)) ∧
          (∀ y, IsUnder (child d bs) y → ¬ IsUnder (child d bt) y →
            (NsOp.rename (child d bs) (child d bt)).apply (nsReplay V.2 V.1) !! y = none) ∧
          (∀ y, ¬ IsUnder (child d bs) y → ¬ IsUnder (child d bt) y →
            (NsOp.rename (child d bs) (child d bt)).apply (nsReplay V.2 V.1) !! y =
              nsReplay V.2 V.1 !! y)⌝ -∗
        osNsAll (L := L) (DFrac.own 1) V' -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rename" (Val (PairV (#(child d bs)) (#(child d bt))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv HV Hz HΦ
  iapply wp_os_stepN "Rename" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases rdRes_none V Γdf $$ HV Hrd with ⟨%Hnr, HV, Hrd⟩
  icases osNsAll_auth _ _ _ $$ HAd HV with %HVe
  subst HVe
  unfold osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hm := ns_eq_replay hw hc
  have hdir : st.ns !! d = some .dir := by rw [hm]; exact hd
  have hdfn := dfds_none hc Hnr
  have hcne : child d bs ≠ child d bt := child_ne_child hne
  have hnofd : ∀ fd df, st.dfds !! fd = some df →
      (st.ns !! child d bs = some .dir → ¬ IsUnder (child d bs) df.path) ∧ df.path ≠ child d bt := by
    intro fd df hdf; rw [hdfn fd] at hdf; cases hdf
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  have hsd : st.ns !! child d bs = some .dir := by rw [hm]; exact hs
  have htn : st.ns !! child d bt = none := by rw [hm]; exact ht
  have ht' : ∀ x, (st.ns !! x).isSome → ¬ IsUnder (child d bt) x := by
    obtain ⟨r0, hr0, hd0⟩ := hw.dir_form hdir
    exact shape_no_under hw.shape htn
      (fun r hr => root_not_under hw.roots hr0 (canonBelow_child hd0 hbt) hr)
  have happ : (NsOp.rename (child d bs) (child d bt)).apply st.ns =
      nsMove st.ns (child d bs) (child d bt) := by
    simp only [NsOp.apply, hsd]; rw [delete_absent htn]
  have hfacts : (∀ r, (r = [] ∨ ∃ r', r = slashB :: r') →
        (NsOp.rename (child d bs) (child d bt)).apply (nsReplay V.2 V.1) !! (child d bt ++ r) =
          nsReplay V.2 V.1 !! (child d bs ++ r)) ∧
      (∀ y, IsUnder (child d bs) y → ¬ IsUnder (child d bt) y →
        (NsOp.rename (child d bs) (child d bt)).apply (nsReplay V.2 V.1) !! y = none) ∧
      (∀ y, ¬ IsUnder (child d bs) y → ¬ IsUnder (child d bt) y →
        (NsOp.rename (child d bs) (child d bt)).apply (nsReplay V.2 V.1) !! y =
          nsReplay V.2 V.1 !! y) := by
    rw [← hm, happ]
    exact ⟨fun r hr => nsMove_under ht' r hr, fun y h1 h2 => nsMove_old ht' y h1 h2,
      fun y h1 h2 => nsMove_other ht' y h1 h2⟩
  have hok : RenameOk st (child d bs) (child d bt) := by
    refine ⟨hcne, parentDir_child hdir hbs, parentDir_child hdir hbt, ?_⟩
    rw [hsd]; exact ⟨not_isUnder_sibling hbt hne, .inl htn⟩
  have hwe : NsWf (st.nsFree.nsDo (.rename (child d bs) (child d bt))) :=
    nsWf_nsDo_free hw hdfn
      (by rw [happ]; exact shape_moveDir hw.roots hw.shape hdir (hw.dir_form hdir) hbs hbt hsd htn)
      (by rw [happ]; exact keys_moveDir ht' (fun p k h => hw.keys h))
  have hce : NsCoh (st.nsFree.nsDo (.rename (child d bs) (child d bt)))
      (V.1, V.2 ++ [.rename (child d bs) (child d bt)]) Γdf :=
    nsCoh_log hc Hnr rfl rfl rfl
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
  · imod osNsAll_update V (V.1, V.2 ++ [.rename (child d bs) (child d bt)]) V $$ HAd HV
      with ⟨HAd, HV⟩
    imod ns_step_close hwf hcoh hs1 Hr Hfr hwe hce false rfl $$ HAb HAm HAf HAt Htok Hcells Hσ
      HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, (V.1, V.2 ++ [.rename (child d bs) (child d bt)]), Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    rcases he with rfl | ⟨e, he, rfl⟩
    · iapply wp_value'
      iapply HΦ $$ %0 %(nsPush V (.rename (child d bs) (child d bt))) [] HV Hz
      ipureintro; exact ⟨.inl ⟨rfl, rfl⟩, hfacts⟩
    · iapply wp_value'
      iapply HΦ $$ %e %(nsPush V (.rename (child d bs) (child d bt))) [] HV Hz
      ipureintro; exact ⟨.inr ⟨he, .inr rfl⟩, hfacts⟩
  · imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb HAm
      HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, V, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %e %V [] HV Hz
    ipureintro; exact ⟨.inr ⟨he, .inl rfl⟩, hfacts⟩

/-- `rename(2)` of `d/bs`, nothing there now, to `d/bt`, with the whole history and the in-flight
flag set: it fails, unchanged (the retry of a rename that moved it). -/
theorem wp_osRenameAbsentG (d bs bt : GoString) (hbs : NameOk bs) (hbt : NameOk bt) (hne : bs ≠ bt)
    (V : NsMap × List NsOp) (hd : nsReplay V.2 V.1 !! d = some .dir)
    (hn : nsReplay V.2 V.1 !! child d bs = none) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) false -∗
        Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rename" (Val (PairV (#(child d bs)) (#(child d bt))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv HV Hz HΦ
  iapply wp_os_stepN "Rename" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases rdRes_none V Γdf $$ HV Hrd with ⟨%Hnr, HV, Hrd⟩
  icases osNsAll_auth _ _ _ $$ HAd HV with %HVe
  subst HVe
  unfold osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hm := ns_eq_replay hw hc
  have hdir : st.ns !! d = some .dir := by rw [hm]; exact hd
  have hdfn := dfds_none hc Hnr
  have hcne : child d bs ≠ child d bt := child_ne_child hne
  have hnofd : ∀ fd df, st.dfds !! fd = some df →
      (st.ns !! child d bs = some .dir → ¬ IsUnder (child d bs) df.path) ∧ df.path ≠ child d bt := by
    intro fd df hdf; rw [hdfn fd] at hdf; cases hdf
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  have hnone : st.ns !! child d bs = none := by rw [hm]; exact hn
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
  iexists Γb, Γm, Γf, Γt, V, Γdf
  unfold osWorld nsWorld
  iframe Hw Hn
  iapply wp_value'
  iapply HΦ $$ %e %he HV Hz

end specs

end Perennial

end
