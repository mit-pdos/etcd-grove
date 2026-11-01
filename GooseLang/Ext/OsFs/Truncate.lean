/-
WP specs of the Linux file extension's `ftruncate` (`FtruncateStart`, `FtruncateFinish`), for a
truncate that grows the file (or keeps its size): it takes no byte of the file, and gives it the
new bytes, zeros. The client holds the file's `OsMeta` whole, so no other change is in flight.
While it is in flight, a truncate affects every byte from the size on, so its first step takes
the client's halves of every mapped cell past the size (up to `hi`, where every mapping ends),
and its second step gives them back.
-/
module

public import GooseLang.Ext.OsFs.Write

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-- The `OsMeta` of a file while a truncate to `sz` is in flight: the size may become `sz`. -/
def ftMeta (m : OsMeta) (sz : Nat) : OsMeta := { m with hi := max m.hi sz }

/-- The `OsMeta` of a file after a truncate to `sz ≥ m.size`. -/
def OsMeta.grown (m : OsMeta) (sz : Nat) : OsMeta := { m with size := sz, hi := max m.hi sz }

/-- Every mapping of `M` ends at or before `hi`. -/
def MapsBelow (M : GMap Loc Nat) (hi : Nat) : Prop := ∀ b len, M !! b = some len → len ≤ hi

/-- The value of a mapped cell showing the byte `b`. -/
abbrev byteCell [GooseExts] (b : w8) : val := toCellVal (some b)

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- An `ftruncate` to `sz` of the file `p` between its two steps: its first step took the whole
of the file's `OsMeta` `m`. -/
def ftTok (t : Nat) (p : GoString) (sz : Nat) (m : OsMeta) : IProp GF :=
  osTok (L := L) t ⟨⟨p, .truncate sz⟩, 1, [], ftMeta m sz⟩

/-- The file `p`, of `OsMeta` `m`, grown to `sz ≥ m.size`: the whole `OsMeta` (`m.grown sz`), the
new bytes, zeros and dirty, whole, and the client's halves of the cells of every mapping over
`[m.size, sz)`, showing them, and over `[sz, hi)`. -/
def osGrown (p : GoString) (m : OsMeta) (sz hi : Nat) : IProp GF :=
  iprop(osMeta (L := L) p (DFrac.own 1) (some (m.grown sz)) ∗
    osBytes (L := L) p m.size (DFrac.own 1) (List.replicate (sz - m.size) (0, false)) ∗
    mcells m.maps m.size sz (fun _ => byteCell 0) ∗ mcellsAny m.maps sz hi)

/-- The client's halves of the (no) cells of an empty range. -/
theorem mcellsAny_nil (M : GMap Loc Nat) (lo hi : Nat) (h : lo = hi) :
    ⊢ mcellsAny (GF := GF) M lo hi := by
  subst h
  unfold mcellsAny
  refine BigSepM.bigSepM_intro (P := iprop(emp)) (fun _ => ?_)
  iintro -
  iexists (fun _ => #())
  rw [Nat.sub_self]
  unfold cellsR
  simp only [List.range'_zero]
  iapply BigSepL.bigSepL_nil.2
  iempintro

/-- The first step of `ftruncate(fd, sz)` growing the file, with the whole of its `OsMeta`, which
stays with the change until its second step (`wp_osFtruncateFinish`), and the client's halves of
the cells of every mapping past the size, which the change affects. -/
theorem wp_osFtruncateStart (fd sz : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (hi : Nat)
    (hE : ↑osN ⊆ E) (hwr : d.writable = true) (hsz0 : 0 ≤ sz.toInt) (hgrow : m.size ≤ sz.toNat)
    (hhi : MapsBelow m.maps hi) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.path (DFrac.own 1) (some m) -∗
      mcellsAny m.maps m.size hi -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗ ftTok (L := L) t d.path sz.toNat m -∗ Φ (osTokV t)) -∗
      WP (ExternalOp osFsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm Hc HΦ
  iapply wp_os_step "FtruncateStart" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_frac _ $$ Htok Hm with %Hfrac
  icases tokRes_meta_whole _ $$ Htok Hm with %Hwhole
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hsz : st.size d.path = m.size := by rw [size_of_file hf, hmo.size]
  have hnot := noTok_of_whole hcoh Hwhole
  have hnbusy : ¬ BusyAt st d.path := by
    rintro ⟨t', c', h1, h2⟩; exact hnot t' c' h1 h2
  have hfree : ∀ i, Affects st ⟨d.path, .truncate sz.toNat⟩ i → ¬ InflightAt st d.path i := by
    rintro i - ⟨t', c', h1, h2, -⟩; exact hnot t' c' h1 h2
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  obtain ⟨t0, ht0⟩ := exists_fresh st.inflight
  imodintro
  isplitr
  · ipureintro
    have hwf0 := osWf_addTok (t := t0) (c := ⟨d.path, .truncate sz.toNat⟩) hwf ht0 hf hfree
    exact ⟨_, _, _, ⟨fd, sz, t0, d, rfl, hfd, hwr, hsz0, hnbusy, ht0, rfl, rfl⟩,
      mapsFresh_same rfl, heapRendered_render hwf0 rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', sz', t, d', hv, hfd', -, -, -, ht, hst', rfl⟩ := Hst
  injection hv with h1 h3
  cases go.intoVal_inj h1; cases go.intoVal_inj h3
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  subst hst'
  generalize hc : (⟨d.path, .truncate sz.toNat⟩ : OsChange) = c at hfree Hr Hfr ⊢
  have hcp : c.path = d.path := by rw [← hc]
  have hlo : affLo st c = m.size := by rw [← hc]; simp [affLo, hsz]; omega
  have hhi' : affHi st c = m.size := by rw [← hc]; simp [affHi, hsz]
  have haff : ∀ i, Affects st c i ↔ m.size ≤ i := by
    intro i; rw [← hc]; simp [Affects, hsz]; omega
  have hwf1 := osWf_addTok (t := t) (c := c) hwf ht (hcp ▸ hf) (hcp ▸ hfree)
  have hcoh1 := osCoh_addTok (t := t) (q := 1) (m := m) (om := ftMeta m sz.toNat)
    (xs := []) hcoh hcp hf Hml
    ⟨rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_max_left _ _,
      by rw [← hc]; simp only [OsChange.target, ftMeta]; have := hmo.lo; have := hmo.size
         have := (hwf.sizes d.path f hf).1; omega,
      by rw [← hc]; simp only [OsChange.target, ftMeta]; omega⟩
    ht (hcp ▸ hfree) (fun _ => rfl)
    Hfrac (fun _ => hnot) (by rw [hlo, hhi']; simp) (fun k hk => by simp at hk)
  -- the cells: the client's halves of the cells past the size go to the invariant
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmo.maps b1 l1).1 h1) ((hmo.maps b2 l2).1 h2) hne)
  unfold mcellsAny
  ihave Hc := (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
    iprop(∃ vf, cellsR b (min m.size len) (min hi len - min m.size len) vf))).1 $$ Hc
  icases halves_mapsCells_ex m.size hi _ hdisj $$ Hc with ⟨%C, Hc, %hC⟩
  have hI := inflightAt_addTok (c := c) ht
  have hmapsC : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l d.path i ∧ Affects st c i := by
    intro l hl
    obtain ⟨i, b, len, hm, h1, h2, h3, rfl⟩ := (hC l).1 hl
    exact ⟨i, ⟨b, ⟨d.path, len⟩, (hmo.maps b len).1 ((GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
      (haff i).2 h1⟩
  have hTmem : ∀ l, l ∈ C.toList.map (·.1) ↔ (C !! l).isSome := by
    intro l; simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hkv, rfl⟩; rw [(GMap.mem_toList _ _ _).1 hkv]; rfl
    · intro hl; obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
      exact ⟨(l, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  have hTnd : (C.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := C)
  imod cells_step st _ h h' (C.toList.map (·.1)) C ∅ hwf hwf1 Hr Hfr (fun b m0 h0 => .inr h0) hTnd
    (fun l hl => by obtain ⟨i, hi, -⟩ := hmapsC l ((hTmem l).1 hl); exact .inl ⟨_, _, hi⟩)
    (fun l v hl => by
      have hs : (C !! l).isSome := by rw [hl]; rfl
      obtain ⟨i, hi, ha⟩ := hmapsC l hs
      exact ⟨(hTmem l).2 hs, _, by rw [cellView_mapsTo hwf hi, decide_eq_false (hfree i ha)]⟩)
    (fun l v h => by simp at h)
    (fun l hl hn => by rw [(hTmem l).1 hl |> Option.isSome_iff_exists.1 |>.choose_spec] at hn; cases hn)
    (fun l hl _ x hx => by
      obtain ⟨i, hi, ha⟩ := hmapsC l ((hTmem l).1 hl)
      rw [cellView_mapsTo hwf1 hi] at hx; cases hx
      exact decide_eq_true ((hI _ _).2 (.inr ⟨hcp, ha⟩)))
    (fun l hl => by
      by_cases hm : Mapped st l
      · obtain ⟨q', i, hqi⟩ := hm
        rw [cellView_mapsTo hwf1 hqi, cellView_mapsTo hwf hqi, cellByte_eq, cellByte_eq]
        have hn : ¬ (c.path = q' ∧ Affects st c i) := by
          rintro ⟨hp, ha⟩
          obtain ⟨b, m0, hb, hp0, hi0, rfl⟩ := hqi
          have hb' : m.maps !! b = some m0.len := by
            rw [hmo.maps b m0.len, hb]; congr 1; cases m0; simp only at hp0 ⊢
            rw [hp0, ← hp, hcp]
          apply hl; apply (hTmem _).2; apply (hC _).2
          have h1 := (haff i).1 ha
          have h2 := hhi b m0.len hb'
          exact ⟨i, b, m0.len, (GMap.mem_toList _ _ _).2 hb', h1, by omega, hi0, rfl⟩
        have hII : InflightAt { st with inflight := <[t := c]> st.inflight } q' i ↔
            InflightAt st q' i := by rw [hI]; exact ⟨fun h => h.resolve_right hn, .inl⟩
        simp only [hII]; rfl
      · rw [cellView_none (st := st) hm]; exact cellView_none hm)
    $$ [Hσ Hcells Hc] with ⟨Hσ, Hcells, -⟩
  · iframe
  -- the ghost maps
  imod meta_replace _ (q := 1) (om := ftMeta m sz.toNat) (fun h1 => absurd rfl h1)
    $$ [HAm Hm] with ⟨HAm, Hm⟩
  · iframe
  have hΓt : Γt !! t = none := by
    have := hcoh.toks t; rw [ht] at this
    cases h0 : Γt !! t
    · rfl
    · rw [h0] at this; cases this
  imod gAuth_insert _ _ _ t ⟨c, 1, [], ftMeta m sz.toNat⟩ hΓt $$ HAt with ⟨HAt, Ht⟩
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells
  isplitl [Htok Hm]
  · isplitr
    · ipureintro; exact ⟨hwf1, hcoh1⟩
    rw [show tokRes (gooseOsGS (L := L)) { st with inflight := <[t := c]> st.inflight }
        (<[t := ⟨c, 1, [], ftMeta m sz.toNat⟩]> Γt) =
      tokRes gooseOsGS st (<[t := ⟨c, 1, [], ftMeta m sz.toNat⟩]> Γt) from rfl]
    unfold tokRes
    iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
        bytesG gooseOsGS ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
      hΓt).2
    rw [hcp]
    iframe
    simp only [List.map_nil]
    iapply (bytesG_nil gooseOsGS _ _ _).2; iempintro
  iapply wp_value'
  iapply HΦ $$ Hfd
  unfold ftTok osTok
  rw [← hc]; iexact Ht

/-- The second step of a growing `ftruncate`, giving back the client's halves of the cells of
every mapping past the old size. On success the file is grown (`osGrown`); on failure it may be
grown, or unchanged. -/
theorem wp_osFtruncateFinish (t : Nat) (p : GoString) (sz : Nat) (m : OsMeta) (hi : Nat)
    (hE : ↑osN ⊆ E) (hgrow : m.size ≤ sz) (hhi : MapsBelow m.maps hi) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ ftTok (L := L) t p sz m -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ osGrown (L := L) p m sz hi) ∨
         (⌜e ≠ 0⌝ ∗ (osGrown (L := L) p m sz hi ∨
           (osMeta (L := L) p (DFrac.own 1) (some m) ∗ mcellsAny m.maps m.size hi)))) -∗
        Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "FtruncateFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  sorry

end specs

end Perennial
