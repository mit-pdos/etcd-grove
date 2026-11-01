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

/-! ## The file after a growing truncate -/

section ftFile
variable (f : OsFile) (n : Nat)

theorem truncate_length : (f.truncate n).cur.length = n := resizeBytes_length _ _

theorem truncate_getElem? (hn : f.cur.length ≤ n) (i : Nat) :
    (f.truncate n).cur[i]? =
      if i < f.cur.length then f.cur[i]? else if i < n then some 0 else none := by
  show (resizeBytes f.cur n)[i]? = _
  rw [resizeBytes_getElem?]
  by_cases h1 : i < f.cur.length
  · simp [h1, show i < n by omega]
  · simp [h1]

theorem truncate_dirty (hn : f.cur.length ≤ n) (i : Nat) :
    (f.truncate n).dirty i = (f.dirty i || inRange f.cur.length n i) := by
  show (f.dirty i || inRange (min f.cur.length n) (max f.cur.length n) i) = _
  rw [Nat.min_eq_left hn, Nat.max_eq_right hn]

theorem truncate_sizeLo : (f.truncate n).sizeLo = min f.sizeLo n := by
  show min f.sizeLo (resizeBytes f.cur n).length = _; rw [resizeBytes_length]

theorem truncate_sizeHi : (f.truncate n).sizeHi = max f.sizeHi n := by
  show max f.sizeHi (resizeBytes f.cur n).length = _; rw [resizeBytes_length]

theorem truncate_durable : (f.truncate n).durable = f.durable := rfl
theorem truncate_lost : (f.truncate n).lost = f.lost := rfl
theorem truncate_named : (f.truncate n).named = f.named := rfl

/-- Truncating a file to its size changes nothing. -/
theorem truncate_self (h1 : f.sizeLo ≤ f.cur.length) (h2 : f.cur.length ≤ f.sizeHi) :
    f.truncate f.cur.length = f := by
  have hc : resizeBytes f.cur f.cur.length = f.cur := by unfold resizeBytes; simp
  have hl := resizeBytes_length f.cur f.cur.length
  cases f with
  | mk cur durable dirty sizeLo sizeHi lost named =>
    simp only at hc hl h1 h2
    simp only [OsFile.truncate, OsFile.change]
    rw [hc]
    congr 1
    all_goals first | omega | (funext i; cases dirty i <;> simp [inRange])

end ftFile

section ftFinish
variable {st : OsState} {Γb : GMap (GoString × Nat) (w8 × Bool)} {Γm : GMap GoString (Option OsMeta)}
  {Γf : GMap w64 OsFd} {Γt : GMap Nat TokInfo}

/-- The state and the ghost maps after the second step of a truncate that grew the file to `n`
(its size, if it failed and left it unchanged). -/
theorem ftFinish_coh (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) {t : Nat} {ti : TokInfo}
    {p : GoString} {sz n : Nat} {f : OsFile} (hti : Γt !! t = some ti)
    (hc : ti.c = ⟨p, .truncate sz⟩) (hf : st.file p = some f)
    (Hml : Γm !! p = some (some ti.om)) (hn1 : f.cur.length ≤ n) (hn2 : n ≤ sz) :
    let stn := ({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p
      (f.truncate n)
    (∀ t' c', t' ≠ t → st.inflight !! t' = some c' → stn.size c'.path = st.size c'.path) ∧
    (∀ q i, InflightAt stn q i ↔ q ≠ p ∧ InflightAt st q i) ∧
    (∀ i, InflightAt st p i ↔ f.cur.length ≤ i) ∧
    OsWf stn ∧
    OsCoh stn (insertBytes p f.cur.length (List.replicate (n - f.cur.length) (0, false)) Γb)
      (<[p := some { ti.om with size := n }]> Γm) Γf (GMap.delete t Γt) := by
  intro stn
  have hct : st.inflight !! t = some ti.c := by
    have := hcoh.toks t; rw [hti] at this; exact this.symm
  have hcp : ti.c.path = p := by rw [hc]
  have hq1 : ti.q = 1 := hcoh.tok_q t ti hti (by rw [hc]; trivial)
  have hother : ∀ t' c', t' ≠ t → st.inflight !! t' = some c' → c'.path ≠ p := by
    intro t' c' hne h'
    have := hcoh.tok_alone t ti hti hq1 t' c' hne h'; rwa [hcp] at this
  have hsz := size_of_file hf
  obtain ⟨f1, hf1, hmo⟩ := hcoh.meta_some p ti.om Hml
  rw [← file_eq_some, hf] at hf1; cases hf1
  have hszf := hwf.sizes p f hf
  have hlen := truncate_length f n
  have htg := hmo.targets t ti.c hct hcp
  rw [hc] at htg; simp only [OsChange.target] at htg
  have hsizes : ∀ t' c', t' ≠ t → st.inflight !! t' = some c' →
      stn.size c'.path = st.size c'.path := by
    intro t' c' hne h'
    show (({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p _).size _ = _
    rw [size_setFile]; split
    · rename_i hp; exact absurd (by rw [hp]) (hother t' c' hne h')
    · rfl
  have hdel : ∀ t' c', stn.inflight !! t' = some c' → st.inflight !! t' = some c' ∧ t' ≠ t := by
    intro t' c' h1
    change (GMap.delete t st.inflight) !! t' = some c' at h1
    rw [GMap.lookup_delete_iff] at h1; split at h1
    · cases h1
    · rename_i hne; exact ⟨h1, fun e => hne e.symm⟩
  have hIk : ∀ q i, InflightAt stn q i ↔ q ≠ p ∧ InflightAt st q i := by
    intro q i
    constructor
    · rintro ⟨t', c', h1, h2, h3⟩
      obtain ⟨h1, hne⟩ := hdel t' c' h1
      rw [affects_congr1 c' (hsizes t' c' hne h1)] at h3
      exact ⟨fun hq => hother t' c' hne h1 (h2.trans hq), t', c', h1, h2, h3⟩
    · rintro ⟨hq, t', c', h1, h2, h3⟩
      have hne : t' ≠ t := by
        rintro rfl; rw [hct] at h1; cases h1; exact hq (h2.symm.trans hcp)
      refine ⟨t', c', ?_, h2, ?_⟩
      · change (GMap.delete t st.inflight) !! t' = some c'
        rw [GMap.lookup_delete_ne _ (Ne.symm hne)]; exact h1
      · rw [affects_congr1 c' (hsizes t' c' hne h1)]; exact h3
  have hIp : ∀ i, InflightAt st p i ↔ f.cur.length ≤ i := by
    intro i
    constructor
    · rintro ⟨t', c', h1, h2, h3⟩
      by_cases he : t' = t
      · subst he; rw [hct] at h1; cases h1
        rw [hc] at h3; simp only [Affects, hsz] at h3; omega
      · exact absurd h2 (hother t' c' he h1)
    · intro hi
      exact ⟨t, ti.c, hct, hcp, by rw [hc]; simp only [Affects, hsz]; omega⟩
  have hfk : stn.file p = some (f.truncate n) := file_setFile_eq _ _ _
  have hfq : ∀ q, q ≠ p → stn.file q = st.file q := fun q hq => file_setFile_ne _ _ (Ne.symm hq)
  have hex : ∀ q f0, st.file q = some f0 → ∃ f1, stn.file q = some f1 := by
    intro q f0 h0
    by_cases hq : q = p
    · subst hq; exact ⟨_, hfk⟩
    · exact ⟨f0, by rw [hfq q hq]; exact h0⟩
  have hwfk : OsWf stn := by
    refine ⟨fun fd d h => ?_, fun b m h => ?_, hwf.maps_disj, fun t' c' h => ?_,
      fun t1 c1 t2 c2 i h1 h2 hne hp => ?_, fun q f1 h1 => ?_, fun q f1 i h1 => ?_⟩
    · obtain ⟨f0, h0⟩ := hwf.fds fd d h; exact hex _ _ h0
    · obtain ⟨⟨f0, h0⟩, h1, h2, h3⟩ := hwf.maps b m h; exact ⟨hex _ _ h0, h1, h2, h3⟩
    · obtain ⟨f0, h0⟩ := hwf.infl t' c' (hdel t' c' h).1; exact hex _ _ h0
    · obtain ⟨h1, n1⟩ := hdel t1 c1 h1; obtain ⟨h2, n2⟩ := hdel t2 c2 h2
      rw [affects_congr1 c1 (hsizes t1 c1 n1 h1), affects_congr1 c2 (hsizes t2 c2 n2 h2)]
      exact hwf.infl_disj t1 c1 t2 c2 i h1 h2 hne hp
    · by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        rw [truncate_sizeLo, truncate_sizeHi, hlen]; omega
      · rw [hfq q hq] at h1; exact hwf.sizes q f1 h1
    · by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        intro hd hl hi hdl
        rw [truncate_durable, truncate_lost] at *
        rw [truncate_dirty f n hn1, Bool.or_eq_false_iff] at hd
        rw [hlen] at hi
        have hil : i < f.cur.length := by
          have := hd.2; simp only [inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
          omega
        rw [truncate_getElem? f n hn1, if_pos hil]
        exact hwf.coherent q f i hf hd.1 hl hil hdl
      · rw [hfq q hq] at h1; exact hwf.coherent q f1 i h1
  refine ⟨hsizes, hIk, hIp, hwfk, ?_⟩
  have hfp : st.files !! p = some (some f) := file_eq_some.1 hf
  refine ⟨fun q => ?_, fun q => ?_, fun q m' hm => ?_, fun q i x hx => ?_, fun q f1 i h1 hi => ?_,
    hcoh.fds, fun t' => ?_, fun t' ti' h => ?_, fun t' ti' h hq1 => ?_, fun t' ti' h => ?_⟩
  · rw [GMap.lookup_insert_eq_iff]
    show _ ↔ (({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p _).files !! q = none
    rw [files_setFile]; split
    · simp
    · exact hcoh.meta_dom q
  · rw [GMap.lookup_insert_eq_iff]
    show _ ↔ (({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p _).files !! q = some none
    rw [files_setFile]; split
    · simp
    · exact hcoh.meta_none q
  · have htg' : ∀ c', (∃ t', stn.inflight !! t' = some c') → c'.target stn = c'.target st := by
      rintro c' ⟨t', h'⟩
      obtain ⟨h1, n1⟩ := hdel t' c' h'
      exact target_congr1 c' (hsizes t' c' n1 h1)
    rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · rename_i hpq; subst hpq; cases hm
      refine ⟨f.truncate n, file_eq_some.1 hfk, ⟨hlen.symm, by rw [truncate_named]; exact hmo.named,
        by rw [truncate_sizeLo]; have := hmo.lo; dsimp only; omega,
        by rw [truncate_sizeHi]; have := hmo.hi; dsimp only; omega,
        fun hok i => by rw [truncate_lost]; exact hmo.ok hok i, hmo.maps, fun t' c' h1 h2 => ?_⟩⟩
      obtain ⟨h1, n1⟩ := hdel t' c' h1
      exact absurd h2 (hother t' c' n1 h1)
    · rename_i hpq
      obtain ⟨f1, h1, hm1⟩ := hcoh.meta_some q m' hm
      refine ⟨f1, ?_, ⟨hm1.size, hm1.named, hm1.lo, hm1.hi, hm1.ok, hm1.maps, fun t' c' h1 h2 => ?_⟩⟩
      · show (({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p _).files !! q = _
        rw [files_setFile, if_neg hpq]; exact h1
      · rw [htg' c' ⟨t', h1⟩]; exact hm1.targets t' c' (hdel t' c' h1).1 h2
  · rw [lookup_insertBytes] at hx
    split at hx
    · rename_i hr
      obtain ⟨rfl, h1, h2⟩ := hr
      simp only [List.length_replicate] at h2
      rw [List.getElem?_replicate, if_pos (by omega)] at hx; cases hx
      refine ⟨_, hfk, ?_, fun h => by cases h⟩
      rw [truncate_getElem? f n hn1, if_neg (by omega), if_pos (by omega)]
    · rename_i hr
      obtain ⟨f1, h1, hb, hcl⟩ := hcoh.bytes q i x hx
      by_cases hq : q = p
      · subst hq; rw [hf] at h1; cases h1
        have hil : i < f.cur.length := (List.getElem?_eq_some_iff.1 hb).1
        have he : (f.truncate n).cur[i]? = f.cur[i]? := by
          rw [truncate_getElem? f n hn1, if_pos hil]
        refine ⟨_, hfk, by rw [he]; exact hb, fun hx2 => ?_⟩
        obtain ⟨⟨c1, c2, c3, c4⟩, c5⟩ := hcl hx2
        refine ⟨⟨?_, by rw [truncate_lost]; exact c2, by rw [truncate_sizeLo]; omega,
          by rw [truncate_durable, he]; exact c4⟩, fun h => ((hIk _ _).1 h).1 rfl⟩
        rw [truncate_dirty f n hn1, c1]; simp [inRange]; omega
      · refine ⟨f1, by rw [hfq q hq]; exact h1, hb, fun hx2 => ?_⟩
        obtain ⟨c1, c2⟩ := hcl hx2
        exact ⟨c1, fun h => c2 ((hIk _ _).1 h).2⟩
  · rw [lookup_insertBytes]
    split
    · rename_i hr; simp only [List.length_replicate] at hr
      rw [List.getElem?_replicate, if_pos (by omega)]; rfl
    · rename_i hr
      by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        rw [hlen] at hi
        simp only [List.length_replicate, _root_.true_and, not_and, Nat.not_lt] at hr
        exact hcoh.bytes_full q f i hf (by
          apply Classical.byContradiction; intro h0; have := hr (by omega); omega)
      · rw [hfq q hq] at h1; exact hcoh.bytes_full q f1 i h1 hi
  · show (GMap.delete t Γt !! t').map TokInfo.c = (GMap.delete t st.inflight) !! t'
    rw [GMap.lookup_delete_iff, GMap.lookup_delete_iff]; split
    · rfl
    · exact hcoh.toks t'
  · rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · rename_i hne
      have h' : st.inflight !! t' = some ti'.c := by
        have := hcoh.toks t'; rw [h] at this; exact this.symm
      rw [reaches_congr1 ti'.c (hsizes t' ti'.c (fun e => hne e.symm) h')]
      exact hcoh.tok_q t' ti' h
  · intro t'' c'' hne h''
    rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · exact hcoh.tok_alone t' ti' h hq1 t'' c'' hne (hdel t'' c'' h'').1
  · rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · rename_i hne
      have h' : st.inflight !! t' = some ti'.c := by
        have := hcoh.toks t'; rw [h] at this; exact this.symm
      have hne' : t' ≠ t := fun e => hne e.symm
      obtain ⟨f1, h1, hsv1⟩ := hcoh.tok_saved t' ti' h
      have hq : ti'.c.path ≠ p := hother t' ti'.c hne' h'
      rw [affRange_congr1 ti'.c (hsizes t' ti'.c hne' h')]
      exact ⟨f1, by rw [hfq _ hq]; exact h1, hsv1⟩

end ftFinish

/-- What a mapped cell at byte `i` shows after a truncate to `n`: a zero below `n`, a hole past it. -/
def ftCell [GooseExts] (n i : Nat) : val := toCellVal (if i < n then some (0 : w8) else none)

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

theorem cellsR_split' (b : Loc) (a c d : Nat) (vf : Nat → val) (h1 : a ≤ c) (h2 : c ≤ d) :
    cellsR (GF := GF) b a (d - a) vf ⊢ cellsR b a (c - a) vf ∗ cellsR b c (d - c) vf := by
  obtain ⟨k1, rfl⟩ : ∃ k, c = a + k := ⟨c - a, by omega⟩
  obtain ⟨k2, rfl⟩ : ∃ k, d = a + k1 + k := ⟨d - (a + k1), by omega⟩
  rw [show a + k1 + k2 - a = k1 + k2 by omega, show a + k1 - a = k1 by omega,
    show a + k1 + k2 - (a + k1) = k2 by omega]
  exact (cellsR_append _ _ _ _ _).1

/-- The client's halves of the cells `[lo, hi)` of mappings that end at or before `hi`, split
at `mid ≥ lo` (which may be past `hi`). -/
theorem mcells_split (M : GMap Loc Nat) (lo mid hi : Nat) (vf : Nat → val) (h1 : lo ≤ mid)
    (h2 : MapsBelow M hi) :
    mcells (GF := GF) M lo hi vf ⊢ mcells M lo mid vf ∗ mcells M mid hi vf := by
  unfold mcells
  rw [← BigSepM.bigSepM_sep_eq]
  apply BigSepM.bigSepM_mono
  intro b len hb
  have := h2 b len hb
  exact cellsR_split' b _ _ _ vf (by omega) (by omega)

theorem mcells_congr (M : GMap Loc Nat) (lo hi : Nat) (vf vf' : Nat → val)
    (h : ∀ i, lo ≤ i → i < hi → vf i = vf' i) :
    mcells (GF := GF) M lo hi vf ⊢ mcells M lo hi vf' := by
  unfold mcells
  apply BigSepM.bigSepM_mono
  intro b len _
  exact (cellsR_congr _ _ _ _ _ (fun i h1 h2 => h i (by omega) (by omega))).1

/-- The second step of a growing `ftruncate`, giving back the client's halves of the cells of
every mapping past the old size. On success the file is grown (`osGrown`); on failure it may be
grown, or unchanged, its `OsMeta` keeping the crash bound the first step widened (`ftMeta`: the
ghost state does not record the bound from before, as a failed `pwrite`'s `pwMeta` keeps its
own). -/
theorem wp_osFtruncateFinish (t : Nat) (p : GoString) (sz : Nat) (m : OsMeta) (hi : Nat)
    (hE : ↑osN ⊆ E) (hgrow : m.size ≤ sz) (hhi : MapsBelow m.maps hi) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ ftTok (L := L) t p sz m -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ osGrown (L := L) p m sz hi) ∨
         (⌜e ≠ 0⌝ ∗ (osGrown (L := L) p m sz hi ∨
           (osMeta (L := L) p (DFrac.own 1) (some (ftMeta m sz)) ∗ mcellsAny m.maps m.size hi)))) -∗
        Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "FtruncateFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_os_step "FtruncateFinish" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold ftTok osTok
  generalize hti0 : (⟨⟨p, .truncate sz⟩, 1, [], ftMeta m sz⟩ : TokInfo) = ti
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  have hct : st.inflight !! t = some ti.c := by
    have := hcoh.toks t; rw [Hti] at this; exact this.symm
  have hc : ti.c = ⟨p, .truncate sz⟩ := by rw [← hti0]
  obtain ⟨f, hf, -⟩ := hcoh.tok_saved t ti Hti
  rw [hc] at hf; simp only at hf
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
        bytesG gooseOsGS ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
      Hti).1 $$ Htok with ⟨⟨Hm, -⟩, Htok⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hcp : ti.c.path = p := by rw [hc]
  rw [hcp] at Hml
  obtain ⟨f1, hf1, hmo⟩ := coh_meta hcoh Hml
  rw [hf] at hf1; cases hf1
  have hti_om : ti.om = ftMeta m sz := by rw [← hti0]
  have hmsz : m.size = f.cur.length := by
    have := hmo.size; rw [hti_om] at this; simpa [ftMeta] using this
  have hszf := hwf.sizes p f hf
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  have hfin := fun n (h1 : f.cur.length ≤ n) (h2 : n ≤ sz) =>
    ftFinish_coh (n := n) hwf hcoh Hti hc hf Hml h1 h2
  have hst1 : ({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p
      (f.truncate f.cur.length) = { st with inflight := GMap.delete t st.inflight } := by
    rw [truncate_self f hszf.1 hszf.2]
    exact setFile_self (st := { st with inflight := GMap.delete t st.inflight }) hf
  imodintro
  isplitr
  · ipureintro
    obtain ⟨-, -, -, hwfk, -⟩ := hfin sz (by omega) (Nat.le_refl _)
    exact ⟨_, renderHeap (({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p
      (f.truncate sz)) h, _, ⟨t, p, sz, f, rfl, by rw [hct, hc], hf, .inl ⟨rfl, rfl⟩⟩,
      mapsFresh_same rfl, heapRendered_render hwfk rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨t', p', sz', f', hv, hinfl, hf', hrest⟩ := Hst
  have htt : t' = t := by injection hv with hv; exact (extVal_inj hv).symm
  subst htt
  rw [hct, hc] at hinfl; cases hinfl
  rw [hf] at hf'; cases hf'
  obtain ⟨n, e, hn1, hn2, hst', he', hne⟩ : ∃ (n : Nat) (e : w64), f.cur.length ≤ n ∧ n ≤ sz ∧
      st' = ({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile p
        (f.truncate n) ∧ e' = Val (#e) ∧
      ((e = 0 ∧ n = sz) ∨ (e ≠ 0 ∧ (n = sz ∨ n = f.cur.length))) := by
    rcases hrest with ⟨h1, h2⟩ | ⟨e, he, h2, h1 | h1⟩
    · exact ⟨sz, 0, by omega, Nat.le_refl _, h1, h2, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨f.cur.length, e, Nat.le_refl _, by omega, by rw [h1, hst1], h2, .inr ⟨he, .inr rfl⟩⟩
    · exact ⟨sz, e, by omega, Nat.le_refl _, h1, h2, .inr ⟨he, .inl rfl⟩⟩
  subst hst' he'
  obtain ⟨hsizes, hIk, hIp, hwfk, hcohk⟩ := hfin n hn1 hn2
  -- the meta
  have eqm : gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm ti.c.path (DFrac.own ti.q) (some ti.om) ⊢
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p (DFrac.own 1) (some (ftMeta m sz)) := by
    rw [hcp, hti_om, show ti.q = 1 by rw [← hti0]]
  ihave Hm := eqm $$ Hm
  imod meta_replace _ (q := 1) (om := { ftMeta m sz with size := n }) (fun h1 => absurd rfl h1)
    $$ [HAm Hm] with ⟨HAm, Hm⟩
  · iframe
  -- the bytes
  imod bytesG_alloc _ p f.cur.length (List.replicate (n - f.cur.length) (0, false)) Γb
    (fun j hj => by
      cases hb : Γb !! (p, f.cur.length + j) with
      | none => rfl
      | some x =>
        exfalso
        obtain ⟨f2, hf2, hb2, -⟩ := hcoh.bytes _ _ _ hb
        rw [hf] at hf2; cases hf2
        have := (List.getElem?_eq_some_iff.1 hb2).1; omega) $$ HAb with ⟨HAb, Hbs⟩
  -- the token
  imod gAuth_delete _ _ _ _ _ $$ HAt Ht with HAt
  -- the cells: the cells past the size come back, showing the new bytes
  have hmaps : ti.om.maps = m.maps := by rw [hti_om]; rfl
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmo.maps b1 l1).1 (hmaps ▸ h1)) ((hmo.maps b2 l2).1 (hmaps ▸ h2)) hne)
  generalize hC : mapsCells m.size hi (ftCell n) m.maps.toList = C
  have hClk := fun l v => hC ▸ lookup_mapsCells m.size hi (ftCell n) m.maps.toList hdisj l v
  have hTmem : ∀ l, l ∈ C.toList.map (·.1) ↔ (C !! l).isSome := by
    intro l; simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hkv, rfl⟩; rw [(GMap.mem_toList _ _ _).1 hkv]; rfl
    · intro hl; obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
      exact ⟨(l, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  have hTnd : (C.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := C)
  have hin : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l p i ∧ f.cur.length ≤ i ∧
      C !! l = some (ftCell n i) := by
    intro l hl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨i, ⟨b, len, hm, h1, h2, h3, rfl⟩, rfl⟩ := (hClk _ v).1 hv
    exact ⟨i, ⟨b, ⟨p, len⟩, (hmo.maps b len).1 (hmaps ▸ (GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
      by omega, hv⟩
  have hfk : (({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile p
      (f.truncate n)).file p = some (f.truncate n) := file_setFile_eq _ _ _
  imod cells_step st _ h h' (C.toList.map (·.1)) ∅ C hwf hwfk Hr Hfr (fun b m0 h0 => .inr h0) hTnd
    (fun l hl => by obtain ⟨i, hi, -⟩ := hin l ((hTmem l).1 hl); exact .inl ⟨_, _, hi⟩)
    (fun l v h => by simp at h)
    (fun l v hl => by
      have hs : (C !! l).isSome := by rw [hl]; rfl
      obtain ⟨i, hi, ha, hv⟩ := hin l hs
      rw [hl] at hv; cases hv
      have hn : ¬ InflightAt (({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile p
          (f.truncate n)) p i := fun h => ((hIk _ _).1 h).1 rfl
      refine ⟨(hTmem l).2 hs, _, by rw [cellView_mapsTo hwfk hi, decide_eq_false hn], ?_⟩
      rw [cellByte_eq, if_neg hn, hfk]
      simp only [Option.bind_some]
      rw [truncate_getElem? f n hn1, if_neg (by omega)]; rfl)
    (fun l hl _ x hx => by
      obtain ⟨i, hi, ha, -⟩ := hin l ((hTmem l).1 hl)
      rw [cellView_mapsTo hwf hi] at hx; cases hx
      exact decide_eq_true ((hIp i).2 ha))
    (fun l hl hn => by
      rw [Option.isSome_iff_exists.1 ((hTmem l).1 hl) |>.choose_spec] at hn; cases hn)
    (fun l hl => by
      by_cases hm : Mapped st l
      · obtain ⟨q', i, hqi⟩ := hm
        rw [cellView_mapsTo hwfk hqi, cellView_mapsTo hwf hqi, cellByte_eq, cellByte_eq]
        by_cases hpq : q' = p
        · subst hpq
          have hil : i < f.cur.length := by
            apply Classical.byContradiction; intro hge
            obtain ⟨b, m0, hb, hp0, hi0, rfl⟩ := hqi
            have hb' : m.maps !! b = some m0.len := by
              rw [← hmaps, hmo.maps b m0.len, hb]; congr 1; cases m0; simp only at hp0 ⊢; rw [hp0]
            have := hhi b _ hb'
            apply hl; apply (hTmem _).2
            rw [(hClk _ _).2 ⟨i, ⟨b, m0.len, (GMap.mem_toList _ _ _).2 hb', by omega, by omega,
              hi0, rfl⟩, rfl⟩]
            rfl
          have hn1' : ¬ InflightAt (({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile q'
              (f.truncate n)) q' i := fun h => ((hIk _ _).1 h).1 rfl
          have hn2' : ¬ InflightAt st q' i := fun h => by have := (hIp i).1 h; omega
          rw [if_neg hn1', if_neg hn2', decide_eq_false hn1', decide_eq_false hn2', hfk, hf]
          simp only [Option.bind_some]
          rw [truncate_getElem? f n hn1, if_pos hil]
        · have hII : InflightAt (({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile p
              (f.truncate n)) q' i ↔ InflightAt st q' i := by
            rw [hIk]; exact ⟨fun h => h.2, fun h => ⟨hpq, h⟩⟩
          simp only [hII]
          rw [file_setFile_ne _ _ (Ne.symm hpq)]; rfl
      · rw [cellView_none (st := st) hm]; exact cellView_none hm)
    $$ [Hσ Hcells] with ⟨Hσ, Hcells, Hc⟩
  · iframe; unfold halves; iapply BigSepM.bigSepM_empty.2; iempintro
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells
  isplitl [Htok]
  · isplitr
    · ipureintro
      rw [hti_om] at hcohk
      exact ⟨hwfk, hcohk⟩
    have htc := tokRes_congr (gooseOsGS (L := L)) (st := st)
      (st' := ({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile p
        (f.truncate n)) (Γt := GMap.delete t' Γt) (fun t2 ti2 h2 => by
      rw [GMap.lookup_delete_iff] at h2; split at h2
      · cases h2
      · rename_i hne
        have h2' : st.inflight !! t2 = some ti2.c := by
          have := hcoh.toks t2; rw [h2] at this; exact this.symm
        exact hsizes t2 ti2.c (fun e => hne e.symm) h2')
    unfold tokRes at htc
    iapply htc $$ Htok
  iapply wp_value'
  -- the client's view
  have hcells : mcells (GF := GF) m.maps m.size hi (ftCell n) ⊢
      mcells m.maps m.size n (fun _ => byteCell 0) ∗ mcellsAny m.maps n hi := by
    iintro H
    icases mcells_split m.maps m.size n hi _ (by omega) hhi $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iapply (mcells_congr _ _ _ (ftCell n) _ (fun i _ hi => by
        show toCellVal _ = toCellVal _; rw [if_pos hi])) $$ H1
    · iapply mcells_any $$ H2
  ihave Hc : mcells m.maps m.size hi (ftCell n) $$ [Hc]
  · unfold mcells
    iapply (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
      cellsR b (min m.size len) (min hi len - min m.size len) (ftCell n))).2
    iapply (halves_mapsCells _ _ _ _ hdisj).1
    rw [hC]; iexact Hc
  ihave Hbs := (show bytesG (gooseOsGS (L := L)) p f.cur.length (DFrac.own 1)
      (List.replicate (n - f.cur.length) (0, false)) ⊢
    bytesG (gooseOsGS (L := L)) p m.size (DFrac.own 1) (List.replicate (n - m.size) (0, false)) by
      rw [hmsz]) $$ Hbs
  unfold osMeta
  rcases hne with ⟨rfl, rfl⟩ | ⟨he, rfl | rfl⟩
  · iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    unfold osGrown osMeta osBytes
    icases hcells $$ Hc with ⟨Hc1, Hc2⟩
    rw [show m.grown n = { ftMeta m n with size := n } from rfl]
    iframe
  · iapply HΦ
    iright
    isplitr
    · ipureintro; exact he
    ileft
    unfold osGrown osMeta osBytes
    icases hcells $$ Hc with ⟨Hc1, Hc2⟩
    rw [show m.grown n = { ftMeta m n with size := n } from rfl]
    iframe
  · iapply HΦ
    iright
    isplitr
    · ipureintro; exact he
    iright
    rw [show ftMeta m sz = { ftMeta m sz with size := f.cur.length } by rw [← hmsz]; rfl]
    iframe Hm
    iapply mcells_any $$ Hc

end specs

end Perennial
