/-
WP specs of the Linux file extension's `ftruncate` (`FtruncateStart`, `FtruncateFinish`), for a
truncate that shrinks the file (to `sz ≤` its size), of a file that no mapping maps. The client
holds the file's `OsMeta` whole, so no other change is in flight, and the bytes past the new size
whole: the first step takes them (the change affects every byte from `sz` on), and the second
step, on success, removes them. On failure the client gets nothing back.
-/
module

public import GooseLang.Ext.OsFs.Truncate

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-- The `OsMeta` of a file while a shrink to `sz` is in flight: a crash may leave it as small as
`sz`. -/
def shMeta (m : OsMeta) (sz : Nat) : OsMeta := { m with lo := min m.lo sz }

/-- The `OsMeta` of a file after a truncate to `sz ≤ m.size`. -/
def OsMeta.shrunk (m : OsMeta) (sz : Nat) : OsMeta := { m with size := sz, lo := min m.lo sz }

theorem OsMeta.shrunk_size (m : OsMeta) (sz : Nat) : (m.shrunk sz).size = sz := rfl
theorem OsMeta.shrunk_maps (m : OsMeta) (sz : Nat) : (m.shrunk sz).maps = m.maps := rfl

theorem OsMeta.shrunk_shMeta (m : OsMeta) (sz : Nat) : (shMeta m sz).shrunk sz = m.shrunk sz := by
  simp only [OsMeta.shrunk, shMeta, Nat.min_assoc, Nat.min_self]

theorem OsMeta.shrunk_shrunk (m : OsMeta) (sz : Nat) : (m.shrunk sz).shrunk sz = m.shrunk sz := by
  simp only [OsMeta.shrunk, Nat.min_assoc, Nat.min_self]

/-! ## The file after a shrinking truncate -/

section shFile
variable (f : OsFile) (n : Nat)

theorem truncate_getElem?_le (hn : n ≤ f.cur.length) (i : Nat) :
    (f.truncate n).cur[i]? = if i < n then f.cur[i]? else none := by
  show (resizeBytes f.cur n)[i]? = _
  rw [resizeBytes_getElem?]
  by_cases h1 : i < n
  · simp [h1, show i < f.cur.length by omega]
  · simp [h1]

theorem truncate_dirty_le (hn : n ≤ f.cur.length) (i : Nat) :
    (f.truncate n).dirty i = (f.dirty i || inRange n f.cur.length i) := by
  show (f.dirty i || inRange (min f.cur.length n) (max f.cur.length n) i) = _
  rw [Nat.min_eq_right hn, Nat.max_eq_left hn]

end shFile

/-! ## The view of the mapped cells, unchanged by a change to an unmapped file -/

section cells
attribute [local instance] Classical.propDecidable

theorem cellView_noMap {st st' : OsState} (hwf : OsWf st) (hwf' : OsWf st')
    (hm : st'.maps = st.maps) (p : GoString)
    (hp : ∀ b mm, st.maps !! b = some mm → mm.path ≠ p)
    (hf : ∀ q, q ≠ p → st'.file q = st.file q)
    (hI : ∀ q i, q ≠ p → (InflightAt st' q i ↔ InflightAt st q i)) :
    cellView st' = cellView st := by
  apply GMap.ext; intro l
  show cellView st' !! l = cellView st !! l
  have hM : ∀ q i, MapsTo st' l q i ↔ MapsTo st l q i := by
    intro q i; simp only [MapsTo, hm]
  by_cases h : Mapped st l
  · obtain ⟨q, i, hqi⟩ := h
    have hq : q ≠ p := by
      obtain ⟨b, mm, hb, hpq, -, -⟩ := hqi
      rw [← hpq]; exact hp b mm hb
    rw [cellView_mapsTo hwf' ((hM q i).2 hqi), cellView_mapsTo hwf hqi]
    have hII := propext (hI q i hq)
    unfold cellByte
    rw [hf q hq]
    simp only [hII]
  · rw [cellView_none h, cellView_none (fun ⟨q, i, hpi⟩ => h ⟨q, i, (hM q i).1 hpi⟩)]

end cells

/-! ## The ghost maps after the second step -/

section shFinish
variable {st : OsState} {Γb : GMap (GoString × Nat) (w8 × Bool)} {Γm : GMap GoString (Option OsMeta)}
  {Γf : GMap w64 OsFd} {Γt : GMap Nat TokInfo}

/-- The state and the ghost maps after the second step of a truncate to `sz` that shrank the file
to `n` (its size, if it failed and left it unchanged). -/
theorem shFinish_coh (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) {t : Nat} {ti : TokInfo}
    {p : GoString} {sz n : Nat} {f : OsFile} (hti : Γt !! t = some ti)
    (hc : ti.c = ⟨p, .truncate sz⟩) (hf : st.file p = some f)
    (Hml : Γm !! p = some (some ti.om)) (hn1 : sz ≤ n) (hn2 : n ≤ f.cur.length) :
    let stn := ({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p
      (f.truncate n)
    (∀ t' c', t' ≠ t → st.inflight !! t' = some c' → stn.size c'.path = st.size c'.path) ∧
    (∀ q i, InflightAt stn q i ↔ q ≠ p ∧ InflightAt st q i) ∧
    (∀ i, InflightAt st p i ↔ sz ≤ i) ∧
    OsWf stn ∧
    OsCoh stn (deleteBytes p n (f.cur.length - n) Γb)
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
  have hIp : ∀ i, InflightAt st p i ↔ sz ≤ i := by
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
        rw [truncate_dirty_le f n hn2, Bool.or_eq_false_iff] at hd
        rw [hlen] at hi
        rw [truncate_getElem?_le f n hn2, if_pos hi]
        exact hwf.coherent q f i hf hd.1 hl (by omega) hdl
      · rw [hfq q hq] at h1; exact hwf.coherent q f1 i h1
  refine ⟨hsizes, hIk, hIp, hwfk, ?_⟩
  refine ⟨fun q => ?_, fun q => ?_, fun q m' hm => ?_, fun q i x hx => ?_, fun q f1 i h1 hi => ?_,
    hcoh.fds, fun t' => ?_, fun t' ti' h => ?_, fun t' ti' h hq1 => ?_, fun t' ti' h => ?_,
    fun t' ti' h => ?_⟩
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
        fun hok i => by rw [truncate_lost]; exact hmo.ok hok i, hmo.maps, fun t' c' h1 h2 => ?_,
        fun i d h => by rw [truncate_durable]; exact hmo.dur i d h,
        by rw [truncate_durable]; exact hmo.durLen⟩⟩
      obtain ⟨h1, n1⟩ := hdel t' c' h1
      exact absurd h2 (hother t' c' n1 h1)
    · rename_i hpq
      obtain ⟨f1, h1, hm1⟩ := hcoh.meta_some q m' hm
      refine ⟨f1, ?_, ⟨hm1.size, hm1.named, hm1.lo, hm1.hi, hm1.ok, hm1.maps, fun t' c' h1 h2 => ?_,
        hm1.dur, hm1.durLen⟩⟩
      · show (({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p _).files !! q = _
        rw [files_setFile, if_neg hpq]; exact h1
      · rw [htg' c' ⟨t', h1⟩]; exact hm1.targets t' c' (hdel t' c' h1).1 h2
  · rw [lookup_deleteBytes] at hx
    split at hx
    · cases hx
    · rename_i hr
      obtain ⟨f1, h1, hb, hcl⟩ := hcoh.bytes q i x hx
      by_cases hq : q = p
      · subst hq; rw [hf] at h1; cases h1
        have hil : i < f.cur.length := (List.getElem?_eq_some_iff.1 hb).1
        have hin : i < n := by
          apply Classical.byContradiction; intro h0; exact hr ⟨rfl, by omega, by omega⟩
        have he : (f.truncate n).cur[i]? = f.cur[i]? := by
          rw [truncate_getElem?_le f n hn2, if_pos hin]
        refine ⟨_, hfk, by rw [he]; exact hb, fun hx2 => ?_⟩
        obtain ⟨⟨c1, c2, c3, c4⟩, c5⟩ := hcl hx2
        refine ⟨⟨?_, by rw [truncate_lost]; exact c2, by rw [truncate_sizeLo]; omega,
          by rw [truncate_durable, he]; exact c4⟩, fun h => ((hIk _ _).1 h).1 rfl⟩
        rw [truncate_dirty_le f n hn2, c1]; simp [inRange]; omega
      · refine ⟨f1, by rw [hfq q hq]; exact h1, hb, fun hx2 => ?_⟩
        obtain ⟨c1, c2⟩ := hcl hx2
        exact ⟨c1, fun h => c2 ((hIk _ _).1 h).2⟩
  · rw [lookup_deleteBytes]
    split
    · rename_i hr
      by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        rw [hlen] at hi; omega
      · exact absurd hr.1 hq
    · by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        rw [hlen] at hi
        exact hcoh.bytes_full q f i hf (by omega)
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
  · rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · rename_i hne
      intro j hj
      have h' : st.inflight !! t' = some ti'.c := by
        have := hcoh.toks t'; rw [h] at this; exact this.symm
      have hne' : t' ≠ t := fun e => hne e.symm
      have hs' := hsizes t' ti'.c hne' h'
      obtain ⟨hjl, f1, h1, hc1⟩ := hcoh.tok_clean t' ti' h j hj
      have hq : ti'.c.path ≠ p := hother t' ti'.c hne' h'
      have hlo1 : affLo stn ti'.c = affLo st ti'.c := by unfold affLo; rw [hs']
      have hhi1 : affHi stn ti'.c = affHi st ti'.c := by unfold affHi; rw [hs']
      rw [hlo1, hhi1]
      exact ⟨hjl, f1, by rw [hfq _ hq]; exact h1, hc1⟩

end shFinish

/-! ## Specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- A shrinking `ftruncate` to `sz` of the file `p` between its two steps: its first step took the
whole of the file's `OsMeta` `m` and the bytes `xs` past `sz`. -/
def shTok (t : Nat) (p : GoString) (sz : Nat) (m : OsMeta) (xs : List (w8 × Bool)) : IProp GF :=
  osTok (L := L) t ⟨⟨p, .truncate sz⟩, 1, xs.map Prod.fst, shMeta m sz, xs.map Prod.snd⟩

/-- No mapping of the state maps a file whose ghost `OsMeta` has no mapping. -/
theorem noMap_of_meta {st : OsState} {p : GoString} {m : OsMeta} {f : OsFile}
    (hmo : MetaOk st p m f) (hmaps : m.maps = ∅) :
    ∀ b mm, st.maps !! b = some mm → mm.path ≠ p := by
  intro b mm hb hp
  have : m.maps !! b = some mm.len := by
    rw [hmo.maps b mm.len, hb]; cases mm; simp only at hp ⊢; rw [hp]
  rw [hmaps] at this; cases this

/-- The first step of `ftruncate(fd, sz)` shrinking an unmapped file, with the whole of its
`OsMeta` and the bytes past `sz`, which stay with the change until its second step
(`wp_osFtruncateShrinkFinish`). -/
theorem wp_osFtruncateShrinkStart (fd sz : w64) (dq : DFrac) (d : OsFd) (m : OsMeta)
    (xs : List (w8 × Bool)) (hE : ↑osN ⊆ E) (hwr : d.writable = true) (hsz0 : 0 ≤ sz.toInt)
    (hshr : sz.toNat ≤ m.size) (hmaps : m.maps = ∅) (hxs : xs.length = m.size - sz.toNat)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.path (DFrac.own 1) (some m) -∗
      osBytes (L := L) d.path sz.toNat (DFrac.own 1) xs -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗ shTok (L := L) t d.path sz.toNat m xs -∗ Φ (osTokV t)) -∗
      WP (ExternalOp osFsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs HΦ
  iapply wp_os_step "FtruncateStart" _ Φ (by simp [val.isPanic]) hE (by simp [OldOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta osBytes
  icases bytesG_lookup _ d.path _ _ xs Γb $$ HAb Hbs with %Hbl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_frac _ $$ Htok Hm with %Hfrac
  icases tokRes_meta_whole _ $$ Htok Hm with %Hwhole
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hsz : st.size d.path = m.size := by rw [size_of_file hf, hmo.size]
  have hszf := hwf.sizes d.path f hf
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
  have hlo : affLo st c = sz.toNat := by rw [← hc]; simp [affLo, hsz]; omega
  have hhi' : affHi st c = m.size := by rw [← hc]; simp [affHi, hsz]
  have hwf1 := osWf_addTok (t := t) (c := c) hwf ht (hcp ▸ hf) (hcp ▸ hfree)
  have hcoh1 := osCoh_addTok (t := t) (q := 1) (m := m) (om := shMeta m sz.toNat)
    (xs := xs) hcoh hcp hf Hml
    ⟨rfl, rfl, rfl, rfl, Nat.min_le_left _ _, Nat.le_refl _,
      by rw [← hc]; simp only [OsChange.target, shMeta]; omega,
      by rw [← hc]; simp only [OsChange.target, shMeta]; have := hmo.hi; have := hmo.size
         have := hszf.2; omega, rfl⟩
    ht (hcp ▸ hfree) (fun _ => rfl)
    Hfrac (fun _ => hnot) (by rw [hlo, hhi', hxs]) (fun k hk => by rw [hlo]; exact Hbl k hk)
  -- the cells: the file is unmapped, so none changes
  have hcv : cellView { st with inflight := <[t := c]> st.inflight } = cellView st :=
    cellView_noMap hwf hwf1 rfl d.path (noMap_of_meta hmo hmaps) (fun _ _ => rfl)
      (fun q i hq => by
        rw [inflightAt_addTok ht]
        exact ⟨fun h => h.resolve_right (fun h2 => hq (hcp ▸ h2.1).symm), .inl⟩)
  imod cells_same hwf hwf1 Hr Hfr rfl hcv $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  -- the ghost maps
  imod meta_replace _ (q := 1) (om := shMeta m sz.toNat) (fun h1 => absurd rfl h1)
    $$ [HAm Hm] with ⟨HAm, Hm⟩
  · iframe
  imod bytesG_update _ d.path _ xs (xs.map (fun x => (x.1, false))) Γb (by simp) $$ [HAb Hbs]
    with ⟨HAb, Hbs⟩
  · iframe
  have hΓt : Γt !! t = none := by
    have := hcoh.toks t; rw [ht] at this
    cases h0 : Γt !! t
    · rfl
    · rw [h0] at this; cases this
  imod gAuth_insert _ _ _ t ⟨c, 1, xs.map Prod.fst, shMeta m sz.toNat, xs.map Prod.snd⟩ hΓt $$ HAt
    with ⟨HAt, Ht⟩
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells
  isplitl [Htok Hm Hbs]
  · isplitr
    · ipureintro; rw [hlo] at hcoh1; exact ⟨hwf1, hcoh1⟩
    rw [show tokRes (gooseOsGS (L := L)) { st with inflight := <[t := c]> st.inflight }
        (<[t := ⟨c, 1, xs.map Prod.fst, shMeta m sz.toNat, xs.map Prod.snd⟩]> Γt) =
      tokRes gooseOsGS st (<[t := ⟨c, 1, xs.map Prod.fst, shMeta m sz.toNat, xs.map Prod.snd⟩]> Γt)
      from rfl]
    unfold tokRes
    iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
        bytesG gooseOsGS ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
      hΓt).2
    simp only [List.map_map]
    rw [hcp, hlo, show List.map ((fun x => (x, false)) ∘ Prod.fst) xs =
      List.map (fun x => (x.fst, false)) xs from rfl]
    iframe
  iapply wp_value'
  iapply HΦ $$ Hfd
  unfold shTok osTok
  rw [← hc]; iexact Ht

/-- The second step of a shrinking `ftruncate` of an unmapped file: on success the file is shrunk
and its `OsMeta` given back (`m.shrunk sz`; the bytes past `sz` are gone); on failure the file
is shrunk so, or unchanged: then its `OsMeta` as the first step left it (`shMeta m sz`) and the
bytes past `sz` come back, with their values (not clean), so that the caller may retry. -/
theorem wp_osFtruncateShrinkFinish (t : Nat) (p : GoString) (sz : Nat) (m : OsMeta)
    (xs : List (w8 × Bool)) (hE : ↑osN ⊆ E) (hshr : sz ≤ m.size) (hmaps : m.maps = ∅)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ shTok (L := L) t p sz m xs -∗
      (∀ e : w64, ((⌜e = 0⌝ ∗ osMeta (L := L) p (DFrac.own 1) (some (m.shrunk sz))) ∨
          (⌜e ≠ 0⌝ ∗ (osMeta (L := L) p (DFrac.own 1) (some (m.shrunk sz)) ∨
            ∃ ys : List (w8 × Bool), ⌜ys.map Prod.fst = xs.map Prod.fst⌝ ∗
              osMeta (L := L) p (DFrac.own 1) (some (shMeta m sz)) ∗
              osBytes (L := L) p sz (DFrac.own 1) ys))) -∗
        Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "FtruncateFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_os_step "FtruncateFinish" _ Φ (by simp [val.isPanic]) hE (by simp [OldOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold shTok osTok
  generalize hti0 : (⟨⟨p, .truncate sz⟩, 1, xs.map Prod.fst, shMeta m sz, xs.map Prod.snd⟩ :
    TokInfo) = ti
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  have hct : st.inflight !! t = some ti.c := by
    have := hcoh.toks t; rw [Hti] at this; exact this.symm
  have hc : ti.c = ⟨p, .truncate sz⟩ := by rw [← hti0]
  obtain ⟨f, hf, hsv⟩ := hcoh.tok_saved t ti Hti
  rw [hc] at hf; simp only at hf
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
        bytesG gooseOsGS ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
      Hti).1 $$ Htok with ⟨⟨Hm, Hbs⟩, Htok⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hcp : ti.c.path = p := by rw [hc]
  rw [hcp] at Hml
  obtain ⟨f1, hf1, hmo⟩ := coh_meta hcoh Hml
  rw [hf] at hf1; cases hf1
  have hti_om : ti.om = shMeta m sz := by rw [← hti0]
  have hmsz : m.size = f.cur.length := by
    have := hmo.size; rw [hti_om] at this; simpa [shMeta] using this
  have hszf := hwf.sizes p f hf
  have hmaps' : ti.om.maps = ∅ := by rw [hti_om]; exact hmaps
  have hnomap := noMap_of_meta hmo hmaps'
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  have hfin := fun n (h1 : sz ≤ n) (h2 : n ≤ f.cur.length) =>
    shFinish_coh (n := n) hwf hcoh Hti hc hf Hml h1 h2
  have hst1 : ({ st with inflight := GMap.delete t st.inflight } : OsState).setFile p
      (f.truncate f.cur.length) = { st with inflight := GMap.delete t st.inflight } := by
    rw [truncate_self f hszf.1 hszf.2]
    exact setFile_self (st := { st with inflight := GMap.delete t st.inflight }) hf
  imodintro
  isplitr
  · ipureintro
    obtain ⟨-, -, -, hwfk, -⟩ := hfin sz (Nat.le_refl _) (by omega)
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
  obtain ⟨n, e, hn1, hn2, hst', he', hne⟩ : ∃ (n : Nat) (e : w64), sz ≤ n ∧ n ≤ f.cur.length ∧
      st' = ({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile p
        (f.truncate n) ∧ e' = Val (#e) ∧
      ((e = 0 ∧ n = sz) ∨ (e ≠ 0 ∧ (n = sz ∨ n = f.cur.length))) := by
    rcases hrest with ⟨h1, h2⟩ | ⟨e, he, h2, h1 | h1⟩
    · exact ⟨sz, 0, Nat.le_refl _, by omega, h1, h2, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨f.cur.length, e, by omega, Nat.le_refl _, by rw [h1, hst1], h2, .inr ⟨he, .inr rfl⟩⟩
    · exact ⟨sz, e, Nat.le_refl _, by omega, h1, h2, .inr ⟨he, .inl rfl⟩⟩
  subst hst' he'
  obtain ⟨hsizes, hIk, hIp, hwfk, hcohk⟩ := hfin n hn1 hn2
  -- the meta
  have eqm : gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm ti.c.path (DFrac.own ti.q) (some ti.om) ⊢
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p (DFrac.own 1) (some ti.om) := by
    rw [hcp, show ti.q = 1 by rw [← hti0]]
  ihave Hm := eqm $$ Hm
  imod meta_replace _ (q := 1) (om := { ti.om with size := n }) (fun h1 => absurd rfl h1)
    $$ [HAm Hm] with ⟨HAm, Hm⟩
  · iframe
  -- the bytes past `n` go
  have hsvl : ti.saved.length = f.cur.length - sz := by
    rw [hsv]; simp [affRange, affLo, affHi, hc, size_of_file hf]; omega
  have hlo : affLo st ti.c = sz := by
    rw [hc]; simp [affLo, size_of_file hf]; omega
  ihave Hbs := (show bytesG (gooseOsGS (L := L)) ti.c.path (affLo st ti.c) (DFrac.own 1)
      (ti.saved.map (·, false)) ⊢ bytesG (gooseOsGS (L := L)) p sz (DFrac.own 1)
      (ti.saved.map (·, false)) by rw [hcp, hlo]) $$ Hbs
  have hdl : (ti.saved.map (·, false)).length = f.cur.length - sz := by
    rw [List.length_map, hsvl]
  have hdel : gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb ∗
      bytesG (gooseOsGS (L := L)) p sz (DFrac.own 1) (ti.saved.map (·, false)) ⊢ |==>
      (gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (deleteBytes p n (f.cur.length - n) Γb) ∗
        (⌜n = f.cur.length⌝ -∗
          bytesG (gooseOsGS (L := L)) p sz (DFrac.own 1) (ti.saved.map (·, false)))) := by
    by_cases hnl : n = f.cur.length
    · rw [hnl, Nat.sub_self, show deleteBytes p f.cur.length 0 Γb = Γb from rfl]
      iintro ⟨H, Hb⟩; imodintro; iframe H; iintro -; iexact Hb
    · have hn : n = sz := by
        rcases hne with ⟨-, hn⟩ | ⟨-, hn | hn⟩
        · exact hn
        · exact hn
        · exact absurd hn hnl
      rw [hn, ← hdl]
      iintro H
      imod bytesG_delete _ p sz _ Γb $$ H with HA
      imodintro
      iframe HA
      iintro %h
      exact False.elim (hnl (hn.trans h))
  imod hdel $$ [HAb Hbs] with ⟨HAb, Hbr⟩
  · iframe
  -- the token
  imod gAuth_delete _ _ _ _ _ $$ HAt Ht with HAt
  -- the cells: the file is unmapped, so none changes
  have hcv : cellView (({ st with inflight := GMap.delete t' st.inflight } : OsState).setFile p
      (f.truncate n)) = cellView st :=
    cellView_noMap hwf hwfk rfl p hnomap (fun q hq => file_setFile_ne _ _ (Ne.symm hq))
      (fun q i hq => by rw [hIk]; exact ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩)
  imod cells_same hwf hwfk Hr Hfr rfl hcv $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells
  isplitl [Htok]
  · isplitr
    · ipureintro; exact ⟨hwfk, hcohk⟩
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
  rcases hne with ⟨rfl, hn⟩ | ⟨he, hn⟩
  · iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    unfold osMeta
    rw [show (some { ti.om with size := n } : Option OsMeta) = some (m.shrunk sz) by
      rw [hti_om, hn]; rfl]
    iexact Hm
  · rcases hn with hn | hn
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact he
      ileft
      unfold osMeta
      rw [show (some { ti.om with size := n } : Option OsMeta) = some (m.shrunk sz) by
        rw [hti_om, hn]; rfl]
      iexact Hm
    · ihave Hb := Hbr $$ %hn
      have hsv' : ti.saved = xs.map Prod.fst := by rw [← hti0]
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact he
      iright
      iexists (ti.saved.map (·, false))
      isplitr
      · ipureintro; rw [hsv', List.map_map, List.map_map]; rfl
      unfold osMeta osBytes
      rw [show (some { ti.om with size := n } : Option OsMeta) = some (shMeta m sz) by
        rw [hti_om, hn, ← hmsz]; rfl]
      iframe

end specs

end Perennial
