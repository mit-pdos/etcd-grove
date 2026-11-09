/-
WP specs of the Linux file extension's `ftruncate` (`FtruncateStart`, `FtruncateFinish`), for a
truncate that shrinks the file (to `sz ≤` its size), of a file that no mapping maps. The client
holds the file's `OsMeta` whole, so no other change is in flight, and the bytes past the new size
whole: the first step takes them (the change affects every byte from `sz` on), and the second
step, on success, removes them. On failure the client gets nothing back.
-/
module

public import GooseLang.Ext.Fs.Truncate

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-- The `OsMeta` of a file while a shrink to `sz` is in flight: a crash may leave it as small as
`sz`. -/
def shMeta (m : OsMeta) (sz : Nat) : OsMeta := { m with lo := min m.lo sz }

/-- The `OsMeta` of a file after a truncate to `sz ≤ m.size`. -/
def OsMeta.shrunk (m : OsMeta) (sz : Nat) : OsMeta :=
  { m with size := sz, lo := min m.lo sz, vk := none }

theorem OsMeta.shrunk_size (m : OsMeta) (sz : Nat) : (m.shrunk sz).size = sz := rfl
theorem OsMeta.shrunk_maps (m : OsMeta) (sz : Nat) : (m.shrunk sz).maps = m.maps := rfl

theorem OsMeta.shrunk_shMeta (m : OsMeta) (sz : Nat) : (shMeta m sz).shrunk sz = m.shrunk sz := by
  simp only [OsMeta.shrunk, shMeta, Nat.min_assoc, Nat.min_self]

theorem OsMeta.shrunk_shrunk (m : OsMeta) (sz : Nat) : (m.shrunk sz).shrunk sz = m.shrunk sz := by
  simp only [OsMeta.shrunk, Nat.min_assoc, Nat.min_self]

/-! ## The file after a shrinking truncate -/

section shFile
variable (f : OsFile) (n : Nat)

theorem truncate_old_le (i : Nat) (hi : i < n) (hn : n ≤ f.size) :
    (f.truncate n).contents[i]? = f.contents[i]? := by
  rw [truncate_getElem?, contents_getElem?, if_pos hi, if_pos (by omega), if_pos (by omega)]

/-- Shrinking a file keeps clean the clean bytes it keeps. -/
theorem truncate_clean_le (hn : n ≤ f.size) (i : Nat) (hi : i < n) (h : CleanPhys f i) :
    CleanPhys (f.truncate n) i := by
  unfold OsFile.truncate
  apply change_clean f _ _ _ i (by omega) (by rw [resized_length]; omega) _ h
  rw [List.getD_eq_getElem?_getD, resized_getElem?, if_pos hi, if_pos (by omega)]; rfl

theorem truncate_sizeLo_le (hn : n ≤ f.size) : (f.truncate n).sizeLo = min f.sizeLo n := by
  simp only [OsFile.truncate, OsFile.change, resized_length]

theorem truncate_sizeHi_le (h : f.size ≤ f.sizeHi) (hn : n ≤ f.size) :
    (f.truncate n).sizeHi = f.sizeHi := by
  simp only [OsFile.truncate, OsFile.change, resized_length]; omega

end shFile

/-- What the second step of a shrinking truncate to `sz` may leave of the file `f`: `f` cut to
`sz` (`f.truncate sz`), or `f` itself. The bytes it keeps are kept, clean ones clean. -/
structure ShrunkFile (f f' : OsFile) (sz : Nat) : Prop where
  either : f' = f.truncate sz ∨ f' = f
  size_ge : sz ≤ f'.size
  size_le : f'.size ≤ f.size
  old : ∀ i, i < f'.size → f'.contents[i]? = f.contents[i]?
  clean : ∀ i, i < f'.size → CleanPhys f i → CleanPhys f' i
  vers : ∀ k, (f.secs k).vers ≠ [] → (f'.secs k).vers ≠ []
  head : ∀ k v, (f.secs k).vers.head? = some v → (f'.secs k).vers.head? = some v
  ok : ∀ k, (f'.secs k).dirty = false →
    (f'.secs k).vers = (f.secs k).vers ∧ (f'.secs k).dirty = (f.secs k).dirty
  sizeLo : f'.sizeLo = min f.sizeLo f'.size
  sizeHi : f'.sizeHi = f.sizeHi

theorem shrunkFile_truncate {f : OsFile} {sz : Nat} (hsz : f.size ≤ f.sizeHi) (h : sz ≤ f.size) :
    ShrunkFile f (f.truncate sz) sz :=
  ⟨.inl rfl, by rw [truncate_size]; exact Nat.le_refl _, by rw [truncate_size]; exact h,
    fun i hi => truncate_old_le f sz i (by rwa [truncate_size] at hi) h,
    fun i hi => truncate_clean_le f sz h i (by rwa [truncate_size] at hi), truncate_vers f sz,
    truncate_head f sz, truncate_ok f sz, by rw [truncate_sizeLo_le f sz h, truncate_size],
    truncate_sizeHi_le f sz hsz h⟩

theorem shrunkFile_self {f : OsFile} {sz : Nat} (hsz : f.sizeLo ≤ f.size) (h : sz ≤ f.size) :
    ShrunkFile f f sz :=
  ⟨.inr rfl, h, Nat.le_refl _, fun _ _ => rfl, fun _ _ h => h, fun _ h => h, fun _ _ h => h,
    fun _ _ => ⟨rfl, rfl⟩, by omega, rfl⟩

/-! ## The view of the mapped cells, unchanged by a change to an unmapped file -/

section cells
attribute [local instance] Classical.propDecidable

theorem cellView_noMap {st st' : OsState} (hwf : OsWf st) (hwf' : OsWf st')
    (hm : st'.proc.maps = st.proc.maps) (p : Ino)
    (hp : ∀ b mm, st.proc.maps !! b = some mm → mm.ino ≠ p)
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
variable {st : OsState} {Γb : GMap (Ino × Nat) (w8 × Bool)} {Γm : GMap Ino OsMeta}
  {Γf : GMap w64 OsFd} {Γt : GMap Nat TokInfo}

/-- The state and the ghost maps after the second step of a truncate to `sz` that left the file
`f'` (cut to `sz`, or unchanged). -/
theorem shFinish_coh (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) {t : Nat} {ti : TokInfo}
    {p : Ino} {sz : Nat} {f f' : OsFile} (hti : Γt !! t = some ti)
    (hc : ti.c = ⟨p, .truncate sz⟩) (hf : st.file p = some f)
    (Hml : Γm !! p = some ti.om) (hg : ShrunkFile f f' sz) :
    let stn := (st.setProc { st.proc with inflight := GMap.delete t st.proc.inflight } : OsState).setFile p f'
    (∀ t' c', t' ≠ t → st.proc.inflight !! t' = some c' → stn.size c'.ino = st.size c'.ino) ∧
    (∀ q i, InflightAt stn q i ↔ q ≠ p ∧ InflightAt st q i) ∧
    (∀ i, InflightAt st p i ↔ sz ≤ i) ∧
    OsWf stn ∧
    OsCoh stn (deleteBytes p f'.size (f.size - f'.size) Γb)
      (<[p := { ti.om with size := f'.size, vk := none }]>
        Γm) Γf (GMap.delete t Γt) := by
  intro stn
  have hct : st.proc.inflight !! t = some ti.c := by
    have := hcoh.toks t; rw [hti] at this; exact this.symm
  have hcp : ti.c.ino = p := by rw [hc]
  have hq1 : ti.q = 1 := hcoh.tok_q t ti hti (by rw [hc]; trivial)
  have hother : ∀ t' c', t' ≠ t → st.proc.inflight !! t' = some c' → c'.ino ≠ p := by
    intro t' c' hne h'
    have := hcoh.tok_alone t ti hti hq1 t' c' hne h'; rwa [hcp] at this
  have hsz := size_of_file hf
  obtain ⟨f1, hf1, hmo⟩ := hcoh.meta_some p ti.om Hml
  have hf1' : st.file p = some f1 := hf1
  rw [hf] at hf1'; cases hf1'
  have hszf := hwf.sizes p f hf
  have htg := hmo.targets t ti.c hct hcp
  rw [hc] at htg; simp only [OsChange.target] at htg
  have hn1 := hg.size_ge
  have hn2 := hg.size_le
  have hsizes : ∀ t' c', t' ≠ t → st.proc.inflight !! t' = some c' →
      stn.size c'.ino = st.size c'.ino := by
    intro t' c' hne h'
    show ((st.setProc { st.proc with inflight := GMap.delete t st.proc.inflight } : OsState).setFile p _).size _ = _
    rw [size_setFile]; split
    · rename_i hp; exact absurd (by rw [hp]) (hother t' c' hne h')
    · rfl
  have hdel : ∀ t' c', stn.proc.inflight !! t' = some c' → st.proc.inflight !! t' = some c' ∧ t' ≠ t := by
    intro t' c' h1
    change (GMap.delete t st.proc.inflight) !! t' = some c' at h1
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
      · change (GMap.delete t st.proc.inflight) !! t' = some c'
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
  have hfk : stn.file p = some f' := file_setFile_eq _ _ _
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
        rw [hg.sizeLo, hg.sizeHi]; omega
      · rw [hfq q hq] at h1; exact hwf.sizes q f1 h1
    · by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        exact hg.vers i (hwf.vers q f i hf)
      · rw [hfq q hq] at h1; exact hwf.vers q f1 i h1
  refine ⟨hsizes, hIk, hIp, hwfk, ?_⟩
  have hfp : st.fs.files !! p = some f := hf
  refine ⟨fun q => ?_, fun q m' hm => ?_, fun q i x hx => ?_, fun q f1 i h1 hi => ?_,
    hcoh.fds, fun t' => ?_, fun t' ti' h => ?_, fun t' ti' h hq1 => ?_, fun t' ti' h => ?_,
    fun t' ti' h => ?_⟩
  · rw [GMap.lookup_insert_eq_iff]
    show _ ↔ ((st.setProc { st.proc with inflight := GMap.delete t st.proc.inflight } : OsState).setFile p _).fs.files !! q = none
    rw [files_setFile]; split
    · simp
    · exact hcoh.meta_dom q
  · have htg' : ∀ c', (∃ t', stn.proc.inflight !! t' = some c') → c'.target stn = c'.target st := by
      rintro c' ⟨t', h'⟩
      obtain ⟨h1, n1⟩ := hdel t' c' h'
      exact target_congr1 c' (hsizes t' c' n1 h1)
    rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · rename_i hpq; subst hpq; cases hm
      refine ⟨f', hfk, ⟨rfl,
        by show ti.om.lo ≤ _; rw [hg.sizeLo]; have := hmo.lo; have := htg.1; omega,
        by show _ ≤ ti.om.hi; rw [hg.sizeHi]; exact hmo.hi,
        fun hok k hd => by
          rw [(hg.ok k hd).1]
          exact hmo.ok hok k (by rw [← (hg.ok k hd).2]; exact hd),
        hmo.maps, fun t' c' h1 h2 => ?_, fun b d0 h v hv => ?_,
          (fun _ h => by cases h), fun z hz b hzb v hv => ?_⟩⟩
      · obtain ⟨h1, n1⟩ := hdel t' c' h1
        exact absurd h2 (hother t' c' n1 h1)
      · obtain ⟨w, hw⟩ : ∃ w, (f.secs (b / 512)).vers.head? = some w := by
          cases hh : (f.secs (b / 512)).vers with
          | nil => exact absurd hh (hwf.vers p f _ hf)
          | cons w _ => exact ⟨w, rfl⟩
        rw [hg.head _ w hw] at hv
        exact (Option.some.inj hv) ▸ hmo.dur b d0 h w hw
      · obtain ⟨w, hw⟩ : ∃ w, (f.secs (b / 512)).vers.head? = some w := by
          cases hh : (f.secs (b / 512)).vers with
          | nil => exact absurd hh (hwf.vers p f _ hf)
          | cons w _ => exact ⟨w, rfl⟩
        rw [hg.head _ w hw] at hv
        exact (Option.some.inj hv) ▸ hmo.dz z hz b hzb w hw
    · rename_i hpq
      obtain ⟨f1, h1, hm1⟩ := hcoh.meta_some q m' hm
      refine ⟨f1, ?_, ⟨hm1.size, hm1.lo, hm1.hi, hm1.ok, hm1.maps, fun t' c' h1 h2 => ?_,
        hm1.dur, hm1.vk, hm1.dz⟩⟩
      · show ((st.setProc { st.proc with inflight := GMap.delete t st.proc.inflight } : OsState).setFile p _).fs.files !! q = _
        rw [files_setFile, if_neg hpq]; exact h1
      · rw [htg' c' ⟨t', h1⟩]; exact hm1.targets t' c' (hdel t' c' h1).1 h2
  · rw [lookup_deleteBytes] at hx
    split at hx
    · cases hx
    · rename_i hr
      obtain ⟨f1, h1, hb, hcl⟩ := hcoh.bytes q i x hx
      by_cases hq : q = p
      · subst hq; rw [hf] at h1; cases h1
        have hil : i < f.size := by rw [← contents_length]; exact (List.getElem?_eq_some_iff.1 hb).1
        have hin : i < f'.size := by
          apply Classical.byContradiction; intro h0; exact hr ⟨rfl, by omega, by omega⟩
        refine ⟨_, hfk, by rw [hg.old i hin]; exact hb, fun hx2 => ?_⟩
        obtain ⟨c1, -⟩ := hcl hx2
        exact ⟨hg.clean i hin c1, fun h => ((hIk _ _).1 h).1 rfl⟩
      · refine ⟨f1, by rw [hfq q hq]; exact h1, hb, fun hx2 => ?_⟩
        obtain ⟨c1, c2⟩ := hcl hx2
        exact ⟨c1, fun h => c2 ((hIk _ _).1 h).2⟩
  · rw [lookup_deleteBytes]
    split
    · rename_i hr
      by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1; omega
      · exact absurd hr.1 hq
    · by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        exact hcoh.bytes_full q f i hf (by omega)
      · rw [hfq q hq] at h1; exact hcoh.bytes_full q f1 i h1 hi
  · show (GMap.delete t Γt !! t').map TokInfo.c = (GMap.delete t st.proc.inflight) !! t'
    rw [GMap.lookup_delete_iff, GMap.lookup_delete_iff]; split
    · rfl
    · exact hcoh.toks t'
  · rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · rename_i hne
      have h' : st.proc.inflight !! t' = some ti'.c := by
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
      have h' : st.proc.inflight !! t' = some ti'.c := by
        have := hcoh.toks t'; rw [h] at this; exact this.symm
      have hne' : t' ≠ t := fun e => hne e.symm
      obtain ⟨f1, h1, hsv1⟩ := hcoh.tok_saved t' ti' h
      have hq : ti'.c.ino ≠ p := hother t' ti'.c hne' h'
      rw [affRange_congr1 ti'.c (hsizes t' ti'.c hne' h')]
      exact ⟨f1, by rw [hfq _ hq]; exact h1, hsv1⟩
  · rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · rename_i hne
      intro j hj
      have h' : st.proc.inflight !! t' = some ti'.c := by
        have := hcoh.toks t'; rw [h] at this; exact this.symm
      have hne' : t' ≠ t := fun e => hne e.symm
      have hs' := hsizes t' ti'.c hne' h'
      obtain ⟨hjl, f1, h1, hc1⟩ := hcoh.tok_clean t' ti' h j hj
      have hq : ti'.c.ino ≠ p := hother t' ti'.c hne' h'
      have hlo1 : affLo stn ti'.c = affLo st ti'.c := by unfold affLo; rw [hs']
      have hhi1 : affHi stn ti'.c = affHi st ti'.c := by unfold affHi; rw [hs']
      rw [hlo1, hhi1]
      exact ⟨hjl, f1, by rw [hfq _ hq]; exact h1, hc1⟩

end shFinish

/-! ## Specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- A shrinking `ftruncate` to `sz` of the file `p` between its two steps: its first step took the
whole of the file's `OsMeta` `m` and the bytes `xs` past `sz`. -/
def shTok (t : Nat) (p : Ino) (sz : Nat) (m : OsMeta) (xs : List (w8 × Bool)) : IProp GF :=
  osTok (L := L) t ⟨⟨p, .truncate sz⟩, 1, xs.map Prod.fst, shMeta m sz, xs.map Prod.snd⟩

/-- No mapping of the state maps a file whose ghost `OsMeta` has no mapping. -/
theorem noMap_of_meta {st : OsState} {p : Ino} {m : OsMeta} {f : OsFile}
    (hmo : MetaOk st p m f) (hmaps : m.maps = ∅) :
    ∀ b mm, st.proc.maps !! b = some mm → mm.ino ≠ p := by
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
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      osBytes (L := L) d.ino sz.toNat (DFrac.own 1) xs -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗ shTok (L := L) t d.ino sz.toNat m xs -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs HΦ
  iapply wp_os_step "FtruncateStart" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta osBytes
  icases bytesG_lookup _ d.ino _ _ xs Γb $$ HAb Hbs with %Hbl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_frac _ $$ Htok Hm with %Hfrac
  icases tokRes_meta_whole _ $$ Htok Hm with %Hwhole
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hsz : st.size d.ino = m.size := by rw [size_of_file hf, hmo.size]
  have hszf := hwf.sizes d.ino f hf
  have hnot := noTok_of_whole hcoh Hwhole
  have hnbusy : ¬ BusyAt st d.ino := by
    rintro ⟨t', c', h1, h2⟩; exact hnot t' c' h1 h2
  have hfree : ∀ i, Affects st ⟨d.ino, .truncate sz.toNat⟩ i → ¬ InflightAt st d.ino i := by
    rintro i - ⟨t', c', h1, h2, -⟩; exact hnot t' c' h1 h2
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  obtain ⟨t0, ht0, hc0⟩ := exists_fresh2 st.proc.inflight st.proc.calls
  imodintro
  isplitr
  · ipureintro
    have hwf0 := osWf_addTok (t := t0) (c := ⟨d.ino, .truncate sz.toNat⟩) hwf ht0 hf hfree
    exact ⟨_, _, _, ⟨fd, sz, t0, d, rfl, hfd, hwr, hsz0, hnbusy, ht0, hc0, rfl, rfl⟩,
      mapsFresh_same rfl, heapRendered_render hwf0 rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', sz', t, d', hv, hfd', -, -, -, ht, -, hst', rfl⟩ := Hst
  injection hv with h1 h3
  cases go.intoVal_inj h1; cases go.intoVal_inj h3
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  subst hst'
  rw [show ∀ c', st.addInflight t c' = (st.setProc { st.proc with inflight := <[t := c']> st.proc.inflight })
    from fun _ => rfl] at Hr Hfr ⊢
  generalize hc : (⟨d.ino, .truncate sz.toNat⟩ : OsChange) = c at hfree Hr Hfr ⊢
  have hcp : c.ino = d.ino := by rw [← hc]
  have hlo : affLo st c = sz.toNat := by rw [← hc]; simp [affLo, hsz]; omega
  have hhi' : affHi st c = m.size := by rw [← hc]; simp [affHi, hsz]
  have hwf1 := osWf_addTok (t := t) (c := c) hwf ht (hcp ▸ hf) (hcp ▸ hfree)
  have hcoh1 := osCoh_addTok (t := t) (q := 1) (m := m) (om := shMeta m sz.toNat)
    (xs := xs) hcoh hcp hf Hml
    ⟨rfl, rfl, rfl, Nat.min_le_left _ _, Nat.le_refl _,
      by rw [← hc]; simp only [OsChange.target, shMeta]; omega,
      by rw [← hc]; simp only [OsChange.target, shMeta]; have := hmo.hi; have := hmo.size
         have := hszf.2; omega, rfl, rfl, rfl⟩
    ht (hcp ▸ hfree) (fun _ => rfl)
    Hfrac (fun _ => hnot) (by rw [hlo, hhi', hxs]) (fun k hk => by rw [hlo]; exact Hbl k hk)
  -- the cells: the file is unmapped, so none changes
  have hcv : cellView (st.setProc { st.proc with inflight := <[t := c]> st.proc.inflight }) = cellView st :=
    cellView_noMap hwf hwf1 rfl d.ino (noMap_of_meta hmo hmaps) (fun _ _ => rfl)
      (fun q i hq => by
        rw [inflightAt_addTok ht]
        exact ⟨fun h => h.resolve_right (fun h2 => hq (hcp ▸ h2.1).symm), .inl⟩)
  imod cells_same hwf hwf1 Hr Hfr rfl hcv $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  -- the ghost maps
  imod meta_replace _ (q := 1) (om := shMeta m sz.toNat) (fun h1 => absurd rfl h1)
    $$ [HAm Hm] with ⟨HAm, Hm⟩
  · iframe
  imod bytesG_update _ d.ino _ xs (xs.map (fun x => (x.1, false))) Γb (by simp) $$ [HAb Hbs]
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
    rw [show tokRes (gooseOsGS (L := L)) (st.setProc { st.proc with inflight := <[t := c]> st.proc.inflight })
        (<[t := ⟨c, 1, xs.map Prod.fst, shMeta m sz.toNat, xs.map Prod.snd⟩]> Γt) =
      tokRes gooseOsGS st (<[t := ⟨c, 1, xs.map Prod.fst, shMeta m sz.toNat, xs.map Prod.snd⟩]> Γt)
      from rfl]
    unfold tokRes
    iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.c.ino (DFrac.own ti.q) ti.om ∗
        bytesG gooseOsGS ti.c.ino (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
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
bytes past `sz` come back, with their values (not clean), so that the caller may retry. Either way
the versions known (`vk`) are forgotten: the last sector may have one more. -/
theorem wp_osFtruncateShrinkFinish (t : Nat) (p : Ino) (sz : Nat) (m : OsMeta)
    (xs : List (w8 × Bool)) (hE : ↑osN ⊆ E) (hshr : sz ≤ m.size) (hmaps : m.maps = ∅)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ shTok (L := L) t p sz m xs -∗
      (∀ e : w64, ((⌜e = 0⌝ ∗ osMeta (L := L) p (DFrac.own 1) (m.shrunk sz)) ∨
          (⌜e ≠ 0⌝ ∗ (osMeta (L := L) p (DFrac.own 1) (m.shrunk sz) ∨
            ∃ ys : List (w8 × Bool), ⌜ys.map Prod.fst = xs.map Prod.fst⌝ ∗
              osMeta (L := L) p (DFrac.own 1)
                { shMeta m sz with vk := none } ∗
              osBytes (L := L) p sz (DFrac.own 1) ys))) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FtruncateFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_os_step "FtruncateFinish" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold shTok osTok
  generalize hti0 : (⟨⟨p, .truncate sz⟩, 1, xs.map Prod.fst, shMeta m sz, xs.map Prod.snd⟩ :
    TokInfo) = ti
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  have hct : st.proc.inflight !! t = some ti.c := by
    have := hcoh.toks t; rw [Hti] at this; exact this.symm
  have hc : ti.c = ⟨p, .truncate sz⟩ := by rw [← hti0]
  obtain ⟨f, hf, hsv⟩ := hcoh.tok_saved t ti Hti
  rw [hc] at hf; simp only at hf
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.c.ino (DFrac.own ti.q) ti.om ∗
        bytesG gooseOsGS ti.c.ino (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
      Hti).1 $$ Htok with ⟨⟨Hm, Hbs⟩, Htok⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hcp : ti.c.ino = p := by rw [hc]
  rw [hcp] at Hml
  obtain ⟨f1, hf1, hmo⟩ := coh_meta hcoh Hml
  rw [hf] at hf1; cases hf1
  have hti_om : ti.om = shMeta m sz := by rw [← hti0]
  have hmsz : m.size = f.size := by
    have := hmo.size; rw [hti_om] at this; simpa [shMeta] using this
  have hszf := hwf.sizes p f hf
  have hmaps' : ti.om.maps = ∅ := by rw [hti_om]; exact hmaps
  have hnomap := noMap_of_meta hmo hmaps'
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  have hfin := fun (f2 : OsFile) (hg : ShrunkFile f f2 sz) =>
    shFinish_coh (f' := f2) hwf hcoh Hti hc hf Hml hg
  have hgT : ShrunkFile f (f.truncate sz) sz := shrunkFile_truncate hszf.2 (by omega)
  imodintro
  isplitr
  · ipureintro
    obtain ⟨-, -, -, hwfk, -⟩ := hfin _ hgT
    exact ⟨_, renderHeap ((st.setProc { st.proc with inflight := GMap.delete t st.proc.inflight } : OsState).setFile p
      (f.truncate sz)) h, _, ⟨t, p, sz, f, rfl, by rw [hct, hc], hf, .inl ⟨rfl, rfl⟩⟩,
      mapsFresh_same rfl, heapRendered_render hwfk rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨t', p', sz', f', hv, hinfl, hf', hrest⟩ := Hst
  have htt : t' = t := by injection hv with hv; exact (extVal_inj hv).symm
  subst htt
  rw [hct, hc] at hinfl; cases hinfl
  rw [hf] at hf'; cases hf'
  obtain ⟨f2, e, hg, hst', he', hne⟩ : ∃ (f2 : OsFile) (e : w64), ShrunkFile f f2 sz ∧
      st' = (st.setProc { st.proc with inflight := GMap.delete t' st.proc.inflight } : OsState).setFile p f2 ∧
      e' = Val (#e) ∧ ((e = 0 ∧ f2 = f.truncate sz) ∨ (e ≠ 0 ∧ (f2 = f.truncate sz ∨ f2 = f))) := by
    rcases hrest with ⟨h1, h2⟩ | ⟨e, he, h2, h1 | h1⟩
    · exact ⟨_, 0, hgT, h1, h2, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨f, e, shrunkFile_self hszf.1 (by omega),
        by rw [h1]; exact (setFile_self (st := st.doneInflight t') hf).symm, h2, .inr ⟨he, .inr rfl⟩⟩
    · exact ⟨_, e, hgT, h1, h2, .inr ⟨he, .inl rfl⟩⟩
  subst hst' he'
  obtain ⟨hsizes, hIk, hIp, hwfk, hcohk⟩ := hfin f2 hg
  generalize hn : f2.size = n at hcohk
  have hn1 : sz ≤ n := hn ▸ hg.size_ge
  have hn2 : n ≤ f.size := hn ▸ hg.size_le
  replace hne : (e = 0 ∧ n = sz) ∨ (e ≠ 0 ∧ (n = sz ∨ n = f.size)) := by
    rcases hne with ⟨h1, rfl⟩ | ⟨h1, rfl | rfl⟩
    · exact .inl ⟨h1, by rw [← hn, truncate_size]⟩
    · exact .inr ⟨h1, .inl (by rw [← hn, truncate_size])⟩
    · exact .inr ⟨h1, .inr hn.symm⟩
  -- the meta
  have eqm : gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm ti.c.ino (DFrac.own ti.q) ti.om ⊢
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p (DFrac.own 1) ti.om := by
    rw [hcp, show ti.q = 1 by rw [← hti0]]
  ihave Hm := eqm $$ Hm
  imod meta_replace _ (q := 1)
    (om := { ti.om with size := n, vk := none })
    (fun h1 => absurd rfl h1)
    $$ [HAm Hm] with ⟨HAm, Hm⟩
  · iframe
  -- the bytes past `n` go
  have hsvl : ti.saved.length = f.size - sz := by
    rw [hsv]; simp [affRange, affLo, affHi, hc, size_of_file hf]; omega
  have hlo : affLo st ti.c = sz := by
    rw [hc]; simp [affLo, size_of_file hf]; omega
  ihave Hbs := (show bytesG (gooseOsGS (L := L)) ti.c.ino (affLo st ti.c) (DFrac.own 1)
      (ti.saved.map (·, false)) ⊢ bytesG (gooseOsGS (L := L)) p sz (DFrac.own 1)
      (ti.saved.map (·, false)) by rw [hcp, hlo]) $$ Hbs
  have hdl : (ti.saved.map (·, false)).length = f.size - sz := by
    rw [List.length_map, hsvl]
  have hdel : gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb ∗
      bytesG (gooseOsGS (L := L)) p sz (DFrac.own 1) (ti.saved.map (·, false)) ⊢ |==>
      (gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (deleteBytes p n (f.size - n) Γb) ∗
        (⌜n = f.size⌝ -∗
          bytesG (gooseOsGS (L := L)) p sz (DFrac.own 1) (ti.saved.map (·, false)))) := by
    by_cases hnl : n = f.size
    · rw [hnl, Nat.sub_self, show deleteBytes p f.size 0 Γb = Γb from rfl]
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
  have hcv : cellView ((st.setProc { st.proc with inflight := GMap.delete t' st.proc.inflight } : OsState).setFile p
      f2) = cellView st :=
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
      (st' := (st.setProc { st.proc with inflight := GMap.delete t' st.proc.inflight } : OsState).setFile p
        f2) (Γt := GMap.delete t' Γt) (fun t2 ti2 h2 => by
      rw [GMap.lookup_delete_iff] at h2; split at h2
      · cases h2
      · rename_i hne
        have h2' : st.proc.inflight !! t2 = some ti2.c := by
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
    rw [show ({ ti.om with size := n, vk := none } : OsMeta) =
        (m.shrunk sz) by
      rw [hti_om, hn]; rfl]
    iexact Hm
  · rcases hn with hn | hn
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact he
      ileft
      unfold osMeta
      rw [show ({ ti.om with size := n, vk := none } : OsMeta) =
        (m.shrunk sz) by
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
      rw [show ({ ti.om with size := n, vk := none } : OsMeta) =
          { shMeta m sz with vk := none } by
        rw [hti_om, hn, ← hmsz]; rfl]
      iframe

end specs

end Fs
end Perennial
