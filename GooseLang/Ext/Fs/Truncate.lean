/-
WP specs of the Linux file extension's `ftruncate` (`FtruncateStart`, `FtruncateFinish`), for a
truncate that grows the file (or keeps its size): it takes no byte of the file, and gives it the
new bytes, whatever the sectors hold past the old size (zeros, unless a crash left other bytes
there: F3, `OsFile.resized`). The client holds the file's `OsMeta` whole, so no other change is in flight.
While it is in flight, a truncate affects every byte from the size on, so its first step takes
the client's halves of every mapped cell past the size (up to `hi`, where every mapping ends),
and its second step gives them back.
-/
module

public import GooseLang.Ext.Fs.Write

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-- The `OsMeta` of a file while a truncate to `sz` is in flight: the size may become `sz`. -/
def ftMeta (m : OsMeta) (sz : Nat) : OsMeta := { m with hi := max m.hi sz }

/-- The `OsMeta` of a file after a truncate to `sz ≥ m.size`: which sectors have how many versions is
not known any more (ext4 may grow it in chunks, each a change of the last sector). -/
def OsMeta.grown (m : OsMeta) (sz : Nat) : OsMeta :=
  { m with size := sz, hi := max m.hi sz, vk := none }

/-- The `OsMeta` of a file after a failed truncate to `sz` that may have left it unchanged: the size
bound widened (`ftMeta`), the versions known forgotten. -/
def ftFail (m : OsMeta) (sz : Nat) : OsMeta := { ftMeta m sz with vk := none }

theorem ftFail_size (m : OsMeta) (sz : Nat) : (ftFail m sz).size = m.size := rfl
theorem ftFail_maps (m : OsMeta) (sz : Nat) : (ftFail m sz).maps = m.maps := rfl

theorem ftFail_grown (m : OsMeta) (sz : Nat) : (ftFail m sz).grown sz = m.grown sz := by
  cases m; simp only [ftFail, ftMeta, OsMeta.grown, OsMeta.mk.injEq, _root_.and_true,
    _root_.true_and]; omega

theorem ftFail_ftFail (m : OsMeta) (sz : Nat) : ftFail (ftFail m sz) sz = ftFail m sz := by
  cases m; simp only [ftFail, ftMeta, OsMeta.mk.injEq, _root_.and_true, _root_.true_and]; omega

theorem ftFail_of_grown (m : OsMeta) (sz : Nat) : ftFail (m.grown sz) sz = m.grown sz := by
  cases m; simp only [ftFail, ftMeta, OsMeta.grown, OsMeta.mk.injEq, _root_.and_true,
    _root_.true_and]; omega

/-- Every mapping of `M` ends at or before `hi`. -/
def MapsBelow (M : GMap Loc Nat) (hi : Nat) : Prop := ∀ b len, M !! b = some len → len ≤ hi

/-- The value of a mapped cell showing the byte `b`. -/
abbrev byteCell [GooseExts] (b : w8) : val := toCellVal (some b)

/-! ## The file after a growing truncate -/

section ftFile
variable (f : OsFile) (n : Nat)

theorem truncate_size : (f.truncate n).size = n := by
  simp only [OsFile.truncate, change_size, resized_length]

theorem truncate_contents : (f.truncate n).contents = f.resized n := by
  apply change_contents
  intro b hb _
  rw [resized_length] at hb
  rw [List.getD_eq_getElem?_getD, resized_getElem?, if_pos hb]; rfl

theorem truncate_getElem? (i : Nat) :
    (f.truncate n).contents[i]? = if i < n then some (f.rawAt i) else none := by
  rw [truncate_contents, resized_getElem?]

/-- A grown file keeps its old bytes. -/
theorem truncate_old (hn : f.size ≤ n) (i : Nat) (hi : i < f.size) :
    (f.truncate n).contents[i]? = f.contents[i]? := by
  rw [truncate_getElem?, contents_getElem?, if_pos (by omega), if_pos hi]

theorem truncate_sizeLo (hsz : f.sizeLo ≤ f.size) (hn : f.size ≤ n) :
    (f.truncate n).sizeLo = f.sizeLo := by
  simp only [OsFile.truncate, OsFile.change, resized_length]; omega

theorem truncate_sizeHi : (f.truncate n).sizeHi = max f.sizeHi n := by
  simp only [OsFile.truncate, OsFile.change, resized_length]

/-- Growing a file keeps its old clean bytes clean. -/
theorem truncate_clean (hn : f.size ≤ n) (hsz : f.sizeLo ≤ f.size) (i : Nat) (h : CleanPhys f i) :
    CleanPhys (f.truncate n) i := by
  have hi : i < f.size := by have := h.1; omega
  unfold OsFile.truncate
  apply change_clean f _ _ _ i (by omega) (by rw [resized_length]; omega) _ h
  rw [List.getD_eq_getElem?_getD, resized_getElem?, if_pos (by omega)]; rfl

theorem truncate_vers (k : Nat) (h : (f.secs k).vers ≠ []) : ((f.truncate n).secs k).vers ≠ [] :=
  change_vers _ _ _ _ k h

/-- A truncate keeps the oldest version of every sector. -/
theorem truncate_head (k : Nat) (v : SecBytes) (h : (f.secs k).vers.head? = some v) :
    ((f.truncate n).secs k).vers.head? = some v := by
  simp only [OsFile.truncate, OsFile.change]; split
  · rw [List.head?_append, h]; rfl
  · exact h

/-- A truncate leaves every sector it does not make dirty as it was. -/
theorem truncate_ok (k : Nat) (h : ((f.truncate n).secs k).dirty = false) :
    (f.truncate n).secs k = f.secs k := by
  simp only [OsFile.truncate, OsFile.change] at h ⊢
  by_cases hs : secHits (min f.size n) (max f.size n) k = true
  · rw [if_pos hs] at h; cases h
  · rw [if_neg hs]

end ftFile

section ftFinish
variable {st : OsState} {Γb : GMap (Ino × Nat) (w8 × Bool)} {Γm : GMap Ino OsMeta}
  {Γf : GMap w64 OsFd} {Γt : GMap Nat TokInfo}

/-- What the second step of a growing truncate may leave of the file `f`: `f` grown to `n ≤ sz`
(`f.truncate n`), or `f` itself. Its old bytes are kept, clean ones clean; the bytes from the old
size on are what the sectors hold. -/
structure GrownFile (f f' : OsFile) (sz : Nat) : Prop where
  size_ge : f.size ≤ f'.size
  size_le : f'.size ≤ sz
  old : ∀ i, i < f.size → f'.contents[i]? = f.contents[i]?
  clean : ∀ i, CleanPhys f i → CleanPhys f' i
  vers : ∀ k, (f.secs k).vers ≠ [] → (f'.secs k).vers ≠ []
  head : ∀ k v, (f.secs k).vers.head? = some v → (f'.secs k).vers.head? = some v
  ok : ∀ k, (f'.secs k).dirty = false → f'.secs k = f.secs k
  sizeLo : f'.sizeLo = f.sizeLo
  sizeHi : f'.sizeHi = max f.sizeHi f'.size
  zero : ZeroPast f → ZeroPast f'

theorem grownFile_truncate {f : OsFile} {n sz : Nat} (hsz : f.sizeLo ≤ f.size) (h1 : f.size ≤ n)
    (h2 : n ≤ sz) : GrownFile f (f.truncate n) sz :=
  ⟨by rw [truncate_size]; exact h1, by rw [truncate_size]; exact h2, truncate_old f n h1,
    truncate_clean f n h1 hsz, truncate_vers f n, truncate_head f n, truncate_ok f n,
    truncate_sizeLo f n hsz h1, by rw [truncate_sizeHi, truncate_size], zero_truncate n⟩

theorem grownFile_self {f : OsFile} {sz : Nat} (hsz : f.size ≤ f.sizeHi) (h : f.size ≤ sz) :
    GrownFile f f sz :=
  ⟨Nat.le_refl _, h, fun _ _ => rfl, fun _ h => h, fun _ h => h, fun _ _ h => h, fun _ _ => rfl,
    rfl, by omega, id⟩

/-- The ghost bytes of a grown file `f'` from the old size `lo` on: its bytes there, not clean. -/
def grownBytes (f' : OsFile) (lo : Nat) : List (w8 × Bool) := (f'.contents.drop lo).map (·, false)

theorem grownBytes_length (f' : OsFile) (lo : Nat) : (grownBytes f' lo).length = f'.size - lo := by
  simp [grownBytes, contents_length]

/-- The state and the ghost maps after the second step of a truncate that left the file `f'`. -/
theorem ftFinish_coh (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) {t : Nat} {ti : TokInfo}
    {p : Ino} {sz : Nat} {f f' : OsFile} (hti : Γt !! t = some ti)
    (hc : ti.c = ⟨p, .truncate sz⟩) (hf : st.file p = some f)
    (Hml : Γm !! p = some ti.om) (hg : GrownFile f f' sz) :
    let stn := (st.setProc { st.proc with inflight := GMap.delete t st.proc.inflight } : OsState).setFile p f'
    (∀ t' c', t' ≠ t → st.proc.inflight !! t' = some c' → stn.size c'.ino = st.size c'.ino) ∧
    (∀ q i, InflightAt stn q i ↔ q ≠ p ∧ InflightAt st q i) ∧
    (∀ i, InflightAt st p i ↔ f.size ≤ i) ∧
    OsWf stn ∧
    OsCoh stn (insertBytes p f.size (grownBytes f' f.size) Γb)
      (<[p := { ti.om with size := f'.size, vk := none }]> Γm) Γf (GMap.delete t Γt) := by
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
  have hIp : ∀ i, InflightAt st p i ↔ f.size ≤ i := by
    intro i
    constructor
    · rintro ⟨t', c', h1, h2, h3⟩
      by_cases he : t' = t
      · subst he; rw [hct] at h1; cases h1
        rw [hc] at h3; simp only [Affects, hsz] at h3
        have := hg.size_le; have := hg.size_ge; omega
      · exact absurd h2 (hother t' c' he h1)
    · intro hi
      exact ⟨t, ti.c, hct, hcp, by
        rw [hc]; simp only [Affects, hsz]; have := hg.size_le; have := hg.size_ge; omega⟩
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
        rw [hg.sizeLo, hg.sizeHi]; have := hg.size_ge; omega
      · rw [hfq q hq] at h1; exact hwf.sizes q f1 h1
    · by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        exact hg.vers i (hwf.vers q f i hf)
      · rw [hfq q hq] at h1; exact hwf.vers q f1 i h1
  refine ⟨hsizes, hIk, hIp, hwfk, ?_⟩
  have hfp : st.fs.files !! p = some f := hf
  have hgl := grownBytes_length f' f.size
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
      refine ⟨f', hfk, ⟨rfl, by rw [hg.sizeLo]; exact hmo.lo,
        by rw [hg.sizeHi]; have := hmo.hi; have := hg.size_le; dsimp only; omega,
        fun hok k hd => by
          rw [hg.ok k hd]
          exact hmo.ok hok k (by rw [← hg.ok k hd]; exact hd),
        hmo.maps, fun t' c' h1 h2 => ?_, fun b d0 h v hv => ?_,
        fun hz => hg.zero (hmo.zero hz), (fun _ h => by cases h), fun z hz b hzb v hv => ?_⟩⟩
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
        hm1.dur, hm1.zero, hm1.vk, hm1.dz⟩⟩
      · show ((st.setProc { st.proc with inflight := GMap.delete t st.proc.inflight } : OsState).setFile p _).fs.files !! q = _
        rw [files_setFile, if_neg hpq]; exact h1
      · rw [htg' c' ⟨t', h1⟩]; exact hm1.targets t' c' (hdel t' c' h1).1 h2
  · rw [lookup_insertBytes] at hx
    split at hx
    · rename_i hr
      obtain ⟨rfl, h1, h2⟩ := hr
      rw [hgl] at h2
      simp only [grownBytes, List.getElem?_map, List.getElem?_drop,
        show f.size + (i - f.size) = i by omega] at hx
      cases hx' : f'.contents[i]? with
      | none => rw [hx'] at hx; cases hx
      | some y =>
        rw [hx'] at hx; cases hx
        exact ⟨_, hfk, hx', fun h => by cases h⟩
    · rename_i hr
      obtain ⟨f1, h1, hb, hcl⟩ := hcoh.bytes q i x hx
      by_cases hq : q = p
      · subst hq; rw [hf] at h1; cases h1
        have hil : i < f.size := by rw [← contents_length]; exact (List.getElem?_eq_some_iff.1 hb).1
        refine ⟨_, hfk, by rw [hg.old i hil]; exact hb, fun hx2 => ?_⟩
        obtain ⟨c1, -⟩ := hcl hx2
        exact ⟨hg.clean i c1, fun h => ((hIk _ _).1 h).1 rfl⟩
      · refine ⟨f1, by rw [hfq q hq]; exact h1, hb, fun hx2 => ?_⟩
        obtain ⟨c1, c2⟩ := hcl hx2
        exact ⟨c1, fun h => c2 ((hIk _ _).1 h).2⟩
  · rw [lookup_insertBytes]
    split
    · rename_i hr; rw [List.getElem?_eq_getElem (by omega)]; rfl
    · rename_i hr
      by_cases hq : q = p
      · subst hq; rw [hfk] at h1; cases h1
        simp only [hgl, _root_.true_and, not_and, Nat.not_lt] at hr
        exact hcoh.bytes_full q f i hf (by
          apply Classical.byContradiction; intro h0; have := hr (by omega); omega)
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

end ftFinish

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- An `ftruncate` to `sz` of the file `p` between its two steps: its first step took the whole
of the file's `OsMeta` `m`. -/
def ftTok (t : Nat) (p : Ino) (sz : Nat) (m : OsMeta) : IProp GF :=
  osTok (L := L) t ⟨⟨p, .truncate sz⟩, 1, [], ftMeta m sz, []⟩

/-- The file `p`, of `OsMeta` `m`, grown to `sz ≥ m.size`: the whole `OsMeta` (`m.grown sz`), the
new bytes `zs`, not clean, whole, and the client's halves of the cells of every mapping over
`[m.size, sz)`, showing them, and over `[sz, hi)`. The new bytes are what the sectors hold past
the old size: zeros if the file's `OsMeta` says so (`zero`: a file made in this generation), else
whatever a crash left there (F3, `OsFile.resized`). -/
def osGrown (p : Ino) (m : OsMeta) (sz hi : Nat) : IProp GF :=
  iprop(∃ zs : List w8, ⌜zs.length = sz - m.size ∧
      (m.zero = true → zs = List.replicate (sz - m.size) 0)⌝ ∗ osMeta (L := L) p (DFrac.own 1) (m.grown sz) ∗
    osBytes (L := L) p m.size (DFrac.own 1) (zs.map (·, false)) ∗
    mcells m.maps m.size sz (fun i => byteCell (zs.getD (i - m.size) 0)) ∗ mcellsAny m.maps sz hi)

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
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      mcellsAny m.maps m.size hi -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗ ftTok (L := L) t d.ino sz.toNat m -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm Hc HΦ
  iapply wp_os_step "FtruncateStart" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
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
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hsz : st.size d.ino = m.size := by rw [size_of_file hf, hmo.size]
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
  have hlo : affLo st c = m.size := by rw [← hc]; simp [affLo, hsz]; omega
  have hhi' : affHi st c = m.size := by rw [← hc]; simp [affHi, hsz]
  have haff : ∀ i, Affects st c i ↔ m.size ≤ i := by
    intro i; rw [← hc]; simp [Affects, hsz]; omega
  have hwf1 := osWf_addTok (t := t) (c := c) hwf ht (hcp ▸ hf) (hcp ▸ hfree)
  have hcoh1 := osCoh_addTok (t := t) (q := 1) (m := m) (om := ftMeta m sz.toNat)
    (xs := []) hcoh hcp hf Hml
    ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_max_left _ _,
      by rw [← hc]; simp only [OsChange.target, ftMeta]; have := hmo.lo; have := hmo.size
         have := (hwf.sizes d.ino f hf).1; omega,
      by rw [← hc]; simp only [OsChange.target, ftMeta]; omega, rfl, rfl, rfl, rfl⟩
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
  have hmapsC : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l d.ino i ∧ Affects st c i := by
    intro l hl
    obtain ⟨i, b, len, hm, h1, h2, h3, rfl⟩ := (hC l).1 hl
    exact ⟨i, ⟨b, ⟨d.ino, len⟩, (hmo.maps b len).1 ((GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
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
        have hn : ¬ (c.ino = q' ∧ Affects st c i) := by
          rintro ⟨hp, ha⟩
          obtain ⟨b, m0, hb, hp0, hi0, rfl⟩ := hqi
          have hb' : m.maps !! b = some m0.len := by
            rw [hmo.maps b m0.len, hb]; congr 1; cases m0; simp only at hp0 ⊢
            rw [hp0, ← hp, hcp]
          apply hl; apply (hTmem _).2; apply (hC _).2
          have h1 := (haff i).1 ha
          have h2 := hhi b m0.len hb'
          exact ⟨i, b, m0.len, (GMap.mem_toList _ _ _).2 hb', h1, by omega, hi0, rfl⟩
        have hII : InflightAt (st.setProc { st.proc with inflight := <[t := c]> st.proc.inflight }) q' i ↔
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
  imod gAuth_insert _ _ _ t ⟨c, 1, [], ftMeta m sz.toNat, []⟩ hΓt $$ HAt with ⟨HAt, Ht⟩
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells
  isplitl [Htok Hm]
  · isplitr
    · ipureintro; exact ⟨hwf1, hcoh1⟩
    rw [show tokRes (gooseOsGS (L := L)) (st.setProc { st.proc with inflight := <[t := c]> st.proc.inflight })
        (<[t := ⟨c, 1, [], ftMeta m sz.toNat, []⟩]> Γt) =
      tokRes gooseOsGS st (<[t := ⟨c, 1, [], ftMeta m sz.toNat, []⟩]> Γt) from rfl]
    unfold tokRes
    iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.c.ino (DFrac.own ti.q) ti.om ∗
        bytesG gooseOsGS ti.c.ino (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
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
own). Either way the versions known (`vk`) are forgotten: the last sector may have one more. -/
theorem wp_osFtruncateFinish (t : Nat) (p : Ino) (sz : Nat) (m : OsMeta) (hi : Nat)
    (hE : ↑osN ⊆ E) (hgrow : m.size ≤ sz) (hhi : MapsBelow m.maps hi) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ ftTok (L := L) t p sz m -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ osGrown (L := L) p m sz hi) ∨
         (⌜e ≠ 0⌝ ∗ (osGrown (L := L) p m sz hi ∨
           (osMeta (L := L) p (DFrac.own 1) (ftFail m sz) ∗
             mcellsAny m.maps m.size hi)))) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FtruncateFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_os_step "FtruncateFinish" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold ftTok osTok
  generalize hti0 : (⟨⟨p, .truncate sz⟩, 1, [], ftMeta m sz, []⟩ : TokInfo) = ti
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  have hct : st.proc.inflight !! t = some ti.c := by
    have := hcoh.toks t; rw [Hti] at this; exact this.symm
  have hc : ti.c = ⟨p, .truncate sz⟩ := by rw [← hti0]
  obtain ⟨f, hf, -⟩ := hcoh.tok_saved t ti Hti
  rw [hc] at hf; simp only at hf
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.c.ino (DFrac.own ti.q) ti.om ∗
        bytesG gooseOsGS ti.c.ino (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
      Hti).1 $$ Htok with ⟨⟨Hm, -⟩, Htok⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hcp : ti.c.ino = p := by rw [hc]
  rw [hcp] at Hml
  obtain ⟨f1, hf1, hmo⟩ := coh_meta hcoh Hml
  rw [hf] at hf1; cases hf1
  have hti_om : ti.om = ftMeta m sz := by rw [← hti0]
  have hmsz : m.size = f.size := by
    have := hmo.size; rw [hti_om] at this; simpa [ftMeta] using this
  have hszf := hwf.sizes p f hf
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  have hfin := fun (f2 : OsFile) (hg : GrownFile f f2 sz) =>
    ftFinish_coh (f' := f2) hwf hcoh Hti hc hf Hml hg
  have hgT : GrownFile f (f.truncate sz) sz :=
    grownFile_truncate hszf.1 (by omega) (Nat.le_refl _)
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
  obtain ⟨f2, e, hg, hst', he', hne⟩ : ∃ (f2 : OsFile) (e : w64), GrownFile f f2 sz ∧
      st' = (st.setProc { st.proc with inflight := GMap.delete t' st.proc.inflight } : OsState).setFile p f2 ∧
      e' = Val (#e) ∧ ((e = 0 ∧ f2 = f.truncate sz) ∨ (e ≠ 0 ∧ (f2 = f.truncate sz ∨ f2 = f))) := by
    rcases hrest with ⟨h1, h2⟩ | ⟨e, he, h2, h1 | h1⟩
    · exact ⟨_, 0, hgT, h1, h2, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨f, e, grownFile_self hszf.2 (by omega),
        by rw [h1]; exact (setFile_self (st := st.doneInflight t') hf).symm, h2, .inr ⟨he, .inr rfl⟩⟩
    · exact ⟨_, e, hgT, h1, h2, .inr ⟨he, .inl rfl⟩⟩
  subst hst' he'
  obtain ⟨hsizes, hIk, hIp, hwfk, hcohk⟩ := hfin f2 hg
  have hn1 := hg.size_ge
  -- the meta
  have eqm : gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm ti.c.ino (DFrac.own ti.q) ti.om ⊢
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p (DFrac.own 1) (ftMeta m sz) := by
    rw [hcp, hti_om, show ti.q = 1 by rw [← hti0]]
  ihave Hm := eqm $$ Hm
  imod meta_replace _ (q := 1) (om := { ftMeta m sz with size := f2.size, vk := none }) (fun h1 => absurd rfl h1)
    $$ [HAm Hm] with ⟨HAm, Hm⟩
  · iframe
  -- the bytes
  imod bytesG_alloc _ p f.size (grownBytes f2 f.size) Γb
    (fun j hj => by
      cases hb : Γb !! (p, f.size + j) with
      | none => rfl
      | some x =>
        exfalso
        obtain ⟨f3, hf3, hb3, -⟩ := hcoh.bytes _ _ _ hb
        rw [hf] at hf3; cases hf3
        have := (List.getElem?_eq_some_iff.1 hb3).1; rw [contents_length] at this; omega)
    $$ HAb with ⟨HAb, Hbs⟩
  -- the token
  imod gAuth_delete _ _ _ _ _ $$ HAt Ht with HAt
  -- the cells: the cells past the size come back, showing the new bytes
  have hmaps : ti.om.maps = m.maps := by rw [hti_om]; rfl
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmo.maps b1 l1).1 (hmaps ▸ h1)) ((hmo.maps b2 l2).1 (hmaps ▸ h2)) hne)
  generalize hC : mapsCells m.size hi (fun i => toCellVal f2.contents[i]?) m.maps.toList = C
  have hClk := fun l v => hC ▸ lookup_mapsCells m.size hi (fun i => toCellVal f2.contents[i]?)
    m.maps.toList hdisj l v
  have hTmem : ∀ l, l ∈ C.toList.map (·.1) ↔ (C !! l).isSome := by
    intro l; simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hkv, rfl⟩; rw [(GMap.mem_toList _ _ _).1 hkv]; rfl
    · intro hl; obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
      exact ⟨(l, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  have hTnd : (C.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := C)
  have hin : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l p i ∧ f.size ≤ i ∧
      C !! l = some (toCellVal f2.contents[i]?) := by
    intro l hl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨i, ⟨b, len, hm, h1, h2, h3, rfl⟩, rfl⟩ := (hClk _ v).1 hv
    exact ⟨i, ⟨b, ⟨p, len⟩, (hmo.maps b len).1 (hmaps ▸ (GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
      by omega, hv⟩
  have hfk : ((st.setProc { st.proc with inflight := GMap.delete t' st.proc.inflight } : OsState).setFile p
      f2).file p = some f2 := file_setFile_eq _ _ _
  imod cells_step st _ h h' (C.toList.map (·.1)) ∅ C hwf hwfk Hr Hfr (fun b m0 h0 => .inr h0) hTnd
    (fun l hl => by obtain ⟨i, hi, -⟩ := hin l ((hTmem l).1 hl); exact .inl ⟨_, _, hi⟩)
    (fun l v h => by simp at h)
    (fun l v hl => by
      have hs : (C !! l).isSome := by rw [hl]; rfl
      obtain ⟨i, hi, ha, hv⟩ := hin l hs
      rw [hl] at hv; cases hv
      have hn : ¬ InflightAt ((st.setProc { st.proc with inflight := GMap.delete t' st.proc.inflight } : OsState).setFile p
          f2) p i := fun h => ((hIk _ _).1 h).1 rfl
      refine ⟨(hTmem l).2 hs, _, by rw [cellView_mapsTo hwfk hi, decide_eq_false hn], ?_⟩
      rw [cellByte_eq, if_neg hn, hfk]
      rfl)
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
          have hil : i < f.size := by
            apply Classical.byContradiction; intro hge
            obtain ⟨b, m0, hb, hp0, hi0, rfl⟩ := hqi
            have hb' : m.maps !! b = some m0.len := by
              rw [← hmaps, hmo.maps b m0.len, hb]; congr 1; cases m0; simp only at hp0 ⊢; rw [hp0]
            have := hhi b _ hb'
            apply hl; apply (hTmem _).2
            rw [(hClk _ _).2 ⟨i, ⟨b, m0.len, (GMap.mem_toList _ _ _).2 hb', by omega, by omega,
              hi0, rfl⟩, rfl⟩]
            rfl
          have hn1' : ¬ InflightAt ((st.setProc { st.proc with inflight := GMap.delete t' st.proc.inflight } : OsState).setFile q'
              f2) q' i := fun h => ((hIk _ _).1 h).1 rfl
          have hn2' : ¬ InflightAt st q' i := fun h => by have := (hIp i).1 h; omega
          rw [if_neg hn1', if_neg hn2', decide_eq_false hn1', decide_eq_false hn2', hfk, hf]
          simp only [Option.bind_some]
          rw [hg.old i hil]
        · have hII : InflightAt ((st.setProc { st.proc with inflight := GMap.delete t' st.proc.inflight } : OsState).setFile p
              f2) q' i ↔ InflightAt st q' i := by
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
  -- the client's view
  have hcells : mcells (GF := GF) m.maps m.size hi (fun i => toCellVal f2.contents[i]?) ⊢
      mcells m.maps m.size f2.size
        (fun i => byteCell ((f2.contents.drop m.size).getD (i - m.size) 0)) ∗
      mcellsAny m.maps f2.size hi := by
    iintro H
    icases mcells_split m.maps m.size f2.size hi _ (by omega) hhi $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iapply (mcells_congr _ _ _ _ _ (fun i h1 h2 => by
        show toCellVal _ = toCellVal _
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop, show m.size + (i - m.size) = i by omega,
          List.getElem?_eq_getElem (by rw [contents_length]; omega)]; rfl)) $$ H1
    · iapply mcells_any $$ H2
  ihave Hc : mcells m.maps m.size hi (fun i => toCellVal f2.contents[i]?) $$ [Hc]
  · unfold mcells
    iapply (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
      cellsR b (min m.size len) (min hi len - min m.size len) (fun i => toCellVal f2.contents[i]?))).2
    iapply (halves_mapsCells _ _ _ _ hdisj).1
    rw [hC]; iexact Hc
  ihave Hbs := (show bytesG (gooseOsGS (L := L)) p f.size (DFrac.own 1) (grownBytes f2 f.size) ⊢
    bytesG (gooseOsGS (L := L)) p m.size (DFrac.own 1) ((f2.contents.drop m.size).map (·, false)) by
      rw [hmsz]; exact .rfl) $$ Hbs
  have hzl : (f2.contents.drop m.size).length = f2.size - m.size := by
    rw [List.length_drop, contents_length]
  unfold osMeta
  rcases hne with ⟨rfl, rfl⟩ | ⟨he, rfl | rfl⟩
  · iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    unfold osGrown osMeta osBytes
    icases hcells $$ Hc with ⟨Hc1, Hc2⟩
    iexists (f.truncate sz).contents.drop m.size
    generalize hn : (f.truncate sz).size = n at hzl ⊢
    obtain rfl : n = sz := by rw [← hn, truncate_size]
    rw [show m.grown n = { ftMeta m n with size := n, vk := none } from rfl]
    iframe
    ipureintro
    refine ⟨hzl, fun hz => ?_⟩
    rw [truncate_contents, hmsz]
    exact resized_drop_zero (hmo.zero (by rw [hti_om]; simpa [ftMeta] using hz)) n
  · iapply HΦ
    iright
    isplitr
    · ipureintro; exact he
    ileft
    unfold osGrown osMeta osBytes
    icases hcells $$ Hc with ⟨Hc1, Hc2⟩
    iexists (f.truncate sz).contents.drop m.size
    generalize hn : (f.truncate sz).size = n at hzl ⊢
    obtain rfl : n = sz := by rw [← hn, truncate_size]
    rw [show m.grown n = { ftMeta m n with size := n, vk := none } from rfl]
    iframe
    ipureintro
    refine ⟨hzl, fun hz => ?_⟩
    rw [truncate_contents, hmsz]
    exact resized_drop_zero (hmo.zero (by rw [hti_om]; simpa [ftMeta] using hz)) n
  · iapply HΦ
    iright
    isplitr
    · ipureintro; exact he
    iright
    rw [show ftFail m sz = { ftMeta m sz with size := f2.size, vk := none } by
      rw [← hmsz]; rfl]
    iframe Hm
    iclear Hbs
    iapply mcells_any $$ Hc

end specs

end Fs
end Perennial
