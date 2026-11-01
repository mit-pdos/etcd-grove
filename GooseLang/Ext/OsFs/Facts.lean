/-
Pure facts about the Linux file extension's state, for its specs: how the derived notions
(`Affects`, `InflightAt`, the mapped cells' view) change, or do not, across the operations.
-/
module

public import GooseLang.Ext.OsFs.Ghost

@[expose] public section

noncomputable section

namespace Perennial

/-! ## Facts about the state -/

theorem cellView_congr {st st' : OsState} (h1 : st'.maps = st.maps) (h2 : st'.files = st.files)
    (h3 : st'.inflight = st.inflight) : cellView st' = cellView st := by
  cases st; cases st'; simp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem mapsFresh_same [GooseExts] [GoGlobalContext] {st st' : OsState}
    {h : GMap Loc (NonAtomic val)} (hm : st'.maps = st.maps) : MapsFresh st st' h := by
  intro b m h1 h2; rw [hm] at h1; rw [h1] at h2; cases h2

theorem heapRendered_same [GooseExts] [GoGlobalContext] {st st' : OsState}
    {h : GMap Loc (NonAtomic val)} (hwf' : OsWf st') (hm : st'.maps = st.maps)
    (hcv : cellView st' = cellView st)
    (Hag : ∀ l x, cellView st !! l = some x → ∃ m, h !! l = some (m, toCellVal x.1)) :
    HeapRendered st st' h h := by
  have hM : ∀ l p i, MapsTo st' l p i ↔ MapsTo st l p i := by
    intro l p i; simp only [MapsTo, hm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l p i hpi _
    have hv := cellView_mapsTo hwf' hpi
    rw [hcv] at hv
    obtain ⟨m, hh⟩ := Hag l _ hv
    exact ⟨m, _, hh, by rw [hh, cellVal_eq]⟩
  · intro l p i hpi hn; exact absurd ⟨p, i, (hM l p i).1 hpi⟩ hn
  · intro l hn hm'; obtain ⟨p, i, hpi⟩ := hm'; exact absurd ⟨p, i, (hM l p i).2 hpi⟩ hn
  · intro l _ _; rfl

theorem size_of_file {st : OsState} {p : GoString} {f : OsFile} (hf : st.file p = some f) :
    st.size p = f.cur.length := by
  simp [OsState.size, hf]

/-- Below the size, the bytes a change affects are the bytes it takes. -/
theorem affects_iff_affRange (st : OsState) (c : OsChange) (i : Nat) (f : OsFile)
    (hf : st.file c.path = some f) (hi : i < f.cur.length) :
    Affects st c i ↔ i ∈ affRange st c := by
  unfold Affects affRange affLo affHi inRange
  rw [size_of_file hf]
  cases c.kind <;> dsimp only <;>
    simp only [List.mem_range'_1, Bool.and_eq_true, decide_eq_true_eq] <;> omega

theorem coh_byte {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {p : GoString}
    {i : Nat} {x : w8 × Bool} (hx : Γb !! (p, i) = some x) :
    ∃ f, st.file p = some f ∧ ∃ h : i < f.cur.length, f.cur[i] = x.1 := by
  obtain ⟨f, hf, hb, -⟩ := hcoh.bytes p i x hx
  obtain ⟨h, h'⟩ := List.getElem?_eq_some_iff.1 hb
  exact ⟨f, hf, h, h'⟩

theorem coh_tok {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {t : w64}
    {c : OsChange} (ht : st.inflight !! t = some c) : ∃ ti, Γt !! t = some ti ∧ ti.c = c := by
  have := hcoh.toks t
  rw [ht] at this
  cases h : Γt !! t with
  | none => rw [h] at this; cases this
  | some ti => rw [h] at this; exact ⟨ti, rfl, Option.some.inj this⟩

/-- A size `fstat` may see is past every byte that no change affects. -/
theorem statSees_gt {st : OsState} {p : GoString} {f : OsFile} {i sz : Nat}
    (hf : st.file p = some f) (hi : i < f.cur.length) (hn : ¬ InflightAt st p i)
    (hs : StatSees st p sz) : i < sz := by
  rcases hs with rfl | ⟨t, c, ht, hcp, hlo, -⟩
  · rw [size_of_file hf]; exact hi
  · have hna : ¬ Affects st c i := fun ha => hn ⟨t, c, ht, hcp, ha⟩
    subst hcp
    rw [size_of_file hf] at hlo
    unfold Affects inRange at hna
    unfold OsChange.target at hlo
    rw [size_of_file hf] at hna hlo
    cases hk : c.kind with
    | write off data => simp only [hk] at hna hlo; simp at hna; omega
    | truncate sz' => simp only [hk] at hna hlo; omega

/-- With no change in flight on `p` that may resize it, `fstat` sees the size. -/
theorem statSees_eq {st : OsState} {p : GoString} {sz : Nat}
    (h : ∀ t c, st.inflight !! t = some c → c.path = p → ¬ Reaches st c)
    (hs : StatSees st p sz) : sz = st.size p := by
  rcases hs with rfl | ⟨t, c, ht, hcp, hlo, hhi⟩
  · rfl
  · have hr := h t c ht hcp
    subst hcp
    unfold Reaches at hr
    unfold OsChange.target at hlo hhi
    cases hk : c.kind with
    | write off data => simp only [hk] at hr hlo hhi; omega
    | truncate _ => simp [hk] at hr


/-! ## States with the same sizes and changes in flight -/

section congr
variable {st st' : OsState}

theorem affects_congr (hs : ∀ p, st'.size p = st.size p) (c : OsChange) (i : Nat) :
    Affects st' c i = Affects st c i := by
  unfold Affects; rw [hs]

theorem target_congr (hs : ∀ p, st'.size p = st.size p) (c : OsChange) :
    c.target st' = c.target st := by
  unfold OsChange.target; rw [hs]

theorem affLo_congr (hs : ∀ p, st'.size p = st.size p) (c : OsChange) :
    affLo st' c = affLo st c := by
  unfold affLo; rw [hs]

theorem affHi_congr (hs : ∀ p, st'.size p = st.size p) (c : OsChange) :
    affHi st' c = affHi st c := by
  unfold affHi; rw [hs]

theorem affRange_congr (hs : ∀ p, st'.size p = st.size p) (c : OsChange) :
    affRange st' c = affRange st c := by
  unfold affRange; rw [affLo_congr hs, affHi_congr hs]

theorem reaches_congr (hs : ∀ p, st'.size p = st.size p) (c : OsChange) :
    Reaches st' c = Reaches st c := by
  unfold Reaches; rw [hs]

theorem inflightAt_congr (hs : ∀ p, st'.size p = st.size p) (hin : st'.inflight = st.inflight)
    (p : GoString) (i : Nat) : InflightAt st' p i = InflightAt st p i := by
  unfold InflightAt; rw [hin]; simp only [affects_congr hs]

theorem cellByte_congr (hf : ∀ p, (st'.file p).map OsFile.cur = (st.file p).map OsFile.cur)
    (hI : ∀ p i, InflightAt st' p i = InflightAt st p i) (p : GoString) (i : Nat) :
    cellByte st' p i = cellByte st p i := by
  have := hf p
  unfold cellByte
  rw [hI p i]
  cases h1 : st'.file p <;> cases h2 : st.file p <;> rw [h1, h2] at this <;> simp at this <;>
    first | rfl | (dsimp only; simp only [this])

theorem cellView_congr' (hwf : OsWf st) (hwf' : OsWf st') (hm : st'.maps = st.maps)
    (hb : ∀ p i, cellByte st' p i = cellByte st p i)
    (hI : ∀ p i, InflightAt st' p i = InflightAt st p i) : cellView st' = cellView st := by
  apply GMap.ext; intro l
  show cellView st' !! l = cellView st !! l
  have hM : ∀ p i, MapsTo st' l p i ↔ MapsTo st l p i := by
    intro p i; simp only [MapsTo, hm]
  by_cases h : Mapped st l
  · obtain ⟨p, i, hpi⟩ := h
    rw [cellView_mapsTo hwf' ((hM p i).2 hpi), cellView_mapsTo hwf hpi, hb, hI]
  · rw [cellView_none h, cellView_none (fun ⟨p, i, hpi⟩ => h ⟨p, i, (hM p i).1 hpi⟩)]

end congr

/-! ## Replacing a file -/

theorem file_setFile (st : OsState) (p q : GoString) (f : OsFile) :
    (st.setFile p f).file q = if p = q then some f else st.file q := by
  simp only [OsState.file, OsState.setFile, GMap.lookup_insert_eq_iff]
  split <;> rfl

theorem size_setFile (st : OsState) (p q : GoString) (f : OsFile) :
    (st.setFile p f).size q = if p = q then f.cur.length else st.size q := by
  simp only [OsState.size, file_setFile]
  split <;> rfl

/-- Replacing a file by one of the same size keeps the sizes. -/
theorem size_setFile_same {st : OsState} {p : GoString} {f f' : OsFile} (hf : st.file p = some f)
    (hl : f'.cur.length = f.cur.length) (q : GoString) : (st.setFile p f').size q = st.size q := by
  rw [size_setFile]; split
  · subst_vars; rw [size_of_file hf, hl]
  · rfl

theorem MetaOk.transfer {st st' : OsState} {q : GoString} {m : OsMeta} {f : OsFile}
    (hs : ∀ p, st'.size p = st.size p) (hm : st'.maps = st.maps) (hin : st'.inflight = st.inflight)
    (h : MetaOk st q m f) : MetaOk st' q m f :=
  ⟨h.size, h.named, h.lo, h.hi, h.ok, by rw [hm]; exact h.maps,
    by rw [hin]; intro t c ht hc; rw [target_congr hs]; exact h.targets t c ht hc⟩

theorem file_setFile_ne (st : OsState) {p q : GoString} (f : OsFile) (h : p ≠ q) :
    (st.setFile p f).file q = st.file q := by
  rw [file_setFile, if_neg h]

theorem file_setFile_eq (st : OsState) (p : GoString) (f : OsFile) :
    (st.setFile p f).file p = some f := by
  rw [file_setFile, if_pos rfl]

theorem files_setFile (st : OsState) (p q : GoString) (f : OsFile) :
    (st.setFile p f).files !! q = if p = q then some (some f) else st.files !! q := by
  simp only [OsState.setFile, GMap.lookup_insert_eq_iff]

/-- Replacing a file by one with the same contents keeps every derived notion of the other
files, and of the mapped cells. -/
theorem osWf_setFile_sameCur {st : OsState} {p : GoString} {f f' : OsFile} (hwf : OsWf st)
    (hf : st.file p = some f) (hcur : f'.cur = f.cur)
    (hsz : f'.sizeLo ≤ f'.cur.length ∧ f'.cur.length ≤ f'.sizeHi)
    (hcoh : ∀ i, f'.dirty i = false → f'.lost i = false → i < f'.cur.length →
      i < f'.durable.length → f'.durable[i]? = f'.cur[i]?) :
    OsWf (st.setFile p f') := by
  have hs := size_setFile_same hf (by rw [hcur])
  have hex : ∀ q f0, st.file q = some f0 → ∃ f1, (st.setFile p f').file q = some f1 := by
    intro q f0 h0; rw [file_setFile]; split
    · exact ⟨_, rfl⟩
    · exact ⟨_, h0⟩
  refine ⟨fun fd d h => ?_, fun b m h => ?_, hwf.maps_disj, fun t c h => ?_, ?_, ?_, ?_⟩
  · obtain ⟨f0, h0⟩ := hwf.fds fd d h; exact hex _ _ h0
  · obtain ⟨⟨f0, h0⟩, h1, h2, h3⟩ := hwf.maps b m h; exact ⟨hex _ _ h0, h1, h2, h3⟩
  · obtain ⟨f0, h0⟩ := hwf.infl t c h; exact hex _ _ h0
  · intro t1 c1 t2 c2 i h1 h2 hne hp
    simp only [affects_congr hs]
    exact hwf.infl_disj t1 c1 t2 c2 i h1 h2 hne hp
  · intro q f1 h1
    rw [file_setFile] at h1; split at h1
    · cases h1; exact hsz
    · exact hwf.sizes q f1 h1
  · intro q f1 i h1
    rw [file_setFile] at h1; split at h1
    · cases h1; exact hcoh i
    · exact hwf.coherent q f1 i h1

/-! ## Syncs -/

section sync
variable (f : OsFile) (busy : Nat → Prop) [DecidablePred busy]

/-- A file's bytes neither dirty nor lost are on disk. -/
def FileCoherent (f : OsFile) : Prop :=
  ∀ i, f.dirty i = false → f.lost i = false → i < f.cur.length → i < f.durable.length →
    f.durable[i]? = f.cur[i]?

theorem synced_durable (i : Nat) (hi : i < f.cur.length) :
    (f.synced busy).durable[i]? =
      some (if (f.dirty i ∧ ¬ busy i) ∨ f.durable.length ≤ i then f.cur.getD i 0
        else f.durable.getD i 0) := by
  simp [OsFile.synced, hi]

/-- After a successful sync with no byte busy, a byte not lost is clean. -/
theorem synced_clean (hcoh : FileCoherent f) (hb : ∀ i, ¬ busy i) (i : Nat)
    (hi : i < f.cur.length) (hl : f.lost i = false) : CleanPhys (f.synced busy) i := by
  refine ⟨by simp [OsFile.synced, hb], by simp [OsFile.synced, hl], by simp [OsFile.synced, hi], ?_⟩
  rw [synced_durable f busy i hi]
  show _ = f.cur[i]?
  rw [List.getElem?_eq_getElem hi]
  simp only [hb, not_false_eq_true, and_true, Option.some.injEq]
  split
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · rename_i h
    have hd : f.dirty i = false := by cases hd : f.dirty i <;> simp_all
    have hdl : i < f.durable.length := by omega
    have := hcoh i hd hl hi hdl
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hdl] at this
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hdl, Option.some.inj this]

theorem synced_coherent (hcoh : FileCoherent f) (hb : ∀ i, ¬ busy i) :
    FileCoherent (f.synced busy) := by
  intro i _ hl hi _
  have hi : i < f.cur.length := hi
  by_cases hd : f.dirty i = true
  · rw [synced_durable f busy i hi]
    show _ = f.cur[i]?
    simp [hd, hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · have hl' : f.lost i = false := by
      simp only [OsFile.synced] at hl
      cases h : f.lost i <;> cases h2 : f.dirty i <;> simp_all
    exact (synced_clean f busy hcoh hb i hi hl').2.2.2

theorem syncFailed_clean (i : Nat) (h : CleanPhys f i) :
    CleanPhys (f.syncFailed busy) i := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by simp [OsFile.syncFailed, h1], by simp [OsFile.syncFailed, h1, h2], h3, h4⟩

theorem syncFailed_coherent (hcoh : FileCoherent f) (hb : ∀ i, ¬ busy i) :
    FileCoherent (f.syncFailed busy) := by
  intro i _ hl hi hdl
  simp only [OsFile.syncFailed, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    Bool.not_eq_false', decide_eq_true_eq] at hl
  obtain ⟨hl, hd⟩ := hl
  have hd' : f.dirty i = false := by rcases hd with hd | hd; exact hd; exact absurd hd (hb i)
  exact hcoh i hd' hl hi hdl

end sync

/-! ## Replacing a file by one with the same contents -/

section sameCur
variable {st : OsState} {p : GoString} {f f' : OsFile}

theorem sizes_setFile_sameCur (hf : st.file p = some f) (hcur : f'.cur = f.cur) :
    ∀ q, (st.setFile p f').size q = st.size q :=
  size_setFile_same hf (by rw [hcur])

theorem inflightAt_setFile_sameCur (hf : st.file p = some f) (hcur : f'.cur = f.cur) :
    ∀ q i, InflightAt (st.setFile p f') q i = InflightAt st q i :=
  inflightAt_congr (sizes_setFile_sameCur hf hcur) rfl

theorem cellView_setFile_sameCur (hwf : OsWf st) (hwf' : OsWf (st.setFile p f'))
    (hf : st.file p = some f) (hcur : f'.cur = f.cur) : cellView (st.setFile p f') = cellView st := by
  have hI := inflightAt_setFile_sameCur hf hcur
  refine cellView_congr' hwf hwf' rfl (cellByte_congr (fun q => ?_) hI) hI
  rw [file_setFile]; split
  · subst_vars; rw [hf]; simp [hcur]
  · rfl

/-- The ghost maps after replacing the file `p` by `f'`, with the same contents, and its
`OsMeta` by `m'`, and the bytes `xs` the client holds by `ys`, with the same values: the clean
bytes of `f` stay clean, and those `ys` marks clean are clean. -/
theorem osCoh_setFile_sameCur {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt)
    (hf : st.file p = some f) (hcur : f'.cur = f.cur) {m' : OsMeta}
    (hmo : MetaOk (st.setFile p f') p m' f') (lo : Nat) (xs ys : List (w8 × Bool))
    (hys : ys.length = xs.length)
    (hxs : ∀ k (hk : k < xs.length), Γb !! (p, lo + k) = some xs[k])
    (hval : ∀ k (hk : k < ys.length), ys[k].1 = (xs[k]'(hys ▸ hk)).1)
    (hkeep : ∀ i, CleanPhys f i → CleanPhys f' i)
    (hnew : ∀ k (hk : k < ys.length), ys[k].2 = true → CleanPhys f' (lo + k))
    (hnoI : ∀ i, ¬ InflightAt st p i) :
    OsCoh (st.setFile p f') (insertBytes p lo ys Γb) (<[p := some m']> Γm) Γf Γt := by
  have hs := sizes_setFile_sameCur hf hcur
  have hI := inflightAt_setFile_sameCur hf hcur
  have hfp : st.files !! p = some (some f) := file_eq_some.1 hf
  refine ⟨fun q => ?_, fun q => ?_, fun q m hm => ?_, fun q i x hx => ?_, fun q f1 i h1 hi => ?_,
    hcoh.fds, hcoh.toks, fun t ti h => ?_, hcoh.tok_alone, fun t ti h => ?_⟩
  · rw [files_setFile, GMap.lookup_insert_eq_iff]
    split
    · simp
    · exact hcoh.meta_dom q
  · rw [files_setFile, GMap.lookup_insert_eq_iff]
    split
    · simp
    · exact hcoh.meta_none q
  · rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · subst_vars; cases hm; exact ⟨f', by rw [files_setFile, if_pos rfl], hmo⟩
    · rename_i hpq
      obtain ⟨f1, h1, hm1⟩ := hcoh.meta_some q m hm
      exact ⟨f1, by rw [files_setFile, if_neg hpq]; exact h1, hm1.transfer hs rfl rfl⟩
  · rw [lookup_insertBytes] at hx
    split at hx
    · rename_i hr
      obtain ⟨rfl, h1, h2⟩ := hr
      have hk : i - lo < ys.length := by omega
      rw [List.getElem?_eq_getElem hk] at hx; cases hx
      have hk' : i - lo < xs.length := hys ▸ hk
      obtain ⟨f1, h1', hb, -⟩ := hcoh.bytes q (lo + (i - lo)) _ (hxs _ hk')
      rw [hf] at h1'; cases h1'
      refine ⟨f', file_setFile_eq st q f', ?_, fun hc => ⟨?_, by rw [hI]; exact hnoI i⟩⟩
      · rw [hcur, hval _ hk]; rw [show lo + (i - lo) = i by omega] at hb; exact hb
      · have := hnew _ hk hc; rwa [show lo + (i - lo) = i by omega] at this
    · obtain ⟨f1, h1, hb, hc⟩ := hcoh.bytes q i x hx
      by_cases hpq : p = q
      · subst hpq; rw [hf] at h1; cases h1
        refine ⟨f', file_setFile_eq st p f', by rw [hcur]; exact hb, fun hx2 => ?_⟩
        obtain ⟨hc1, hc2⟩ := hc hx2
        exact ⟨hkeep i hc1, by rw [hI]; exact hc2⟩
      · refine ⟨f1, by rw [file_setFile_ne st f' hpq]; exact h1, hb, fun hx2 => ?_⟩
        obtain ⟨hc1, hc2⟩ := hc hx2
        exact ⟨hc1, by rw [hI]; exact hc2⟩
  · rw [lookup_insertBytes]
    split
    · rename_i hr; rw [List.getElem?_eq_getElem (by omega)]; rfl
    · rw [file_setFile] at h1
      split at h1
      · subst_vars; cases h1; exact hcoh.bytes_full _ f i hf (by rw [← hcur]; exact hi)
      · exact hcoh.bytes_full q f1 i h1 hi
  · rw [reaches_congr hs]; exact hcoh.tok_q t ti h
  · obtain ⟨f1, h1, hsv⟩ := hcoh.tok_saved t ti h
    rw [affRange_congr hs]
    rw [file_setFile]; split
    · subst_vars; rw [hf] at h1; cases h1; exact ⟨f', rfl, by rw [hcur]; exact hsv⟩
    · exact ⟨f1, h1, hsv⟩

end sameCur

/-! ## Changing the mappings -/

section maps

theorem size_congr_files {st st' : OsState} (h : st'.files = st.files) :
    ∀ p, st'.size p = st.size p := by
  intro p; simp [OsState.size, OsState.file, h]

theorem cellView_lookup_congr {st st' : OsState} (hwf : OsWf st) (hwf' : OsWf st')
    (hfi : st'.files = st.files) (hin : st'.inflight = st.inflight) (l : Loc)
    (hl : ∀ p i, MapsTo st' l p i ↔ MapsTo st l p i) : cellView st' !! l = cellView st !! l := by
  have hs := size_congr_files hfi
  have hI := inflightAt_congr hs hin
  have hb : ∀ p i, cellByte st' p i = cellByte st p i :=
    cellByte_congr (fun p => by simp [OsState.file, hfi]) hI
  by_cases h : Mapped st l
  · obtain ⟨p, i, hpi⟩ := h
    rw [cellView_mapsTo hwf' ((hl p i).2 hpi), cellView_mapsTo hwf hpi, hb, hI]
  · rw [cellView_none h, cellView_none (fun ⟨p, i, hpi⟩ => h ⟨p, i, (hl p i).1 hpi⟩)]

theorem cellByte_noinfl {st : OsState} {p : GoString} {f : OsFile} {i : Nat}
    (hf : st.file p = some f) (hn : ¬ InflightAt st p i) : cellByte st p i = f.cur[i]? := by
  unfold cellByte
  rw [hf]
  dsimp only
  split
  · rename_i hi; rw [List.getElem?_eq_getElem hi]
  · rename_i hi; rw [List.getElem?_eq_none (by omega)]

/-- The ghost maps when only the mappings change, and the files' `OsMeta`s follow them. -/
theorem osCoh_setMaps {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt)
    (X : GMap Loc OsMap) (Γm' : GMap GoString (Option OsMeta))
    (hdom : ∀ q, Γm' !! q = none ↔ Γm !! q = none)
    (hnone : ∀ q, Γm' !! q = some none ↔ Γm !! q = some none)
    (hsome : ∀ q m', Γm' !! q = some (some m') → ∃ m, Γm !! q = some (some m) ∧
      m'.size = m.size ∧ m'.lo = m.lo ∧ m'.hi = m.hi ∧ m'.named = m.named ∧ m'.ok = m.ok ∧
      ∀ b len, m'.maps !! b = some len ↔ X !! b = some ⟨q, len⟩) :
    OsCoh { st with maps := X } Γb Γm' Γf Γt :=
  { hcoh with
    meta_dom := fun q => (hdom q).trans (hcoh.meta_dom q)
    meta_none := fun q => (hnone q).trans (hcoh.meta_none q)
    meta_some := fun q m' h => by
      obtain ⟨m, hm, h1, h2, h3, h4, h5, h6⟩ := hsome q m' h
      obtain ⟨f, hf, hmo⟩ := hcoh.meta_some q m hm
      exact ⟨f, hf, ⟨h1 ▸ hmo.size, h4 ▸ hmo.named, h2 ▸ hmo.lo, h3 ▸ hmo.hi,
        fun hok => hmo.ok (h5 ▸ hok), h6,
        fun t c ht hc => by rw [h2, h3]; exact hmo.targets t c ht hc⟩⟩ }

end maps

end Perennial
