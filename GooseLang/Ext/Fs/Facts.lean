/-
Pure facts about the Linux file extension's state, for its specs: how the derived notions
(`InflightAt`, the mapped cells' view) change, or do not, across the operations; the ghost maps
after a file is replaced (`osCoh_setFile`); what a sync does. Untrusted.
-/
module

public import GooseLang.Ext.Fs.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-! ## Facts about the state -/

theorem mapsFresh_same [GooseExts] [GoGlobalContext] {st st' : OsState}
    {h : GMap Loc (NonAtomic val)} (hm : st'.proc.maps = st.proc.maps) : MapsFresh st st' h := by
  intro b m h1 h2; rw [hm] at h1; rw [h1] at h2; cases h2

theorem heapRendered_same [GooseExts] [GoGlobalContext] {st st' : OsState}
    {h : GMap Loc (NonAtomic val)} (hwf' : OsWf st') (hm : st'.proc.maps = st.proc.maps)
    (hcv : cellView st' = cellView st)
    (Hag : ∀ l x, cellView st !! l = some x → ∃ m, h !! l = some (m, toCellVal x.1)) :
    HeapRendered st st' h h := by
  have hM : ∀ l i k, MapsTo st' l i k ↔ MapsTo st l i k := by
    intro l i k; simp only [MapsTo, hm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l i k hik _
    have hv := cellView_mapsTo hwf' hik
    rw [hcv] at hv
    obtain ⟨m, hh⟩ := Hag l _ hv
    exact ⟨m, _, hh, by rw [hh, cellVal_eq]⟩
  · intro l i k hik hn; exact absurd ⟨i, k, (hM l i k).1 hik⟩ hn
  · intro l hn hm'; obtain ⟨i, k, hik⟩ := hm'; exact absurd ⟨i, k, (hM l i k).2 hik⟩ hn
  · intro l _ _; rfl

theorem size_of_file {st : OsState} {i : Ino} {f : OsFile} (hf : st.file i = some f) :
    st.size i = f.size := by
  simp [OsState.size, hf]

theorem coh_byte {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {i : Ino}
    {b : Nat} {x : ByteG} (hx : Γb !! (i, b) = some x) :
    ∃ f, st.file i = some f ∧ b < f.size ∧ x.1 = f.cache b ∧ (∃ s, (x.1, s) ∈ x.2) ∧
      CandRel (cutOf Γm i) x.2 (f.cand b) :=
  hcoh.bytes i b x hx

/-- A byte resource of a file with no cut is the state's byte exactly. -/
theorem coh_byte_exact {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {i : Ino}
    {b : Nat} {x : ByteG} (hcut : cutOf Γm i = none) (hx : Γb !! (i, b) = some x) :
    ∃ f, st.file i = some f ∧ b < f.size ∧ x = (f.cache b, f.cand b) := by
  obtain ⟨f, hf, hb, h1, -, h3⟩ := hcoh.bytes i b x hx
  rw [hcut] at h3
  exact ⟨f, hf, hb, Prod.ext h1 h3.symm⟩

/-- The cut of `i` after `i`'s `OsMeta` is replaced by `m'`. -/
theorem cutOf_insert (Γm : GMap Ino OsMeta) (i q : Ino) (m' : OsMeta) :
    cutOf (<[i := m']> Γm) q = if i = q then m'.cut else cutOf Γm q := by
  unfold cutOf; rw [GMap.lookup_insert_eq_iff]; split <;> simp

theorem coh_tok {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {t : Nat}
    {c : OsChange} (ht : st.proc.inflight !! t = some c) : ∃ ti, Γt !! t = some ti ∧ ti.Is c := by
  have := hcoh.toks t
  rw [ht] at this
  cases h : Γt !! t with
  | none => rw [h] at this; cases this
  | some ti => exact ⟨ti, rfl, hcoh.tok_is t ti c h ht⟩

/-- With no change in flight on `i`, `fstat` sees the size. -/
theorem statSees_eq {st : OsState} {i : Ino} {sz : Nat}
    (h : ∀ t c, st.proc.inflight !! t = some c → c.ino ≠ i)
    (hs : StatSees st i sz) : sz = st.size i := by
  rcases hs with rfl | ⟨t, c, ht, hci, -, -⟩
  · rfl
  · exact absurd hci (h t c ht)

/-! ## States with the same changes in flight -/

section congr
variable {st st' : OsState}

theorem inflightAt_congr (hin : st'.proc.inflight = st.proc.inflight) (i : Ino) (b : Nat) :
    InflightAt st' i b = InflightAt st i b := by
  unfold InflightAt; rw [hin]

theorem cellByte_congr (hf : ∀ i, (st'.file i).map OsFile.contents = (st.file i).map OsFile.contents)
    (hI : ∀ i b, InflightAt st' i b = InflightAt st i b) (i : Ino) (b : Nat) :
    cellByte st' i b = cellByte st i b := by
  have := hf i
  unfold cellByte
  rw [hI i b]
  cases h1 : st'.file i <;> cases h2 : st.file i <;> rw [h1, h2] at this <;> simp at this <;>
    first | rfl | (dsimp only; simp only [this])

theorem cellView_congr' (hwf : OsWf st) (hwf' : OsWf st') (hm : st'.proc.maps = st.proc.maps)
    (hb : ∀ i b, cellByte st' i b = cellByte st i b)
    (hI : ∀ i b, InflightAt st' i b = InflightAt st i b) : cellView st' = cellView st := by
  apply GMap.ext; intro l
  show cellView st' !! l = cellView st !! l
  have hM : ∀ i k, MapsTo st' l i k ↔ MapsTo st l i k := by
    intro i k; simp only [MapsTo, hm]
  by_cases h : Mapped st l
  · obtain ⟨i, k, hik⟩ := h
    rw [cellView_mapsTo hwf' ((hM i k).2 hik), cellView_mapsTo hwf hik, hb, hI]
  · rw [cellView_none h, cellView_none (fun ⟨i, k, hik⟩ => h ⟨i, k, (hM i k).1 hik⟩)]

end congr

/-- The mapped cells' view depends on the mappings, the files' contents and the changes in flight. -/
theorem cellView_congr {st st' : OsState} (hwf : OsWf st) (hwf' : OsWf st')
    (h1 : st'.proc.maps = st.proc.maps)
    (h2 : ∀ i, (st'.file i).map OsFile.contents = (st.file i).map OsFile.contents)
    (h3 : st'.proc.inflight = st.proc.inflight) : cellView st' = cellView st := by
  have hI := inflightAt_congr h3
  exact cellView_congr' hwf hwf' h1 (cellByte_congr h2 hI) hI

/-! ## Replacing a file -/

theorem file_setFile (st : OsState) (i q : Ino) (f : OsFile) :
    (st.setFile i f).file q = if i = q then some f else st.file q := by
  simp only [OsState.file, OsState.setFile, GMap.lookup_insert_eq_iff]

theorem size_setFile (st : OsState) (i q : Ino) (f : OsFile) :
    (st.setFile i f).size q = if i = q then f.size else st.size q := by
  simp only [OsState.size, file_setFile]
  split <;> rfl

theorem file_setFile_ne (st : OsState) {i q : Ino} (f : OsFile) (h : i ≠ q) :
    (st.setFile i f).file q = st.file q := by
  rw [file_setFile, if_neg h]

theorem file_setFile_eq (st : OsState) (i : Ino) (f : OsFile) :
    (st.setFile i f).file i = some f := by
  rw [file_setFile, if_pos rfl]

theorem files_setFile (st : OsState) (i q : Ino) (f : OsFile) :
    (st.setFile i f).fs.files !! q = if i = q then some f else st.fs.files !! q := by
  simp only [OsState.setFile, GMap.lookup_insert_eq_iff]

theorem setFile_proc (st : OsState) (i : Ino) (f : OsFile) : (st.setFile i f).proc = st.proc := rfl

theorem MetaOk.transfer {st st' : OsState} {q : Ino} {m : OsMeta} {f : OsFile}
    (hm : st'.proc.maps = st.proc.maps) (hin : st'.proc.inflight = st.proc.inflight)
    (h : MetaOk st q m f) : MetaOk st' q m f :=
  ⟨h.size, h.lo, h.hi, by rw [hm]; exact h.maps, by rw [hin]; exact h.targets, h.dur, h.zf, h.tail, h.cz, h.rz, h.zc, h.ce⟩

/-- `OsWf` after the file `i` is replaced by `f'` (and the stamp perhaps advanced): the new file's
sizes in order and its stamps at most the new one. -/
theorem osWf_setFile {st : OsState} {i : Ino} {f f' : OsFile} (hwf : OsWf st)
    (hf : st.file i = some f) (hsz : f'.sizeLo ≤ f'.size ∧ f'.size ≤ f'.sizeHi ∧ f'.sizeHi ≤ maxBytes) (n : Nat)
    (hn : st.fs.stamp ≤ n) (hst : ∀ b p, p ∈ f'.cand b → p.2 ≤ n) (p : ProcState)
    (hp : p.fds = st.proc.fds ∧ p.maps = st.proc.maps)
    (hinfl : ∀ t c, p.inflight !! t = some c → ∃ c', st.proc.inflight !! t = some c' ∧ c'.ino = c.ino)
    (hone : ∀ t1 c1 t2 c2, p.inflight !! t1 = some c1 → p.inflight !! t2 = some c2 →
      c1.ino = c2.ino → t1 = t2) :
    OsWf { fs := { st.fs with files := <[i := f']> st.fs.files, stamp := n }, proc := p } := by
  have hex : ∀ q f0, st.file q = some f0 →
      ∃ f1, ({ fs := { st.fs with files := <[i := f']> st.fs.files, stamp := n }, proc := p } :
        OsState).file q = some f1 := by
    intro q f0 h0
    show ∃ f1, (<[i := f']> st.fs.files) !! q = some f1
    rw [GMap.lookup_insert_eq_iff]; split
    · exact ⟨_, rfl⟩
    · exact ⟨_, h0⟩
  refine ⟨fun fd d h => ?_, fun b m h => ?_, ?_, fun t c h => ?_, hone, ?_, ?_⟩
  · rw [hp.1] at h; obtain ⟨f0, h0⟩ := hwf.fds fd d h; exact hex _ _ h0
  · rw [hp.2] at h; obtain ⟨⟨f0, h0⟩, h1, h2, h3⟩ := hwf.maps b m h; exact ⟨hex _ _ h0, h1, h2, h3⟩
  · intro b1 m1 b2 m2 h1 h2; rw [hp.2] at h1 h2; exact hwf.maps_disj b1 m1 b2 m2 h1 h2
  · obtain ⟨c', h', hci⟩ := hinfl t c h; obtain ⟨f0, h0⟩ := hwf.infl t c' h'; rw [← hci]
    exact hex _ _ h0
  · intro q f1 h1
    change (<[i := f']> st.fs.files) !! q = some f1 at h1
    rw [GMap.lookup_insert_eq_iff] at h1; split at h1
    · cases h1; exact hsz
    · exact hwf.sizes q f1 h1
  · intro q f1 b p0 h1 hp0
    change (<[i := f']> st.fs.files) !! q = some f1 at h1
    rw [GMap.lookup_insert_eq_iff] at h1; split at h1
    · cases h1; exact hst b p0 hp0
    · exact Nat.le_trans (hwf.stamps q f1 b p0 h1 hp0) hn

/-- `osWf_setFile` for a step that leaves the process alone and the stamp as it is. -/
theorem osWf_setFile' {st : OsState} {i : Ino} {f f' : OsFile} (hwf : OsWf st)
    (hf : st.file i = some f) (hsz : f'.sizeLo ≤ f'.size ∧ f'.size ≤ f'.sizeHi ∧ f'.sizeHi ≤ maxBytes)
    (hst : ∀ b p, p ∈ f'.cand b → p.2 ≤ st.fs.stamp) : OsWf (st.setFile i f') :=
  osWf_setFile hwf hf hsz st.fs.stamp (Nat.le_refl _) hst st.proc ⟨rfl, rfl⟩
    (fun t c h => ⟨c, h, rfl⟩) hwf.infl_one

/-- **The ghost maps after the file `i` is replaced by `f'`**, with no change in flight on it, and
the state's process the same: its bytes exactly the new map's, its `OsMeta` `m'`. -/
theorem osCoh_setFile {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {i : Ino}
    {f f' : OsFile} (hf : st.file i = some f) (hnt : ∀ t ti, Γt !! t = some ti → ti.ino ≠ i)
    (Γb' : GMap (Ino × Nat) ByteG) (m' : OsMeta) (st' : OsState)
    (hst' : st'.fs.files = <[i := f']> st.fs.files) (hproc : st'.proc = st.proc)
    (hmo : MetaOk st' i m' f')
    (hbi : ∀ b x, Γb' !! (i, b) = some x → b < f'.size ∧ x.1 = f'.cache b ∧
      (∃ s, (x.1, s) ∈ x.2) ∧ CandRel m'.cut x.2 (f'.cand b))
    (hfull : ∀ b, b < f'.size → (Γb' !! (i, b)).isSome)
    (hother : ∀ q b, q ≠ i → Γb' !! (q, b) = Γb !! (q, b))
    (hstamp : st.fs.stamp ≤ st'.fs.stamp) (hcut : ∀ c, m'.cut = some c → c ≤ st'.fs.stamp) :
    OsCoh st' Γb' (<[i := m']> Γm) Γf Γt := by
  have hfile : ∀ q, st'.file q = if i = q then some f' else st.file q := by
    intro q; simp only [OsState.file, hst', GMap.lookup_insert_eq_iff]
  refine ⟨fun q => ?_, fun q m hm => ?_, fun q b x hx => ?_, fun q f1 b h1 hb => ?_,
    by rw [hproc]; exact hcoh.fds, fun t => by rw [hproc]; exact hcoh.toks t,
    fun t ti c h hc => by rw [hproc] at hc; exact hcoh.tok_is t ti c h hc,
    fun t ti h => ?_, fun t ti h => ?_, fun t ti h => ?_, fun t ti h hk => ?_, fun q m c hm hc => ?_⟩
  · rw [hst', GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff]
    split
    · simp
    · exact hcoh.meta_dom q
  · rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · subst_vars; cases hm; exact ⟨f', by rw [hst', GMap.lookup_insert_eq_iff, if_pos rfl], hmo⟩
    · rename_i hpq
      obtain ⟨f1, h1, hm1⟩ := hcoh.meta_some q m hm
      exact ⟨f1, by rw [hst', GMap.lookup_insert_eq_iff, if_neg hpq]; exact h1,
        hm1.transfer (by rw [hproc]) (by rw [hproc])⟩
  · rw [cutOf_insert]
    by_cases hq : q = i
    · subst hq; obtain ⟨h1, h2⟩ := hbi b x hx
      exact ⟨f', by rw [hfile, if_pos rfl], h1, by rw [if_pos rfl]; exact h2⟩
    · rw [hother q b hq] at hx
      obtain ⟨f1, h1, hb, hx⟩ := hcoh.bytes q b x hx
      exact ⟨f1, by rw [hfile, if_neg (Ne.symm hq)]; exact h1, hb, by rw [if_neg (Ne.symm hq)]; exact hx⟩
  · rw [hfile] at h1; split at h1
    · subst_vars; cases h1; exact hfull b hb
    · rename_i hq; rw [hother q b (Ne.symm hq)]; exact hcoh.bytes_full q f1 b h1 hb
  · have := hcoh.tok_meta t ti h
    rw [GMap.lookup_insert_ne _ _ (Ne.symm (hnt t ti h))]; exact this
  · obtain ⟨f1, h1, hrest⟩ := hcoh.tok_file t ti h
    exact ⟨f1, by rw [hfile, if_neg (Ne.symm (hnt t ti h))]; exact h1, hrest⟩
  · obtain ⟨f1, h1, hrest⟩ := hcoh.tok_cand t ti h
    exact ⟨f1, by rw [hfile, if_neg (Ne.symm (hnt t ti h))]; exact h1, hrest⟩
  · obtain ⟨f1, h1, hrest⟩ := hcoh.tok_rz t ti h hk
    exact ⟨f1, by rw [hfile, if_neg (Ne.symm (hnt t ti h))]; exact h1, hrest⟩
  · rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · cases hm; exact hcut c hc
    · exact Nat.le_trans (hcoh.cut_le q m c hm hc) hstamp

/-- No change in flight on a file whose whole `OsMeta` the client holds (`tokRes_meta_whole`), as
the state has it. -/
theorem noInfl_of_noTok {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {i : Ino}
    (h : ∀ t ti, Γt !! t = some ti → ti.ino ≠ i) :
    ∀ t c, st.proc.inflight !! t = some c → c.ino ≠ i := by
  intro t c ht hci
  obtain ⟨ti, hti, his⟩ := coh_tok hcoh ht
  exact h t ti hti (his.1 ▸ hci)

/-! ## Syncs -/

section sync
variable (f : OsFile) (busy : Nat → Prop) [DecidablePred busy]

theorem synced_size : (f.synced busy).size = f.size := rfl

theorem synced_cache_lt (b : Nat) (hb : b < f.size) : (f.synced busy).cache b = f.cache b := by
  simp only [OsFile.synced]; split
  · rfl
  · exact diskByte_of_lt hb

theorem synced_contents : (f.synced busy).contents = f.contents := by
  apply List.ext_getElem?; intro b
  rw [contents_getElem?, contents_getElem?, synced_size]
  split
  · rename_i hb; rw [synced_cache_lt f busy b hb]
  · rfl

/-- After a sync, every byte not busy has the one candidate its page-cache value, stamped 0. -/
theorem synced_cand (b : Nat) (hnb : ¬ busy b) :
    (f.synced busy).cand b = [((f.synced busy).cache b, 0)] := by
  simp [OsFile.synced, hnb]

end sync

/-! ## Changing the mappings -/

section maps

theorem cellView_lookup_congr {st st' : OsState} (hwf : OsWf st) (hwf' : OsWf st')
    (hfi : st'.fs.files = st.fs.files) (hin : st'.proc.inflight = st.proc.inflight) (l : Loc)
    (hl : ∀ i k, MapsTo st' l i k ↔ MapsTo st l i k) : cellView st' !! l = cellView st !! l := by
  have hI := inflightAt_congr hin
  have hb : ∀ i k, cellByte st' i k = cellByte st i k :=
    cellByte_congr (fun i => by simp [OsState.file, hfi]) hI
  by_cases h : Mapped st l
  · obtain ⟨i, k, hik⟩ := h
    rw [cellView_mapsTo hwf' ((hl i k).2 hik), cellView_mapsTo hwf hik, hb, hI]
  · rw [cellView_none h, cellView_none (fun ⟨i, k, hik⟩ => h ⟨i, k, (hl i k).1 hik⟩)]

theorem cellByte_noinfl {st : OsState} {i : Ino} {f : OsFile} {b : Nat}
    (hf : st.file i = some f) (hn : ¬ InflightAt st i b) : cellByte st i b = f.contents[b]? := by
  unfold cellByte
  rw [hf]
  dsimp only
  split
  · rename_i hb; rw [List.getElem?_eq_getElem hb]
  · rename_i hb; rw [List.getElem?_eq_none (by omega)]

/-- The ghost maps when only the mappings change, and the files' `OsMeta`s follow them. -/
theorem osCoh_setMaps {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt)
    (X : GMap Loc OsMap) (Γm' : GMap Ino OsMeta)
    (hdom : ∀ q, Γm' !! q = none ↔ Γm !! q = none)
    (hsome : ∀ q m', Γm' !! q = some m' → ∃ m, Γm !! q = some m ∧
      m' = { m with maps := m'.maps } ∧
      ∀ b len, m'.maps !! b = some len ↔ X !! b = some ⟨q, len⟩)
    (htok : ∀ t ti, Γt !! t = some ti → Γm' !! ti.ino = some ti.meta) :
    OsCoh { st with proc := { st.proc with maps := X } } Γb Γm' Γf Γt :=
  { hcoh with
    meta_dom := fun q => (hdom q).trans (hcoh.meta_dom q)
    meta_some := fun q m' h => by
      obtain ⟨m, hm, he, h6⟩ := hsome q m' h
      obtain ⟨f, hf, hmo⟩ := hcoh.meta_some q m hm
      rw [he]
      exact ⟨f, hf, ⟨hmo.size, hmo.lo, hmo.hi, by rw [← he]; exact h6, hmo.targets, hmo.dur,
        hmo.zf, hmo.tail, hmo.cz, hmo.rz, hmo.zc, hmo.ce⟩⟩
    bytes := fun q b x hx => by
      have hc : cutOf Γm' q = cutOf Γm q := by
        unfold cutOf
        cases h1 : Γm' !! q with
        | none => rw [(hdom q).1 h1]
        | some m' =>
          obtain ⟨m, hm, he, -⟩ := hsome q m' h1
          rw [hm]; simp only [Option.bind_some]; rw [he]
      rw [hc]; exact hcoh.bytes q b x hx
    tok_meta := htok
    cut_le := fun q m' c h hc => by
      obtain ⟨m, hm, he, -⟩ := hsome q m' h
      exact hcoh.cut_le q m c hm (by rw [he] at hc; exact hc) }

end maps

/-! ## Zeros past the size -/

/-- **A file grows with zeros.** -/
theorem resized_drop (f : OsFile) (sz : Nat) :
    (f.resized sz).drop f.size = List.replicate (sz - f.size) 0 := by
  apply List.ext_getElem
  · simp [OsFile.resized]
  · intro n h1 h2
    simp only [List.getElem_drop, List.getElem_replicate]
    simp [OsFile.resized]
    omega

theorem pageIn_mono {a b n : Nat} (h : a ≤ b) (ha : pageIn a n = true) : pageIn b n = true := by
  simp only [pageIn, decide_eq_true_eq] at *; omega

end Fs
end Perennial

end
