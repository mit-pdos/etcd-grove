/-
Pure facts about the Linux file extension's state, for its specs: how the derived notions
(`Affects`, `InflightAt`, the mapped cells' view) change, or do not, across the operations; what a
sync does to clean bytes. Untrusted.
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

/-- Below the size, the bytes a change affects are the bytes it takes. -/
theorem affects_iff_affRange (st : OsState) (c : OsChange) (b : Nat) (f : OsFile)
    (hf : st.file c.ino = some f) (hb : b < f.size) :
    Affects st c b ↔ b ∈ affRange st c := by
  unfold Affects affRange affLo affHi inRange
  rw [size_of_file hf]
  cases c.kind <;> dsimp only <;>
    simp only [List.mem_range'_1, Bool.and_eq_true, decide_eq_true_eq] <;> omega

theorem coh_byte {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {i : Ino}
    {b : Nat} {x : w8 × Bool} (hx : Γb !! (i, b) = some x) :
    ∃ f, st.file i = some f ∧ ∃ h : b < f.contents.length, f.contents[b] = x.1 := by
  obtain ⟨f, hf, hb, -⟩ := hcoh.bytes i b x hx
  obtain ⟨h, h'⟩ := List.getElem?_eq_some_iff.1 hb
  exact ⟨f, hf, h, h'⟩

theorem coh_tok {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {t : Nat}
    {c : OsChange} (ht : st.proc.inflight !! t = some c) : ∃ ti, Γt !! t = some ti ∧ ti.c = c := by
  have := hcoh.toks t
  rw [ht] at this
  cases h : Γt !! t with
  | none => rw [h] at this; cases this
  | some ti => rw [h] at this; exact ⟨ti, rfl, Option.some.inj this⟩

/-- A size `fstat` may see is past every byte that no change affects. -/
theorem statSees_gt {st : OsState} {i : Ino} {f : OsFile} {b sz : Nat}
    (hf : st.file i = some f) (hb : b < f.size) (hn : ¬ InflightAt st i b)
    (hs : StatSees st i sz) : b < sz := by
  rcases hs with rfl | ⟨t, c, ht, hci, hlo, -⟩
  · rw [size_of_file hf]; exact hb
  · have hna : ¬ Affects st c b := fun ha => hn ⟨t, c, ht, hci, ha⟩
    subst hci
    rw [size_of_file hf] at hlo
    unfold Affects inRange at hna
    unfold OsChange.target at hlo
    rw [size_of_file hf] at hna hlo
    cases hk : c.kind with
    | write off data => simp only [hk] at hna hlo; simp at hna; omega
    | truncate sz' => simp only [hk] at hna hlo; omega

/-- With no change in flight on `i` that may resize it, `fstat` sees the size. -/
theorem statSees_eq {st : OsState} {i : Ino} {sz : Nat}
    (h : ∀ t c, st.proc.inflight !! t = some c → c.ino = i → ¬ Reaches st c)
    (hs : StatSees st i sz) : sz = st.size i := by
  rcases hs with rfl | ⟨t, c, ht, hci, hlo, hhi⟩
  · rfl
  · have hr := h t c ht hci
    subst hci
    unfold Reaches at hr
    unfold OsChange.target at hlo hhi
    cases hk : c.kind with
    | write off data => simp only [hk] at hr hlo hhi; omega
    | truncate _ => simp [hk] at hr

/-! ## States with the same sizes and changes in flight -/

section congr
variable {st st' : OsState}

theorem affects_congr (hs : ∀ i, st'.size i = st.size i) (c : OsChange) (b : Nat) :
    Affects st' c b = Affects st c b := by
  unfold Affects; rw [hs]

theorem target_congr (hs : ∀ i, st'.size i = st.size i) (c : OsChange) :
    c.target st' = c.target st := by
  unfold OsChange.target; rw [hs]

theorem affLo_congr (hs : ∀ i, st'.size i = st.size i) (c : OsChange) :
    affLo st' c = affLo st c := by
  unfold affLo; rw [hs]

theorem affHi_congr (hs : ∀ i, st'.size i = st.size i) (c : OsChange) :
    affHi st' c = affHi st c := by
  unfold affHi; rw [hs]

theorem affRange_congr (hs : ∀ i, st'.size i = st.size i) (c : OsChange) :
    affRange st' c = affRange st c := by
  unfold affRange; rw [affLo_congr hs, affHi_congr hs]

theorem reaches_congr (hs : ∀ i, st'.size i = st.size i) (c : OsChange) :
    Reaches st' c = Reaches st c := by
  unfold Reaches; rw [hs]

theorem inflightAt_congr (hs : ∀ i, st'.size i = st.size i)
    (hin : st'.proc.inflight = st.proc.inflight) (i : Ino) (b : Nat) :
    InflightAt st' i b = InflightAt st i b := by
  unfold InflightAt; rw [hin]; simp only [affects_congr hs]

theorem secBusy_congr (hs : ∀ i, st'.size i = st.size i)
    (hin : st'.proc.inflight = st.proc.inflight) (i : Ino) (n : Nat) :
    SecBusy st' i n = SecBusy st i n := by
  unfold SecBusy; simp only [inflightAt_congr hs hin]

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

/-- The mapped cells' view depends on the mappings, the files and the changes in flight. -/
theorem cellView_congr {st st' : OsState} (hwf : OsWf st) (hwf' : OsWf st')
    (h1 : st'.proc.maps = st.proc.maps) (h2 : st'.fs.files = st.fs.files)
    (h3 : st'.proc.inflight = st.proc.inflight) : cellView st' = cellView st := by
  have hs : ∀ i, st'.size i = st.size i := by intro i; simp [OsState.size, OsState.file, h2]
  have hI := inflightAt_congr hs h3
  exact cellView_congr' hwf hwf' h1 (cellByte_congr (fun i => by simp [OsState.file, h2]) hI) hI

/-! ## Replacing a file -/

theorem file_setFile (st : OsState) (i q : Ino) (f : OsFile) :
    (st.setFile i f).file q = if i = q then some f else st.file q := by
  simp only [OsState.file, OsState.setFile, GMap.lookup_insert_eq_iff]

theorem size_setFile (st : OsState) (i q : Ino) (f : OsFile) :
    (st.setFile i f).size q = if i = q then f.size else st.size q := by
  simp only [OsState.size, file_setFile]
  split <;> rfl

/-- Replacing a file by one of the same size keeps the sizes. -/
theorem size_setFile_same {st : OsState} {i : Ino} {f f' : OsFile} (hf : st.file i = some f)
    (hl : f'.size = f.size) (q : Ino) : (st.setFile i f').size q = st.size q := by
  rw [size_setFile]; split
  · subst_vars; rw [size_of_file hf, hl]
  · rfl

theorem MetaOk.transfer {st st' : OsState} {q : Ino} {m : OsMeta} {f : OsFile}
    (hs : ∀ i, st'.size i = st.size i) (hm : st'.proc.maps = st.proc.maps)
    (hin : st'.proc.inflight = st.proc.inflight) (h : MetaOk st q m f) : MetaOk st' q m f :=
  ⟨h.size, h.lo, h.hi, h.ok, by rw [hm]; exact h.maps,
    by rw [hin]; intro t c ht hc; rw [target_congr hs]; exact h.targets t c ht hc, h.dur, h.zero,
    h.vk, h.dz⟩

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

/-- Replacing a file by one with the same contents keeps every derived notion of the other files,
and of the mapped cells. -/
theorem osWf_setFile_sameCur {st : OsState} {i : Ino} {f f' : OsFile} (hwf : OsWf st)
    (hf : st.file i = some f) (hsize : f'.size = f.size)
    (hsz : f'.sizeLo ≤ f'.size ∧ f'.size ≤ f'.sizeHi) (hv : ∀ n, (f'.secs n).vers ≠ []) :
    OsWf (st.setFile i f') := by
  have hs := size_setFile_same hf hsize
  have hex : ∀ q f0, st.file q = some f0 → ∃ f1, (st.setFile i f').file q = some f1 := by
    intro q f0 h0; rw [file_setFile]; split
    · exact ⟨_, rfl⟩
    · exact ⟨_, h0⟩
  refine ⟨fun fd d h => ?_, fun b m h => ?_, hwf.maps_disj, fun t c h => ?_, ?_, ?_, ?_⟩
  · obtain ⟨f0, h0⟩ := hwf.fds fd d h; exact hex _ _ h0
  · obtain ⟨⟨f0, h0⟩, h1, h2, h3⟩ := hwf.maps b m h; exact ⟨hex _ _ h0, h1, h2, h3⟩
  · obtain ⟨f0, h0⟩ := hwf.infl t c h; exact hex _ _ h0
  · intro t1 c1 t2 c2 b h1 h2 hne hp
    simp only [affects_congr hs]
    exact hwf.infl_disj t1 c1 t2 c2 b h1 h2 hne hp
  · intro q f1 h1
    rw [file_setFile] at h1; split at h1
    · cases h1; exact hsz
    · exact hwf.sizes q f1 h1
  · intro q f1 n h1
    rw [file_setFile] at h1; split at h1
    · cases h1; exact hv n
    · exact hwf.vers q f1 n h1

/-! ## Syncs -/

section sync
variable (f : OsFile) (busy : Nat → Prop) [DecidablePred busy]

theorem synced_size : (f.synced busy).size = f.size := rfl
theorem syncFailed_size : (f.syncFailed busy).size = f.size := rfl

theorem synced_last (n : Nat) : ((f.synced busy).secs n).last = (f.secs n).last := by
  simp only [OsFile.synced]
  split
  · simp [Sector.last]
  · rfl

theorem syncFailed_last (n : Nat) : ((f.syncFailed busy).secs n).last = (f.secs n).last := by
  simp only [OsFile.syncFailed]
  split <;> rfl

theorem synced_rawAt (b : Nat) : (f.synced busy).rawAt b = f.rawAt b := by
  simp only [OsFile.rawAt, synced_last]

theorem syncFailed_rawAt (b : Nat) : (f.syncFailed busy).rawAt b = f.rawAt b := by
  simp only [OsFile.rawAt, syncFailed_last]

theorem synced_contents : (f.synced busy).contents = f.contents := by
  unfold OsFile.contents; rw [synced_size]; congr 1; funext b; exact synced_rawAt f busy b

theorem syncFailed_contents : (f.syncFailed busy).contents = f.contents := by
  unfold OsFile.contents; rw [syncFailed_size]; congr 1; funext b; exact syncFailed_rawAt f busy b

/-- After a successful sync, a byte of the file in an idle sector that is dirty or has one version
(not lost) is clean. -/
theorem synced_clean (b : Nat) (hb : b < f.size) (hnb : ¬ busy (b / 512))
    (hl : (f.secs (b / 512)).dirty = true ∨ (f.secs (b / 512)).vers.length ≤ 1)
    (hne : (f.secs (b / 512)).vers ≠ []) : CleanPhys (f.synced busy) b := by
  refine ⟨by simp [OsFile.synced]; exact hb, fun v hv => ?_⟩
  rw [synced_rawAt]
  simp only [OsFile.synced] at hv
  split at hv
  · simp only [List.mem_singleton] at hv; subst hv; rfl
  · rename_i hn
    have hd : (f.secs (b / 512)).dirty = false := by
      cases h : (f.secs (b / 512)).dirty
      · rfl
      · exact absurd ⟨h, hnb⟩ hn
    rcases hl with hl | hl
    · rw [hd] at hl; cases hl
    · -- one version: it is the last
      obtain ⟨w, hw⟩ : ∃ w, (f.secs (b / 512)).vers = [w] := by
        cases h : (f.secs (b / 512)).vers with
        | nil => exact absurd h hne
        | cons w ws => cases ws with
          | nil => exact ⟨w, rfl⟩
          | cons w' ws' => rw [h] at hl; simp at hl
      rw [hw] at hv; simp only [List.mem_singleton] at hv; subst hv
      simp [OsFile.rawAt, Sector.last, hw]

theorem syncFailed_clean (b : Nat) (h : CleanPhys f b) : CleanPhys (f.syncFailed busy) b := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun v hv => ?_⟩
  rw [syncFailed_rawAt]
  simp only [OsFile.syncFailed] at hv
  split at hv <;> exact h2 v hv

theorem synced_vers (n : Nat) (h : (f.secs n).vers ≠ []) : ((f.synced busy).secs n).vers ≠ [] := by
  simp only [OsFile.synced]; split
  · simp
  · exact h

theorem syncFailed_vers (n : Nat) (h : (f.secs n).vers ≠ []) :
    ((f.syncFailed busy).secs n).vers ≠ [] := by
  simp only [OsFile.syncFailed]; split
  · exact h
  · exact h

end sync

/-! ## Replacing a file by one with the same contents -/

section sameCur
variable {st : OsState} {i : Ino} {f f' : OsFile}

theorem sizes_setFile_sameCur (hf : st.file i = some f) (hsize : f'.size = f.size) :
    ∀ q, (st.setFile i f').size q = st.size q :=
  size_setFile_same hf hsize

theorem inflightAt_setFile_sameCur (hf : st.file i = some f) (hsize : f'.size = f.size) :
    ∀ q b, InflightAt (st.setFile i f') q b = InflightAt st q b :=
  inflightAt_congr (sizes_setFile_sameCur hf hsize) rfl

theorem cellView_setFile_sameCur (hwf : OsWf st) (hwf' : OsWf (st.setFile i f'))
    (hf : st.file i = some f) (hcur : f'.contents = f.contents) (hsize : f'.size = f.size) :
    cellView (st.setFile i f') = cellView st := by
  have hI := inflightAt_setFile_sameCur hf hsize
  refine cellView_congr' hwf hwf' rfl (cellByte_congr (fun q => ?_) hI) hI
  rw [file_setFile]; split
  · subst_vars; rw [hf]; simp [hcur]
  · rfl

/-- The ghost maps after replacing the file `i` by `f'`, with the same contents, and its `OsMeta`
by `m'`, and the bytes `xs` the client holds by `ys`, with the same values: the clean bytes of `f`
stay clean, and those `ys` marks clean are clean. -/
theorem osCoh_setFile_sameCur {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt)
    (hf : st.file i = some f) (hcur : f'.contents = f.contents) (hsize : f'.size = f.size)
    {m' : OsMeta} (hmo : MetaOk (st.setFile i f') i m' f') (lo : Nat) (xs ys : List (w8 × Bool))
    (hys : ys.length = xs.length)
    (hxs : ∀ k (hk : k < xs.length), Γb !! (i, lo + k) = some xs[k])
    (hval : ∀ k (hk : k < ys.length), ys[k].1 = (xs[k]'(hys ▸ hk)).1)
    (hkeep : ∀ b, CleanPhys f b → CleanPhys f' b)
    (hnew : ∀ k (hk : k < ys.length), ys[k].2 = true → CleanPhys f' (lo + k))
    (hnoI : ∀ b, ¬ InflightAt st i b) :
    OsCoh (st.setFile i f') (insertBytes i lo ys Γb) (<[i := m']> Γm) Γf Γt := by
  have hs := sizes_setFile_sameCur hf hsize
  have hI := inflightAt_setFile_sameCur hf hsize
  refine ⟨fun q => ?_, fun q m hm => ?_, fun q b x hx => ?_, fun q f1 b h1 hb => ?_,
    hcoh.fds, hcoh.toks, fun t ti h => ?_, hcoh.tok_alone, fun t ti h => ?_,
    fun t ti h => ?_⟩
  · rw [files_setFile, GMap.lookup_insert_eq_iff]
    split
    · simp
    · exact hcoh.meta_dom q
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
      have hk : b - lo < ys.length := by omega
      rw [List.getElem?_eq_getElem hk] at hx; cases hx
      have hk' : b - lo < xs.length := hys ▸ hk
      obtain ⟨f1, h1', hb, -⟩ := hcoh.bytes q (lo + (b - lo)) _ (hxs _ hk')
      rw [hf] at h1'; cases h1'
      refine ⟨f', file_setFile_eq st q f', ?_, fun hc => ⟨?_, by rw [hI]; exact hnoI b⟩⟩
      · rw [hcur, hval _ hk]; rw [show lo + (b - lo) = b by omega] at hb; exact hb
      · have := hnew _ hk hc; rwa [show lo + (b - lo) = b by omega] at this
    · obtain ⟨f1, h1, hb, hc⟩ := hcoh.bytes q b x hx
      by_cases hpq : i = q
      · subst hpq; rw [hf] at h1; cases h1
        refine ⟨f', file_setFile_eq st i f', by rw [hcur]; exact hb, fun hx2 => ?_⟩
        obtain ⟨hc1, hc2⟩ := hc hx2
        exact ⟨hkeep b hc1, by rw [hI]; exact hc2⟩
      · refine ⟨f1, by rw [file_setFile_ne st f' hpq]; exact h1, hb, fun hx2 => ?_⟩
        obtain ⟨hc1, hc2⟩ := hc hx2
        exact ⟨hc1, by rw [hI]; exact hc2⟩
  · rw [lookup_insertBytes]
    split
    · rename_i hr; rw [List.getElem?_eq_getElem (by omega)]; rfl
    · rw [file_setFile] at h1
      split at h1
      · subst_vars; cases h1; exact hcoh.bytes_full _ f b hf (by rw [← hsize]; exact hb)
      · exact hcoh.bytes_full q f1 b h1 hb
  · rw [reaches_congr hs]; exact hcoh.tok_q t ti h
  · obtain ⟨f1, h1, hsv⟩ := hcoh.tok_saved t ti h
    rw [affRange_congr hs]
    rw [file_setFile]; split
    · subst_vars; rw [hf] at h1; cases h1; exact ⟨f', rfl, by rw [hcur]; exact hsv⟩
    · exact ⟨f1, h1, hsv⟩
  · intro j hj
    obtain ⟨hjl, f1, h1, hc⟩ := hcoh.tok_clean t ti h j hj
    have hlo : affLo (st.setFile i f') ti.c = affLo st ti.c := by unfold affLo; rw [hs]
    have hhi : affHi (st.setFile i f') ti.c = affHi st ti.c := by unfold affHi; rw [hs]
    rw [hlo, hhi]
    refine ⟨hjl, ?_⟩
    rw [file_setFile]; split
    · subst_vars; rw [hf] at h1; cases h1; exact ⟨f', rfl, hkeep _ hc⟩
    · exact ⟨f1, h1, hc⟩

end sameCur

/-! ## Changing the mappings -/

section maps

theorem size_congr_files {st st' : OsState} (h : st'.fs.files = st.fs.files) :
    ∀ i, st'.size i = st.size i := by
  intro i; simp [OsState.size, OsState.file, h]

theorem cellView_lookup_congr {st st' : OsState} (hwf : OsWf st) (hwf' : OsWf st')
    (hfi : st'.fs.files = st.fs.files) (hin : st'.proc.inflight = st.proc.inflight) (l : Loc)
    (hl : ∀ i k, MapsTo st' l i k ↔ MapsTo st l i k) : cellView st' !! l = cellView st !! l := by
  have hs := size_congr_files hfi
  have hI := inflightAt_congr hs hin
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
      m'.size = m.size ∧ m'.lo = m.lo ∧ m'.hi = m.hi ∧ m'.ok = m.ok ∧ m'.dur = m.dur ∧
      m'.zero = m.zero ∧ m'.vk = m.vk ∧ m'.dz = m.dz ∧
      ∀ b len, m'.maps !! b = some len ↔ X !! b = some ⟨q, len⟩) :
    OsCoh { st with proc := { st.proc with maps := X } } Γb Γm' Γf Γt :=
  { hcoh with
    meta_dom := fun q => (hdom q).trans (hcoh.meta_dom q)
    meta_some := fun q m' h => by
      obtain ⟨m, hm, h1, h2, h3, h5, h7, h8, h9, h10, h6⟩ := hsome q m' h
      obtain ⟨f, hf, hmo⟩ := hcoh.meta_some q m hm
      exact ⟨f, hf, ⟨h1 ▸ hmo.size, h2 ▸ hmo.lo, h3 ▸ hmo.hi,
        fun hok => hmo.ok (h5 ▸ hok), h6,
        fun t c ht hc => by rw [h2, h3]; exact hmo.targets t c ht hc, h7 ▸ hmo.dur,
        fun hz => hmo.zero (h8 ▸ hz), fun ns hns => hmo.vk ns (h9 ▸ hns),
        fun z hz => hmo.dz z (h10 ▸ hz)⟩⟩ }

end maps


/-! ## Zeros past the size (`OsMeta.zero`) -/

/-- The page cache holds zeros past the size. -/
def ZeroPast (f : OsFile) : Prop := ∀ b, f.size ≤ b → f.rawAt b = 0

theorem secHits_of_mem {lo hi b : Nat} (h1 : lo ≤ b) (h2 : b < hi) : secHits lo hi (b / 512) = true := by
  have := Nat.div_add_mod b 512
  have := Nat.mod_lt b (show 0 < 512 by decide)
  simp only [secHits, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

/-- A change keeps zeros past the size, if every byte below the old size it cuts off is in its range. -/
theorem zero_change {f : OsFile} {c : List w8} {lo hi : Nat} (hz : ZeroPast f)
    (hcov : ∀ b, c.length ≤ b → b < f.size → lo ≤ b ∧ b < hi) : ZeroPast (f.change c lo hi) := by
  intro b hb
  have hbc : c.length ≤ b := hb
  rw [rawAt_def]
  simp only [OsFile.change]
  split
  · have hl : ({ vers := (f.secs (b / 512)).vers ++ [secOf c (b / 512)], dirty := true } :
        Sector).last = secOf c (b / 512) := by simp [Sector.last]
    rw [hl, secOf_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none hbc]; rfl
  · rename_i hn
    rw [← rawAt_def]
    by_cases hs : f.size ≤ b
    · exact hz b hs
    · obtain ⟨h1, h2⟩ := hcov b hbc (by omega)
      exact absurd (secHits_of_mem h1 h2) hn

theorem written_length_ge (f : OsFile) (off : Nat) (d : List w8) :
    f.size ≤ (f.written off d).length := by
  unfold OsFile.written
  split
  · simp [OsFile.contents]
  · simp [OsFile.resized]; omega

theorem zero_landWrite {f : OsFile} (off : Nat) (data : List w8) (k : Nat) (hz : ZeroPast f) :
    ZeroPast (f.landWrite off data k) := by
  unfold OsFile.landWrite
  split
  · exact hz
  · exact zero_change hz (fun b h1 h2 => by have := written_length_ge f off (data.take k); omega)

theorem zero_truncate {f : OsFile} (sz : Nat) (hz : ZeroPast f) : ZeroPast (f.truncate sz) := by
  unfold OsFile.truncate
  exact zero_change hz (fun b h1 h2 => by rw [resized_length] at h1; omega)

theorem zero_synced {f : OsFile} {busy : Nat → Prop} [DecidablePred busy] (hz : ZeroPast f) :
    ZeroPast (f.synced busy) := fun b hb => by rw [synced_rawAt]; exact hz b hb

theorem zero_syncFailed {f : OsFile} {busy : Nat → Prop} [DecidablePred busy] (hz : ZeroPast f) :
    ZeroPast (f.syncFailed busy) := fun b hb => by rw [syncFailed_rawAt]; exact hz b hb

/-- **A file that holds zeros past its size grows with zeros.** -/
theorem resized_drop_zero {f : OsFile} (hz : ZeroPast f) (sz : Nat) :
    (f.resized sz).drop f.size = List.replicate (sz - f.size) 0 := by
  apply List.ext_getElem
  · simp [OsFile.resized]
  · intro n h1 h2
    simp only [List.getElem_drop, List.getElem_replicate]
    simp only [OsFile.resized, List.getElem_map, List.getElem_range]
    exact hz _ (by omega)

theorem zero_newFile : ZeroPast newFile := by
  intro b _
  have h := secOf_getD [] b
  simp only [List.getD_nil] at h
  simpa [newFile, OsFile.ofBytes, OsFile.ofDisk, rawAt_def, Sector.last] using h

end Fs
end Perennial
