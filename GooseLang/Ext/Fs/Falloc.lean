/-
WP specs of the Linux file extension's `fallocate` (`FallocStart`, `FallocFinish` for mode 0, a
truncate to `max size (off + len)`; `FallocKeep` for `FALLOC_FL_KEEP_SIZE`, no visible change) and
of the OFD lock (`OfdLock`, trivial), as `Truncate.lean`'s and `wp_osFlock`.
-/
module

public import GooseLang.Ext.Fs.Truncate

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- `fcntl(fd, F_OFD_SETLK[W], ...)`: any errno, nothing changed (the lock state is not
modelled). -/
theorem wp_osOfdLock (fd cmd : w64) (dq : DFrac) (d : OsFd) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      (∀ e : w64, osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "OfdLock" (Val (PairV (#fd) (#cmd)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_step "OfdLock" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, cmd, 0, d, rfl, hfd, rfl, rfl⟩, mapsFresh_same rfl,
      heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', cmd', e, d', hv, -, rfl, rfl⟩ := Hst
  imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, Γf, Γt
  iframe
  isplitr
  · ipureintro; exact ⟨hwf, hcoh⟩
  iapply wp_value'
  iapply HΦ $$ Hfd

/-- `fallocate(fd, FALLOC_FL_KEEP_SIZE, off, len)`: any errno, no visible change. It may allocate
blocks past the end (`OsFile.keepAlloc`), so it takes the file's `OsMeta` whole. -/
theorem wp_osFallocKeep (fd off len : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (hE : ↑osN ⊆ E)
    (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      (∀ e : w64, osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FallocKeep" (Val (PairV (#fd) (PairV (#off) (#len))))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm HΦ
  iapply wp_os_step "FallocKeep" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %Hnt
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hnoI : ∀ i, ¬ InflightAt st d.ino i := by
    rintro i ⟨t, c, ht, hcp, -⟩; exact noTok_of_whole hcoh Hnt t c ht hcp
  have hszf := hwf.sizes d.ino f hf
  have hvf : ∀ n, (f.secs n).vers ≠ [] := fun n => hwf.vers d.ino f n hf
  have hwfK : OsWf (st.setFile d.ino f.keepAlloc) :=
    osWf_setFile_sameCur hwf hf rfl hszf (fun n => hvf n)
  have hcur : f.keepAlloc.contents = f.contents := rfl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, _, ⟨fd, off, len, 0, d, f, rfl, hfd, hwr, hoff, hlen, hf, rfl, rfl⟩,
      mapsFresh_same rfl, heapRendered_same hwfK rfl (cellView_setFile_sameCur hwf hwfK hf hcur rfl)
        Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', off', len', e, d', f', hv, hfd', -, -, -, hf', rfl, rfl⟩ := Hst
  injection hv with h1 h2
  cases go.intoVal_inj h1
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  rw [hf] at hf'; cases hf'
  imod gAuth_update _ _ _ _ _ m $$ HAm Hm with ⟨HAm, Hm⟩
  imod cells_same hwf hwfK Hr Hfr rfl (cellView_setFile_sameCur hwf hwfK hf hcur rfl)
    $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, _, Γf, Γt
  have hs := sizes_setFile_sameCur (f' := f.keepAlloc) hf rfl
  have htr : tokRes gooseOsGS (st.setFile d.ino f.keepAlloc) Γt = tokRes (gooseOsGS (L := L)) st Γt := by
    unfold tokRes; simp only [affLo_congr hs]
  rw [htr]
  iframe
  isplitr
  · ipureintro
    refine ⟨hwfK, osCoh_setFile_sameCur (f' := f.keepAlloc) hcoh hf hcur rfl ?_ 0 [] []
      rfl (fun k hk => absurd hk (by simp)) (fun k hk => absurd hk (by simp)) (fun b hb => hb)
      (fun k hk => absurd hk (by simp)) hnoI⟩
    exact ⟨hmo.size, hmo.lo, hmo.hi, hmo.ok, hmo.maps,
      fun t c ht hcp => absurd hcp (noTok_of_whole hcoh Hnt t c ht), hmo.dur, hmo.zero, hmo.vk,
      hmo.dz⟩
  iapply wp_value'
  iapply HΦ $$ Hfd Hm

/-- The first step of `fallocate(fd, 0, off, len)`, a truncate to `max size (off + len)` in
flight, as `wp_osFtruncateStart`. -/
theorem wp_osFallocStart (fd off len : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (hi : Nat)
    (hE : ↑osN ⊆ E) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt)
    (hhi : MapsBelow m.maps hi) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      mcellsAny m.maps m.size hi -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗
        ftTok (L := L) t d.ino (max m.size (off.toNat + len.toNat)) m -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FallocStart" (Val (PairV (#fd) (PairV (#off) (#len))))) @ s; E
        {{ Φ }} := by
  obtain ⟨S, hS⟩ : ∃ S, S = max m.size (off.toNat + len.toNat) := ⟨_, rfl⟩
  rw [← hS]
  have hgrow : m.size ≤ S := by rw [hS]; exact Nat.le_max_left _ _
  iintro #Hinv Hfd Hm Hc HΦ
  iapply wp_os_step "FallocStart" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
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
  have hfree : ∀ i, Affects st ⟨d.ino, .truncate S⟩ i → ¬ InflightAt st d.ino i := by
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
    have hwf0 := osWf_addTok (t := t0) (c := ⟨d.ino, .truncate S⟩) hwf ht0 hf hfree
    exact ⟨_, _, st.addInflight t0 ⟨d.ino, .truncate S⟩,
      ⟨fd, off, len, t0, d, rfl, hfd, hwr, hoff, hlen, hnbusy, ht0, hc0, by rw [hsz, ← hS], rfl⟩,
      mapsFresh_same rfl, heapRendered_render hwf0 rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', off', len', t, d', hv, hfd', -, -, -, -, ht, -, hst', rfl⟩ := Hst
  injection hv with h1 h2
  injection h2 with h3 h4
  cases go.intoVal_inj h1; cases go.intoVal_inj h3; cases go.intoVal_inj h4
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  rw [hsz, ← hS] at hst'
  subst hst'
  rw [show ∀ c', st.addInflight t c' = (st.setProc { st.proc with inflight := <[t := c']> st.proc.inflight })
    from fun _ => rfl] at Hr Hfr ⊢
  generalize hc : (⟨d.ino, .truncate S⟩ : OsChange) = c at hfree Hr Hfr ⊢
  have hcp : c.ino = d.ino := by rw [← hc]
  have hlo : affLo st c = m.size := by rw [← hc]; simp [affLo, hsz]; omega
  have hhi' : affHi st c = m.size := by rw [← hc]; simp [affHi, hsz]
  have haff : ∀ i, Affects st c i ↔ m.size ≤ i := by
    intro i; rw [← hc]; simp [Affects, hsz]; omega
  have hwf1 := osWf_addTok (t := t) (c := c) hwf ht (hcp ▸ hf) (hcp ▸ hfree)
  have hcoh1 := osCoh_addTok (t := t) (q := 1) (m := m) (om := ftMeta m S)
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
  imod meta_replace _ (q := 1) (om := ftMeta m S) (fun h1 => absurd rfl h1)
    $$ [HAm Hm] with ⟨HAm, Hm⟩
  · iframe
  have hΓt : Γt !! t = none := by
    have := hcoh.toks t; rw [ht] at this
    cases h0 : Γt !! t
    · rfl
    · rw [h0] at this; cases this
  imod gAuth_insert _ _ _ t ⟨c, 1, [], ftMeta m S, []⟩ hΓt $$ HAt with ⟨HAt, Ht⟩
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells
  isplitl [Htok Hm]
  · isplitr
    · ipureintro; exact ⟨hwf1, hcoh1⟩
    rw [show tokRes (gooseOsGS (L := L)) (st.setProc { st.proc with inflight := <[t := c]> st.proc.inflight })
        (<[t := ⟨c, 1, [], ftMeta m S, []⟩]> Γt) =
      tokRes gooseOsGS st (<[t := ⟨c, 1, [], ftMeta m S, []⟩]> Γt) from rfl]
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

/-- The second step of `fallocate(fd, 0, ...)`: on success the file grown (`osGrown`, its new
bytes what the sectors hold past the old size); on failure it may have grown to any size between,
and the client gets nothing back. -/
theorem wp_osFallocFinish (t : Nat) (p : Ino) (sz : Nat) (m : OsMeta) (hi : Nat)
    (hE : ↑osN ⊆ E) (hgrow : m.size ≤ sz) (hhi : MapsBelow m.maps hi) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ ftTok (L := L) t p sz m -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ osGrown (L := L) p m sz hi) ∨ ⌜e ≠ 0⌝) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FallocFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_os_step "FallocFinish" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
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
      e' = Val (#e) ∧ ((e = 0 ∧ f2 = f.truncate sz) ∨ e ≠ 0) := by
    rcases hrest with ⟨h1, h2⟩ | ⟨e, he, h2, h1 | ⟨n, hn1, hn2, h1⟩⟩
    · exact ⟨_, 0, hgT, h1, h2, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨f, e, grownFile_self hszf.2 (by omega),
        by rw [h1]; exact (setFile_self (st := st.doneInflight t') hf).symm, h2, .inr he⟩
    · exact ⟨_, e, grownFile_truncate hszf.1 hn1 hn2, h1, h2, .inr he⟩
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
  rcases hne with ⟨rfl, rfl⟩ | he
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
    ipureintro; exact he

end specs

end Fs
end Perennial
