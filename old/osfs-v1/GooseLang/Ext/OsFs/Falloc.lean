/-
WP specs of the Linux file extension's `fallocate` (`FallocStart`, `FallocFinish` for mode 0, a
truncate to `max size (off + len)`; `FallocKeep` for `FALLOC_FL_KEEP_SIZE`, no visible change) and
of the OFD lock (`OfdLock`, trivial), as `Truncate.lean`'s and `wp_osFlock`.
-/
module

public import GooseLang.Ext.OsFs.Truncate

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-- The operations of this file: they leave the namespace alone. -/
def FallocOp (o : String) : Prop := o ∈ ["OfdLock", "FallocKeep", "FallocStart", "FallocFinish"]

theorem nsFrame_falloc [GooseExts] [GoGlobalContext] {o : String} (ho : FallocOp o) {v : val}
    {st st' : OsState} {e' : Expr} (h : IsOsStep o v st e' st') : NsFrame st st' := by
  simp only [FallocOp, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · obtain ⟨_, _, _, _, -, -, rfl, -⟩ := h; exact NsFrame.refl _
  · obtain ⟨_, _, _, _, _, -, -, -, -, -, rfl, -⟩ := h; exact NsFrame.refl _
  · obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, rfl, -⟩ := h; exact nsFrame_inflight _ _
  · obtain ⟨t, p, sz, f, -, -, hf, hres⟩ := h
    have h0 := nsFrame_inflight st (GMap.delete t st.inflight)
    rcases hres with ⟨rfl, -⟩ | ⟨-, -, -, rfl | ⟨n, -, -, rfl⟩⟩
    · exact h0.trans (nsFrame_setFile_of _ p _ f (by simpa [OsState.file] using hf))
    · exact h0
    · exact h0.trans (nsFrame_setFile_of _ p _ f (by simpa [OsState.file] using hf))

section step
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- `wp_os_step` for the operations of this file. -/
theorem wp_os_stepF (o : String) (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false)
    (hE : ↑osN ⊆ E) (ho : FallocOp o) :
    ⊢ osInv (L := L) -∗
      (∀ st Γb Γm Γf Γt h, osWorld st Γb Γm Γf Γt h ==∗
        ⌜∃ e' h' st', OsStep o v h st () e' h' st' ()⌝ ∗
        ▷ ∀ e' h' st', ⌜OsStep o v h st () e' h' st' ()⌝ ==∗
          ∃ Γb' Γm' Γf' Γt', osWorld st' Γb' Γm' Γf' Γt' h' ∗ WP e' @ s; E {{ Φ }}) -∗
      WP (ExternalOp osFsExt.name o (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv HF
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl -
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx osCtxF
  icases Hl with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩, Hns⟩
  unfold osInv
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%cv, %n, Hv', Hcells⟩
  icases gVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  imod HF $$ %σ %Γb %Γm %Γf %Γt %h [HAb HAm HAf HAt Htok Hcells Hheap] with ⟨%Hex, Hcont⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨e', h', st', Hst⟩ := Hex
    exact ⟨e', h', st', g, Hst⟩
  inext
  iintro %e' %h' %σ' %g' %Hst -
  imod Hclose2
  imod Hcont $$ %e' %h' %σ' %Hst with ⟨%Γb', %Γm', %Γf', %Γt', Hw, Hwp⟩
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hheap⟩
  imod gVar_update _ _ _ (cellView σ', GMap.size σ'.inflight) $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hcells] with -
  · inext; iexists (cellView σ'), (GMap.size σ'.inflight); iframe
  imodintro
  iframe Hheap Hwp
  isplitl [HAb HAm HAf HAt Htok Hv Hns]
  · iapply (os_local_ctx_eq σ').mpr
    unfold osCtx osCtxF
    isplitl [HAb HAm HAf HAt Htok Hv]
    · iexists Γb', Γm', Γf', Γt'
      iframe
      ipureintro; exact Hwc'
    · iapply nsCtx_frame _ (nsFrame_falloc ho Hst.1) $$ Hns
  · have : (ExtInterp.globalCtx (E := osFsExt) (extGlobalGS osFsExt) g' : IProp GF) =
        iprop(True) := rfl
    rw [this]; itrivial

end step

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- `fcntl(fd, F_OFD_SETLK[W], ...)`: any errno, nothing changed (the lock state is not
modelled). -/
theorem wp_osOfdLock (fd cmd : w64) (dq : DFrac) (d : OsFd) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      (∀ e : w64, osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "OfdLock" (Val (PairV (#fd) (#cmd)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_stepF "OfdLock" _ Φ (by simp [val.isPanic]) hE (by simp [FallocOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, cmd, 0, d, rfl, hfd, rfl, rfl⟩, mapsFresh_same rfl,
      heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
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

/-- `fallocate(fd, FALLOC_FL_KEEP_SIZE, off, len)`: any errno, no visible change. -/
theorem wp_osFallocKeep (fd off len : w64) (dq : DFrac) (d : OsFd) (hE : ↑osN ⊆ E)
    (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      (∀ e : w64, osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "FallocKeep" (Val (PairV (#fd) (PairV (#off) (#len))))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_stepF "FallocKeep" _ Φ (by simp [val.isPanic]) hE (by simp [FallocOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, off, len, 0, d, rfl, hfd, hwr, hoff, hlen, rfl, rfl⟩, mapsFresh_same rfl,
      heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', off', len', e, d', hv, -, -, -, -, rfl, rfl⟩ := Hst
  imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, Γf, Γt
  iframe
  isplitr
  · ipureintro; exact ⟨hwf, hcoh⟩
  iapply wp_value'
  iapply HΦ $$ Hfd

/-- The first step of `fallocate(fd, 0, off, len)`, a truncate to `max size (off + len)` in
flight, as `wp_osFtruncateStart`. -/
theorem wp_osFallocStart (fd off len : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (hi : Nat)
    (hE : ↑osN ⊆ E) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt)
    (hhi : MapsBelow m.maps hi) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.path (DFrac.own 1) (some m) -∗
      mcellsAny m.maps m.size hi -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗ ftTok (L := L) t d.path (max m.size (off.toNat + len.toNat)) m -∗ Φ (osTokV t)) -∗
      WP (ExternalOp osFsExt.name "FallocStart" (Val (PairV (#fd) (PairV (#off) (#len))))) @ s; E
        {{ Φ }} := by
  obtain ⟨S, hS⟩ : ∃ S, S = max m.size (off.toNat + len.toNat) := ⟨_, rfl⟩
  rw [← hS]
  have hgrow : m.size ≤ S := by rw [hS]; exact Nat.le_max_left _ _
  iintro #Hinv Hfd Hm Hc HΦ
  iapply wp_os_stepF "FallocStart" _ Φ (by simp [val.isPanic]) hE (by simp [FallocOp]) $$ Hinv
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
  have hfree : ∀ i, Affects st ⟨d.path, .truncate S⟩ i → ¬ InflightAt st d.path i := by
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
    have hwf0 := osWf_addTok (t := t0) (c := ⟨d.path, .truncate S⟩) hwf ht0 hf hfree
    exact ⟨_, _, { st with inflight := <[t0 := ⟨d.path, .truncate S⟩]> st.inflight },
      ⟨fd, off, len, t0, d, rfl, hfd, hwr, hoff, hlen, hnbusy, ht0, by rw [hsz, ← hS], rfl⟩,
      mapsFresh_same rfl, heapRendered_render hwf0 rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', off', len', t, d', hv, hfd', -, -, -, -, ht, hst', rfl⟩ := Hst
  injection hv with h1 h2
  injection h2 with h3 h4
  cases go.intoVal_inj h1; cases go.intoVal_inj h3; cases go.intoVal_inj h4
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  rw [hsz, ← hS] at hst'
  subst hst'
  generalize hc : (⟨d.path, .truncate S⟩ : OsChange) = c at hfree Hr Hfr ⊢
  have hcp : c.path = d.path := by rw [← hc]
  have hlo : affLo st c = m.size := by rw [← hc]; simp [affLo, hsz]; omega
  have hhi' : affHi st c = m.size := by rw [← hc]; simp [affHi, hsz]
  have haff : ∀ i, Affects st c i ↔ m.size ≤ i := by
    intro i; rw [← hc]; simp [Affects, hsz]; omega
  have hwf1 := osWf_addTok (t := t) (c := c) hwf ht (hcp ▸ hf) (hcp ▸ hfree)
  have hcoh1 := osCoh_addTok (t := t) (q := 1) (m := m) (om := ftMeta m S)
    (xs := []) hcoh hcp hf Hml
    ⟨rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_max_left _ _,
      by rw [← hc]; simp only [OsChange.target, ftMeta]; have := hmo.lo; have := hmo.size
         have := (hwf.sizes d.path f hf).1; omega,
      by rw [← hc]; simp only [OsChange.target, ftMeta]; omega, rfl⟩
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
    rw [show tokRes (gooseOsGS (L := L)) { st with inflight := <[t := c]> st.inflight }
        (<[t := ⟨c, 1, [], ftMeta m S, []⟩]> Γt) =
      tokRes gooseOsGS st (<[t := ⟨c, 1, [], ftMeta m S, []⟩]> Γt) from rfl]
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

/-- The second step of `fallocate(fd, 0, ...)`: on success the file grown (`osGrown`); on failure
it may have grown to any size between, and the client gets nothing back. -/
theorem wp_osFallocFinish (t : Nat) (p : GoString) (sz : Nat) (m : OsMeta) (hi : Nat)
    (hE : ↑osN ⊆ E) (hgrow : m.size ≤ sz) (hhi : MapsBelow m.maps hi) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ ftTok (L := L) t p sz m -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ osGrown (L := L) p m sz hi) ∨ ⌜e ≠ 0⌝) -∗
        Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "FallocFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_os_stepF "FallocFinish" _ Φ (by simp [val.isPanic]) hE (by simp [FallocOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold ftTok osTok
  generalize hti0 : (⟨⟨p, .truncate sz⟩, 1, [], ftMeta m sz, []⟩ : TokInfo) = ti
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
      ((e = 0 ∧ n = sz) ∨ e ≠ 0) := by
    rcases hrest with ⟨h1, h2⟩ | ⟨e, he, h2, h1 | ⟨n, hn1, hn2, h1⟩⟩
    · exact ⟨sz, 0, by omega, Nat.le_refl _, h1, h2, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨f.cur.length, e, Nat.le_refl _, by omega, by rw [h1, hst1], h2, .inr he⟩
    · exact ⟨n, e, hn1, hn2, h1, h2, .inr he⟩
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
  rcases hne with ⟨rfl, rfl⟩ | he
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
    ipureintro; exact he

end specs

end Perennial
