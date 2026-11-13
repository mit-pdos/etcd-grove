/-
The shared mode of the tree: `open(2)` with `O_TRUNC` of a name holding a file (`wp_osOpenTruncS`),
for the WAL's `filePipeline.alloc` (`O_CREATE|O_TRUNC` of `N.tmp`, which may be left over from an
earlier run). Untrusted.

The semantics (`OpenEffect`, `Impl.lean`): an existing file is truncated to size 0 in the open's
step (the change `OsChange.ofResize i f 0 true` announced and landed at once, stamped), no entry logged;
on failure the truncation may or may not have happened; the step needs no change in flight on the
file (`¬ BusyAt`), which the file's whole `OsMeta` gives (`tokRes_meta_whole`). So the spec takes
what a resize's first step takes (`wp_osResizeStart` with target 0: the `OsMeta`, the bytes it cuts
off, the client's halves of the mapped cells) and gives back what its landing gives
(`rsDone true i 0 0 m n`), or, without the truncation, what it took.

`O_CREAT|O_TRUNC` of an absent name is `wp_osOpenCreateS'` (`TreeSharedCreate.lean`), whose `O_TRUNC`
premise is "clear, or the name absent".

The proof (2026-11-13, branch `wal-osau4`): `osWorld_trunc`, the world update of the truncation as
the two steps of a resize to 0 (`resize_start_world`, `wp_osResizeStart`'s body as a world update,
then `resize_done_world`) through the state between them (`startState`, a fresh token), whose heap
is rendered for it (`heapRendered_mid`); `truncSt_eq` says the two steps make `OpenEffect`'s state.
The tree's part is `wp_osOpenFileS'`'s, the truncation a `TreeFrame` step.
-/
module

public import GooseLang.Ext.Fs.TreeSharedCreate
public import GooseLang.Ext.Fs.Truncate

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## The one-step truncation: a resize to 0 announced and landed in the open's step -/

/-- The state after `open(O_TRUNC)` truncates the file `i` (was `f`), as `OpenEffect` writes it. -/
def truncSt (st : OsState) (i : Ino) (f : OsFile) : OsState :=
  st.stampFile i (fun n => let c := OsChange.ofResize i f 0 true; (f.announce c n).land c c.hi 0)

/-- The truncation is the two steps of a resize to 0 under a fresh token `t`. -/
theorem truncSt_eq (st : OsState) (i : Ino) (f : OsFile) (t : Nat)
    (ht : st.proc.inflight !! t = none) :
    ((startState st i f (OsChange.ofResize i f 0 true) t).doneInflight t).setFile i
      ((f.announce (OsChange.ofResize i f 0 true) (st.fs.stamp + 1)).land (OsChange.ofResize i f 0 true)
        (OsChange.ofResize i f 0 true).hi 0) = truncSt st i f := by
  simp only [truncSt, startState, OsState.doneInflight, OsState.setFile, OsState.addInflight,
    OsState.stampFile]
  congr 2
  · apply GMap.ext; intro k
    simp only [GMap.lookup_insert_eq_iff]
    split <;> rfl
  · apply GMap.ext; intro k
    rw [GMap.lookup_delete_iff]; split
    · subst_vars; exact ht.symm
    · rw [GMap.lookup_insert_ne]; assumption

open Classical in
/-- A step from `A` to `C` seen from a state `B` between them (no mapping changes), the heap
re-rendered for `B`. -/
theorem heapRendered_mid [GooseExts] [GoGlobalContext] {A B C : OsState}
    {h h' : GMap Loc (NonAtomic val)} (hB : B.proc.maps = A.proc.maps)
    (hC : C.proc.maps = A.proc.maps) (Hr : HeapRendered A C h h') :
    HeapRendered B C (renderHeap B h) h' := by
  have hMB : ∀ l, Mapped B l ↔ Mapped A l := by intro l; simp only [Mapped, MapsTo, hB]
  have hMC : ∀ l, Mapped C l ↔ Mapped A l := by intro l; simp only [Mapped, MapsTo, hC]
  have hlk : ∀ l, renderHeap B h !! l = (if hm : Mapped B l then
      (h !! l).map (fun x => (x.1, cellVal B hm.choose hm.choose_spec.choose)) else h !! l) :=
    fun _ => rfl
  obtain ⟨H1, -, -, H4⟩ := Hr
  refine ⟨fun l p i hpi hmd => ?_, fun l p i hpi hn => ?_, fun l hn hmd => ?_, fun l hn hn' => ?_⟩
  · obtain ⟨m, v0, h1, h2⟩ := H1 l p i hpi ((hMB l).1 hmd)
    exact ⟨m, _, by rw [hlk, dif_pos hmd, h1]; rfl, h2⟩
  · exact absurd ((hMB l).2 ((hMC l).1 ⟨p, i, hpi⟩)) hn
  · exact absurd ((hMC l).2 ((hMB l).1 hmd)) hn
  · rw [hlk, dif_neg hn']; exact H4 l hn (fun h => hn' ((hMB l).2 h))

open Classical in
/-- `HeapRendered` sees the source state only through its mappings, and the target only through its
files, changes in flight and mappings. -/
theorem heapRendered_congr [GooseExts] [GoGlobalContext] {A A' C C' : OsState}
    {h h' : GMap Loc (NonAtomic val)} (hA : A'.proc.maps = A.proc.maps)
    (hf : C'.fs.files = C.fs.files) (hi : C'.proc.inflight = C.proc.inflight)
    (hm : C'.proc.maps = C.proc.maps) (Hr : HeapRendered A C h h') : HeapRendered A' C' h h' := by
  have e1 : ∀ l i b, MapsTo C' l i b ↔ MapsTo C l i b := by intro l i b; simp only [MapsTo, hm]
  have e1' : ∀ l, Mapped C' l ↔ Mapped C l := fun l =>
    ⟨fun ⟨i, b, h⟩ => ⟨i, b, (e1 l i b).1 h⟩, fun ⟨i, b, h⟩ => ⟨i, b, (e1 l i b).2 h⟩⟩
  have e2 : ∀ l, Mapped A' l ↔ Mapped A l := by intro l; simp only [Mapped, MapsTo, hA]
  have e3 : ∀ i b, cellVal C' i b = cellVal C i b := by
    intro i b
    have hfi : C'.file i = C.file i := by simp only [OsState.file, hf]
    simp only [cellVal, hfi, inflightAt_congr hi]
  obtain ⟨H1, H2, H3, H4⟩ := Hr
  refine ⟨fun l i b h1 h2 => ?_, fun l i b h1 h2 => ?_, fun l h1 h2 => ?_, fun l h1 h2 => ?_⟩
  · rw [e3]; exact H1 l i b ((e1 l i b).1 h1) ((e2 l).1 h2)
  · rw [e3]; exact H2 l i b ((e1 l i b).1 h1) (fun h => h2 ((e2 l).2 h))
  · exact H3 l (fun h => h1 ((e1' l).2 h)) ((e2 l).1 h2)
  · exact H4 l (fun h => h1 ((e1' l).2 h)) (fun h => h2 ((e2 l).2 h))

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- No mapped cell in an empty range. -/
theorem mcellsAny_empty (M : GMap Loc Nat) (n : Nat) : ⊢ mcellsAny (GF := GF) M n n := by
  unfold mcellsAny
  refine (BigSepM.bigSepM_intro (P := (emp : IProp GF)) ?_)
  intro b len _
  iintro -
  iexists (fun _ => (#() : val))
  unfold cellsR
  rw [Nat.sub_self]
  simp only [List.range'_zero]
  iempintro

attribute [local instance] Classical.propDecidable in
/-- **The first step of a resize as a world update** (`wp_osResizeStart`'s body, for a step that
does more): the change `ofResize p f tg` put in flight under the fresh token `t`, the heap rendered
for it (`renderHeap`); the client's resources become the change's token. -/
theorem resize_start_world {st : OsState} {Γb Γm Γf Γt} {h : GMap Loc (NonAtomic val)}
    {tr : Bool} {p : Ino} {f : OsFile} {tg t : Nat} {m : OsMeta} {xs : List ByteG}
    (hf : st.file p = some f) (ht : st.proc.inflight !! t = none) (hlen : xs.length = m.size - tg) :
    ⊢ osWorld (L := L) st Γb Γm Γf Γt h -∗ osMeta (L := L) p (DFrac.own 1) m -∗
      osBytes (L := L) p (min m.size tg) (DFrac.own 1) xs -∗
      mcellsAny m.maps (min m.size tg) (rsHi tr m.size tg) ==∗
      (∃ Γb' Γm' Γf' Γt', osWorld (L := L) (startState st p f (OsChange.ofResize p f tg tr) t)
        Γb' Γm' Γf' Γt' (renderHeap (startState st p f (OsChange.ofResize p f tg tr) t) h)) ∗ rsTok (L := L) tr t p tg m xs (st.fs.stamp + 1) := by
  iintro Hw Hm Hbs Hc
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osMeta osBytes
  icases bytesG_lookup _ p _ _ xs Γb $$ HAb Hbs with %Hbl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %Hnt
  obtain ⟨f0, hf0, hmo⟩ := coh_meta hcoh Hml
  rw [hf] at hf0; cases hf0
  have hni := noInfl_of_noTok hcoh Hnt
  let c := OsChange.ofResize p f tg tr
  have hclo : c.lo = min m.size tg := by simp [c, OsChange.ofResize, hmo.size]
  have hchi : c.hi = rsHi tr m.size tg := by simp [c, hmo.size]
  have hR := le_rsHi tr m.size tg
  have haff : ∀ i, inRange c.lo c.hi i = true ↔ min m.size tg ≤ i ∧ i < rsHi tr m.size tg := by
    intro i; rw [hclo, hchi]; simp [inRange]
  let n := st.fs.stamp + 1
  let ti : TokInfo := ⟨p, rsKind tr tg, n, m, rsAnn n xs⟩
  have hwf1 := osWf_start (c := c) hwf ht hf rfl hni
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  have Hr := heapRendered_render (st := st) (h := h) hwf1 rfl Hh
  have Hfr : MapsFresh st (startState st p f c t) h := mapsFresh_same rfl
  have hti : ti.Is c := ofResize_is p f tg tr n m _ hmo.size
  have hcoh1 := osCoh_start (c := c) hcoh ht hf Hml hmo Hnt ti hti rfl rfl rfl
    (by rw [hclo, hchi]; omega)
    (by show (rsAnn n xs).length = _; rw [rsAnn_length, hlen, hclo, hchi, ← hmo.size]; omega)
    (fun j hj => by
      simp only [ti, rsAnn, List.getElem_map] at hj ⊢
      have hj' : j < xs.length := by simpa using hj
      refine ⟨xs[j], ?_, rfl⟩
      rw [show c.lo = min f.size tg by simp [c, OsChange.ofResize], ← hmo.size]; exact Hbl j hj')
  have hI := inflightAt_start (c := c) (f := f) (p := p) ht
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmo.maps b1 l1).1 h1) ((hmo.maps b2 l2).1 h2) hne)
  unfold mcellsAny
  ihave Hc := (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
    iprop(∃ vf, cellsR b (min (min m.size tg) len)
      (min (rsHi tr m.size tg) len - min (min m.size tg) len) vf))).1 $$ Hc
  icases halves_mapsCells_ex (min m.size tg) (rsHi tr m.size tg) _ hdisj $$ Hc with ⟨%C, Hc, %hC⟩
  have hmapsC : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l p i ∧ inRange c.lo c.hi i = true := by
    intro l hl
    obtain ⟨i, b, len, hm, h1, h2, h3, rfl⟩ := (hC l).1 hl
    exact ⟨i, ⟨b, ⟨p, len⟩, (hmo.maps b len).1 ((GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
      (haff i).2 ⟨h1, h2⟩⟩
  have hTmem : ∀ l, l ∈ C.toList.map (·.1) ↔ (C !! l).isSome := by
    intro l; simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hkv, rfl⟩; rw [(GMap.mem_toList _ _ _).1 hkv]; rfl
    · intro hl; obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
      exact ⟨(l, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  have hTnd : (C.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := C)
  have hnoI : ∀ i, ¬ InflightAt st p i := by
    rintro i ⟨t', c', h1, h2, -⟩; exact hni t' c' h1 h2
  imod cells_step st _ h _ (C.toList.map (·.1)) C ∅ hwf hwf1 Hr Hfr (fun b m0 h0 => .inr h0) hTnd
    (fun l hl => by obtain ⟨i, hi, -⟩ := hmapsC l ((hTmem l).1 hl); exact .inl ⟨_, _, hi⟩)
    (fun l v hl => by
      have hs : (C !! l).isSome := by rw [hl]; rfl
      obtain ⟨i, hi, ha⟩ := hmapsC l hs
      exact ⟨(hTmem l).2 hs, _, by rw [cellView_mapsTo hwf hi, decide_eq_false (hnoI i)]⟩)
    (fun l v h => by simp at h)
    (fun l hl hn => by rw [(hTmem l).1 hl |> Option.isSome_iff_exists.1 |>.choose_spec] at hn; cases hn)
    (fun l hl _ x hx => by
      obtain ⟨i, hi, ha⟩ := hmapsC l ((hTmem l).1 hl)
      rw [cellView_mapsTo hwf1 hi] at hx; cases hx
      exact decide_eq_true ((hI _ _).2 (.inr ⟨rfl, ha⟩)))
    (fun l hl => by
      by_cases hm : Mapped st l
      · obtain ⟨q', i, hqi⟩ := hm
        rw [cellView_mapsTo hwf1 hqi, cellView_mapsTo hwf hqi, cellByte_eq, cellByte_eq]
        have hn : ¬ (c.ino = q' ∧ inRange c.lo c.hi i = true) := by
          rintro ⟨hp, ha⟩
          obtain ⟨b, m0, hb, hp0, hi0, rfl⟩ := hqi
          have hb' : m.maps !! b = some m0.len := by
            rw [hmo.maps b m0.len, hb]; congr 1; cases m0; simp only at hp0 ⊢
            rw [hp0, ← hp]; rfl
          apply hl; apply (hTmem _).2; apply (hC _).2
          obtain ⟨h1, h2⟩ := (haff i).1 ha
          exact ⟨i, b, m0.len, (GMap.mem_toList _ _ _).2 hb', h1, h2, hi0, rfl⟩
        have hII : InflightAt (startState st p f c t) q' i ↔ InflightAt st q' i := by
          rw [hI]; exact ⟨fun h => h.resolve_right hn, .inl⟩
        have hF : ((startState st p f c t).file q').bind (·.contents[i]?) =
            (st.file q').bind (·.contents[i]?) := by
          rw [startState_file]; split
          · subst_vars; rw [hf]; rfl
          · rfl
        simp only [hII, hF]
      · rw [cellView_none (st := st) hm]; exact cellView_none hm)
    $$ [Hσ Hcells Hc] with ⟨Hσ, Hcells, -⟩
  · iframe
  imod gAuth_update _ _ _ _ _ ti.meta $$ HAm Hm with ⟨HAm, Hm⟩
  imod bytesG_update _ p _ xs (rsAnn n xs) Γb (by simp) $$ [HAb Hbs] with ⟨HAb, Hbs⟩
  · iframe
  have hΓt : Γt !! t = none := by
    have := hcoh.toks t; rw [ht] at this
    cases h0 : Γt !! t
    · rfl
    · rw [h0] at this; cases this
  imod gAuth_insert _ _ _ t ti hΓt $$ HAt with ⟨HAt, Ht⟩
  imodintro
  isplitl [HAb HAm HAf HAt Htok Hm Hbs Hσ Hcells]
  · iexists _, _, Γf, _
    iframe HAb HAm HAf HAt Hσ Hcells
    isplitr
    · ipureintro
      rw [show c.lo = min m.size tg from hclo] at hcoh1; exact ⟨hwf1, hcoh1⟩
    unfold tokRes
    iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.ino (DFrac.own 1) ti.meta ∗
        bytesG gooseOsGS ti.ino ti.lo (DFrac.own 1) ti.saved)) hΓt).2
    have hlo' : ti.lo = min m.size tg := by simp [ti]
    rw [hlo']
    iframe
  unfold rsTok osTok
  iframe Ht; ipureintro; exact hlen

/-- An fd added on an existing file, the heap unchanged. -/
theorem osWorld_addFd0 {st : OsState} {Γb Γm Γf Γt} {h : GMap Loc (NonAtomic val)} {fd : w64}
    {d : OsFd} (hfd : st.proc.fds !! fd = none) (hfile : ∃ f, st.file d.ino = some f) :
    ⊢ osWorld (L := L) st Γb Γm Γf Γt h ==∗
      osWorld (L := L) (st.setProc { st.proc with fds := <[fd := d]> st.proc.fds }) Γb Γm
        (<[fd := d]> Γf) Γt h ∗ osFd (L := L) fd (DFrac.own 1) d := by
  iintro Hw
  icases (osWorld_unfold (L := L)).1 $$ Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_refl st) Hag
  ihave Hw : osWorld (L := L) st Γb Γm Γf Γt h $$ [HAb HAm HAf HAt Htok Hcells Hσ]
  · iapply (osWorld_unfold (L := L)).2; iframe; ipureintro; exact Hwc
  iapply osWorld_addFd (filesSame_refl st) hfd hfile
    (heapRendered_congr rfl rfl rfl rfl hr) (mapsFresh_same rfl) $$ Hw

/-- The facts of a whole `OsMeta` against the world: its entry, and no change in flight on it. -/
theorem osMeta_whole_facts {st : OsState} {Γb Γm Γf Γt} {h : GMap Loc (NonAtomic val)} {i : Ino}
    {m : OsMeta} :
    ⊢ osWorld (L := L) st Γb Γm Γf Γt h -∗ osMeta (L := L) i (DFrac.own 1) m -∗
      osWorld (L := L) st Γb Γm Γf Γt h ∗ osMeta (L := L) i (DFrac.own 1) m ∗
      ⌜(∃ f, st.file i = some f ∧ f.size = m.size) ∧ ¬ BusyAt st i⌝ := by
  iintro Hw Hm
  icases (osWorld_unfold (L := L)).1 $$ Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  unfold osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %Hnt
  obtain ⟨f, hf, hmo⟩ := coh_meta Hwc.2 Hml
  have hni := noInfl_of_noTok Hwc.2 Hnt
  iframe Hm
  isplitl
  · iapply (osWorld_unfold (L := L)).2; iframe; ipureintro; exact Hwc
  ipureintro
  exact ⟨⟨f, hf, hmo.size.symm⟩, fun ⟨t, c, h1, h2⟩ => hni t c h1 h2⟩

attribute [local instance] Classical.propDecidable in
/-- **The files' world after an open's truncation of `i`** (`truncSt`): the two steps of a resize
to 0 (`resize_start_world`, then `resize_done_world`) through a state between them, whose heap is
rendered for it (`heapRendered_mid`). -/
theorem osWorld_trunc {st : OsState} {Γb Γm Γf Γt} {h h' : GMap Loc (NonAtomic val)}
    {i : Ino} {f : OsFile} {m : OsMeta} {xs : List ByteG}
    (hf : st.file i = some f) (hlen : xs.length = m.size)
    (Hr : HeapRendered st (truncSt st i f) h h') :
    ⊢ osWorld (L := L) st Γb Γm Γf Γt h -∗ osMeta (L := L) i (DFrac.own 1) m -∗
      osBytes (L := L) i 0 (DFrac.own 1) xs -∗ mcellsAny m.maps 0 (pageEnd m.size) ==∗
      (∃ Γb' Γm' Γf' Γt', osWorld (L := L) (truncSt st i f) Γb' Γm' Γf' Γt' h') ∗
        ∃ n, rsDone (L := L) true i 0 0 m n := by
  iintro Hw Hm Hbs Hc
  obtain ⟨t, ht, -⟩ := exists_fresh2 st.proc.inflight st.proc.calls
  let c := OsChange.ofResize i f 0 true
  have hlen' : xs.length = m.size - 0 := by omega
  imod resize_start_world (tr := true) (tg := 0) hf ht hlen' $$ Hw Hm [Hbs] [Hc] with
    ⟨⟨%Γb1, %Γm1, %Γf1, %Γt1, Hw⟩, Ht⟩
  · rw [show min m.size 0 = 0 by omega]; iexact Hbs
  · rw [show min m.size 0 = 0 by omega, show rsHi true m.size 0 = pageEnd m.size by
      simp only [rsHi, if_true, Nat.max_zero]]; iexact Hc
  icases (osWorld_unfold (L := L)).1 $$ Hw with ⟨%Hwc1, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf1, hcoh1⟩ := Hwc1
  unfold rsTok osTok
  icases Ht with ⟨Ht, %hxl⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  obtain ⟨c', f', hF⟩ := rsFacts_of hcoh1 Hti hxl
  have hc' : c' = c := by
    have := hF.hct
    simp only [startState, OsState.addInflight, GMap.lookup_insert, Option.some.injEq] at this
    exact this.symm
  subst hc'
  have hf' : f' = f.announce c (st.fs.stamp + 1) := by
    have := hF.hf; rw [startState_file, if_pos rfl] at this; cases this; rfl
  subst hf'
  have hland : (max m.size 0 ≤ c.hi ∧ c.hi = rsHi true m.size 0 ∧ 0 = 0) ∨
      (m.size ≤ 0 ∧ m.size ≤ c.hi ∧ c.hi ≤ 0 ∧ 0 = c.hi) :=
    .inl ⟨hF.hchi ▸ le_rsHi true m.size 0, hF.hchi, rfl⟩
  have Hr2 := heapRendered_mid (A := st) (C := truncSt st i f) (B := startState st i f c t) rfl rfl Hr
  rw [← truncSt_eq st i f t ht] at Hr2
  have Hfr2 : MapsFresh (startState st i f c t)
      (((startState st i f c t).doneInflight t).setFile i
        ((f.announce c (st.fs.stamp + 1)).land c c.hi 0)) (renderHeap (startState st i f c t) h) :=
    mapsFresh_same rfl
  imod resize_done_world hwf1 hcoh1 hF c.hi 0 hland Hr2 Hfr2 $$ HAb HAm HAf HAt Htok Hcells Hσ Ht
    with ⟨Hw, Hd⟩
  rw [← truncSt_eq st i f t ht]
  imodintro
  iframe Hw
  iexists _; iexact Hd

/-- **`open(2)` with `O_TRUNC` of `d/b`, a name holding the file `i`** (shared mode; any access
mode, with or without `O_CREAT`), with a fraction of a claim on names containing `b`, the file's
`OsMeta` whole, its bytes and the client's halves of its mapped cells: no entry logged; the file
truncated (`rsDone true i 0 0 m n`), or, on failure only, left as it was; on success a fresh fd on `i`. -/
theorem wp_osOpenTruncS (R : Roots) (d b : GoString) (j i : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (fl : w64) (m : OsMeta) (xs : List ByteG)
    (hfl : OpenFlagsOk fl.toNat) (htr : fl.toNat / O_TRUNC % 2 = 1) (hb : NameOk b)
    (hN : N.Mem b) (hi : h.cur !! b = some (.file i)) (hlen : xs.length = m.size)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      osMeta (L := L) i (DFrac.own 1) m -∗ osBytes (L := L) i 0 (DFrac.own 1) xs -∗
      mcellsAny (GF := GF) m.maps 0 (pageEnd m.size) -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗ osNames (L := L) j N dqn h -∗
        ((⌜e ≠ 0⌝ ∗ osMeta (L := L) i (DFrac.own 1) m ∗ osBytes (L := L) i 0 (DFrac.own 1) xs ∗
            mcellsAny (GF := GF) m.maps 0 (pageEnd m.size)) ∨
         (∃ n, rsDone (L := L) true i 0 0 m n)) -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd i fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hp Hn Hk Hm Hbs Hc HΦ
  iapply wp_fs_stepM "Open" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h0 Hw Ht
  unfold treeCtx
  icases Ht with ⟨Htr, Hcm⟩
  icases Htr with (Htr | Htr)
  · iexfalso; iapply legacy_callS_excl st k s0 q $$ Hk Htr
  unfold treeShared
  icases Htr with ⟨%V0, %s1, %Γdf, %Γc, %hns, HAd, Hd, HAdf, HAc, Has, Hadfs, Hacs, Hcr⟩
  obtain ⟨hw, hc⟩ := hns
  unfold osSharedInv
  imod inv_acc (osShN_sub hE') $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  icases osPathS_lookup hR hcoh.2 d dq j $$ HAn Hp with %hl
  icases osNames_entry hcoh.2 j N dqn h $$ HAn Hn with %hent
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  have hen : st.tree.entry j b = some (.file i) := by rw [hent b hN]; exact hi
  have hl' : st.lookup (child d b) = some (.file i) := by rw [lookup_child hw.roots hl hb]; exact hen
  have hl0 : (st.metaEnd k).lookup (child d b) = some (.file i) := hl'
  unfold osCallS
  icases gAuth_lookup _ _ _ _ _ _ $$ Hacs Hk with %hk
  have hcall : st.proc.calls !! k = some s0 := by
    have := hc.calls k; rw [hk] at this; exact this.symm
  icases osMeta_whole_facts $$ Hw Hm with ⟨Hw, Hm, %hmf⟩
  obtain ⟨⟨f, hf, hfsz⟩, hnb⟩ := hmf
  icases (osWorld_unfold (L := L)).1 $$ Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h0 _ $$ Hσ Hcells with %Hag
  have htr' : decide ((fl.toNat / O_TRUNC) % 2 = 1) = true := by simp [htr]
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h0) Hwc.1 (filesSame_metaEnd st k) Hag
    exact ⟨_, h0, _, ⟨child d b, fl, k, s0, rfl, treePath_of_lookup hl', hfl, hcall,
      ⟨fun _ i' hi' => by rw [hl0] at hi'; cases hi'; exact hnb, .inr ⟨1, by decide, rfl, .inl rfl⟩⟩⟩,
      hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨p', fl', k', s', hv, -, -, hk', hres⟩ := Hst
  obtain ⟨rfl, rfl, rfl⟩ := tokPathFl_inj hv
  rw [hcall] at hk'; cases hk'
  simp only [htr'] at hres
  unfold callResS
  icases (BigSepM.bigSepM_delete (M := GMap Nat)
    (Φ := fun (_t : Nat) (x : Nat × Qp) =>
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm () (DFrac.own x.2) ()) hk).1 $$ Hcr
    with ⟨Hq, Hcr⟩
  imod gAuth_delete _ _ _ _ _ $$ Hacs Hk with Hacs
  -- the world at the call's end, the heap unchanged
  obtain ⟨hfr0, hr0⟩ := step_filesSame (h := h0) Hwc.1 (filesSame_metaEnd st k) Hag
  ihave Hw : osWorld (L := L) st Γb Γm Γf Γt h0 $$ [HAb HAm HAf HAt Htok Hcells Hσ]
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imod osWorld_filesSame (filesSame_metaEnd st k) hr0 hfr0 $$ Hw with Hw
  have hf0 : (st.metaEnd k).file i = some f := hf
  have hframe : TreeFrame (st.metaEnd k) (truncSt (st.metaEnd k) i f) :=
    treeFrame_stampFile _ i _ f hf0
  have hw1 : FsTreeWf (truncSt (st.metaEnd k) i f) := hframe.wf (fsTreeWf_metaEnd hw k)
  have hc1 : TreeCohS (truncSt (st.metaEnd k) i f) s1 Γdf (GMap.delete k Γc) :=
    (treeCohS_metaEnd hc k).congr rfl rfl rfl rfl
  obtain ⟨-, hres⟩ := hres
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, rfl, hst⟩
  · unfold OpenEffect at heff
    rw [hl0] at heff
    obtain ⟨⟨f', hf', hst1⟩, rfl⟩ := heff
    rw [hf0, Option.some.injEq] at hf'; subst hf'
    simp only [↓reduceIte] at hst1
    subst st1
    obtain ⟨hfd0, hfdn, hdfn⟩ := hfree
    have hst'' : st' = (truncSt (st.metaEnd k) i f).setProc
        { (truncSt (st.metaEnd k) i f).proc with
          fds := <[fd := openFd i fl]> (truncSt (st.metaEnd k) i f).proc.fds } := hst
    subst hst''
    imod osWorld_trunc (st := st.metaEnd k) hf0 hlen
      (heapRendered_congr rfl rfl rfl rfl Hr) $$ Hw Hm Hbs Hc with ⟨⟨%Γb1, %Γm1, %Γf1, %Γt1, Hw⟩, Hrs⟩
    imod osWorld_addFd0 (st := truncSt (st.metaEnd k) i f) (d := openFd i fl) hfdn
      ⟨_, by simp [truncSt, OsState.stampFile, OsState.file, openFd]; rfl⟩ $$ Hw
      with ⟨Hw, Hfd⟩
    imodintro
    iexists Γb1, Γm1, <[fd := openFd i fl]> Γf1, Γt1
    isplitl [Hw]
    · iexact Hw
    isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
    · try unfold treeCtx
      isplitr [Hcm]
      rotate_left
      · iapply commitRes_grow (gooseOsGS (L := L)) (st := st)
          (st' := (truncSt (st.metaEnd k) i f).setProc { (truncSt (st.metaEnd k) i f).proc with
            fds := <[fd := openFd i fl]> (truncSt (st.metaEnd k) i f).proc.fds })
          (commitGrows_of_eq rfl) $$ Hcm
      iright
      simp only [truncSt, OsState.stampFile, OsState.metaEnd, OsState.setProc]
      try unfold treeShared
      iexists V0, s1, Γdf, GMap.delete k Γc
      iframe
      ipureintro
      exact ⟨fsTreeWf_addFd hw1 hdfn, hc1.congr rfl rfl rfl rfl⟩
    iapply wp_value'
    iapply HΦ $$ %fd %0 %(.inl ⟨rfl, hfd0⟩) [Hq] Hp Hn [Hrs]
    · unfold osCallPerm; iexact Hq
    · iright; iexact Hrs
    rw [if_pos rfl]; iexact Hfd
  · rcases hst with rfl | ⟨tgt, heff⟩
    · -- no effect
      imod osWorld_filesSame (filesSame_refl _) (heapRendered_congr rfl rfl rfl rfl Hr) Hfr $$ Hw
        with Hw
      imodintro
      iexists Γb, Γm, Γf, Γt
      isplitl [Hw]
      · unfold osWorld; iexact Hw
      isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
      · try unfold treeCtx
        isplitr [Hcm]
        rotate_left
        · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := st.metaEnd k)
            (commitGrows_of_eq rfl) $$ Hcm
        iright
        simp only [OsState.metaEnd]
        try unfold treeShared
        iexists V0, s1, Γdf, GMap.delete k Γc
        iframe
        ipureintro; exact ⟨fsTreeWf_metaEnd hw k, treeCohS_metaEnd hc k⟩
      iapply wp_value'
      iapply HΦ $$ %(-1) %e %(.inr ⟨he, rfl⟩) [Hq] Hp Hn [Hm Hbs Hc]
      · unfold osCallPerm; iexact Hq
      · ileft; iframe; ipureintro; exact he
      rw [if_neg he]; iempintro
    · -- truncated, and failed
      unfold OpenEffect at heff; rw [hl0] at heff
      obtain ⟨⟨f', hf', hst1⟩, -⟩ := heff
      rw [hf0, Option.some.injEq] at hf'; subst hf'
      simp only [↓reduceIte] at hst1
      have hst'' : st' = truncSt (st.metaEnd k) i f := hst1
      subst hst''
      imod osWorld_trunc (st := st.metaEnd k) hf0 hlen
        (heapRendered_congr rfl rfl rfl rfl Hr) $$ Hw Hm Hbs Hc
        with ⟨⟨%Γb1, %Γm1, %Γf1, %Γt1, Hw⟩, Hrs⟩
      imodintro
      iexists Γb1, Γm1, Γf1, Γt1
      isplitl [Hw]
      · iexact Hw
      isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr Hcm]
      · try unfold treeCtx
        isplitr [Hcm]
        rotate_left
        · iapply commitRes_grow (gooseOsGS (L := L)) (st := st) (st' := truncSt (st.metaEnd k) i f)
            (commitGrows_of_eq rfl) $$ Hcm
        iright
        simp only [truncSt, OsState.stampFile, OsState.metaEnd]
        try unfold treeShared
        iexists V0, s1, Γdf, GMap.delete k Γc
        iframe
        ipureintro; exact ⟨hw1, hc1⟩
      iapply wp_value'
      iapply HΦ $$ %(-1) %e %(.inr ⟨he, rfl⟩) [Hq] Hp Hn [Hrs]
      · unfold osCallPerm; iexact Hq
      · iright; iexact Hrs
      rw [if_neg he]; iempintro

end specs

end Fs
end Perennial

end
