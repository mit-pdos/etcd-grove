/-
WP specs of the resizes, two-step changes (`FtruncateStart`/`FtruncateFinish`; `fallocate`'s are in
`Falloc.lean`, over the same lemmas), on the per-byte model of `Impl.lean`: the first step announces
zeros over the bytes where the old and new sizes part (the bytes cut off, or the bytes the file
grows over) as their new crash candidate, stamped with the change's number, and takes the file's
`OsMeta`, the bytes cut off and the client's halves of the mapped cells over the range; the second
lands the new size (or, for a failed `fallocate`, a prefix of the growth) and gives them back:
the bytes grown over, zero, with their candidates; the cells showing the new contents. Untrusted.
-/
module

public import GooseLang.Ext.Fs.Write

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-! ## The change -/

/-- A resize to `sz` (no other than `f`'s size) is the change the ghost state records. -/
theorem ofResize_is (i : Ino) (f : OsFile) (sz : Nat) (n : Nat) (m0 : OsMeta)
    (saved : List ByteG) (hsz : m0.size = f.size) :
    (TokInfo.mk i (.truncate sz) n m0 saved).Is (OsChange.ofResize i f sz) := by
  refine ⟨rfl, rfl, by simp [TokInfo.lo, OsChange.ofResize, hsz],
    by simp [TokInfo.hi, OsChange.ofResize, hsz], rfl, fun b _ => rfl⟩

/-- The bytes `xs` cut off by a resize, as its first step leaves them: each with zero as a new
candidate, stamped `n`. -/
def rsAnn (n : Nat) (xs : List ByteG) : List ByteG := xs.map (fun x => (x.1, x.2 ++ [(0, n)]))

@[simp] theorem rsAnn_length (n : Nat) (xs : List ByteG) : (rsAnn n xs).length = xs.length := by
  simp [rsAnn]

/-- The `OsMeta` after a resize from `m`'s size, to the target `tg`, landed with the size `sz'`. -/
def rsPost (m : OsMeta) (tg sz' : Nat) : OsMeta :=
  { m.announce (min m.size tg) (max m.size tg) tg with size := sz' }

/-- What a mapped cell at byte `i` of the resized range shows once the size is `sz'`. -/
def rsCell [GooseExts] (sz' i : Nat) : val := toCellVal (if i < sz' then some (0 : w8) else none)

/-- What a mapped cell at byte `i` of the resized range shows if the resize did not land: the old
bytes `xs` from `lo`, then holes. -/
def rsOld [GooseExts] (S lo : Nat) (xs : List ByteG) (i : Nat) : val :=
  toCellVal (if i < S then some (xs.getD (i - lo) (0, [])).1 else none)

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- A resize of the file `p` to the target `tg` between its two steps, the change number `n`: what
its first step took (the `OsMeta` `m`, whole, the bytes `xs` it cuts off, with their new
candidates). -/
def rsTok (t : Nat) (p : Ino) (tg : Nat) (m : OsMeta) (xs : List ByteG) (n : Nat) : IProp GF :=
  iprop(osTok (L := L) t ⟨p, .truncate tg, n, m, rsAnn n xs⟩ ∗ ⌜xs.length = m.size - tg⌝)

/-- A resize landed with the size `sz'`: its `OsMeta`, the bytes it grew the file over, zeros, with
their candidates (those they had, `zs`: the zero alone past the zeros known, then zero stamped `n`),
and the client's halves of the mapped cells over the range, showing the new contents. -/
def rsDone (p : Ino) (tg sz' : Nat) (m : OsMeta) (n : Nat) : IProp GF :=
  iprop(∃ zs : List Cands, ⌜zs.length = sz' - m.size ∧
      ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)]⌝ ∗
    osMeta (L := L) p (DFrac.own 1) (rsPost m tg sz') ∗
    osBytes (L := L) p m.size (DFrac.own 1) (zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)]))) ∗
    mcells m.maps (min m.size tg) (max m.size tg) (rsCell sz'))

/-- A resize that did not land: its `OsMeta` as its first step left it, the bytes it would have cut
off with their new candidates, and the client's halves of the cells, showing the old contents. -/
def rsUndone (p : Ino) (tg : Nat) (m : OsMeta) (xs : List ByteG) (n : Nat) : IProp GF :=
  iprop(osMeta (L := L) p (DFrac.own 1) (m.announce (min m.size tg) (max m.size tg) tg) ∗
    osBytes (L := L) p (min m.size tg) (DFrac.own 1) (rsAnn n xs) ∗
    mcells m.maps (min m.size tg) (max m.size tg) (rsOld m.size (min m.size tg) xs))

/-- The first step of a resize (`ftruncate(fd, sz)`, or `fallocate`'s growth, `op`) to `tg`, with
the whole of the file's `OsMeta`, the bytes it cuts off (`[tg, size)`, whole; none if it grows the
file) and the client's halves of the cells of every mapping over the range. They stay with the
change until its second step, which gets the change's number `n`. -/
theorem wp_osResizeStart (op : String) (v : val) (hop : DataOp op) (hv : v.isPanic = false)
    (fd : w64) (tg : Nat) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG)
    (hE : ↑osN ⊆ E)
    (hstep : ∀ st f t, st.proc.fds !! fd = some d → st.file d.ino = some f → ¬ BusyAt st d.ino →
      st.proc.inflight !! t = none → st.proc.calls !! t = none →
      IsFsStep op v st (Val (osTokV t)) (startState st d.ino f (OsChange.ofResize d.ino f tg) t))
    (hstep' : ∀ st e' st', st.proc.fds !! fd = some d → IsFsStep op v st e' st' →
      ∃ f t, st.file d.ino = some f ∧ st.proc.inflight !! t = none ∧ e' = Val (osTokV t) ∧
        st' = startState st d.ino f (OsChange.ofResize d.ino f tg) t)
    (hlen : xs.length = m.size - tg) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      osBytes (L := L) d.ino (min m.size tg) (DFrac.own 1) xs -∗
      mcellsAny m.maps (min m.size tg) (max m.size tg) -∗
      (∀ t : Nat, ∀ n : Nat, ⌜∀ x ∈ xs, ∀ q ∈ x.2, q.2 < n⌝ -∗ osFd (L := L) fd dq d -∗
        rsTok t d.ino tg m xs n -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs Hc HΦ
  iapply wp_os_step op _ Φ hv hE hop $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta osBytes
  icases bytesG_lookup _ d.ino _ _ xs Γb $$ HAb Hbs with %Hbl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %Hnt
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hni := noInfl_of_noTok hcoh Hnt
  have hnb : ¬ BusyAt st d.ino := by rintro ⟨t', c', ht', hc'⟩; exact hni t' c' ht' hc'
  have hxs : ∀ k (hk : k < xs.length), xs[k] =
      (f.cache (min f.size tg + k), f.cand (min f.size tg + k)) := by
    intro k hk
    obtain ⟨f1, hf1, -, hx⟩ := hcoh.bytes _ _ _ (Hbl k hk)
    rw [hf] at hf1; cases hf1; rw [← hmo.size]; exact hx
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  let c := OsChange.ofResize d.ino f tg
  have hclo : c.lo = min m.size tg := by simp [c, OsChange.ofResize, hmo.size]
  have hchi : c.hi = max m.size tg := by simp [c, OsChange.ofResize, hmo.size]
  have haff : ∀ i, inRange c.lo c.hi i = true ↔ min m.size tg ≤ i ∧ i < max m.size tg := by
    intro i; rw [hclo, hchi]; simp [inRange]
  obtain ⟨t0, ht0, hc0⟩ := exists_fresh2 st.proc.inflight st.proc.calls
  imodintro
  isplitr
  · ipureintro
    have hwf0 := osWf_start (c := c) hwf ht0 hf rfl hni
    exact ⟨_, _, _, hstep st f t0 hfd hf hnb ht0 hc0, mapsFresh_same rfl,
      heapRendered_render hwf0 rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  obtain ⟨f', t, hf', ht, rfl, rfl⟩ := hstep' st e' st' hfd Hst
  rw [hf] at hf'; cases hf'
  let n := st.fs.stamp + 1
  let ti : TokInfo := ⟨d.ino, .truncate tg, n, m, rsAnn n xs⟩
  have hwf1 := osWf_start (c := c) hwf ht hf rfl hni
  have hti : ti.Is c := ofResize_is d.ino f tg n m _ hmo.size
  have hcoh1 := osCoh_start (c := c) hcoh ht hf Hml hmo Hnt ti hti rfl rfl rfl
    (by rw [hclo, hchi]; omega)
    (by show (rsAnn n xs).length = _; rw [rsAnn_length, hlen, hmo.size]
        simp [c, OsChange.ofResize]; omega)
    (fun j hj => by
      simp only [ti, rsAnn, List.getElem_map] at hj ⊢
      have hj' : j < xs.length := by simpa using hj
      rw [hxs j hj', show c.lo = min f.size tg by simp [c, OsChange.ofResize]]; rfl)
  have hI := inflightAt_start (c := c) (f := f) (p := d.ino) ht
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmo.maps b1 l1).1 h1) ((hmo.maps b2 l2).1 h2) hne)
  unfold mcellsAny
  ihave Hc := (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
    iprop(∃ vf, cellsR b (min (min m.size tg) len)
      (min (max m.size tg) len - min (min m.size tg) len) vf))).1 $$ Hc
  icases halves_mapsCells_ex (min m.size tg) (max m.size tg) _ hdisj $$ Hc with ⟨%C, Hc, %hC⟩
  have hmapsC : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l d.ino i ∧ inRange c.lo c.hi i = true := by
    intro l hl
    obtain ⟨i, b, len, hm, h1, h2, h3, rfl⟩ := (hC l).1 hl
    exact ⟨i, ⟨b, ⟨d.ino, len⟩, (hmo.maps b len).1 ((GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
      (haff i).2 ⟨h1, h2⟩⟩
  have hTmem : ∀ l, l ∈ C.toList.map (·.1) ↔ (C !! l).isSome := by
    intro l; simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hkv, rfl⟩; rw [(GMap.mem_toList _ _ _).1 hkv]; rfl
    · intro hl; obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
      exact ⟨(l, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  have hTnd : (C.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := C)
  have hnoI : ∀ i, ¬ InflightAt st d.ino i := by
    rintro i ⟨t', c', h1, h2, -⟩; exact hni t' c' h1 h2
  imod cells_step st _ h h' (C.toList.map (·.1)) C ∅ hwf hwf1 Hr Hfr (fun b m0 h0 => .inr h0) hTnd
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
        have hII : InflightAt (startState st d.ino f c t) q' i ↔ InflightAt st q' i := by
          rw [hI]; exact ⟨fun h => h.resolve_right hn, .inl⟩
        have hF : ((startState st d.ino f c t).file q').bind (·.contents[i]?) =
            (st.file q').bind (·.contents[i]?) := by
          rw [startState_file]; split
          · subst_vars; rw [hf]; rfl
          · rfl
        simp only [hII, hF]
      · rw [cellView_none (st := st) hm]; exact cellView_none hm)
    $$ [Hσ Hcells Hc] with ⟨Hσ, Hcells, -⟩
  · iframe
  imod gAuth_update _ _ _ _ _ ti.meta $$ HAm Hm with ⟨HAm, Hm⟩
  imod bytesG_update _ d.ino _ xs (rsAnn n xs) Γb (by simp) $$ [HAb Hbs] with ⟨HAb, Hbs⟩
  · iframe
  have hΓt : Γt !! t = none := by
    have := hcoh.toks t; rw [ht] at this
    cases h0 : Γt !! t
    · rfl
    · rw [h0] at this; cases this
  imod gAuth_insert _ _ _ t ti hΓt $$ HAt with ⟨HAt, Ht⟩
  imodintro
  iexists _, _, Γf, _
  iframe HAb HAm HAf HAt Hσ Hcells
  isplitl [Htok Hm Hbs]
  · isplitr
    · ipureintro
      rw [show c.lo = min m.size tg from hclo] at hcoh1; exact ⟨hwf1, hcoh1⟩
    unfold tokRes
    iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.ino (DFrac.own 1) ti.meta ∗
        bytesG gooseOsGS ti.ino ti.lo (DFrac.own 1) ti.saved)) hΓt).2
    have hlo' : ti.lo = min m.size tg := by simp [ti, TokInfo.lo]
    rw [hlo']
    iframe
  iapply wp_value'
  iapply HΦ $$ %t %n %(fun x hx q hq => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [hxs k hk] at hq
    exact Nat.lt_succ_of_le (hwf.stamps d.ino f _ q hf hq)) Hfd
  unfold rsTok osTok
  iframe Ht; ipureintro; exact hlen

end specs

end Fs
end Perennial

end
