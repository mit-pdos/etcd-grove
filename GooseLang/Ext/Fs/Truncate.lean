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

/-- The kind of a resize to `tg`: by `ftruncate` (`tr`), or by `fallocate`'s growth. -/
def rsKind (tr : Bool) (tg : Nat) : OsChangeKind := if tr then .truncate tg else .falloc tg

/-- The end of what a resize of a file of size `s` to `tg` announces (`OsChange.ofResize`): for
`ftruncate` (`tr`), the end of the page holding the larger of the two ends; for `fallocate`, the
larger size. -/
def rsHi (tr : Bool) (s tg : Nat) : Nat := if tr then pageEnd (max s tg) else max s tg

theorem le_rsHi (tr : Bool) (s tg : Nat) : max s tg ≤ rsHi tr s tg := by
  have := le_pageEnd (max s tg)
  cases tr <;> simp only [rsHi, Bool.false_eq_true, if_true, if_false] <;> omega

/-- A resize to the size a file has announces no more than one to it from any size. -/
theorem rsHi_same_le (tr : Bool) (s tg : Nat) : rsHi tr tg tg ≤ rsHi tr s tg := by
  have := pageEnd_mono (show max tg tg ≤ max s tg by omega)
  cases tr <;> simp only [rsHi, Bool.false_eq_true, if_true, if_false] <;> omega

@[simp] theorem rsKind_lo (tr : Bool) (i : Ino) (tg n : Nat) (m : OsMeta) (sv : List ByteG) :
    TokInfo.lo ⟨i, rsKind tr tg, n, m, sv⟩ = min m.size tg := by cases tr <;> rfl

@[simp] theorem rsKind_hi (tr : Bool) (i : Ino) (tg n : Nat) (m : OsMeta) (sv : List ByteG) :
    TokInfo.hi ⟨i, rsKind tr tg, n, m, sv⟩ = rsHi tr m.size tg := by cases tr <;> rfl

@[simp] theorem rsKind_target (tr : Bool) (i : Ino) (tg n : Nat) (m : OsMeta) (sv : List ByteG) :
    TokInfo.target ⟨i, rsKind tr tg, n, m, sv⟩ = tg := by cases tr <;> rfl

@[simp] theorem rsKind_val (tr : Bool) (i : Ino) (tg n : Nat) (m : OsMeta) (sv : List ByteG)
    (b : Nat) : TokInfo.val ⟨i, rsKind tr tg, n, m, sv⟩ b = 0 := by cases tr <;> rfl

theorem rsKind_meta (tr : Bool) (i : Ino) (tg n : Nat) (m : OsMeta) (sv : List ByteG) :
    TokInfo.meta ⟨i, rsKind tr tg, n, m, sv⟩ = m.announce (min m.size tg) (rsHi tr m.size tg) tg := by
  simp only [TokInfo.meta, rsKind_lo, rsKind_hi, rsKind_target]

@[simp] theorem ofResize_kind (i : Ino) (f : OsFile) (sz : Nat) (tr : Bool) :
    (OsChange.ofResize i f sz tr).kind = rsKind tr sz := rfl

@[simp] theorem ofResize_hi (i : Ino) (f : OsFile) (sz : Nat) (tr : Bool) :
    (OsChange.ofResize i f sz tr).hi = rsHi tr f.size sz := rfl

/-- A resize to `sz` (no other than `f`'s size) is the change the ghost state records. -/
theorem ofResize_is (i : Ino) (f : OsFile) (sz : Nat) (tr : Bool) (n : Nat) (m0 : OsMeta)
    (saved : List ByteG) (hsz : m0.size = f.size) :
    (TokInfo.mk i (rsKind tr sz) n m0 saved).Is (OsChange.ofResize i f sz tr) := by
  refine ⟨rfl, rfl, by simp [OsChange.ofResize, hsz], by simp [hsz], by simp [OsChange.ofResize],
    fun b _ => by simp [OsChange.ofResize]⟩

/-- The bytes `xs` cut off by a resize, as its first step leaves them: each with zero as a new
candidate, stamped `n`. -/
def rsAnn (n : Nat) (xs : List ByteG) : List ByteG := xs.map (fun x => (x.1, x.2 ++ [(0, n)]))

@[simp] theorem rsAnn_length (n : Nat) (xs : List ByteG) : (rsAnn n xs).length = xs.length := by
  simp [rsAnn]

/-- The page cache known zero past the size after a resize from the size `s`, as `cz` (`OsMeta.cz`)
was: an `ftruncate` (`tr`) zeroed it to the end of what it announced; `fallocate` keeps what was
known. -/
def rsCz (tr : Bool) (s tg cz : Nat) : Nat := if tr then max cz (rsHi tr s tg) else cz

/-- The `OsMeta` after a resize from `m`'s size, to the target `tg`, landed with the size `sz'`. -/
def rsPost (tr : Bool) (m : OsMeta) (tg sz' : Nat) : OsMeta :=
  { m.announce (min m.size tg) (rsHi tr m.size tg) tg with size := sz', cz := rsCz tr m.size tg m.cz }

/-- The candidates known past the size after a resize from `m`'s size to `tg` (`ftruncate`: `tr`)
lands with the size `sz'`, announced as change `n` (each byte announced with zero, stamped `n`, as
its last candidate), the bytes from `min size tg` on having been `xs`: each announced byte past the
new size has its candidates, now past the size (a crash may still keep them: the crash rule's
candidates are the state's, which the landing does not change): below the old size, `xs`'s; past
it, those `m` knew (`OsMeta.pc`); the other bytes as the announcement left them. -/
def rsTail (tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) : GMap Nat Cands :=
  ⟨fun b => if min m.size tg ≤ b ∧ b < rsHi tr m.size tg ∧ sz' ≤ b then
      (if b < m.size then some ((xs.getD (b - min m.size tg) (0, [])).2 ++ [(0, n)])
       else (m.pc b).map (· ++ [(0, n)]))
    else (m.announce (min m.size tg) (rsHi tr m.size tg) tg).tc !! b,
   by
    obtain ⟨l, hl⟩ := (m.announce (min m.size tg) (rsHi tr m.size tg) tg).tc.finite
    refine ⟨l ++ List.range (rsHi tr m.size tg), fun b h => ?_⟩
    by_cases h1 : min m.size tg ≤ b ∧ b < rsHi tr m.size tg ∧ sz' ≤ b
    · exact List.mem_append_right _ (List.mem_range.2 h1.2.1)
    · simp only [h1, if_false] at h; exact List.mem_append_left _ (hl b h)⟩

theorem rsTail_lookup (tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) (b : Nat) :
    rsTail tr m tg sz' n xs !! b = if min m.size tg ≤ b ∧ b < rsHi tr m.size tg ∧ sz' ≤ b then
      (if b < m.size then some ((xs.getD (b - min m.size tg) (0, [])).2 ++ [(0, n)])
       else (m.pc b).map (· ++ [(0, n)]))
    else (m.announce (min m.size tg) (rsHi tr m.size tg) tg).tc !! b := rfl

/-- `rsPost`, and, if `keep`, the candidates of the bytes a truncate cut off (`rsTail`; the bytes
`xs` from the target, announced as change `n`). Sound only for a file with no sync cut
(`OsMeta.cut = none`), whose byte resources' candidates are the state's. -/
def rsPostK (keep : Bool) (tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) : OsMeta :=
  { rsPost tr m tg sz' with
    tc := cond keep (rsTail tr m tg sz' n xs) (rsPost tr m tg sz').tc
    rz := cond keep (n :: m.rz) (rsPost tr m tg sz').rz }

theorem rsPostK_false (tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    rsPostK false tr m tg sz' n xs = rsPost tr m tg sz' := rfl

@[simp] theorem rsPost_rz (tr : Bool) (m : OsMeta) (tg sz' : Nat) : (rsPost tr m tg sz').rz = m.rz := by
  simp [rsPost]

/-- A resize landed with its cut-off candidates known (`keep`) records its stamp. -/
@[simp] theorem rsPostK_rz (keep tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    (rsPostK keep tr m tg sz' n xs).rz = cond keep (n :: m.rz) m.rz := by
  cases keep <;> simp [rsPostK]

/-- `rsPostK` differs from `rsPost` only in `tc` and `rz`. -/
@[simp] theorem rsPostK_size (keep tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    (rsPostK keep tr m tg sz' n xs).size = (rsPost tr m tg sz').size := rfl
@[simp] theorem rsPostK_lo (keep tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    (rsPostK keep tr m tg sz' n xs).lo = (rsPost tr m tg sz').lo := rfl
@[simp] theorem rsPostK_hi (keep tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    (rsPostK keep tr m tg sz' n xs).hi = (rsPost tr m tg sz').hi := rfl
@[simp] theorem rsPostK_maps (keep tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    (rsPostK keep tr m tg sz' n xs).maps = (rsPost tr m tg sz').maps := rfl
@[simp] theorem rsPostK_dlo (keep tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    (rsPostK keep tr m tg sz' n xs).dlo = (rsPost tr m tg sz').dlo := rfl
@[simp] theorem rsPostK_dhi (keep tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    (rsPostK keep tr m tg sz' n xs).dhi = (rsPost tr m tg sz').dhi := rfl
@[simp] theorem rsPostK_zf (keep tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    (rsPostK keep tr m tg sz' n xs).zf = (rsPost tr m tg sz').zf := rfl
@[simp] theorem rsPostK_cut (keep tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    (rsPostK keep tr m tg sz' n xs).cut = (rsPost tr m tg sz').cut := rfl
@[simp] theorem rsPostK_cz (keep tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    (rsPostK keep tr m tg sz' n xs).cz = (rsPost tr m tg sz').cz := rfl

/-- What `rsPostK true` knows of a byte a truncate cut off. -/
theorem rsPostK_true_tc {tr : Bool} {m : OsMeta} {tg sz' n : Nat} {xs : List ByteG} {k : Nat}
    (hsz : sz' ≤ min m.size tg) (hxl : xs.length = m.size - tg) (hk : k < xs.length) :
    (rsPostK true tr m tg sz' n xs).tc !! (min m.size tg + k) = some (xs[k].2 ++ [(0, n)]) := by
  have := le_rsHi tr m.size tg
  show rsTail tr m tg sz' n xs !! (min m.size tg + k) = _
  rw [rsTail_lookup, if_pos ⟨by omega, by omega, by omega⟩, if_pos (by omega),
    Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

/-- What `rsPostK true` knows of a byte announced past the old size. -/
theorem rsPostK_true_tc_past {tr : Bool} {m : OsMeta} {tg sz' n : Nat} {xs : List ByteG} {b : Nat}
    (hsz : sz' ≤ b) (hb : m.size ≤ b) (hb2 : b < rsHi tr m.size tg) :
    (rsPostK true tr m tg sz' n xs).tc !! b = (m.pc b).map (· ++ [(0, n)]) := by
  show rsTail tr m tg sz' n xs !! b = _
  rw [rsTail_lookup, if_pos ⟨by omega, hb2, hsz⟩, if_neg (by omega)]

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
def rsTok (tr : Bool) (t : Nat) (p : Ino) (tg : Nat) (m : OsMeta) (xs : List ByteG) (n : Nat) : IProp GF :=
  iprop(osTok (L := L) t ⟨p, rsKind tr tg, n, m, rsAnn n xs⟩ ∗ ⌜xs.length = m.size - tg⌝)

/-- A resize landed with the size `sz'`: its `OsMeta`, the bytes it grew the file over, zeros, with
their candidates (those they had, `zs`: the zero alone past the zeros known, then zero stamped `n`),
and the client's halves of the mapped cells over the range, showing the new contents. -/
def rsDone (tr : Bool) (p : Ino) (tg sz' : Nat) (m : OsMeta) (n : Nat) : IProp GF :=
  iprop(∃ zs : List Cands, ⌜zs.length = sz' - m.size ∧
      ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)]⌝ ∗
    osMeta (L := L) p (DFrac.own 1) (rsPost tr m tg sz') ∗
    osBytes (L := L) p m.size (DFrac.own 1) (zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)]))) ∗
    mcells m.maps (min m.size tg) (rsHi tr m.size tg) (rsCell sz'))

/-- `rsDone` whose `OsMeta`, if `keep`, knows the candidates of the bytes `xs` cut off
(`rsPostK`). -/
def rsDoneK (keep tr : Bool) (p : Ino) (tg sz' : Nat) (m : OsMeta) (xs : List ByteG) (n : Nat) :
    IProp GF :=
  iprop(∃ zs : List Cands, ⌜zs.length = sz' - m.size ∧
      ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)]⌝ ∗
    osMeta (L := L) p (DFrac.own 1) (rsPostK keep tr m tg sz' n xs) ∗
    osBytes (L := L) p m.size (DFrac.own 1) (zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)]))) ∗
    mcells m.maps (min m.size tg) (rsHi tr m.size tg) (rsCell sz'))

theorem rsDoneK_false (tr : Bool) (p : Ino) (tg sz' : Nat) (m : OsMeta) (xs : List ByteG)
    (n : Nat) : rsDoneK (L := L) false tr p tg sz' m xs n = rsDone (L := L) tr p tg sz' m n := rfl

/-- A resize that did not land: its `OsMeta` as its first step left it, the bytes it would have cut
off with their new candidates, and the client's halves of the cells, showing the old contents. -/
def rsUndone (tr : Bool) (p : Ino) (tg : Nat) (m : OsMeta) (xs : List ByteG) (n : Nat) : IProp GF :=
  iprop(osMeta (L := L) p (DFrac.own 1) (m.announce (min m.size tg) (rsHi tr m.size tg) tg) ∗
    osBytes (L := L) p (min m.size tg) (DFrac.own 1) (rsAnn n xs) ∗
    mcells m.maps (min m.size tg) (rsHi tr m.size tg) (rsOld m.size (min m.size tg) xs))

/-- The first step of a resize (`ftruncate(fd, sz)`, or `fallocate`'s growth, `op`) to `tg`, with
the whole of the file's `OsMeta`, the bytes it cuts off (`[tg, size)`, whole; none if it grows the
file) and the client's halves of the cells of every mapping over the range. They stay with the
change until its second step, which gets the change's number `n`. -/
theorem wp_osResizeStart (op : String) (v : val) (hop : DataOp op) (hv : v.isPanic = false)
    (tr : Bool) (fd : w64) (tg : Nat) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG)
    (hE : ↑osN ⊆ E)
    (hstep : ∀ st f t, st.proc.fds !! fd = some d → st.file d.ino = some f → ¬ BusyAt st d.ino →
      st.proc.inflight !! t = none → st.proc.calls !! t = none → f.size = m.size →
      IsFsStep op v st (Val (osTokV t)) (startState st d.ino f (OsChange.ofResize d.ino f tg tr) t))
    (hstep' : ∀ st e' st', st.proc.fds !! fd = some d →
      (∀ f, st.file d.ino = some f → f.size = m.size) → IsFsStep op v st e' st' →
      ∃ f t, st.file d.ino = some f ∧ st.proc.inflight !! t = none ∧ e' = Val (osTokV t) ∧
        st' = startState st d.ino f (OsChange.ofResize d.ino f tg tr) t)
    (hlen : xs.length = m.size - tg) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      osBytes (L := L) d.ino (min m.size tg) (DFrac.own 1) xs -∗
      mcellsAny m.maps (min m.size tg) (rsHi tr m.size tg) -∗
      (∀ t : Nat, ∀ n : Nat, ⌜0 < n ∧ m.TcZ ∧ ∀ x ∈ xs, ∀ q ∈ x.2, q.2 < n⌝ -∗ osFd (L := L) fd dq d -∗
        rsTok tr t d.ino tg m xs n -∗ Φ (osTokV t)) -∗
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
  have hxs : ∀ k (hk : k < xs.length), ∀ q ∈ xs[k].2, q.2 ≤ st.fs.stamp := by
    intro k hk
    obtain ⟨f1, hf1, -, -, -, hrel⟩ := hcoh.bytes _ _ _ (Hbl k hk)
    rw [hf] at hf1; cases hf1
    exact hrel.stamps_le (fun p hp => hwf.stamps _ f _ p hf hp)
      (fun c hc => hcoh.cut_le d.ino m c Hml (by simpa [cutOf, Hml] using hc))
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  let c := OsChange.ofResize d.ino f tg tr
  have hclo : c.lo = min m.size tg := by simp [c, OsChange.ofResize, hmo.size]
  have hchi : c.hi = rsHi tr m.size tg := by simp [c, hmo.size]
  have hR := le_rsHi tr m.size tg
  have haff : ∀ i, inRange c.lo c.hi i = true ↔ min m.size tg ≤ i ∧ i < rsHi tr m.size tg := by
    intro i; rw [hclo, hchi]; simp [inRange]
  obtain ⟨t0, ht0, hc0⟩ := exists_fresh2 st.proc.inflight st.proc.calls
  imodintro
  isplitr
  · ipureintro
    have hwf0 := osWf_start (c := c) hwf ht0 hf rfl hni
    exact ⟨_, _, _, hstep st f t0 hfd hf hnb ht0 hc0 hmo.size.symm, mapsFresh_same rfl,
      heapRendered_render hwf0 rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  obtain ⟨f', t, hf', ht, rfl, rfl⟩ := hstep' st e' st' hfd
    (fun f1 hf1 => by rw [hf] at hf1; cases hf1; exact hmo.size.symm) Hst
  rw [hf] at hf'; cases hf'
  let n := st.fs.stamp + 1
  let ti : TokInfo := ⟨d.ino, rsKind tr tg, n, m, rsAnn n xs⟩
  have hwf1 := osWf_start (c := c) hwf ht hf rfl hni
  have hti : ti.Is c := ofResize_is d.ino f tg tr n m _ hmo.size
  have hcoh1 := osCoh_start (c := c) hcoh ht hf Hml hmo Hnt ti hti rfl rfl rfl
    (by rw [hclo, hchi]; omega)
    (by show (rsAnn n xs).length = _; rw [rsAnn_length, hlen, hclo, hchi, ← hmo.size]; omega)
    (fun j hj => by
      simp only [ti, rsAnn, List.getElem_map] at hj ⊢
      have hj' : j < xs.length := by simpa using hj
      refine ⟨xs[j], ?_, rfl⟩
      rw [show c.lo = min f.size tg by simp [c, OsChange.ofResize], ← hmo.size]; exact Hbl j hj')
  have hI := inflightAt_start (c := c) (f := f) (p := d.ino) ht
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmo.maps b1 l1).1 h1) ((hmo.maps b2 l2).1 h2) hne)
  unfold mcellsAny
  ihave Hc := (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
    iprop(∃ vf, cellsR b (min (min m.size tg) len)
      (min (rsHi tr m.size tg) len - min (min m.size tg) len) vf))).1 $$ Hc
  icases halves_mapsCells_ex (min m.size tg) (rsHi tr m.size tg) _ hdisj $$ Hc with ⟨%C, Hc, %hC⟩
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
    have hlo' : ti.lo = min m.size tg := by simp [ti]
    rw [hlo']
    iframe
  iapply wp_value'
  iapply HΦ $$ %t %n %(And.intro (Nat.succ_pos _) (And.intro hmo.tcz (fun x hx q hq => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact Nat.lt_succ_of_le (hxs k hk q hq)))) Hfd
  unfold rsTok osTok
  iframe Ht; ipureintro; exact hlen

end specs


/-! ## The second step of a resize -/

section specs2
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- What the second step of a resize finds: the change `c` in flight under `t`, the one the ghost
state records with the file `f` and the `OsMeta` `m` at its first step, and what it holds. -/
structure RsFacts (st : OsState) (Γb : GMap (Ino × Nat) ByteG) (Γm : GMap Ino OsMeta)
    (Γt : GMap Nat TokInfo) (t : Nat) (tr : Bool) (p : Ino) (tg : Nat) (m : OsMeta)
    (xs : List ByteG) (n : Nat) (c : OsChange) (f : OsFile) : Prop where
  hti : Γt !! t = some ⟨p, rsKind tr tg, n, m, rsAnn n xs⟩
  hct : st.proc.inflight !! t = some c
  hcino : c.ino = p
  hckind : c.kind = rsKind tr tg
  hclo : c.lo = min m.size tg
  hchi : c.hi = rsHi tr m.size tg
  hctg : c.target = tg
  hcval : ∀ b, inRange c.lo c.hi b = true → c.val b = 0
  hf : st.file p = some f
  hmsz : m.size = f.size
  hxl : xs.length = m.size - tg
  hcand : ∀ b, min m.size tg ≤ b → b < rsHi tr m.size tg → ∃ c0, f.cand b = c0 ++ [(0, n)] ∧
    ∀ z, m.zf = some z → z ≤ b → c0 = [(0, 0)]
  hmo : MetaOk st p (m.announce (min m.size tg) (rsHi tr m.size tg) tg) f
  hml : Γm !! p = some (m.announce (min m.size tg) (rsHi tr m.size tg) tg)
  /-- An announced byte past the size whose candidates `m` knew has them, then zero stamped `n`. -/
  hcandP : ∀ b c, m.size ≤ b → b < rsHi tr m.size tg → m.pc b = some c → f.cand b = c ++ [(0, n)]

/-- The facts of the second step of a resize, from its token. -/
theorem rsFacts_of {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {t : Nat} {tr : Bool}
    {p : Ino}
    {tg : Nat} {m : OsMeta} {xs : List ByteG} {n : Nat}
    (Hti : Γt !! t = some ⟨p, rsKind tr tg, n, m, rsAnn n xs⟩) (hxl : xs.length = m.size - tg) :
    ∃ c f, RsFacts st Γb Γm Γt t tr p tg m xs n c f := by
  obtain ⟨c, hct⟩ : ∃ c, st.proc.inflight !! t = some c := by
    have := hcoh.toks t; rw [Hti] at this; exact Option.isSome_iff_exists.1 this.symm
  obtain ⟨hcino, hckind, hclo, hchi, hctg, hcval⟩ := hcoh.tok_is t _ c Hti hct
  obtain ⟨f, hf, hm0, -, -⟩ := hcoh.tok_file t _ Hti
  obtain ⟨f', hf', hcand⟩ := hcoh.tok_cand t _ Hti
  rw [hf] at hf'; cases hf'
  have Hml := hcoh.tok_meta t _ Hti
  simp only [rsKind_lo, rsKind_hi, rsKind_target, rsKind_val, rsKind_meta] at hclo hchi hctg hcval hcand hcino hm0 hf Hml
  obtain ⟨f1, hf1, hmo⟩ := coh_meta hcoh Hml
  rw [hf] at hf1; cases hf1
  exact ⟨c, f, ⟨Hti, hct, hcino, hckind, hclo, hchi, hctg, hcval, hf, hm0, hxl,
    fun b h1 h2 => by
      obtain ⟨c0, h, hz, -⟩ := hcand b (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)
      exact ⟨c0, h, hz⟩,
    hmo, Hml,
    fun b c1 h1 h2 hp => by
      obtain ⟨c0, h, hz, ht⟩ := hcand b (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)
      rw [h]; congr 1
      rcases OsMeta.pc_some hp with h3 | ⟨z, h3, h4, rfl⟩
      · exact ht c1 h1 h3
      · exact hz z h3 h4⟩⟩

theorem osWorld_unfold {st : OsState} {Γb Γm Γf Γt} {h : GMap Loc (NonAtomic val)} :
    osWorld (L := L) st Γb Γm Γf Γt h ⊣⊢
      iprop(⌜OsWf st ∧ OsCoh st Γb Γm Γf Γt⌝ ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt ∗
        tokRes (gooseOsGS (L := L)) Γt ∗ cellsRes (cellView st) ∗ naHeapCtx tls h) := .rfl

/-- **A resize landed**: up to `e`, with the new size `sz'` (a cut: all of it, to the target; a
growth: up to `e`, the new end), and the client's resources; if `keep` (a file with no sync cut),
its `OsMeta` knows the candidates of the bytes cut off. -/
theorem resize_done_worldK (keep : Bool) {st : OsState} {Γb Γm Γf Γt} {h h' : GMap Loc (NonAtomic val)}
    {t : Nat} {tr : Bool} {p : Ino} {tg : Nat} {m : OsMeta} {xs : List ByteG} {n : Nat} {c : OsChange}
    {f : OsFile} (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt)
    (hF : RsFacts st Γb Γm Γt t tr p tg m xs n c f) (e sz' : Nat)
    (hland : (max m.size tg ≤ e ∧ e = rsHi tr m.size tg ∧ sz' = tg) ∨
      (m.size ≤ tg ∧ m.size ≤ e ∧ e ≤ tg ∧ sz' = e))
    (htr : tr = true → rsHi tr m.size tg ≤ e) (hkeep : keep = true → m.cut = none)
    (hmax : sz' ≤ maxBytes)
    (Hr : HeapRendered st ((st.doneInflight t).setFile p (f.land c e sz')) h h')
    (Hfr : MapsFresh st ((st.doneInflight t).setFile p (f.land c e sz')) h) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt -∗
      tokRes (gooseOsGS (L := L)) Γt -∗ cellsRes (cellView st) -∗ naHeapCtx tls h -∗
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt t (DFrac.own 1)
        (⟨p, rsKind tr tg, n, m, rsAnn n xs⟩ : TokInfo) ==∗
      (∃ Γb' Γm' Γf' Γt', osWorld (L := L) ((st.doneInflight t).setFile p (f.land c e sz'))
        Γb' Γm' Γf' Γt' h') ∗ rsDoneK (L := L) keep tr p tg sz' m xs n := by
  iintro HAb HAm HAf HAt Htok Hcells Hσ Ht
  obtain ⟨hti, hct, hcino, hckind, hclo, hchi, hctg, hcval, hf, hmsz, hxl, hcand, hmo, hml, hcandP⟩ := hF
  subst hcino
  have hR := le_rsHi tr m.size tg
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.ino (DFrac.own 1) ti.meta ∗
        bytesG gooseOsGS ti.ino ti.lo (DFrac.own 1) ti.saved)) hti).1 $$ Htok with ⟨⟨Hm, Hbs⟩, Htok⟩
  have htm : TokInfo.meta ⟨c.ino, rsKind tr tg, n, m, rsAnn n xs⟩ =
      m.announce (min m.size tg) (rsHi tr m.size tg) tg := rsKind_meta ..
  have htlo : TokInfo.lo ⟨c.ino, rsKind tr tg, n, m, rsAnn n xs⟩ = min m.size tg := rsKind_lo ..
  rw [htm, htlo]
  have hszs := hwf.sizes c.ino f hf
  let f2 := f.land c e sz'
  have hsz2 : f2.size = sz' := rfl
  have hcache : ∀ b, f2.cache b = if c.lo ≤ b ∧ b < e then 0 else f.cache b := by
    intro b
    simp only [f2, OsFile.land, inRange, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h1 : c.lo ≤ b ∧ b < e
    · rw [if_pos h1, if_pos h1]
      apply hcval
      simp only [inRange, Bool.and_eq_true, decide_eq_true_eq, hclo, hchi]
      rcases hland with ⟨h2, h3, hl3⟩ | ⟨h2, h3, h4, hl4⟩ <;> rw [hclo] at h1 <;> omega
    · rw [if_neg h1, if_neg h1]
  have hwf2 : OsWf ((st.doneInflight t).setFile c.ino f2) :=
    osWf_setFile' (osWf_done (t := t) hwf) hf (by simp only [f2, OsFile.land]; omega)
      (fun b p0 hp0 => hwf.stamps c.ino f b p0 hf hp0)
  -- the bytes
  obtain ⟨zs, hzs0⟩ : ∃ zs : List Cands,
      zs = (List.range (sz' - m.size)).map (fun j => (f.cand (m.size + j)).dropLast) := ⟨_, rfl⟩
  have hzsl : zs.length = sz' - m.size := by simp [hzs0]
  have hzs : ∀ b, m.size ≤ b → b < sz' → f.cand b = zs.getD (b - m.size) [] ++ [(0, n)] := by
    intro b h1 h2
    obtain ⟨c0, hc0, -⟩ := hcand b (by omega) (by rcases hland with ⟨hl1, hl2, hl3⟩ | ⟨hl1, hl2, hl3, hl4⟩ <;> omega)
    rw [hc0]; congr 1
    rw [List.getD_eq_getElem?_getD]
    simp only [hzs0, List.getElem?_map, List.getElem?_range (show b - m.size < sz' - m.size by omega),
      Option.map_some, Option.getD_some, show m.size + (b - m.size) = b by omega, hc0]
    simp
  obtain ⟨ys, hys0⟩ : ∃ ys : List ByteG, ys = zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)])) :=
    ⟨_, rfl⟩
  have hysl : ys.length = sz' - m.size := by simp [hys0, hzsl]
  icases bytesG_lookup _ c.ino _ _ _ Γb $$ HAb Hbs with %Hbl
  imod bytesG_delete _ c.ino (min m.size tg) (rsAnn n xs) Γb $$ [HAb Hbs] with HAb
  · iframe
  have hdl : (rsAnn n xs).length = m.size - tg := by rw [rsAnn_length, hxl]
  rw [hdl]
  have hfree : ∀ j, j < ys.length →
      deleteBytes c.ino (min m.size tg) (m.size - tg) Γb !! (c.ino, m.size + j) = none := by
    intro j hj
    rw [lookup_deleteBytes]
    split
    · rfl
    · cases hb : Γb !! (c.ino, m.size + j) with
      | none => rfl
      | some x =>
        exfalso
        obtain ⟨f2', hf2, hb2, -⟩ := hcoh.bytes _ _ _ hb
        rw [hf] at hf2; cases hf2
        omega
  imod bytesG_alloc _ c.ino m.size ys _ hfree $$ HAb with ⟨HAb, Hys⟩
  have hcoh2 : OsCoh ((st.doneInflight t).setFile c.ino f2)
      (insertBytes c.ino m.size ys (deleteBytes c.ino (min m.size tg) (m.size - tg) Γb))
      (<[c.ino := rsPostK keep tr m tg sz' n xs]> Γm) Γf (GMap.delete t Γt) := by
    refine osCoh_setFile (osCoh_done hcoh) hf (noTok_done hwf hcoh hct) _ _ _ rfl rfl ?_ ?_ ?_ ?_
      (Nat.le_refl _) (fun c0 hc0 => hcoh.cut_le _ _ c0 hml (by simpa [rsPostK_cut, rsPost] using hc0))
    · have hlo := hmo.lo
      have hhi := hmo.hi
      simp only [announce_lo, announce_hi] at hlo hhi
      refine ⟨rfl, ?_, ?_, fun b len => by
          have h1 := hmo.maps b len; simp only [announce_maps] at h1
          simp only [rsPostK_maps, rsPost, announce_maps]; exact h1,
        fun t2 c2 h1 h2 => ?_, fun b hb hn => ?_, fun z hz => ?_, fun b cs hb hc => ?_,
        fun b hb hbz => ?_, fun s hs => ?_⟩
      rotate_right 1
      · show s ∈ f.rzs
        have hmz : ∀ s ∈ m.rz, s ∈ f.rzs := fun s hs => hmo.rz s (by simpa using hs)
        cases keep with
        | false => exact hmz s (by simpa [rsPostK, rsPost] using hs)
        | true =>
          rcases List.mem_cons.1 (show s ∈ n :: m.rz from hs) with rfl | hs
          · obtain ⟨f1, hf1, hn1⟩ := hcoh.tok_rz t _ hti (by cases tr <;> rfl)
            rw [hf] at hf1; cases hf1; exact hn1
          · exact hmz s hs
      rotate_right 2
      · rw [show f2.cand b = f.cand b from rfl]
        have hcase : (keep = true ∧ min m.size tg ≤ b ∧ b < rsHi tr m.size tg ∧ sz' ≤ b ∧
              (if b < m.size then some ((xs.getD (b - min m.size tg) (0, [])).2 ++ [(0, n)])
                else (m.pc b).map (· ++ [(0, n)])) = some cs) ∨
            (m.announce (min m.size tg) (rsHi tr m.size tg) tg).tc !! b = some cs := by
          cases keep with
          | false => exact .inr hc
          | true =>
            change rsTail tr m tg sz' n xs !! b = some cs at hc
            rw [rsTail_lookup] at hc
            split at hc
            · rename_i hin; exact .inl ⟨rfl, hin.1, hin.2.1, hin.2.2, hc⟩
            · exact .inr hc
        rcases hcase with ⟨hk1, h1, h2, h3, hcs⟩ | hc'
        · split at hcs
          · -- a byte cut off: its candidates, from its byte resource (no sync cut)
            rename_i hbs
            cases hcs
            have hk : b - min m.size tg < (rsAnn n xs).length := by rw [rsAnn_length]; omega
            obtain ⟨f1, hf1, -, -, -, hrel⟩ := hcoh.bytes _ _ _ (Hbl _ hk)
            rw [hf] at hf1; cases hf1
            have hcut : cutOf Γm c.ino = none := by
              simp [cutOf, hml, OsMeta.announce_cut, hkeep hk1]
            rw [hcut] at hrel
            simp only [CandRel] at hrel
            rw [show min m.size tg + (b - min m.size tg) = b by omega] at hrel
            rw [hrel]
            have hk' : b - min m.size tg < xs.length := by simpa using hk
            simp only [rsAnn, List.getElem_map, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem hk', Option.getD_some]
          · -- a byte past the old size: the candidates `m` knew, then the zero
            rename_i hbs
            obtain ⟨c1, hc1, rfl⟩ := Option.map_eq_some_iff.1 hcs
            exact hcandP b c1 (by omega) h2 hc1
        · have hr := hc'
          rw [announce_tc] at hr
          split at hr
          · cases hr
          · rename_i hnr
            refine hmo.tail b cs ?_ hc'
            have hb2 : sz' ≤ b := hb
            simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hnr
            rw [← hmsz]
            rcases hland with ⟨hl1, hl2, rfl⟩ | ⟨hl1, hl2, hl3, rfl⟩ <;> omega
      · -- the page cache known zero past the size
        have hb2 : sz' ≤ b := hb
        have hbz2 : b < rsCz tr m.size tg m.cz := hbz
        have hsb : m.size ≤ b ∧ ¬ (c.lo ≤ b ∧ b < e) ∨ (c.lo ≤ b ∧ b < e) := by
          rw [hclo]; rcases hland with ⟨hl1, hl2, rfl⟩ | ⟨hl1, hl2, hl3, rfl⟩ <;> omega
        rw [hcache b]
        rcases hsb with ⟨hsb, hne⟩ | hin
        · rw [if_neg hne]
          refine hmo.cz b (by omega) ?_
          rw [announce_cz]
          unfold rsCz at hbz2
          cases tr with
          | false => exact hbz2
          | true =>
            have := htr rfl
            simp only [if_true] at hbz2
            rw [hclo] at hne
            omega
        · rw [if_pos hin]
      · simp only [rsPostK_lo, rsPost, f2, OsFile.land, announce_lo]
        rcases hland with ⟨hl1, hl2, rfl⟩ | ⟨hl1, hl2, hl3, rfl⟩ <;> omega
      · simp only [rsPostK_hi, rsPost, f2, OsFile.land, announce_hi]
        rcases hland with ⟨hl1, hl2, rfl⟩ | ⟨hl1, hl2, hl3, rfl⟩ <;> omega
      · exfalso
        have h1' := doneInflight_sub st t t2 c2 h1
        have := hwf.infl_one t2 c2 t c h1' hct h2
        subst this; simp [OsState.setFile, OsState.doneInflight] at h1
      · have hn' : ¬ ((m.touch (min m.size tg) (rsHi tr m.size tg)).dlo ≤ b ∧
            b < (m.touch (min m.size tg) (rsHi tr m.size tg)).dhi) := hn
        obtain ⟨h1, h2⟩ := not_touch hn'
        have hb' : b < f.size := by
          rw [← hmsz]; rcases hland with ⟨hl1, hl2, rfl⟩ | ⟨hl1, hl2, hl3, rfl⟩ <;> omega
        have := hmo.dur b hb' hn
        rw [show f2.cand b = f.cand b from rfl, this, hcache b, if_neg (by rw [hclo]; omega)]
      · simp only [rsPostK_zf, rsPost, announce_zf, Option.map_eq_some_iff] at hz
        obtain ⟨z0, hz0, rfl⟩ := hz
        have := hmo.zf _ (by simp only [announce_zf, hz0]; rfl)
        refine ⟨?_, fun b hb => this.2 b hb⟩
        have h1 := this.1
        show sz' ≤ _
        rw [← hmsz] at h1
        by_cases hlh : min m.size tg < rsHi tr m.size tg <;>
          simp only [hlh, if_true, if_false] at h1 ⊢ <;>
          rcases hland with ⟨hl1, hl2, rfl⟩ | ⟨h2, h3, h4, rfl⟩ <;> omega
    · intro b x hx
      rw [lookup_insertBytes] at hx
      split at hx
      · rename_i hr
        obtain ⟨-, h1, h2⟩ := hr
        have hj : b - m.size < ys.length := by omega
        rw [List.getElem?_eq_getElem hj] at hx; cases hx
        rw [hysl] at hj
        refine ⟨by show b < sz'; omega, ?_⟩
        simp only [hys0, List.getElem_map]
        refine ⟨?_, ⟨n, by simp⟩, ?_⟩
        · rw [hcache b, if_pos ⟨by rw [hclo]; omega, by rcases hland with ⟨hl1, hl2, hl3⟩ | ⟨hl1, hl2, hl3, rfl⟩ <;> omega⟩]
        · apply CandRel.of_eq
          show f.cand b = _
          rw [hzs b h1 (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
          rfl
      · rename_i hr
        rw [lookup_deleteBytes] at hx
        split at hx
        · cases hx
        · rename_i hr2
          obtain ⟨f1, hf1, hb, hx1, hmem, hrel⟩ := hcoh.bytes _ _ _ hx
          rw [hf] at hf1; cases hf1
          have hb2 : b < sz' := by
            rw [← hmsz] at hb
            rcases hland with ⟨h3, hl2, rfl⟩ | ⟨hl1, hl2, hl3, rfl⟩
            · apply Classical.byContradiction; intro h4
              exact hr2 ⟨rfl, by omega, by omega⟩
            · omega
          refine ⟨hb2, ?_, hmem, ?_⟩
          · rw [hx1, hcache b, if_neg (by rw [hclo]; rw [← hmsz] at hb; omega)]
          · simp only [cutOf, hml, Option.bind_some, OsMeta.announce_cut] at hrel
            show CandRel (rsPost tr m tg sz').cut x.2 (f.cand b)
            simpa [rsPost] using hrel
    · intro b hb
      rw [lookup_insertBytes]
      split
      · rename_i hr; rw [List.getElem?_eq_getElem (by omega)]; rfl
      · rename_i hr
        rw [lookup_deleteBytes, if_neg]
        · apply hcoh.bytes_full _ f b hf
          rw [← hmsz]
          apply Classical.byContradiction; intro h4
          apply hr; refine ⟨rfl, by omega, ?_⟩
          rw [hysl]; show b < m.size + (sz' - m.size); omega
        · rintro ⟨-, h1, h2⟩
          change b < sz' at hb
          rcases hland with ⟨hl1, hl2, rfl⟩ | ⟨h3, hl2, hl3, rfl⟩ <;> omega
    · intro q b hq
      rw [lookup_insertBytes, if_neg (fun h => hq h.1), lookup_deleteBytes, if_neg (fun h => hq h.1)]
  -- the cells
  have hI2 := fun q i => (inflightAt_done (t := t) (c := c) hwf hct q i)
  have hmaps : ∀ b len, m.maps !! b = some len ↔ st.proc.maps !! b = some ⟨c.ino, len⟩ := by
    intro b len; have := hmo.maps b len; simpa using this
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmaps b1 l1).1 h1) ((hmaps b2 l2).1 h2) hne)
  have haff : ∀ i, inRange c.lo c.hi i = true ↔ min m.size tg ≤ i ∧ i < rsHi tr m.size tg := by
    intro i; simp only [inRange, Bool.and_eq_true, decide_eq_true_eq, hclo, hchi]
  generalize hC : mapsCells (min m.size tg) (rsHi tr m.size tg) (rsCell sz') m.maps.toList = C
  have hClk := fun l v => hC ▸ lookup_mapsCells (min m.size tg) (rsHi tr m.size tg)
    (rsCell sz') m.maps.toList hdisj l v
  have hTmem : ∀ l, l ∈ C.toList.map (·.1) ↔ (C !! l).isSome := by
    intro l; simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hkv, rfl⟩; rw [(GMap.mem_toList _ _ _).1 hkv]; rfl
    · intro hl; obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
      exact ⟨(l, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  have hTnd : (C.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := C)
  have hin : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l c.ino i ∧ min m.size tg ≤ i ∧
      i < rsHi tr m.size tg ∧ C !! l = some (rsCell sz' i) := by
    intro l hl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨i, ⟨b, len, hm, h1, h2, h3, rfl⟩, rfl⟩ := (hClk _ v).1 hv
    exact ⟨i, ⟨b, ⟨c.ino, len⟩, (hmaps b len).1 ((GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
      h1, h2, hv⟩
  have hfk : ((st.doneInflight t).setFile c.ino f2).file c.ino = some f2 := file_setFile_eq _ _ _
  have hcont_in : ∀ i, min m.size tg ≤ i → i < rsHi tr m.size tg →
      f2.contents[i]? = if i < sz' then some (0 : w8) else none := by
    intro i h1 h2
    rw [contents_getElem?, hsz2]
    by_cases hlt : i < sz'
    · rw [if_pos hlt, if_pos hlt, hcache i, if_pos]
      refine ⟨by rw [hclo]; exact h1, ?_⟩
      rcases hland with ⟨hl1, rfl, rfl⟩ | ⟨hl1, hl2, hl3, rfl⟩ <;> omega
    · rw [if_neg hlt, if_neg hlt]
  have hcont_out : ∀ i, ¬ (min m.size tg ≤ i ∧ i < rsHi tr m.size tg) →
      f2.contents[i]? = f.contents[i]? := by
    intro i hi
    have hc := hcache i
    rw [if_neg (fun h => hi ⟨by rw [← hclo]; exact h.1, by
      rcases hland with ⟨hl1, rfl, hl3⟩ | ⟨hl1, hl2, h4, hl4⟩ <;> omega⟩)] at hc
    rw [contents_getElem?, contents_getElem?, hsz2, hc, ← hmsz]
    by_cases h1 : i < m.size
    · rw [if_pos h1, if_pos]; rcases hland with ⟨hl1, hl2, rfl⟩ | ⟨hl1, hl2, hl3, rfl⟩ <;> omega
    · rw [if_neg h1, if_neg]; rcases hland with ⟨hl1, hl2, rfl⟩ | ⟨hl1, hl2, hl3, rfl⟩ <;> omega
  imod cells_step st _ h h' (C.toList.map (·.1)) ∅ C hwf hwf2 Hr Hfr (fun b m0 h0 => .inr h0) hTnd
    (fun l hl => by obtain ⟨i, hi, -⟩ := hin l ((hTmem l).1 hl); exact .inl ⟨_, _, hi⟩)
    (fun l v h => by simp at h)
    (fun l v hl => by
      have hs : (C !! l).isSome := by rw [hl]; rfl
      obtain ⟨i, hi, h1, h2, hv⟩ := hin l hs
      rw [hl] at hv; cases hv
      have hn : ¬ InflightAt ((st.doneInflight t).setFile c.ino f2) c.ino i := fun h =>
        ((hI2 _ _).1 h).2 rfl
      refine ⟨(hTmem l).2 hs, _, by rw [cellView_mapsTo hwf2 hi, decide_eq_false hn], ?_⟩
      rw [cellByte_eq, if_neg hn, hfk]
      simp only [Option.bind_some]
      rw [hcont_in i h1 h2]; rfl)
    (fun l hl _ x hx => by
      obtain ⟨i, hi, h1, h2, -⟩ := hin l ((hTmem l).1 hl)
      rw [cellView_mapsTo hwf hi] at hx; cases hx
      exact decide_eq_true ⟨t, c, hct, rfl, (haff i).2 ⟨h1, h2⟩⟩)
    (fun l hl hn => by
      rw [Option.isSome_iff_exists.1 ((hTmem l).1 hl) |>.choose_spec] at hn; cases hn)
    (fun l hl => by
      by_cases hm : Mapped st l
      · obtain ⟨q', i, hqi⟩ := hm
        rw [cellView_mapsTo hwf2 hqi, cellView_mapsTo hwf hqi, cellByte_eq, cellByte_eq]
        by_cases hpq : c.ino = q'
        · subst hpq
          have hn : ¬ (min m.size tg ≤ i ∧ i < rsHi tr m.size tg) := by
            rintro ⟨h1, h2⟩
            obtain ⟨b, m0, hb, hp0, hi0, rfl⟩ := hqi
            have hb' : m.maps !! b = some m0.len :=
              (hmaps b m0.len).2 (by rw [hb]; congr 1; cases m0; simp only at hp0 ⊢; rw [hp0])
            apply hl; apply (hTmem _).2
            rw [(hClk _ _).2 ⟨i, ⟨b, m0.len, (GMap.mem_toList _ _ _).2 hb', h1, h2, hi0, rfl⟩, rfl⟩]
            rfl
          have hnI : ¬ InflightAt st c.ino i := by
            rintro ⟨t2, c2, h1, h2, h3⟩
            have := hwf.infl_one t2 c2 t c h1 hct h2; subst this
            rw [hct] at h1; cases h1
            exact hn ((haff i).1 h3)
          have hnI2 : ¬ InflightAt ((st.doneInflight t).setFile c.ino f2) c.ino i := fun h =>
            ((hI2 _ _).1 h).2 rfl
          rw [if_neg hnI, if_neg hnI2, hfk, hf]
          simp only [Option.bind_some]
          rw [hcont_out i hn]
          simp only [hnI, hnI2, decide_false]
        · have hII : InflightAt ((st.doneInflight t).setFile c.ino f2) q' i ↔ InflightAt st q' i := by
            have := hI2 q' i
            exact ⟨fun h => (this.1 h).1, fun h => this.2 ⟨h, fun e => hpq e.symm⟩⟩
          have hF : ((st.doneInflight t).setFile c.ino f2).file q' = st.file q' :=
            file_setFile_ne _ _ hpq
          rw [hF]
          by_cases hq : InflightAt st q' i
          · rw [if_pos hq, if_pos (hII.2 hq)]; simp only [hII]
          · rw [if_neg hq, if_neg (fun h => hq (hII.1 h))]; simp only [hII]
      · rw [cellView_none (st := st) hm]; exact cellView_none hm)
    $$ [Hσ Hcells] with ⟨Hσ, Hcells, Hc⟩
  · iframe; unfold halves; iapply BigSepM.bigSepM_empty.2; iempintro
  imod gAuth_update _ _ _ _ _ (rsPostK keep tr m tg sz' n xs) $$ HAm Hm with ⟨HAm, Hm⟩
  imod gAuth_delete _ _ _ _ _ $$ HAt Ht with HAt
  have hzsfact : ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)] := by
    intro j z hz hzj hj
    rw [hzsl] at hj
    obtain ⟨c0, hc0, hz0⟩ := hcand (m.size + j) (by omega)
      (by rcases hland with ⟨hl1, hl2, rfl⟩ | ⟨hl1, hl2, hl3, rfl⟩ <;> omega)
    have := hz0 z hz hzj
    simp only [hzs0, List.getElem?_map, List.getElem?_range hj, hc0, this, Option.map_some]
    simp
  imodintro
  isplitr [Hm Hys Hc]
  · iexists _, _, Γf, _
    unfold osWorld tokRes
    iframe HAb HAm HAf HAt Hσ Hcells Htok
    ipureintro; exact ⟨hwf2, hcoh2⟩
  unfold rsDoneK osMeta osBytes
  subst hys0
  iexists zs
  iframe Hm Hys
  isplitr
  · ipureintro; exact ⟨hzsl, hzsfact⟩
  unfold mcells
  iapply (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
    cellsR b (min (min m.size tg) len) (min (rsHi tr m.size tg) len - min (min m.size tg) len)
      (rsCell sz'))).2
  iapply (halves_mapsCells _ _ _ _ hdisj).1
  rw [hC]; iexact Hc


/-- **A resize landed** (`resize_done_worldK` without the candidates of the bytes cut off). -/
theorem resize_done_world {st : OsState} {Γb Γm Γf Γt} {h h' : GMap Loc (NonAtomic val)}
    {t : Nat} {tr : Bool} {p : Ino} {tg : Nat} {m : OsMeta} {xs : List ByteG} {n : Nat} {c : OsChange}
    {f : OsFile} (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt)
    (hF : RsFacts st Γb Γm Γt t tr p tg m xs n c f) (e sz' : Nat)
    (hland : (max m.size tg ≤ e ∧ e = rsHi tr m.size tg ∧ sz' = tg) ∨
      (m.size ≤ tg ∧ m.size ≤ e ∧ e ≤ tg ∧ sz' = e))
    (htr : tr = true → rsHi tr m.size tg ≤ e) (hmax : sz' ≤ maxBytes)
    (Hr : HeapRendered st ((st.doneInflight t).setFile p (f.land c e sz')) h h')
    (Hfr : MapsFresh st ((st.doneInflight t).setFile p (f.land c e sz')) h) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt -∗
      tokRes (gooseOsGS (L := L)) Γt -∗ cellsRes (cellView st) -∗ naHeapCtx tls h -∗
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt t (DFrac.own 1)
        (⟨p, rsKind tr tg, n, m, rsAnn n xs⟩ : TokInfo) ==∗
      (∃ Γb' Γm' Γf' Γt', osWorld (L := L) ((st.doneInflight t).setFile p (f.land c e sz'))
        Γb' Γm' Γf' Γt' h') ∗ rsDone (L := L) tr p tg sz' m n := by
  rw [← rsDoneK_false (xs := xs)]
  exact resize_done_worldK false hwf hcoh hF e sz' hland htr (fun h => by cases h) hmax Hr Hfr

/-- **A resize that did not land**: the change done, the file as its first step left it. -/
theorem resize_undone_world {st : OsState} {Γb Γm Γf Γt} {h h' : GMap Loc (NonAtomic val)}
    {t : Nat} {tr : Bool} {p : Ino} {tg : Nat} {m : OsMeta} {xs : List ByteG} {n : Nat} {c : OsChange}
    {f : OsFile} (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt)
    (hF : RsFacts st Γb Γm Γt t tr p tg m xs n c f)
    (Hr : HeapRendered st (st.doneInflight t) h h') (Hfr : MapsFresh st (st.doneInflight t) h) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt -∗
      tokRes (gooseOsGS (L := L)) Γt -∗ cellsRes (cellView st) -∗ naHeapCtx tls h -∗
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt t (DFrac.own 1)
        (⟨p, rsKind tr tg, n, m, rsAnn n xs⟩ : TokInfo) ==∗
      (∃ Γb' Γm' Γf' Γt', osWorld (L := L) (st.doneInflight t) Γb' Γm' Γf' Γt' h') ∗
        rsUndone (L := L) tr p tg m xs n := by
  iintro HAb HAm HAf HAt Htok Hcells Hσ Ht
  obtain ⟨hti, hct, hcino, hckind, hclo, hchi, hctg, hcval, hf, hmsz, hxl, hcand, hmo, hml, hcandP⟩ := hF
  subst hcino
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem gooseOsGS gooseOsGS.γm ti.ino (DFrac.own 1) ti.meta ∗
        bytesG gooseOsGS ti.ino ti.lo (DFrac.own 1) ti.saved)) hti).1 $$ Htok with ⟨⟨Hm, Hbs⟩, Htok⟩
  have htm : TokInfo.meta ⟨c.ino, rsKind tr tg, n, m, rsAnn n xs⟩ =
      m.announce (min m.size tg) (rsHi tr m.size tg) tg := rsKind_meta ..
  have htlo : TokInfo.lo ⟨c.ino, rsKind tr tg, n, m, rsAnn n xs⟩ = min m.size tg := rsKind_lo ..
  rw [htm, htlo]
  icases bytesG_lookup _ c.ino _ _ _ Γb $$ HAb Hbs with %Hbl
  have hxs : ∀ j (hj : j < xs.length), (xs[j]).1 = f.cache (min m.size tg + j) := by
    intro j hj
    obtain ⟨f1, hf1, -, hx⟩ := hcoh.bytes _ _ _ (Hbl j (by simpa using hj))
    rw [hf] at hf1; cases hf1
    simp only [rsAnn, List.getElem_map, Prod.mk.injEq] at hx
    exact hx.1
  have hwf0 := osWf_done (t := t) hwf
  have hI2 := fun q i => (inflightAt_done (t := t) (c := c) hwf hct q i)
  have hmaps : ∀ b len, m.maps !! b = some len ↔ st.proc.maps !! b = some ⟨c.ino, len⟩ := by
    intro b len; have := hmo.maps b len; simpa using this
  have hdisj : MapsDisj m.maps.toList := mapsDisj_toList _ (fun b1 l1 b2 l2 h1 h2 hne =>
    hwf.maps_disj b1 _ b2 _ ((hmaps b1 l1).1 h1) ((hmaps b2 l2).1 h2) hne)
  have haff : ∀ i, inRange c.lo c.hi i = true ↔ min m.size tg ≤ i ∧ i < rsHi tr m.size tg := by
    intro i; simp only [inRange, Bool.and_eq_true, decide_eq_true_eq, hclo, hchi]
  generalize hC : mapsCells (min m.size tg) (rsHi tr m.size tg) (rsOld m.size (min m.size tg) xs)
    m.maps.toList = C
  have hClk := fun l v => hC ▸ lookup_mapsCells (min m.size tg) (rsHi tr m.size tg)
    (rsOld m.size (min m.size tg) xs) m.maps.toList hdisj l v
  have hTmem : ∀ l, l ∈ C.toList.map (·.1) ↔ (C !! l).isSome := by
    intro l; simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, v⟩, hkv, rfl⟩; rw [(GMap.mem_toList _ _ _).1 hkv]; rfl
    · intro hl; obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
      exact ⟨(l, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  have hTnd : (C.toList.map (·.1)).Nodup := Iris.Std.LawfulFiniteMap.toList_noDupKeys (m := C)
  have hin : ∀ l, (C !! l).isSome → ∃ i, MapsTo st l c.ino i ∧ min m.size tg ≤ i ∧
      i < rsHi tr m.size tg ∧ C !! l = some (rsOld m.size (min m.size tg) xs i) := by
    intro l hl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨i, ⟨b, len, hm, h1, h2, h3, rfl⟩, rfl⟩ := (hClk _ v).1 hv
    exact ⟨i, ⟨b, ⟨c.ino, len⟩, (hmaps b len).1 ((GMap.mem_toList _ _ _).1 hm), rfl, h3, rfl⟩,
      h1, h2, hv⟩
  have hfk : (st.doneInflight t).file c.ino = some f := hf
  have hcont_in : ∀ i, min m.size tg ≤ i → i < rsHi tr m.size tg →
      toCellVal f.contents[i]? = rsOld m.size (min m.size tg) xs i := by
    intro i h1 h2
    rw [contents_getElem?, ← hmsz]
    unfold rsOld
    by_cases hlt : i < m.size
    · rw [if_pos hlt, if_pos hlt]
      have hbx : i - min m.size tg < xs.length := by rw [hxl]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbx]
      simp only [Option.getD_some]
      have := hxs _ hbx; rw [show min m.size tg + (i - min m.size tg) = i by omega] at this
      rw [this]
    · rw [if_neg hlt, if_neg hlt]
  imod cells_step st _ h h' (C.toList.map (·.1)) ∅ C hwf hwf0 Hr Hfr (fun b m0 h0 => .inr h0) hTnd
    (fun l hl => by obtain ⟨i, hi, -⟩ := hin l ((hTmem l).1 hl); exact .inl ⟨_, _, hi⟩)
    (fun l v h => by simp at h)
    (fun l v hl => by
      have hs : (C !! l).isSome := by rw [hl]; rfl
      obtain ⟨i, hi, h1, h2, hv⟩ := hin l hs
      rw [hl] at hv; cases hv
      have hn : ¬ InflightAt (st.doneInflight t) c.ino i := fun h => ((hI2 _ _).1 h).2 rfl
      refine ⟨(hTmem l).2 hs, _, by rw [cellView_mapsTo hwf0 hi, decide_eq_false hn], ?_⟩
      rw [cellByte_eq, if_neg hn, hfk]
      simp only [Option.bind_some]
      rw [hcont_in i h1 h2])
    (fun l hl _ x hx => by
      obtain ⟨i, hi, h1, h2, -⟩ := hin l ((hTmem l).1 hl)
      rw [cellView_mapsTo hwf hi] at hx; cases hx
      exact decide_eq_true ⟨t, c, hct, rfl, (haff i).2 ⟨h1, h2⟩⟩)
    (fun l hl hn => by
      rw [Option.isSome_iff_exists.1 ((hTmem l).1 hl) |>.choose_spec] at hn; cases hn)
    (fun l hl => by
      by_cases hm : Mapped st l
      · obtain ⟨q', i, hqi⟩ := hm
        rw [cellView_mapsTo hwf0 hqi, cellView_mapsTo hwf hqi, cellByte_eq, cellByte_eq]
        by_cases hpq : c.ino = q'
        · subst hpq
          have hn : ¬ (min m.size tg ≤ i ∧ i < rsHi tr m.size tg) := by
            rintro ⟨h1, h2⟩
            obtain ⟨b, m0, hb, hp0, hi0, rfl⟩ := hqi
            have hb' : m.maps !! b = some m0.len :=
              (hmaps b m0.len).2 (by rw [hb]; congr 1; cases m0; simp only at hp0 ⊢; rw [hp0])
            apply hl; apply (hTmem _).2
            rw [(hClk _ _).2 ⟨i, ⟨b, m0.len, (GMap.mem_toList _ _ _).2 hb', h1, h2, hi0, rfl⟩, rfl⟩]
            rfl
          have hnI : ¬ InflightAt st c.ino i := by
            rintro ⟨t2, c2, h1, h2, h3⟩
            have := hwf.infl_one t2 c2 t c h1 hct h2; subst this
            rw [hct] at h1; cases h1
            exact hn ((haff i).1 h3)
          have hnI2 : ¬ InflightAt (st.doneInflight t) c.ino i := fun h => ((hI2 _ _).1 h).2 rfl
          rw [if_neg hnI, if_neg hnI2]
          simp only [hnI, hnI2, decide_false]
          rfl
        · have hII : InflightAt (st.doneInflight t) q' i ↔ InflightAt st q' i := by
            have := hI2 q' i
            exact ⟨fun h => (this.1 h).1, fun h => this.2 ⟨h, fun e => hpq e.symm⟩⟩
          by_cases hq : InflightAt st q' i
          · rw [if_pos hq, if_pos (hII.2 hq)]; simp only [hII]
          · rw [if_neg hq, if_neg (fun h => hq (hII.1 h))]; simp only [hII]; rfl
      · rw [cellView_none (st := st) hm]; exact cellView_none hm)
    $$ [Hσ Hcells] with ⟨Hσ, Hcells, Hc⟩
  · iframe; unfold halves; iapply BigSepM.bigSepM_empty.2; iempintro
  imod gAuth_delete _ _ _ _ _ $$ HAt Ht with HAt
  imodintro
  isplitr [Hm Hbs Hc]
  · iexists _, _, Γf, _
    unfold osWorld tokRes
    iframe HAb HAm HAf HAt Hσ Hcells Htok
    ipureintro; exact ⟨hwf0, osCoh_done hcoh⟩
  unfold rsUndone osMeta osBytes
  iframe Hm Hbs
  unfold mcells
  iapply (BigSepM.bigSepM_toList (Φ := fun (b : Loc) (len : Nat) =>
    cellsR b (min (min m.size tg) len) (min (rsHi tr m.size tg) len - min (min m.size tg) len)
      (rsOld m.size (min m.size tg) xs))).2
  iapply (halves_mapsCells _ _ _ _ hdisj).1
  rw [hC]; iexact Hc

/-- The first step of `ftruncate(fd, sz)`: `wp_osResizeStart`. -/
theorem wp_osFtruncateStart (fd sz : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG)
    (hE : ↑osN ⊆ E) (hwr : d.writable = true) (hsz0 : 0 ≤ sz.toInt)
    (hlen : xs.length = m.size - sz.toNat) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      osBytes (L := L) d.ino (min m.size sz.toNat) (DFrac.own 1) xs -∗
      mcellsAny m.maps (min m.size sz.toNat) (rsHi true m.size sz.toNat) -∗
      (∀ t : Nat, ∀ n : Nat, ⌜0 < n ∧ m.TcZ ∧ ∀ x ∈ xs, ∀ q ∈ x.2, q.2 < n⌝ -∗ osFd (L := L) fd dq d -∗
        rsTok true t d.ino sz.toNat m xs n -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) @ s; E {{ Φ }} := by
  refine wp_osResizeStart "FtruncateStart" _ (by simp [DataOp]) (by simp [val.isPanic]) true fd
    sz.toNat dq d m xs hE (fun st f t hfd hf hnb ht hc _ => ?_) (fun st e' st' hfd _ hst => ?_) hlen Φ
  · simp only [IsFsStep]
    exact ⟨fd, sz, t, d, f, rfl, hfd, hwr, hsz0, hnb, hf, ht, hc, rfl, rfl⟩
  · simp only [IsFsStep] at hst
    obtain ⟨fd', sz', t, d', f, hv, hfd', -, -, -, hf, ht, -, hst', rfl⟩ := hst
    injection hv with h1 h2
    cases go.intoVal_inj h1; cases go.intoVal_inj h2
    simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
    exact ⟨f, t, hf, ht, rfl, hst'⟩

/-- The second step of `ftruncate`: on success the file has the new size (`rsDoneK`); on failure it
may have, or be as its first step left it (`rsUndone`). If `keep` (a file with no sync cut), the
`OsMeta` it lands with knows the candidates of the bytes cut off (`rsPostK`). -/
theorem wp_osFtruncateFinishK (keep : Bool) (t : Nat) (p : Ino) (tg : Nat) (m : OsMeta)
    (xs : List ByteG) (n : Nat) (hkeep : keep = true → m.cut = none) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ rsTok (L := L) true t p tg m xs n -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ rsDoneK (L := L) keep true p tg tg m xs n) ∨
         (⌜e ≠ 0⌝ ∗ (rsDoneK (L := L) keep true p tg tg m xs n ∨ rsUndone (L := L) true p tg m xs n))) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FtruncateFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_os_step "FtruncateFinish" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold rsTok osTok
  icases Ht with ⟨Ht, %hxl⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  obtain ⟨c, f, hF⟩ := rsFacts_of hcoh Hti hxl
  have hcp := hF.hcino
  subst hcp
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  have hwf1 : c.target ≤ maxBytes → OsWf ((st.doneInflight t).setFile c.ino (f.land c c.hi c.target)) :=
    fun htm => osWf_setFile' (osWf_done (t := t) hwf) hF.hf
      (by have := hwf.sizes c.ino f hF.hf; simp only [OsFile.land]; omega)
      (fun b p0 hp0 => hwf.stamps c.ino f b p0 hF.hf hp0)
  have hland' : (max m.size tg ≤ c.hi ∧ c.hi = rsHi true m.size tg ∧ tg = tg) ∨
      (m.size ≤ tg ∧ m.size ≤ c.hi ∧ c.hi ≤ tg ∧ tg = c.hi) :=
    .inl ⟨hF.hchi ▸ le_rsHi true m.size tg, hF.hchi, rfl⟩
  imodintro
  isplitr
  · ipureintro
    by_cases htm : c.target ≤ maxBytes
    · exact ⟨_, renderHeap ((st.doneInflight t).setFile c.ino (f.land c c.hi c.target)) h, _,
        ⟨t, c, tg, f, rfl, hF.hct, hF.hckind, hF.hf, .inl ⟨htm, rfl, rfl⟩⟩,
        mapsFresh_same rfl, heapRendered_render (hwf1 htm) rfl Hh⟩
    · exact ⟨_, renderHeap (st.doneInflight t) h, _,
        ⟨t, c, tg, f, rfl, hF.hct, hF.hckind, hF.hf, .inr ⟨27, by decide, rfl, .inl rfl⟩⟩,
        mapsFresh_same rfl, heapRendered_render (osWf_done hwf) rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨t', c', tg', f', hv, hinfl, hkind', hf', hres⟩ := Hst
  have htt : t = t' := by injection hv with hv; exact extVal_inj hv
  subst htt
  rw [hF.hct, Option.some.injEq] at hinfl; subst hinfl
  rw [hF.hckind] at hkind'; simp only [rsKind, if_true] at hkind'; injection hkind' with ho; subst ho
  rw [hF.hf, Option.some.injEq] at hf'; subst hf'
  rcases hres with ⟨htm, rfl, rfl⟩ | ⟨e, he, rfl, rfl | ⟨htm, rfl⟩⟩
  · rw [hF.hctg] at Hr Hfr htm ⊢
    imod resize_done_worldK keep hwf hcoh hF c.hi tg hland' (fun _ => Nat.le_of_eq hF.hchi.symm) hkeep htm Hr Hfr $$ HAb HAm HAf HAt Htok Hcells Hσ Ht
      with ⟨⟨%Γb', %Γm', %Γf', %Γt', Hw⟩, Hd⟩
    imodintro
    iexists Γb', Γm', Γf', Γt'
    isplitl [Hw]
    · iapply (osWorld_unfold (L := L)).1 $$ Hw
    iapply wp_value'
    iapply HΦ; ileft; iframe; ipureintro; rfl
  · imod resize_undone_world hwf hcoh hF Hr Hfr $$ HAb HAm HAf HAt Htok Hcells Hσ Ht
      with ⟨⟨%Γb', %Γm', %Γf', %Γt', Hw⟩, Hd⟩
    imodintro
    iexists Γb', Γm', Γf', Γt'
    isplitl [Hw]
    · iapply (osWorld_unfold (L := L)).1 $$ Hw
    iapply wp_value'
    iapply HΦ; iright; iframe; ipureintro; exact he
  · rw [hF.hctg] at Hr Hfr htm ⊢
    imod resize_done_worldK keep hwf hcoh hF c.hi tg hland' (fun _ => Nat.le_of_eq hF.hchi.symm) hkeep htm Hr Hfr $$ HAb HAm HAf HAt Htok Hcells Hσ Ht
      with ⟨⟨%Γb', %Γm', %Γf', %Γt', Hw⟩, Hd⟩
    imodintro
    iexists Γb', Γm', Γf', Γt'
    isplitl [Hw]
    · iapply (osWorld_unfold (L := L)).1 $$ Hw
    iapply wp_value'
    iapply HΦ; iright; iframe; ipureintro; exact he

/-- The second step of `ftruncate` (`wp_osFtruncateFinishK` without the candidates of the bytes
cut off). -/
theorem wp_osFtruncateFinish (t : Nat) (p : Ino) (tg : Nat) (m : OsMeta) (xs : List ByteG)
    (n : Nat) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ rsTok (L := L) true t p tg m xs n -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ rsDone (L := L) true p tg tg m n) ∨
         (⌜e ≠ 0⌝ ∗ (rsDone (L := L) true p tg tg m n ∨ rsUndone (L := L) true p tg m xs n))) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FtruncateFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  rw [← rsDoneK_false (xs := xs)]
  exact wp_osFtruncateFinishK false t p tg m xs n (fun h => by cases h) hE Φ

end specs2

end Fs
end Perennial

end
