/-
**What a crash leaves of any sector whose versions are known**, past the size included
(`crashSeen_secAny`; `crashSeen_sec` is the case of a full sector below the size). Untrusted.

A crash leaves sector `n` of a file whose `OsMeta` knows its versions (`OsMeta.vk`) as:

* its durable version (the bytes `OsMeta.dur`/`dz` know), unless the sector is the first of its
  page, known fresh (`OsMeta.fr`) and under the crash's size (ordered growth, `CovCand`);
* its page cache's version, the sector having two (then `n ∈ ns`): the bytes the client holds
  below the size;
* the client's write in flight landed over it in part (`k` bytes, a page cut by `NoTearCrash`, or
  any count for a fresh sector a crash grows over): the write's bytes inside `[off, off + k)`, the
  client's below the size outside, zeros past it;
* the client's growing truncate in flight landed over it: the client's bytes below the size, zeros
  past it.

The sector is whole in each case: never a mix of versions.
-/
module

public import GooseLang.Ext.Fs.CrashSec

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris

/-! ## The changes in flight on a file -/

/-- The only change in flight on the file `i` is `c`. -/
theorem changesOn_single {st : OsState} {i : Ino} {t : Nat} {c : OsChange}
    (hc : st.proc.inflight !! t = some c) (hi : c.ino = i)
    (halone : ∀ t' c', t' ≠ t → st.proc.inflight !! t' = some c' → c'.ino ≠ i) :
    changesOn st i = [c.kind] := by
  unfold changesOn
  rw [List.filter_map]
  generalize hL : st.proc.inflight.toList = L
  have hmemL : ∀ x ∈ L, st.proc.inflight !! x.1 = some x.2 := by
    intro x hx; rw [← hL] at hx; exact (GMap.mem_toList _ _ _).1 hx
  have hnd : (L.map Prod.fst).Nodup := by rw [← hL]; exact GMap.toList_keys_nodup _
  have hall : ∀ x ∈ L.filter ((fun c => decide (c.ino = i)) ∘ (·.2)), x = (t, c) := by
    intro x hx
    rw [List.mem_filter] at hx
    obtain ⟨hx, hxi⟩ := hx
    simp only [Function.comp, decide_eq_true_eq] at hxi
    have hx' := hmemL x hx
    by_cases hxt : x.1 = t
    · rw [hxt, hc] at hx'; cases hx'; rcases x with ⟨x1, x2⟩; simp only at hxt; subst hxt; rfl
    · exact absurd hxi (halone x.1 x.2 hxt hx')
  have hmem : (t, c) ∈ L.filter ((fun c => decide (c.ino = i)) ∘ (·.2)) := by
    rw [List.mem_filter]
    refine ⟨by rw [← hL]; exact (GMap.mem_toList _ _ _).2 hc, ?_⟩
    simp [Function.comp, hi]
  have hnd' : ((L.filter ((fun c => decide (c.ino = i)) ∘ (·.2))).map Prod.fst).Nodup :=
    hnd.sublist ((List.filter_sublist).map _)
  generalize hF : L.filter ((fun c => decide (c.ino = i)) ∘ (·.2)) = F at hall hmem hnd'
  match F, hall, hmem, hnd' with
  | [], _, hmem, _ => cases hmem
  | [x], hall, _, _ => rw [hall x (by simp)]; rfl
  | x :: y :: rest, hall, _, hnd' =>
    have hx := hall x (by simp)
    have hy := hall y (by simp)
    subst hx; rw [hy] at hnd'
    simp at hnd'

/-- Empty writes land nothing. -/
theorem landed_emptyWrites : ∀ {ks : List OsChangeKind} {f g : OsFile}, Landed ks f g →
    (∀ k ∈ ks, ∃ off, k = .write off []) → g = f := by
  intro ks f g h
  induction h with
  | nil f => intro _; rfl
  | write off data k ks f g hk _ ih =>
    intro he
    obtain ⟨off', he'⟩ := he _ List.mem_cons_self
    cases he'
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    have := ih (fun k' hk' => he k' (List.mem_cons_of_mem _ hk'))
    simpa [OsFile.landWrite] using this
  | trunc sz sz' ks f g _ _ _ _ =>
    intro he
    obtain ⟨off', he'⟩ := he _ List.mem_cons_self
    cases he'

/-! ## The sector a landing leaves -/

/-- A landing of a write that misses sector `n` leaves its versions; if `n` is the first of its
page, its freshness too. -/
theorem landWrite_miss (f : OsFile) (off : Nat) (data : List w8) (k : Nat) (hk : k ≤ data.length)
    (hoff : off ≤ f.size) (n : Nat) (hn : k = 0 ∨ secHits (min off f.size) (off + k) n = false) :
    ((f.landWrite off data k).secs n).vers = (f.secs n).vers ∧
    (n % 8 = 0 → ((f.landWrite off data k).secs n).fresh = (f.secs n).fresh) := by
  unfold OsFile.landWrite
  split
  · exact ⟨rfl, fun _ => rfl⟩
  · rename_i hk0
    have hn := hn.resolve_left hk0
    have hlen : (data.take k).length = k := by simp; omega
    have hd : data.take k ≠ [] := fun h => by rw [h] at hlen; simp at hlen; omega
    have hl := written_length f off (data.take k) hd
    rw [hlen] at hl
    simp only [OsFile.change, hn, Bool.false_eq_true, if_false]
    refine ⟨by first | rfl | trivial, fun h8 => ?_⟩
    simp only [secHits, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at hn
    simp only [hl, pageIn, Bool.and_eq_left_iff_imp]
    intro _
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
      Bool.not_eq_false', decide_eq_true_eq, Nat.not_lt]
    omega

/-- A landing of a growing truncate that misses sector `n` leaves its versions; if `n` is the
first of its page, its freshness too. -/
theorem truncate_miss (f : OsFile) (sz : Nat) (hsz : f.size ≤ sz) (n : Nat)
    (hn : secHits (min f.size sz) (max f.size sz) n = false) :
    ((f.truncate sz).secs n).vers = (f.secs n).vers ∧
    (n % 8 = 0 → ((f.truncate sz).secs n).fresh = (f.secs n).fresh) := by
  simp only [OsFile.truncate, OsFile.change, hn, Bool.false_eq_true, if_false]
  refine ⟨by first | rfl | trivial, fun h8 => ?_⟩
  simp only [secHits, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at hn
  simp only [resized_length, pageIn, Bool.and_eq_left_iff_imp]
  intro _
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Bool.not_eq_false', decide_eq_true_eq, Nat.not_lt]
  omega

/-- The bytes of sector `n` after a landing of `k` bytes of a write that hits it: the write's
inside `[off, off + k)`, the file's below its size outside, zeros past it. -/
theorem landWrite_hit_byte (f : OsFile) (off : Nat) (data : List w8) (k : Nat) (hk : k ≤ data.length)
    (hk0 : 0 < k) (hoff : off ≤ f.size) (n : Nat) (hn : secHits (min off f.size) (off + k) n = true)
    (j : Nat) (hj : j < 512) :
    secByte ((f.landWrite off data k).secs n).last j =
      if off ≤ 512 * n + j ∧ 512 * n + j < off + k then data.getD (512 * n + j - off) 0
      else if 512 * n + j < f.size then f.rawAt (512 * n + j) else 0 := by
  have hlen : (data.take k).length = k := by simp; omega
  have hd : data.take k ≠ [] := fun h => by rw [h] at hlen; simp at hlen; omega
  unfold OsFile.landWrite
  rw [if_neg (by omega)]
  simp only [OsFile.change, hn, if_true]
  rw [last_mk_append]
  have h1 := secOf_getD (f.written off (data.take k)) (512 * n + j)
  rw [(divmod_sec n j hj).1, (divmod_sec n j hj).2] at h1
  simp only [secByte]; rw [h1]
  rw [List.getD_eq_getElem?_getD, written_getElem? f off (data.take k) hd hoff, hlen]
  split
  · rename_i hlt
    rw [if_neg (by omega), contents_getElem?]
    split <;> rfl
  · split
    · rename_i h1 h2
      rw [if_pos ⟨by omega, h2⟩, List.getElem?_take, if_pos (by omega)]
      rw [List.getD_eq_getElem?_getD]
    · rename_i h1 h2
      rw [if_neg (by omega), contents_getElem?]
      split <;> rfl

/-- The bytes of sector `n` after a growing truncate's landing that hits it: the file's below its
size, zeros past it. -/
theorem truncate_hit_byte (f : OsFile) (sz : Nat) (hsz : f.size ≤ sz) (n : Nat)
    (hn : secHits (min f.size sz) (max f.size sz) n = true) (j : Nat) (hj : j < 512) :
    secByte ((f.truncate sz).secs n).last j =
      if 512 * n + j < f.size then f.rawAt (512 * n + j) else 0 := by
  simp only [OsFile.truncate, OsFile.change, hn, if_true]
  rw [last_mk_append]
  have h1 := secOf_getD (f.resized sz) (512 * n + j)
  rw [(divmod_sec n j hj).1, (divmod_sec n j hj).2] at h1
  simp only [secByte]; rw [h1]
  rw [List.getD_eq_getElem?_getD, resized_getElem?]
  split
  · split <;> rfl
  · split
    · omega
    · rfl

/-! ## The crash lemma -/

section seen
variable {Q : OsState → OsState → Prop}

/-- Sector `n` is the first of its page, known fresh by `m`, and under the size `sz`: a crash to
`sz` never leaves its durable version (ordered growth). -/
def FreshCov (m : OsMeta) (n sz : Nat) : Prop :=
  n % 8 = 0 ∧ (∃ p, m.fr = some p ∧ p ≤ 512 * n) ∧ 512 * n < sz

/-- **A crash leaves any sector whose versions are known whole** (see the file header). -/
theorem crashSeen_secAny (hQ : ∀ st st', Q st st' → NoTearCrash st st') {i : Ino} {m : OsMeta}
    {rs : List (Nat × DFrac × List (w8 × Bool))} {ts : List (Nat × TokInfo)} {f' : OsFile}
    (h : CrashSeenR Q i m rs ts (some f')) {ns : List Nat} (hvk : m.vk = some ns) (n : Nat)
    (hts : (ts = [] ∧ ∀ b < m.size, ∃ r ∈ rs, r.1 ≤ b ∧ b < r.1 + r.2.2.length) ∨
      ∃ t ti, ts = [(t, ti)] ∧ ti.q = 1 ∧ ti.c.ino = i ∧
        ((∃ off data, ti.c.kind = .write off data ∧ off ≤ m.size) ∨
         ∃ sz, ti.c.kind = .truncate sz ∧ m.size ≤ sz)) :
    (¬ FreshCov m n f'.size ∧
      ∀ j < 512, ∀ d, m.DurAt (512 * n + j) d → secByte (f'.secs n).last j = d) ∨
    (n ∈ ns ∧ ∀ j < 512, 512 * n + j < m.size → ∀ y, ByteSeen m rs ts (512 * n + j) y →
      secByte (f'.secs n).last j = y) ∨
    (∃ t ti off data k, ts = [(t, ti)] ∧ ti.c.kind = .write off data ∧ off ≤ m.size ∧ 0 < k ∧
      k ≤ data.length ∧ secHits (min off m.size) (off + k) n = true ∧
      (PageCut off data.length k ∨ FreshCov m n f'.size) ∧
      ∀ j < 512,
        (off ≤ 512 * n + j → 512 * n + j < off + k →
          secByte (f'.secs n).last j = data.getD (512 * n + j - off) 0) ∧
        ((512 * n + j < off ∨ off + k ≤ 512 * n + j) → 512 * n + j < m.size →
          ∀ y, ByteSeen m rs ts (512 * n + j) y → secByte (f'.secs n).last j = y) ∧
        ((512 * n + j < off ∨ off + k ≤ 512 * n + j) → m.size ≤ 512 * n + j →
          secByte (f'.secs n).last j = 0)) ∨
    (∃ t ti sz, ts = [(t, ti)] ∧ ti.c.kind = .truncate sz ∧
      ∀ j < 512,
        (512 * n + j < m.size → ∀ y, ByteSeen m rs ts (512 * n + j) y →
          secByte (f'.secs n).last j = y) ∧
        (m.size ≤ 512 * n + j → secByte (f'.secs n).last j = 0)) := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQst, hfo, hm, hrs, hts', hoth, hwf⟩ := h
  obtain ⟨f, hf, hmo⟩ := hcoh.meta_some i m hm
  have hfile : st.file i = some f := hf
  have hsz : m.size = f.size := hmo.size
  have hsti : st.size i = f.size := by simp [OsState.size, hfile]
  have hcf : CrashFile st i f f' := by
    obtain ⟨-, -, -, -, -, -, hfiles⟩ := hcr
    by_cases hN : Named st'.fs.treeDur i
    · obtain ⟨f1, f'', hf1, hc, hf''⟩ := (hfiles i).1 hN
      rw [hf] at hf1; cases hf1; rw [hfo] at hf''; cases hf''; exact hc
    · rw [(hfiles i).2 hN] at hfo; cases hfo
  have hlen : (f.secs n).vers.length ≤ 2 := by
    have := hmo.vk ns hvk n; split at this <;> omega
  have hns2 : (f.secs n).vers.length = 2 → n ∈ ns := by
    intro h2
    have := hmo.vk ns hvk n
    split at this
    · assumption
    · omega
  have hne : (f.secs n).vers ≠ [] := hwf.vers i f n hfile
  obtain ⟨w, hw⟩ : ∃ w, (f.secs n).vers.head? = some w := by
    cases hv : (f.secs n).vers with
    | nil => exact absurd hv hne
    | cons a _ => exact ⟨a, rfl⟩
  have hdur : ∀ j < 512, ∀ d, m.DurAt (512 * n + j) d → secByte w j = d := by
    intro j hj d hd
    rcases hd with hd | ⟨z, hz, hzb, rfl⟩
    · have := hmo.dur (512 * n + j) d hd w
      rw [(divmod_sec n j hj).1, (divmod_sec n j hj).2] at this
      exact this hw
    · have := hmo.dz z hz (512 * n + j) hzb w
      rw [(divmod_sec n j hj).1, (divmod_sec n j hj).2] at this
      exact this hw
  have hseenB : ∀ b, ∀ y, ByteSeen m rs ts b y → f.contents[b]? = some y := by
    intro b y hy
    rcases hy with ⟨r, hr, k, x, hk, hb, rfl⟩ | ⟨x, hx, off, data, hkind, hlo, hsv⟩
    · obtain ⟨hk', hx⟩ := List.getElem?_eq_some_iff.1 hk
      have := hrs r hr k hk'
      rw [hx, hb] at this
      obtain ⟨f1, hf1, hc, -⟩ := hcoh.bytes i _ x this
      rw [hfile] at hf1; cases hf1; exact hc
    · have hti := hts' x hx
      have hino : x.2.c.ino = i := by
        rcases hts with ⟨rfl, -⟩ | ⟨t, ti, rfl, -, hi, -⟩
        · cases hx
        · simp only [List.mem_singleton] at hx; subst hx; exact hi
      obtain ⟨f1, hf1, hsave⟩ := hcoh.tok_saved _ _ hti
      rw [hino, hfile] at hf1; cases hf1
      rw [hsave] at hsv
      simp only [List.getElem?_map, affRange] at hsv
      obtain ⟨a, ha, hay⟩ := Option.map_eq_some_iff.1 hsv
      have hlo' : affLo st x.2.c = min off m.size := by
        unfold affLo; rw [hkind]; dsimp only; rw [hino, hsti, hsz]
      rw [hlo'] at ha
      obtain ⟨hlt, hav⟩ := List.getElem?_eq_some_iff.1 ha
      rw [List.getElem_range'] at hav
      have hbf : b < f.size := by
        have : affHi st x.2.c ≤ f.size := by
          unfold affHi; rw [hkind]; dsimp only; rw [hino, hsti]; omega
        simp only [List.length_range'] at hlt; omega
      rw [← hay, ← hav, show min off m.size + 1 * (b - min off m.size) = b by
        omega, List.getD_eq_getElem?_getD, contents_getElem?, if_pos hbf]
      rfl
  -- the bytes below the size the client holds are the file's
  have hraw : ∀ b, b < f.size → ∀ y, ByteSeen m rs ts b y → f.rawAt b = y := by
    intro b hb y hy
    have := hseenB b y hy
    rw [contents_getElem?, if_pos hb, Option.some.injEq] at this
    exact this
  have hcur : ∀ j < 512, 512 * n + j < m.size → ∀ y, ByteSeen m rs ts (512 * n + j) y →
      secByte (f.secs n).last j = y := fun j hj hb y hy =>
    last_byte f n j hj (by omega) y (hseenB _ y hy)
  obtain ⟨sz, vs, -, hcand, hcov, rfl⟩ := hcf
  have hV : ((OsFile.ofDisk vs sz f.kept).secs n).last = vs n := by
    simp [OsFile.ofDisk, Sector.last]
  have hsz' : (OsFile.ofDisk vs sz f.kept).size = sz := rfl
  rw [hV, hsz']
  -- freshness from the ghost
  have hfresh : FreshCov m n sz → (f.secs n).fresh = true := by
    rintro ⟨-, ⟨p, hp, hpn⟩, -⟩
    exact (hmo.fr p hp).2 n hpn
  -- a version of the sector: the durable one or, of a sector with two, the page cache's
  have hver : vs n ∈ (f.secs n).vers →
      (vs n = w ∨ ((f.secs n).vers.length = 2 ∧ vs n = (f.secs n).last)) := by
    intro hv
    rcases mem_le_two hlen hv with h1 | h1
    · rw [hw] at h1; cases h1; exact .inl rfl
    · have hl : (f.secs n).last = vs n := by simp [Sector.last, h1]
      by_cases h2 : (f.secs n).vers.length = 2
      · exact .inr ⟨h2, hl.symm⟩
      · left
        have h1' : (f.secs n).vers.length = 1 := by
          have := List.length_pos_iff.2 hne; omega
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 h1'
        rw [ha] at hw h1; simp at hw h1; rw [← hw, h1]
  have hL2 : ∀ (hl2 : (f.secs n).vers.length = 2), vs n = (f.secs n).last →
      n ∈ ns ∧ ∀ j < 512, 512 * n + j < m.size → ∀ y, ByteSeen m rs ts (512 * n + j) y →
        secByte (vs n) j = y := by
    intro hl2 he
    exact ⟨hns2 hl2, fun j hj hb y hy => by rw [he]; exact hcur j hj hb y hy⟩
  -- the covered fresh case: by `CovCand`, the page cache's version of a sector with two, or a
  -- landing that hits the sector
  have hcovv : vs n ∈ (f.secs n).covVers → (f.secs n).fresh = true →
      (f.secs n).vers.length = 2 ∧ vs n = (f.secs n).last := by
    intro hv hfr
    simp only [Sector.covVers, hfr, if_true] at hv
    have hl : (f.secs n).vers.tail.length ≤ 1 := by simp; omega
    match hvs : (f.secs n).vers, hl, hv with
    | [], _, hv => simp [hvs] at hv
    | [a], _, hv => simp [hvs] at hv
    | [a, b], _, hv =>
      simp only [hvs, List.tail_cons, List.mem_singleton] at hv
      exact ⟨by simp [hvs], by simp [Sector.last, hvs, hv]⟩
    | a :: b :: c :: _, _, _ => simp [hvs] at hlen
  -- the changes in flight on the file
  have hchg : ∀ k ∈ changesOn st i, ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i ∧ c.kind = k := by
    intro k hk
    simp only [changesOn, List.mem_map, List.mem_filter, decide_eq_true_eq] at hk
    obtain ⟨c, ⟨hc, hci⟩, rfl⟩ := hk
    obtain ⟨⟨t, c'⟩, ht, rfl⟩ := hc
    exact ⟨t, c', (GMap.mem_toList _ _ _).1 ht, hci, rfl⟩
  have htok : ∀ t c, st.proc.inflight !! t = some c → ∃ ti, Γt !! t = some ti ∧ ti.c = c := by
    intro t c h
    have := hcoh.toks t; rw [h] at this
    obtain ⟨ti, hti, hc⟩ := Option.map_eq_some_iff.1 this
    exact ⟨ti, hti, hc⟩
  rcases hts with ⟨rfl, hcovr⟩ | ⟨t, ti, rfl, hq, hino, hkind⟩
  · -- no change of the client's: every change in flight is an empty write, and lands nothing
    have hempty : ∀ k ∈ changesOn st i, ∃ off, k = .write off [] := by
      intro k hk
      obtain ⟨t, c, hc, hci, rfl⟩ := hchg k hk
      obtain ⟨ti, hti, rfl⟩ := htok t c hc
      rcases hoth t ti hti hci with hx | ⟨hq, hav⟩
      · cases hx
      · cases hkd : ti.c.kind with
        | truncate sz =>
          exact absurd (hcoh.tok_q t ti hti (by simp [Reaches, hkd])) hq
        | write off data =>
          refine ⟨off, ?_⟩
          have hnr : ¬ Reaches st ti.c := fun hr => hq (hcoh.tok_q t ti hti hr)
          simp only [Reaches, hkd, hci, hsti, Nat.not_lt] at hnr
          have : data = [] := by
            apply List.eq_nil_of_length_eq_zero
            apply Classical.byContradiction; intro hl
            obtain ⟨r, hr, h1, h2⟩ := hcovr off (by omega)
            apply hav r hr (off - r.1) (by omega)
            simp only [affRange, affLo, affHi, hkd, hci, hsti, List.mem_range'_1]
            omega
          rw [this]
    have hvin : vs n ∈ (f.secs n).vers := by
      rcases hcand n with hv | ⟨ks, g, hp, hl, hv⟩
      · exact hv
      · rw [landed_emptyWrites hl (fun k hk => hempty k (hp.mem_iff.1 hk))] at hv
        rw [hv]; simp only [Sector.last]
        cases hvs : (f.secs n).vers.getLast? with
        | none => simp [List.getLast?_eq_none_iff.1 hvs] at hne
        | some a => simpa using List.mem_of_getLast? hvs
    by_cases hfc : FreshCov m n sz
    · right; left
      rcases hcov n hfc.2.2 with hv | ⟨ks, g, hp, hl, hv, hvc⟩
      · obtain ⟨h2, he⟩ := hcovv hv (hfresh hfc)
        exact hL2 h2 he
      · rw [landed_emptyWrites hl (fun k hk => hempty k (hp.mem_iff.1 hk))] at hv hvc
        rw [← hv] at hvc
        obtain ⟨h2, he⟩ := hcovv hvc (hfresh hfc)
        exact hL2 h2 he
    · rcases hver hvin with he | ⟨h2, he⟩
      · left; rw [he]; exact ⟨hfc, hdur⟩
      · right; left; exact hL2 h2 he
  · -- the client's change, the only one in flight on the file
    have hti := hts' _ List.mem_cons_self
    have hct : st.proc.inflight !! t = some ti.c := by
      have := hcoh.toks t; rw [hti] at this; exact this.symm
    have hsingle : changesOn st i = [ti.c.kind] :=
      changesOn_single hct hino (fun t' c he hc => by
        rw [← hino]; exact hcoh.tok_alone t ti hti hq t' c he hc)
    have hks : ∀ ks, ks.Perm (changesOn st i) → ks = [ti.c.kind] := by
      intro ks hp; rw [hsingle] at hp; exact List.perm_singleton.1 hp
    rcases hkind with ⟨off, data, hkd, hoff⟩ | ⟨sz', hkd, hgrow⟩
    · -- a write
      have hoff' : off ≤ f.size := by omega
      -- a landing of `k` bytes that hits the sector: the client's write's case
      have hW : ∀ k, k ≤ data.length → 0 < k → secHits (min off f.size) (off + k) n = true →
          (PageCut off data.length k ∨ FreshCov m n sz) →
          vs n = ((f.landWrite off data k).secs n).last →
          ∃ t' ti' off' data' k', [(t, ti)] = [(t', ti')] ∧ ti'.c.kind = .write off' data' ∧
            off' ≤ m.size ∧ 0 < k' ∧ k' ≤ data'.length ∧
            secHits (min off' m.size) (off' + k') n = true ∧
            (PageCut off' data'.length k' ∨ FreshCov m n sz) ∧
            ∀ j < 512,
              (off' ≤ 512 * n + j → 512 * n + j < off' + k' →
                secByte (vs n) j = data'.getD (512 * n + j - off') 0) ∧
              ((512 * n + j < off' ∨ off' + k' ≤ 512 * n + j) → 512 * n + j < m.size →
                ∀ y, ByteSeen m rs [(t, ti)] (512 * n + j) y → secByte (vs n) j = y) ∧
              ((512 * n + j < off' ∨ off' + k' ≤ 512 * n + j) → m.size ≤ 512 * n + j →
                secByte (vs n) j = 0) := by
        intro k hk hk0 hhit hcut he
        refine ⟨t, ti, off, data, k, rfl, hkd, hoff, hk0, hk, by rw [hsz]; exact hhit, hcut,
          fun j hj => ⟨fun h1 h2 => ?_, fun h1 h2 y hy => ?_, fun h1 h2 => ?_⟩⟩
        · rw [he, landWrite_hit_byte f off data k hk hk0 hoff' n hhit j hj, if_pos ⟨h1, h2⟩]
        · rw [he, landWrite_hit_byte f off data k hk hk0 hoff' n hhit j hj, if_neg (by omega),
            if_pos (by omega)]
          exact hraw _ (by omega) y hy
        · rw [he, landWrite_hit_byte f off data k hk hk0 hoff' n hhit j hj, if_neg (by omega),
            if_neg (by omega)]
      -- what the crash leaves of the sector: a version of it, or a page cut that hits it
      have hcases : vs n ∈ (f.secs n).vers ∨
          ∃ k, k ≤ data.length ∧ 0 < k ∧ secHits (min off f.size) (off + k) n = true ∧
            PageCut off data.length k ∧ vs n = ((f.landWrite off data k).secs n).last := by
        by_cases hhit : secHits (min off f.size) (off + data.length) n = true
        · have hci : st.proc.inflight !! t = some ⟨i, .write off data⟩ := by
            rw [hct, show ti.c = ⟨i, .write off data⟩ by rw [← hino, ← hkd]]
          obtain ⟨k, hk, hcut⟩ := hQ st st' hQst t i off data hci f _ hf hfo
          rcases hcut n hhit with h1 | h1
          · left; rw [← hV]; exact h1
          · rw [hV] at h1
            by_cases hk0 : k = 0
            · subst hk0; left; rw [h1]
              have : f.landWrite off data 0 = f := by simp [OsFile.landWrite]
              rw [this]
              simp only [Sector.last]
              cases hvs : (f.secs n).vers.getLast? with
              | none => simp [List.getLast?_eq_none_iff.1 hvs] at hne
              | some a => simpa using List.mem_of_getLast? hvs
            by_cases hh : secHits (min off f.size) (off + k) n = true
            · exact .inr ⟨k, hk.1, by omega, hh, hk, h1⟩
            · left
              rw [h1, Sector.last, (landWrite_miss f off data k hk.1 hoff' n (.inr (by simpa using hh))).1]
              cases hvs : (f.secs n).vers.getLast? with
              | none => simp [List.getLast?_eq_none_iff.1 hvs] at hne
              | some a => simpa using List.mem_of_getLast? hvs
        · left
          rcases hcand n with hv | ⟨ks, g, hp, hl, hv⟩
          · exact hv
          · rw [hks ks hp, hkd] at hl
            cases hl with
            | write _ _ k _ _ _ hk hl' =>
              cases hl'
              rw [hv, Sector.last, (landWrite_miss f off data k hk hoff' n (.inr (by
                simp only [Bool.not_eq_true, secHits, Bool.and_eq_false_iff, decide_eq_false_iff_not,
                  Nat.not_lt] at hhit ⊢
                omega))).1]
              cases hvs : (f.secs n).vers.getLast? with
              | none => simp [List.getLast?_eq_none_iff.1 hvs] at hne
              | some a => simpa using List.mem_of_getLast? hvs
      rcases hcases with hvin | ⟨k, hk, hk0, hhit, hcut, he⟩
      · by_cases hfc : FreshCov m n sz
        · rcases hcov n hfc.2.2 with hv | ⟨ks, g, hp, hl, hv, hvc⟩
          · right; left
            obtain ⟨h2, he⟩ := hcovv hv (hfresh hfc)
            exact hL2 h2 he
          · rw [hks ks hp, hkd] at hl
            cases hl with
            | write _ _ k _ _ _ hk hl' =>
              cases hl'
              by_cases hh : 0 < k ∧ secHits (min off f.size) (off + k) n = true
              · right; right; left
                exact hW k hk hh.1 hh.2 (.inr hfc) hv
              · right; left
                obtain ⟨hvs, hfr⟩ := landWrite_miss f off data k hk hoff' n (by
                  by_cases hk0 : k = 0
                  · exact .inl hk0
                  · exact .inr (by simpa using fun h => hh ⟨by omega, h⟩))
                have hvc' : vs n ∈ (f.secs n).covVers := by
                  rw [hv]; unfold Sector.covVers at hvc ⊢
                  rw [hfr hfc.1, hvs] at hvc
                  simpa [Sector.last, hvs] using hvc
                obtain ⟨h2, he⟩ := hcovv hvc' (hfresh hfc)
                exact hL2 h2 he
        · rcases hver hvin with he | ⟨h2, he⟩
          · left; rw [he]; exact ⟨hfc, hdur⟩
          · right; left; exact hL2 h2 he
      · right; right; left
        exact hW k hk hk0 hhit (.inl hcut) he
    · -- a growing truncate
      have hT : ∀ sz'', f.size ≤ sz'' → secHits (min f.size sz'') (max f.size sz'') n = true →
          vs n = ((f.truncate sz'').secs n).last →
          ∃ t' ti' sz, [(t, ti)] = [(t', ti')] ∧ ti'.c.kind = .truncate sz ∧
            ∀ j < 512,
              (512 * n + j < m.size → ∀ y, ByteSeen m rs [(t, ti)] (512 * n + j) y →
                secByte (vs n) j = y) ∧
              (m.size ≤ 512 * n + j → secByte (vs n) j = 0) := by
        intro sz'' hge hhit he
        refine ⟨t, ti, sz', rfl, hkd, fun j hj => ⟨fun h1 y hy => ?_, fun h1 => ?_⟩⟩
        · rw [he, truncate_hit_byte f sz'' hge n hhit j hj, if_pos (by omega)]
          exact hraw _ (by omega) y hy
        · rw [he, truncate_hit_byte f sz'' hge n hhit j hj, if_neg (by omega)]
      have hland : ∀ ks g, ks.Perm (changesOn st i) → Landed ks f g →
          (∃ sz'', f.size ≤ sz'' ∧ secHits (min f.size sz'') (max f.size sz'') n = true ∧
            (g.secs n).last = ((f.truncate sz'').secs n).last) ∨
          ((g.secs n).vers = (f.secs n).vers ∧ (n % 8 = 0 → (g.secs n).fresh = (f.secs n).fresh)) := by
        intro ks g hp hl
        rw [hks ks hp, hkd] at hl
        cases hl with
        | trunc _ sz'' _ _ _ h1 h2 hl' =>
          cases hl'
          by_cases hh : secHits (min f.size sz'') (max f.size sz'') n = true
          · exact .inl ⟨sz'', by omega, hh, rfl⟩
          · exact .inr (truncate_miss f sz'' (by omega) n (by simpa using hh))
      have hlastIn : (f.secs n).last ∈ (f.secs n).vers := by
        simp only [Sector.last]
        cases hvs : (f.secs n).vers.getLast? with
        | none => simp [List.getLast?_eq_none_iff.1 hvs] at hne
        | some a => simpa using List.mem_of_getLast? hvs
      have hcases : vs n ∈ (f.secs n).vers ∨
          ∃ sz'', f.size ≤ sz'' ∧ secHits (min f.size sz'') (max f.size sz'') n = true ∧
            vs n = ((f.truncate sz'').secs n).last := by
        rcases hcand n with hv | ⟨ks, g, hp, hl, hv⟩
        · exact .inl hv
        · rcases hland ks g hp hl with ⟨sz'', h1, h2, h3⟩ | ⟨h1, -⟩
          · exact .inr ⟨sz'', h1, h2, hv.trans h3⟩
          · left; rw [hv, Sector.last, h1]; exact hlastIn
      rcases hcases with hvin | ⟨sz'', h1, h2, he⟩
      · by_cases hfc : FreshCov m n sz
        · rcases hcov n hfc.2.2 with hv | ⟨ks, g, hp, hl, hv, hvc⟩
          · right; left
            obtain ⟨h2, he⟩ := hcovv hv (hfresh hfc)
            exact hL2 h2 he
          · rcases hland ks g hp hl with ⟨sz'', h1, h2, h3⟩ | ⟨hvs, hfr⟩
            · right; right; right; exact hT sz'' h1 h2 (hv.trans h3)
            · right; left
              have hvc' : vs n ∈ (f.secs n).covVers := by
                rw [hv]; unfold Sector.covVers at hvc ⊢
                rw [hfr hfc.1, hvs] at hvc
                simpa [Sector.last, hvs] using hvc
              obtain ⟨h2, he⟩ := hcovv hvc' (hfresh hfc)
              exact hL2 h2 he
        · rcases hver hvin with he | ⟨h2, he⟩
          · left; rw [he]; exact ⟨hfc, hdur⟩
          · right; left; exact hL2 h2 he
      · right; right; right; exact hT sz'' h1 h2 he

/-- A crash keeps a file with no `FALLOC_FL_KEEP_SIZE` blocks so, if its `OsMeta` knows fresh
sectors. -/
theorem crashSeen_kept {i : Ino} {m : OsMeta} {rs : List (Nat × DFrac × List (w8 × Bool))}
    {ts : List (Nat × TokInfo)} {f' : OsFile} (h : CrashSeenR Q i m rs ts (some f')) {p : Nat}
    (hp : m.fr = some p) : f'.kept = false := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQst, hfo, hm, -, -, -, -⟩ := h
  obtain ⟨f, hf, hmo⟩ := hcoh.meta_some i m hm
  obtain ⟨-, -, -, -, -, -, hfiles⟩ := hcr
  by_cases hN : Named st'.fs.treeDur i
  · obtain ⟨f1, f'', hf1, hc, hf''⟩ := (hfiles i).1 hN
    rw [hf] at hf1; cases hf1; rw [hfo] at hf''; cases hf''
    obtain ⟨sz, vs, -, -, -, rfl⟩ := hc
    exact (hmo.fr p hp).1
  · rw [(hfiles i).2 hN] at hfo; cases hfo

end seen

end Fs
end Perennial

end
