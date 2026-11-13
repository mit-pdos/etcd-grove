/-
What a crash may leave of a file while a `WriteAt` of `data` at `off` runs over it (its attempts
and between them), as the crash-aware write specs (`Spec/os/Crash.lean`) state it, over the
per-byte model:

* `WriteCrash m bs off data f`: `f` is a file a crash may leave of the file `m`, `bs` during the
  write: on disk, a size within the write's crash bounds, each byte of the old file one of its old
  candidates or the data's byte (inside the write) or, at or past the crash bounds' smallest size,
  zero (writeback's zeroing, `CrashFile`), zeros past the zeros known and the write's end.
* `WriteOk Good m bs off data`: every such file is `Good` (the caller's obligation, once).
* `WIn m bs off data m' bs'`: the file `m'`, `bs'` is one the write may pass through (its `OsMeta`'s
  bounds within the write's, each byte's candidates the old ones or the data's byte, the bytes
  outside the write unchanged).

`fileOk_idle` and `fileOk_flight` give `FileOk Good` of every state the write passes through,
idle or with an attempt in flight, from `WriteOk`; `wIn_fin` (and `fin_vals`) that an attempt's
finish keeps `WIn` (and the bytes written so far). Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.CrashFile

@[expose] public section

noncomputable section

namespace Perennial

open Iris Fs

/-- The largest size a write of `n` bytes at `off` of a file of size `m.size` may leave. -/
abbrev wT (m : OsMeta) (off n : Nat) : Nat := max m.size (off + n)

/-- `f` is a file a crash may leave of the file `m`, `bs` while a write of `data` at `off` runs. -/
def WriteCrash (m : OsMeta) (bs : List ByteG) (off : Nat) (data : List w8) (f : OsFile) : Prop :=
  (∃ img, f = OsFile.ofDisk img f.size) ∧
  min m.lo (wT m off data.length) ≤ f.size ∧ f.size ≤ max m.hi (wT m off data.length) ∧
  (∀ b (hb : b < bs.length), b < f.size →
    (∃ s, (f.cache b, s) ∈ bs[b].2) ∨
      (off ≤ b ∧ b < off + data.length ∧ f.cache b = data.getD (b - off) 0) ∨
      (min m.lo (wT m off data.length) ≤ b ∧ f.cache b = 0)) ∧
  (∀ z, m.zf = some z → ∀ b, max z (off + data.length) ≤ b → b < f.size → f.cache b = 0)

/-- Every file a crash may leave of `m`, `bs` while a write of `data` at `off` runs is `Good`. -/
def WriteOk (Good : Option OsFile → Prop) (m : OsMeta) (bs : List ByteG) (off : Nat)
    (data : List w8) : Prop :=
  ∀ f, WriteCrash m bs off data f → Good (some f)

/-- The file `m'`, `bs'` is one a write of `data` at `off` over `m`, `bs` may pass through. -/
structure WIn (m : OsMeta) (bs : List ByteG) (off : Nat) (data : List w8) (m' : OsMeta)
    (bs' : List ByteG) : Prop where
  lo : min m.lo (wT m off data.length) ≤ m'.lo
  hi : m'.hi ≤ max m.hi (wT m off data.length)
  zf : ∀ z, m.zf = some z → ∃ z', m'.zf = some z' ∧ z' ≤ max z (off + data.length)
  len : bs'.length = m'.size
  sz1 : m.size ≤ m'.size
  sz2 : m'.size ≤ wT m off data.length
  maps : m'.maps = m.maps
  cands : ∀ b (hb : b < bs'.length) (hb0 : b < bs.length), ∀ q ∈ bs'[b].2,
    q ∈ bs[b].2 ∨ (off ≤ b ∧ b < off + data.length ∧ q.1 = data.getD (b - off) 0)
  out : ∀ b, (b < off ∨ off + data.length ≤ b) → bs'[b]? = bs[b]?

/-- `WIn` reads of the `OsMeta` it reaches only its bounds, zeros, size and mappings. -/
theorem WIn.congr {m : OsMeta} {bs : List ByteG} {off : Nat} {data : List w8} {m1 : OsMeta}
    {bs' : List ByteG} (h : WIn m bs off data m1 bs') (m2 : OsMeta) (hlo : m2.lo = m1.lo)
    (hhi : m2.hi = m1.hi) (hzf : m2.zf = m1.zf) (hsz : m2.size = m1.size)
    (hmaps : m2.maps = m1.maps) : WIn m bs off data m2 bs' :=
  ⟨by rw [hlo]; exact h.lo, by rw [hhi]; exact h.hi, by rw [hzf]; exact h.zf,
    by rw [hsz]; exact h.len, by rw [hsz]; exact h.sz1, by rw [hsz]; exact h.sz2,
    by rw [hmaps]; exact h.maps, h.cands, h.out⟩

theorem wIn_refl {m : OsMeta} {bs : List ByteG} (off : Nat) (data : List w8)
    (hlen : bs.length = m.size) : WIn m bs off data m bs :=
  ⟨by simp only [wT]; omega, by simp only [wT]; omega, fun z hz => ⟨z, hz, by omega⟩, hlen,
    Nat.le_refl _, by simp only [wT]; omega, rfl,
    fun _ _ _ q hq => .inl hq, fun _ _ => rfl⟩

theorem pwSize_ge3 (sz off k : Nat) : sz ≤ pwSize sz off k := by
  unfold pwSize; split <;> omega

theorem drop_getElem' {α : Type} (l : List α) (c b : Nat) (h1 : c ≤ b)
    (h : b - c < (l.drop c).length) : (l.drop c)[b - c] = l[b]'(by simp at h; omega) := by
  simp only [List.getElem_drop]; congr 1; omega

theorem range_getElem' (m : OsMeta) (bs : List ByteG) (off n b : Nat) (h1 : cfLo m off ≤ b)
    (h : b - cfLo m off < (cfRange m bs off n).length) :
    (cfRange m bs off n)[b - cfLo m off] =
      bs[b]'(by simp only [cfRange, List.length_take, List.length_drop] at h; omega) := by
  simp only [cfRange, List.getElem_take, List.getElem_drop]; congr 1; omega

theorem range_getElem2 (m : OsMeta) (bs : List ByteG) (off n j b : Nat)
    (hj : j < (cfRange m bs off n).length) (hb : cfLo m off + j = b) :
    (cfRange m bs off n)[j] =
      bs[b]'(by simp only [cfRange, List.length_take, List.length_drop] at hj; omega) := by
  subst hb; simp only [cfRange, List.getElem_take, List.getElem_drop]

/-- A byte of a run of a file a crash may leave, below its size: one of its candidates, or zero at
or past `M.lo`. -/
theorem fileCrashedR_byte {M : OsMeta} {rs : List (Nat × DFrac × List ByteG)} {f : OsFile}
    (h : FileCrashedR M rs (some f)) {r : Nat × DFrac × List ByteG} (hr : r ∈ rs) {b : Nat}
    (h1 : r.1 ≤ b) (h2 : b - r.1 < r.2.2.length) (hb : b < f.size) :
    (∃ s, (f.cache b, s) ∈ (r.2.2[b - r.1]).2) ∨ (M.lo ≤ b ∧ f.cache b = 0) := by
  have := (h f rfl).2.2.2.1 r hr (b - r.1) h2 (by omega)
  rwa [show r.1 + (b - r.1) = b by omega] at this

/-- A durable byte of a run survives a crash, below the crash's size and `M.lo`. -/
theorem crashed_dur {M : OsMeta} {rs : List (Nat × DFrac × List ByteG)} {f : OsFile}
    (h : FileCrashedR M rs (some f)) {r : Nat × DFrac × List ByteG} (hr : r ∈ rs) {b : Nat}
    {x : w8} (h1 : r.1 ≤ b) (h2 : b - r.1 < r.2.2.length) (hx : (r.2.2[b - r.1]).2 = [(x, 0)])
    (hb : b < f.size) (hlo : b < M.lo) : f.contents[b]? = some x := by
  obtain ⟨s, hs⟩ | ⟨h0, -⟩ := fileCrashedR_byte h hr h1 h2 hb
  rotate_left; · omega
  rw [hx, List.mem_singleton] at hs
  rw [contents_getElem?_of_lt hb, (Prod.mk.inj hs).1]

/-- **Every idle state the write passes through: its crash is `Good`.** -/
theorem fileOk_idle {Good : Option OsFile → Prop} {m m' : OsMeta} {bs bs' : List ByteG}
    {off : Nat} {data : List w8} (hW : WIn m bs off data m' bs') (hok : WriteOk Good m bs off data)
    (hlen : bs.length = m.size) : FileOk Good (m', bs', none) := by
  intro f hf
  apply hok
  obtain ⟨hd, hlo, hhi, -, hz⟩ := hf f rfl
  have hl := hW.lo; have hh := hW.hi
  refine ⟨hd, by simp only [fMeta] at hlo; omega, by simp only [fMeta] at hhi; omega,
    fun b hb hbf => ?_, fun z hz0 b hb hbf => ?_⟩
  · have hb' : b < bs'.length := by rw [hW.len]; have := hW.sz1; omega
    obtain ⟨s, hs⟩ | ⟨h0l, h0⟩ := fileCrashedR_byte hf (List.mem_singleton.2 rfl) (Nat.zero_le b)
      (by simpa using hb') hbf
    rotate_left
    · simp only [fMeta] at h0l; exact .inr (.inr ⟨by omega, h0⟩)
    simp only [Nat.sub_zero] at hs
    rcases hW.cands b hb' hb _ hs with h | ⟨h1, h2, h3⟩
    · exact .inl ⟨s, h⟩
    · exact .inr (.inl ⟨h1, h2, h3⟩)
  · obtain ⟨z', hz', hle⟩ := hW.zf z hz0
    exact hz z' hz' b (by omega) hbf

theorem pwAnn_getElem' (data : List w8) (n : Nat) (xs : List ByteG) (j : Nat)
    (hj : j < xs.length) :
    (pwAnn data n xs)[j]'(by simpa using hj) = (xs[j].1, xs[j].2 ++ [(data.getD j 0, n)]) := by
  simp [pwAnn]

/-- **Every state with an attempt in flight (from `off'`, the rest of the data): its crash is
`Good`.** -/
theorem fileOk_flight {Good : Option OsFile → Prop} {m m' : OsMeta} {bs bs' : List ByteG}
    {off off' : Nat} {data data' : List w8} (t n : Nat) (hW : WIn m bs off data m' bs')
    (hok : WriteOk Good m bs off data) (hlen : bs.length = m.size) (hoff : off ≤ off')
    (hend : off' + data'.length = off + data.length) (hd : data' = data.drop (off' - off))
    (hne : data' ≠ []) (hg : off' ≤ m'.size) :
    FileOk Good (m', bs', some (t, off', data', n)) := by
  intro f hf
  apply hok
  have hdl : 0 < data'.length := List.length_pos_iff.2 hne
  obtain ⟨hdisk, hlo, hhi, -, hz⟩ := hf f rfl
  simp only [fMeta, cfMeta, announce_lo, announce_hi, announce_zf] at hlo hhi hz
  have hl := hW.lo; have hh := hW.hi; have h1 := hW.sz1; have h2 := hW.sz2
  have hlb := hW.len
  have hT : max m'.size (off' + data'.length) = wT m off data.length := by
    have := h2; have := h1; simp only [wT] at *; omega
  rw [hT] at hlo hhi
  refine ⟨hdisk, by omega, by omega, fun b hb hbf => ?_, fun z hz0 b hb hbf => ?_⟩
  · have hb' : b < bs'.length := by omega
    have hlo' : cfLo m' off' = off' := Nat.min_eq_left hg
    -- which run holds the byte
    have hcand : ∀ q ∈ bs'[b].2, ∀ s, q = (f.cache b, s) →
        (∃ s, (f.cache b, s) ∈ bs[b].2) ∨
          (off ≤ b ∧ b < off + data.length ∧ f.cache b = data.getD (b - off) 0) ∨
          (min m.lo (wT m off data.length) ≤ b ∧ f.cache b = 0) := by
      intro q hq s hqs
      rcases hW.cands b hb' hb q hq with h | ⟨h1, h2, h3⟩
      · exact .inl ⟨s, hqs ▸ h⟩
      · exact .inr (.inl ⟨h1, h2, by rw [← h3, hqs]⟩)
    have hzero : (fMeta (m', bs', some (t, off', data', n))).lo ≤ b → f.cache b = 0 →
        (∃ s, (f.cache b, s) ∈ bs[b].2) ∨
          (off ≤ b ∧ b < off + data.length ∧ f.cache b = data.getD (b - off) 0) ∨
          (min m.lo (wT m off data.length) ≤ b ∧ f.cache b = 0) := by
      intro h0l h0
      simp only [fMeta, cfMeta, announce_lo] at h0l
      exact .inr (.inr ⟨by omega, h0⟩)
    by_cases c1 : b < off'
    · obtain ⟨s, hs⟩ | ⟨h0l, h0⟩ := fileCrashedR_byte hf (r := (0, DFrac.own (1 : Qp).half, bs'.take (cfLo m' off')))
        (by simp [fRuns]) (Nat.zero_le b) (by simp only [List.length_take]; omega) hbf
      rotate_left; · exact hzero h0l h0
      simp only [Nat.sub_zero, List.getElem_take] at hs
      exact hcand _ hs s rfl
    by_cases c2 : b < cfHi m' off' data'.length
    · obtain ⟨s, hs⟩ | ⟨h0l, h0⟩ := fileCrashedR_byte hf
        (r := (cfLo m' off', DFrac.own 1, pwAnn data' n (cfRange m' bs' off' data'.length)))
        (by simp [fRuns]) (by omega)
        (by simp only [pwAnn_length, cfRange, List.length_take, List.length_drop]; omega) hbf
      rotate_left; · exact hzero h0l h0
      rw [pwAnn_getElem' data' n _ (b - cfLo m' off')
        (by simp only [cfRange, List.length_take, List.length_drop]; omega)] at hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | hs
      · rw [range_getElem' m' bs' off' data'.length b (by omega)
          (by simp only [cfRange, List.length_take, List.length_drop]; omega)] at hs
        exact hcand _ hs s rfl
      · right; left
        obtain ⟨hs1, -⟩ := Prod.mk.inj hs
        refine ⟨by omega, by simp only [cfHi] at c2; omega, ?_⟩
        rw [hs1, hd, hlo']
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
          show off' - off + (b - off') = b - off by omega]
    · obtain ⟨s, hs⟩ | ⟨h0l, h0⟩ := fileCrashedR_byte hf
        (r := (cfHi m' off' data'.length, DFrac.own (1 : Qp).half, bs'.drop (cfHi m' off' data'.length)))
        (by simp [fRuns]) (by omega) (by simp only [List.length_drop]; omega) hbf
      rotate_left; · exact hzero h0l h0
      rw [drop_getElem' bs' _ b (by omega) (by simp only [List.length_drop]; omega)] at hs
      exact hcand _ hs s rfl
  · obtain ⟨z', hz', hle⟩ := hW.zf z hz0
    have := hz (if min off' m'.size < off' + data'.length then max z' (off' + data'.length) else z')
      (by rw [hz']; rfl) b
    rw [if_pos (by omega)] at this
    exact this (by omega) hbf

/-- The bytes of a file of `OsMeta` `m'` after an attempt of `data'` at `off'` landed `k` of them. -/
def finBytes (m' : OsMeta) (bs' : List ByteG) (off' : Nat) (data' : List w8) (k n : Nat)
    (zs : List Cands) : List ByteG :=
  bs'.take (cfLo m' off') ++ pwBytes m'.size off' data' k n (cfRange m' bs' off' data'.length) zs ++
    bs'.drop (cfHi m' off' data'.length)

theorem getElem?_tpd (bs P : List ByteG) (a c b : Nat) (ha : a ≤ bs.length) :
    (bs.take a ++ P ++ bs.drop c)[b]? =
      if b < a then bs[b]? else if b < a + P.length then P[b - a]? else bs[c + (b - a - P.length)]? := by
  rw [List.append_assoc]
  by_cases h1 : b < a
  · rw [if_pos h1, List.getElem?_append_left (by simp; omega), List.getElem?_take, if_pos h1]
  · rw [if_neg h1, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_take, Nat.min_eq_left ha]
    by_cases h2 : b < a + P.length
    · rw [if_pos h2, List.getElem?_append_left (by omega)]
    · rw [if_neg h2, List.getElem?_append_right (by omega), List.getElem?_drop]
      try (congr 2; omega)

theorem finBytes_length {m' : OsMeta} {bs' : List ByteG} {off' : Nat} {data' : List w8} {k n : Nat}
    {zs : List Cands} (hlen : bs'.length = m'.size) (hg : off' ≤ m'.size) (hk : k ≤ data'.length) :
    (finBytes m' bs' off' data' k n zs).length = pwSize m'.size off' k := by
  simp only [finBytes, List.length_append, List.length_take, List.length_drop, pwBytes_length,
    cfLo, cfHi]
  unfold pwSize; split <;> omega

/-- **An attempt's finish keeps `WIn`.** -/
theorem wIn_fin {m m' : OsMeta} {bs bs' : List ByteG} {off off' : Nat} {data data' : List w8}
    {k n : Nat} {zs : List Cands} (hW : WIn m bs off data m' bs') (hlen : bs.length = m.size)
    (hoff : off ≤ off')
    (hend : off' + data'.length = off + data.length) (hd : data' = data.drop (off' - off))
    (hne : data' ≠ []) (hg : off' ≤ m'.size) (hk : k ≤ data'.length) :
    WIn m bs off data (pwPost m' off' data'.length k) (finBytes m' bs' off' data' k n zs) := by
  have hdl : 0 < data'.length := List.length_pos_iff.2 hne
  have hl := hW.lo; have hh := hW.hi; have h1 := hW.sz1; have h2 := hW.sz2
  have hlb := hW.len
  have hT : max m'.size (off' + data'.length) = wT m off data.length := by
    have := h2; have := h1; simp only [wT] at *; omega
  have hps := pwSize_ge3 m'.size off' k
  have hps2 : pwSize m'.size off' k ≤ max m'.size (off' + data'.length) := by
    unfold pwSize; split <;> omega
  have hlo' : cfLo m' off' = off' := Nat.min_eq_left hg
  have hpl : (pwBytes m'.size off' data' k n (cfRange m' bs' off' data'.length) zs).length =
      min (off' + data'.length) (pwSize m'.size off' k) - off' := pwBytes_length _ _ _ _ _ _ _
  refine ⟨?_, ?_, ?_, finBytes_length hlb hg hk, ?_, ?_, by simp [pwPost, hW.maps], ?_, ?_⟩
  · simp only [pwPost, announce_lo]; rw [hT]; omega
  · simp only [pwPost, announce_hi]; rw [hT]; omega
  · intro z hz
    obtain ⟨z', hz', hle⟩ := hW.zf z hz
    refine ⟨max z' (off' + data'.length), ?_, by omega⟩
    simp only [pwPost, announce_zf, hz', Option.map_some, Option.some.injEq]
    rw [if_pos (by rw [Nat.min_eq_left hg]; omega)]
    try rw [Nat.min_eq_left hg]
  · show m.size ≤ pwSize m'.size off' k; omega
  · show pwSize m'.size off' k ≤ _; rw [← hT]; exact hps2
  · intro b hb hb0 q hq
    have hb' : b < bs'.length := by omega
    have hget := getElem?_tpd bs' (pwBytes m'.size off' data' k n (cfRange m' bs' off' data'.length) zs)
      (cfLo m' off') (cfHi m' off' data'.length) b (by rw [hlb]; omega)
    rw [← finBytes, List.getElem?_eq_getElem hb, hlo'] at hget
    by_cases c1 : b < off'
    · rw [if_pos c1, List.getElem?_eq_getElem hb'] at hget
      rw [Option.some.inj hget] at hq
      exact hW.cands b hb' hb0 q hq
    rw [if_neg c1] at hget
    by_cases c2 : b < off' + (pwBytes m'.size off' data' k n (cfRange m' bs' off' data'.length) zs).length
    · rw [if_pos c2] at hget
      rw [List.getElem?_eq_getElem (by omega)] at hget
      rw [Option.some.inj hget] at hq
      have hj : b - off' < (cfRange m' bs' off' data'.length).length := by
        simp only [cfRange, List.length_take, List.length_drop, cfHi]; rw [hlo']; omega
      simp only [pwBytes, List.getElem_map, List.getElem_range] at hq
      rw [if_pos hj] at hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hq
        rw [range_getElem2 m' bs' off' _ (b - off') b hj (by rw [hlo']; omega)] at hq
        exact hW.cands b hb' hb0 q hq
      · right
        refine ⟨by omega, by omega, ?_⟩
        rw [hd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
          show off' - off + (b - off') = b - off by omega]
    · rw [if_neg c2] at hget
      have hc : cfHi m' off' data'.length + (b - off' - (pwBytes m'.size off' data' k n
          (cfRange m' bs' off' data'.length) zs).length) = b := by
        rw [hpl] at c2 ⊢; unfold cfHi; omega
      rw [hc, List.getElem?_eq_getElem hb'] at hget
      rw [Option.some.inj hget] at hq
      exact hW.cands b hb' hb0 q hq
  · intro b hout
    rw [← hW.out b hout]
    have hget := getElem?_tpd bs' (pwBytes m'.size off' data' k n (cfRange m' bs' off' data'.length) zs)
      (cfLo m' off') (cfHi m' off' data'.length) b (by rw [hlb]; omega)
    rw [← finBytes, hlo'] at hget
    rw [hget]
    rcases hout with h | h
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by rw [hpl]; omega)]
      by_cases hbs : b < m'.size
      · have : cfHi m' off' data'.length + (b - off' - (min (off' + data'.length)
            (pwSize m'.size off' k) - off')) = b := by
          unfold cfHi; omega
        rw [hpl, this]
      · rw [hpl]
        rw [List.getElem?_eq_none (show bs'.length ≤ cfHi m' off' data'.length + (b - off' -
            (min (off' + data'.length) (pwSize m'.size off' k) - off')) by unfold cfHi; omega),
          List.getElem?_eq_none (show bs'.length ≤ b by omega)]

/-- **The bytes written so far after an attempt** from `off + nn` (the attempt's `k` bytes, those
written before kept), and the size past them. -/
theorem fin_vals {m' : OsMeta} {bs' : List ByteG} {off nn w k n : Nat} {data : List w8}
    {zs : List Cands} (hlen : bs'.length = m'.size) (hS : off + w ≤ m'.size) (hnw : nn ≤ w)
    (hw : w ≤ data.length) (hk : k ≤ data.length - nn)
    (hpre : ∀ i < w, (bs'[off + i]?).map Prod.fst = data[i]?) :
    off + max w (nn + k) ≤ pwSize m'.size (off + nn) k ∧
      ∀ i < max w (nn + k),
        ((finBytes m' bs' (off + nn) (data.drop nn) k n zs)[off + i]?).map Prod.fst = data[i]? := by
  have hdl : (data.drop nn).length = data.length - nn := List.length_drop
  refine ⟨by unfold pwSize; split <;> omega, fun i hi => ?_⟩
  have hg : off + nn ≤ m'.size := by omega
  have hlo' : cfLo m' (off + nn) = off + nn := Nat.min_eq_left hg
  have hpl : (pwBytes m'.size (off + nn) (data.drop nn) k n (cfRange m' bs' (off + nn)
      (data.drop nn).length) zs).length =
      min (off + nn + (data.drop nn).length) (pwSize m'.size (off + nn) k) - (off + nn) :=
    pwBytes_length _ _ _ _ _ _ _
  have hget := getElem?_tpd bs' (pwBytes m'.size (off + nn) (data.drop nn) k n
    (cfRange m' bs' (off + nn) (data.drop nn).length) zs) (cfLo m' (off + nn))
    (cfHi m' (off + nn) (data.drop nn).length) (off + i) (by rw [hlen]; omega)
  rw [← finBytes, hlo'] at hget
  rw [hget]
  by_cases c1 : off + i < off + nn
  · rw [if_pos c1]; exact hpre i (by omega)
  rw [if_neg c1]
  have hin : off + i < off + nn + (pwBytes m'.size (off + nn) (data.drop nn) k n
      (cfRange m' bs' (off + nn) (data.drop nn).length) zs).length := by
    rw [hpl, hdl]; unfold pwSize; split <;> omega
  rw [if_pos hin, List.getElem?_eq_getElem (by omega), Option.map_some,
    pwBytes_getElem _ _ _ _ _ _ _ _ (by omega), show off + nn + (off + i - (off + nn)) = off + i by omega]
  unfold pwByte
  by_cases c2 : off + i < off + nn + k
  · rw [if_pos c2, show off + i - (off + nn) = i - nn by omega, List.getD_eq_getElem?_getD,
      List.getElem?_drop, show nn + (i - nn) = i by omega,
      List.getElem?_eq_getElem (show i < data.length by omega), Option.getD_some]
  · rw [if_neg c2]
    have hiw : i < w := by omega
    have hp := hpre i hiw
    rw [show off + i - (off + nn) = i - nn by omega, List.getD_eq_getElem?_getD]
    simp only [cfRange, hlo', List.getElem?_take, List.getElem?_drop]
    rw [if_pos (by unfold cfHi; rw [hdl]; omega), show off + nn + (i - nn) = off + i by omega]
    rw [List.getElem?_eq_getElem (by omega)] at hp ⊢
    simp only [Option.map_some, Option.getD_some] at hp ⊢
    rw [hp]

end Perennial
