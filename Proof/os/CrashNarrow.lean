/-
Pure facts of the crash-aware write (`Proof/os/CrashFile.lean`): every state a `WriteAt` passes
through, retries included, is a narrowing (`Narrow`) of the file it started from (an attempt
writes the rest of the data, from `off + nn`, after a short write left `nn` bytes written), and a
crash of a narrowing, idle or with the next attempt in flight, leaves a file that a crash of the
first attempt in flight could leave (`fileOk_narrow`). So the caller shows `FileOk` of one state,
the first attempt's (`cfWriting`).
-/
module

public import Proof.os.CrashFile

@[expose] public section

noncomputable section

namespace Perennial

open Iris Fs

/-- The file after an attempt that wrote the first `k` bytes of `data` at `off`: its `OsMeta`... -/
def finMeta (m : OsMeta) (off : Nat) (data : List w8) (k : Nat) : OsMeta :=
  { pwMeta m off data.length with size := pwSize m.size off k }

/-- ... and its bytes. -/
def finBytes (m : OsMeta) (bs : List (w8 × Bool)) (off : Nat) (data : List w8) (k : Nat) :
    List (w8 × Bool) :=
  bs.take (cfLo m off) ++ pwBytes m.size off data k (cfRange m bs off data.length) ++
    bs.drop (cfHi m off data.length)

/-- `m'`, `bs'` is what a write of `data` at `off` may have made of `m`, `bs`: the same crash
bounds below, at most the write's above, at least the size, and the bytes outside the write
unchanged. -/
structure Narrow (m : OsMeta) (bs : List (w8 × Bool)) (off : Nat) (data : List w8)
    (m' : OsMeta) (bs' : List (w8 × Bool)) : Prop where
  lo : m'.lo = m.lo
  ok : m'.ok = m.ok
  maps : m'.maps = m.maps
  hi : m'.hi ≤ max m.hi (off + data.length)
  size : m.size ≤ m'.size
  len : bs'.length = m'.size
  pre : ∀ i < cfLo m off, bs'[i]? = bs[i]?
  suf : off + data.length ≤ m.size → ∀ i, off + data.length ≤ i → bs'[i]? = bs[i]?
  /-- The size grows only up to the write's end. -/
  szhi : m'.size ≤ max m.size (off + data.length)

theorem narrow_refl {m : OsMeta} {bs : List (w8 × Bool)} (off : Nat) (data : List w8)
    (hlen : bs.length = m.size) : Narrow m bs off data m bs :=
  ⟨rfl, rfl, rfl, by omega, Nat.le_refl _, hlen, fun _ _ => rfl, fun _ _ _ => rfl, by omega⟩

section fin
variable {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8} {k : Nat}

theorem pwSize_ge' (sz off k : Nat) : sz ≤ pwSize sz off k := by
  unfold pwSize; split <;> omega

theorem pwBytes_len' (_hlen : bs.length = m.size) :
    (pwBytes m.size off data k (cfRange m bs off data.length)).length =
      min (off + data.length) (pwSize m.size off k) - cfLo m off := by
  rw [pwBytes_length]; rfl

theorem finBytes_length (hlen : bs.length = m.size) (hk : k ≤ data.length) :
    (finBytes m bs off data k).length = pwSize m.size off k := by
  unfold finBytes
  simp only [List.length_append, List.length_take, List.length_drop, pwBytes_len' hlen]
  unfold cfLo cfHi pwSize
  split <;> omega

theorem finBytes_pre (hlen : bs.length = m.size) (i : Nat) (hi : i < cfLo m off) :
    (finBytes m bs off data k)[i]? = bs[i]? := by
  unfold finBytes
  rw [List.append_assoc, List.getElem?_append_left (by simp only [List.length_take]; unfold cfLo at hi ⊢; omega),
    List.getElem?_take_of_lt hi]

theorem finBytes_suf (hlen : bs.length = m.size) (hk : k ≤ data.length)
    (hs : off + data.length ≤ m.size) (i : Nat) (hi : off + data.length ≤ i) :
    (finBytes m bs off data k)[i]? = bs[i]? := by
  have hP := pwSize_ge' m.size off k
  have h1 : (bs.take (cfLo m off) ++ pwBytes m.size off data k (cfRange m bs off data.length)).length =
      off + data.length := by
    simp only [List.length_append, List.length_take, pwBytes_len' hlen]
    unfold cfLo; omega
  unfold finBytes
  rw [List.getElem?_append_right (by omega), h1, List.getElem?_drop]
  unfold cfHi
  congr 1; omega

theorem finBytes_data (hlen : bs.length = m.size) (hn : 0 < data.length) (i : Nat)
    (hi : i < data.length) :
    ((finBytes m bs off data data.length)[off + i]?).map Prod.fst = data[i]? := by
  have hP : pwSize m.size off data.length = max m.size (off + data.length) := by
    unfold pwSize; split <;> omega
  have hpl := pwBytes_len' (m := m) (bs := bs) (off := off) (data := data) (k := data.length) hlen
  rw [hP] at hpl
  have hlo : cfLo m off ≤ off := by unfold cfLo; omega
  unfold finBytes
  rw [List.append_assoc, List.getElem?_append_right (by simp only [List.length_take]; unfold cfLo at hlo ⊢; omega),
    List.getElem?_append_left (by simp only [List.length_take, hpl]; unfold cfLo; omega)]
  simp only [List.length_take]
  have hmin : min (cfLo m off) bs.length = cfLo m off := by unfold cfLo; omega
  rw [hmin]
  have hlt : off + i - cfLo m off < (pwBytes m.size off data data.length
      (cfRange m bs off data.length)).length := by rw [hpl]; omega
  rw [List.getElem?_eq_getElem hlt, Option.map_some, pwBytes_getElem _ _ _ _ _ _ hlt,
    List.getElem?_eq_getElem hi]
  unfold pwByte
  have h2 : min off m.size + (off + i - cfLo m off) = off + i := by unfold cfLo; omega
  rw [h2, if_neg (by omega), if_pos (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The first `k` bytes of the data, written by a write that starts inside the file. -/
theorem finBytes_written (hlen : bs.length = m.size) (hoff : off ≤ m.size) (hk : k ≤ data.length)
    (i : Nat) (hi : i < k) :
    ((finBytes m bs off data k)[off + i]?).map Prod.fst = data[i]? := by
  have hP : off + k ≤ pwSize m.size off k := by unfold pwSize; split <;> omega
  have hpl := pwBytes_len' (m := m) (bs := bs) (off := off) (data := data) (k := k) hlen
  have hlo : cfLo m off = off := by unfold cfLo; omega
  have hil : i < data.length := by omega
  unfold finBytes
  rw [List.append_assoc, List.getElem?_append_right (by simp only [List.length_take]; omega),
    List.getElem?_append_left (by simp only [List.length_take, hpl]; omega)]
  simp only [List.length_take]
  have hmin : min (cfLo m off) bs.length = off := by omega
  rw [hmin]
  have hlt : off + i - off < (pwBytes m.size off data k
      (cfRange m bs off data.length)).length := by rw [hpl]; omega
  rw [List.getElem?_eq_getElem hlt, Option.map_some, pwBytes_getElem _ _ _ _ _ _ hlt,
    List.getElem?_eq_getElem hil]
  unfold pwByte
  have h2 : min off m.size + (off + i - off) = off + i := by omega
  rw [h2, if_neg (by omega), if_pos (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]

/-- The bytes past the first `k`, with their flags, are what they were. -/
theorem finBytes_mid (hlen : bs.length = m.size) (hoff : off ≤ m.size) (hk : k ≤ data.length)
    (b : Nat) (hb : off + k ≤ b) : (finBytes m bs off data k)[b]? = bs[b]? := by
  by_cases hbm : b < m.size
  · by_cases hbe : off + data.length ≤ b
    · exact finBytes_suf hlen hk (by omega) b hbe
    have hP : pwSize m.size off k = m.size := by unfold pwSize; split <;> omega
    have hpl := pwBytes_len' (m := m) (bs := bs) (off := off) (data := data) (k := k) hlen
    rw [hP] at hpl
    have hlo : cfLo m off = off := by unfold cfLo; omega
    unfold finBytes
    rw [List.append_assoc, List.getElem?_append_right (by simp only [List.length_take]; omega),
      List.getElem?_append_left (by simp only [List.length_take, hpl]; omega)]
    simp only [List.length_take]
    have hmin : min (cfLo m off) bs.length = off := by omega
    rw [hmin]
    have hlt : b - off < (pwBytes m.size off data k (cfRange m bs off data.length)).length := by
      rw [hpl]; omega
    rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem (by omega : b < bs.length)]
    congr 1
    have hx : (cfRange m bs off data.length).getD (b - off) (0, false) = bs[b]'(by omega) := by
      unfold cfRange
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by unfold cfHi; rw [hlo]; omega),
        List.getElem?_drop, hlo, show off + (b - off) = b by omega,
        List.getElem?_eq_getElem (by omega : b < bs.length)]
      rfl
    have hmo : min off m.size = off := by omega
    simp only [pwBytes, List.getElem_map, List.getElem_range, hmo]
    unfold pwByte
    rw [if_neg (by omega), if_neg (by omega), show off + (b - off) - off = b - off by omega, hx]
    simp [show off + k ≤ off + (b - off) by omega]
  · have h1 : bs[b]? = none := List.getElem?_eq_none (by omega)
    rw [h1]
    apply List.getElem?_eq_none
    rw [finBytes_length hlen hk]
    unfold pwSize; split <;> omega

/-- **An attempt keeps the narrowing**: after `nn` of the bytes were written, the rest of the data
at `off + nn` (the write starts inside the file). -/
theorem narrow_fin {m' : OsMeta} {bs' : List (w8 × Bool)} (hN : Narrow m bs off data m' bs')
    (hoff : off ≤ m.size) (nn : Nat) (hnn : nn ≤ data.length) (hk : k ≤ (data.drop nn).length) :
    Narrow m bs off data (finMeta m' (off + nn) (data.drop nn) k)
      (finBytes m' bs' (off + nn) (data.drop nn) k) := by
  have hs := hN.size
  have hdl : (data.drop nn).length = data.length - nn := List.length_drop
  have he : off + nn + (data.drop nn).length = off + data.length := by rw [hdl]; omega
  refine ⟨hN.lo, hN.ok, hN.maps, ?_, ?_, finBytes_length hN.len hk, ?_, ?_, ?_⟩
  · show max m'.hi (off + nn + (data.drop nn).length) ≤ _
    rw [he]; have := hN.hi; omega
  · show m.size ≤ pwSize m'.size (off + nn) k
    have := pwSize_ge' m'.size (off + nn) k; omega
  · intro i hi
    rw [finBytes_pre hN.len i (by unfold cfLo at hi ⊢; omega)]
    exact hN.pre i hi
  · intro hs' i hi
    rw [finBytes_suf hN.len hk (by omega) i (by omega)]
    exact hN.suf hs' i hi
  · show pwSize m'.size (off + nn) k ≤ _
    have := hN.szhi; unfold pwSize; split <;> omega

end fin

theorem cfRange_getElem? {m : OsMeta} {bs : List (w8 × Bool)} {o n : Nat} (ho : o ≤ m.size) (j : Nat) :
    (cfRange m bs o n)[j]? = if o + j < cfHi m o n then bs[o + j]? else none := by
  have hlo : cfLo m o = o := by unfold cfLo; omega
  unfold cfRange
  rw [List.getElem?_take, List.getElem?_drop, hlo]
  by_cases h : o + j < cfHi m o n
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- A byte of a run a crash keeps: what it was (clean if it was), or clean. -/
theorem runByte {m1 : OsMeta} {rs1 : List (Nat × DFrac × List (w8 × Bool))} {f : OsFile}
    (hR : FileCrashedR m1 rs1 (some f)) (hK : RunsKept rs1 (some f)) {r} (hr : r ∈ rs1) (k : Nat)
    (x : w8 × Bool) (hx : r.2.2[k]? = some x) (hb : r.1 + k < f.size) :
    (f.contents[r.1 + k]? = some x.1 ∧ (x.2 = true → CleanPhys f (r.1 + k))) ∨
      CleanPhys f (r.1 + k) := by
  by_cases hx2 : x.2 = true
  · obtain ⟨hc, hcl⟩ := (hR f rfl).2.2 r hr k x hx hx2
    exact .inl ⟨hc, fun _ => hcl⟩
  · rcases hK f rfl r hr k x hx hb with hc | hc
    · exact .inl ⟨hc, fun h => absurd h hx2⟩
    · exact .inr hc

/-- A crash of a narrowing of `m`, `bs` after `w` of the bytes were written, idle or with an
attempt from `nn ≤ w` in flight (the rest of the data from `off + nn`), leaves a file a crash of the
first attempt in flight may leave: its clean and its held bytes are the first attempt's where that
held them; under the first attempt, the bytes written so far, or the old ones as the first attempt
would leave them (`hmid`: the bytes past `off + w` are `bs`'s), or clean ones; and past `m`'s size
the bytes written so far, or the next attempt's, or clean ones. -/
theorem fileOk_narrow {Good : Option OsFile → Prop} {m m' : OsMeta}
    {bs bs' : List (w8 × Bool)} {off : Nat} {data : List w8}
    (hW : FileOk Good (cfWriting m bs off data)) (hlen : bs.length = m.size) (hoff : off ≤ m.size)
    (hN : Narrow m bs off data m' bs') (nn w : Nat) (hnw : nn ≤ w) (hw : w ≤ data.length)
    (hS : off + w ≤ m'.size) (hU : m'.size ≤ max m.size (off + w))
    (hpre : ∀ i < w, (bs'[off + i]?).map Prod.fst = data[i]?)
    (hmid : ∀ i, off + w ≤ i → bs'[i]? = bs[i]?) :
    FileOk Good (m', bs', none) ∧ ∀ t,
      FileOk Good (m', bs', some (t, off + nn, data.drop nn)) := by
  -- the bytes the first attempt's runs hold are where a run of `bs'` has them
  have hcov : ∀ (rs1 : List (Nat × DFrac × List (w8 × Bool))),
      (∀ i, (i < cfLo m off ∨ (off + data.length ≤ m.size ∧ off + data.length ≤ i)) →
        i < bs.length → ∃ r' ∈ rs1, ∃ k', r'.2.2[k']? = bs[i]? ∧ r'.1 + k' = i) →
      ∀ r ∈ fRuns (cfWriting m bs off data), ∀ k x, r.2.2[k]? = some x →
        ∃ r' ∈ rs1, ∃ k', r'.2.2[k']? = some x ∧ r'.1 + k' = r.1 + k := by
    intro rs1 H r hr k x hk
    simp only [fRuns, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [List.getElem?_take] at hk
      split at hk
      · obtain ⟨r', hr', k', h1, h2⟩ := H k (.inl ‹_›) (List.getElem?_eq_some_iff.1 hk).1
        exact ⟨r', hr', k', h1.trans hk, by simpa using h2⟩
      · cases hk
    · simp only [List.getElem?_drop] at hk
      have hlt := (List.getElem?_eq_some_iff.1 hk).1
      have hs : off + data.length ≤ m.size := by unfold cfHi at hlt; omega
      have hhi : cfHi m off data.length = off + data.length := by unfold cfHi; omega
      obtain ⟨r', hr', k', h1, h2⟩ := H (cfHi m off data.length + k) (.inr ⟨hs, by omega⟩) hlt
      exact ⟨r', hr', k', h1.trans hk, h2⟩
  have hmono : ∀ (m1 : OsMeta) (rs1 : List (Nat × DFrac × List (w8 × Bool))) (f : OsFile),
      m1.lo = m.lo → m1.hi ≤ max m.hi (off + data.length) →
      (∀ i, (i < cfLo m off ∨ (off + data.length ≤ m.size ∧ off + data.length ≤ i)) →
        i < bs.length → ∃ r' ∈ rs1, ∃ k', r'.2.2[k']? = bs[i]? ∧ r'.1 + k' = i) →
      FileCrashedR m1 rs1 (some f) → RunsKept rs1 (some f) →
      FileCrashedR (fMeta (cfWriting m bs off data)) (fRuns (cfWriting m bs off data)) (some f) ∧
        RunsKept (fRuns (cfWriting m bs off data)) (some f) := by
    intro m1 rs1 f hlo hhi H hR hK
    refine ⟨fileCrashedR_mono (m1 := m1) (rs1 := rs1) (Nat.le_of_eq hlo.symm)
      (by show _ ≤ max m.hi _; omega)
      (fun r hr k x hk _ => hcov rs1 H r hr k x hk) hR, ?_⟩
    intro f' hf' r hr k x hk hks
    cases hf'
    obtain ⟨r', hr', k', h1, h2⟩ := hcov rs1 H r hr k x hk
    rw [← h2]; rw [← h2] at hks; exact hK f rfl r' hr' k' x h1 hks
  have hbs' : ∀ b, b < m'.size → ∃ x, bs'[b]? = some x := by
    intro b hb; exact ⟨_, List.getElem?_eq_getElem (by rw [hN.len]; exact hb)⟩
  -- a crash that leaves every byte of `bs'` written, as it was, or clean, and past `m'`'s size
  -- clean bytes or the data, is one the first attempt allows
  have hclose : ∀ f,
      FileCrashedR (fMeta (cfWriting m bs off data)) (fRuns (cfWriting m bs off data)) (some f) →
      RunsKept (fRuns (cfWriting m bs off data)) (some f) →
      (∀ b x, bs'[b]? = some x → b < f.size → (off ≤ b ∧ f.contents[b]? = data[b - off]?) ∨
        (f.contents[b]? = some x.1 ∧ (x.2 = true → CleanPhys f b)) ∨ CleanPhys f b) →
      (∀ b, m'.size ≤ b → b < f.size → CleanPhys f b ∨
        (off ≤ b ∧ b < off + data.length ∧ f.contents[b]? = data[b - off]?)) →
      Good (some f) := by
    intro f h1 h2 hQ hT
    refine hW f h1 h2 (fun b hb1 hb2 => ?_) (fun j x hx hj => ?_)
    · by_cases hbm : b < m'.size
      · obtain ⟨x, hx⟩ := hbs' b hbm
        have hbw : b < off + w := by omega
        have hv : some x.1 = data[b - off]? := by
          have := hpre (b - off) (by omega)
          rwa [show off + (b - off) = b by omega, hx] at this
        rcases hQ b x hx hb2 with ⟨-, hc⟩ | ⟨hc, -⟩ | hc
        · exact .inr ⟨by omega, by omega, hc⟩
        · exact .inr ⟨by omega, by omega, hc.trans hv⟩
        · exact .inl hc
      · exact hT b (by omega) hb2
    · have hx' := hx
      rw [cfRange_getElem? hoff] at hx'
      split at hx'
      rotate_left
      · cases hx'
      rename_i hjh
      have hjm : off + j < m.size := by unfold cfHi at hjh; omega
      obtain ⟨y, hy⟩ := hbs' (off + j) (by have := hN.size; omega)
      rcases hQ (off + j) y hy hj with ⟨-, hc⟩ | ⟨hc, hcl⟩ | hc
      · left; rwa [show off + j - off = j by omega] at hc
      · by_cases hjw : j < w
        · left
          have := hpre j hjw
          rw [hy] at this
          exact hc.trans this
        · right; left
          have := hmid (off + j) (by omega)
          rw [hy, hx'] at this
          cases this
          exact ⟨hc, hcl⟩
      · exact .inr (.inr hc)
  refine ⟨fun f hR hK hT _ => ?_, fun t f hR hK hT hTk => ?_⟩
  · have H : ∀ i, (i < cfLo m off ∨ (off + data.length ≤ m.size ∧ off + data.length ≤ i)) →
        i < bs.length → ∃ r' ∈ fRuns (m', bs', none), ∃ k', r'.2.2[k']? = bs[i]? ∧ r'.1 + k' = i := by
      intro i hi hib
      refine ⟨(0, DFrac.own (1 : Qp).half, bs'), List.mem_singleton_self _, i, ?_, by simp⟩
      rcases hi with hi | ⟨hs, hi⟩
      · exact hN.pre i hi
      · exact hN.suf hs i hi
    obtain ⟨h1, h2⟩ := hmono m' _ f hN.lo hN.hi H hR hK
    refine hclose f h1 h2 (fun b x hx hbf => .inr ?_) (fun b hb1 hb2 => .inl (hT b hb1 hb2))
    have := runByte hR hK (r := (0, DFrac.own (1 : Qp).half, bs')) (List.mem_singleton_self _) b x
      (by simpa using hx) (by simpa using hbf)
    simpa using this
  · have hdl : (data.drop nn).length = data.length - nn := List.length_drop
    have he : off + nn + (data.drop nn).length = off + data.length := by rw [hdl]; omega
    have hlo' : cfLo m' (off + nn) = off + nn := by unfold cfLo; omega
    have H : ∀ i, (i < cfLo m off ∨ (off + data.length ≤ m.size ∧ off + data.length ≤ i)) →
        i < bs.length → ∃ r' ∈ fRuns (m', bs', some (t, off + nn, data.drop nn)), ∃ k',
          r'.2.2[k']? = bs[i]? ∧ r'.1 + k' = i := by
      intro i hi hib
      have hsz := hN.size
      rcases hi with hi | ⟨hs, hi⟩
      · refine ⟨(0, DFrac.own (1 : Qp).half, bs'.take (cfLo m' (off + nn))), List.mem_cons_self, i,
          ?_, by simp⟩
        rw [List.getElem?_take_of_lt (by unfold cfLo at hi ⊢; omega)]
        exact hN.pre i hi
      · have hhi : cfHi m' (off + nn) (data.drop nn).length = off + data.length := by
          unfold cfHi; rw [he]; omega
        refine ⟨(cfHi m' (off + nn) (data.drop nn).length, DFrac.own (1 : Qp).half,
            bs'.drop (cfHi m' (off + nn) (data.drop nn).length)),
          List.mem_cons_of_mem _ (List.mem_singleton_self _), i - (off + data.length), ?_, ?_⟩
        · simp only [List.getElem?_drop, hhi]
          rw [show off + data.length + (i - (off + data.length)) = i by omega]
          exact hN.suf hs i hi
        · show cfHi m' (off + nn) (data.drop nn).length + (i - (off + data.length)) = i
          rw [hhi]; omega
    obtain ⟨h1, h2⟩ := hmono (pwMeta m' (off + nn) (data.drop nn).length) _ f hN.lo
      (by have := hN.hi; show max m'.hi _ ≤ max m.hi _; rw [he]; omega) H hR hK
    refine hclose f h1 h2 (fun b x hx hbf => ?_) (fun b hb1 hb2 => ?_)
    · by_cases hb0 : b < off + nn
      · right
        have := runByte hR hK (r := (0, DFrac.own (1 : Qp).half, bs'.take (cfLo m' (off + nn))))
          List.mem_cons_self b x (by rw [List.getElem?_take_of_lt (by omega)]; exact hx)
          (by simpa using hbf)
        simpa using this
      by_cases hb1 : cfHi m' (off + nn) (data.drop nn).length ≤ b
      · right
        have hcb : cfHi m' (off + nn) (data.drop nn).length +
            (b - cfHi m' (off + nn) (data.drop nn).length) = b := by omega
        have := runByte hR hK (r := (cfHi m' (off + nn) (data.drop nn).length, DFrac.own (1 : Qp).half,
            bs'.drop (cfHi m' (off + nn) (data.drop nn).length)))
          (List.mem_cons_of_mem _ (List.mem_singleton_self _))
          (b - cfHi m' (off + nn) (data.drop nn).length) x
          (by dsimp only; rw [List.getElem?_drop, hcb]; exact hx)
          (by dsimp only; rw [hcb]; exact hbf)
        dsimp only at this
        rw [hcb] at this
        exact this
      · have hj : (cfRange m' bs' (off + nn) (data.drop nn).length)[b - (off + nn)]? = some x := by
          rw [cfRange_getElem? (by omega), if_pos (by omega),
            show off + nn + (b - (off + nn)) = b by omega]
          exact hx
        have := hTk (b - (off + nn)) x hj (by omega)
        rw [show off + nn + (b - (off + nn)) = b by omega] at this
        rcases this with hc | hc | hc
        · left
          refine ⟨by omega, ?_⟩
          rw [hc, List.getElem?_drop]; congr 1; omega
        · exact .inr (.inl hc)
        · exact .inr (.inr hc)
    · rcases hT b (by show (pwMeta m' (off + nn) (data.drop nn).length).size ≤ b; exact hb1)
        hb2 with hc | ⟨h3, h4, h5⟩
      · exact .inl hc
      · right
        refine ⟨by omega, by rw [← he]; exact h4, ?_⟩
        rw [h5, List.getElem?_drop]
        congr 1; omega

end Perennial
