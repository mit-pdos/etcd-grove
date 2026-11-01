/-
Pure facts of the crash-aware write (`Proof/os/CrashFile.lean`): every state a `WriteAt` passes
through, retries included, is a narrowing (`Narrow`) of the file it started from, and a crash of a
narrowing, idle or with the next attempt in flight, leaves a file that a crash of the first
attempt in flight could leave (`crashOk_narrow`). So the caller shows `CrashOk` of one state, the
first attempt's (`cfWriting`).
-/
module

public import Proof.os.CrashFile

@[expose] public section

noncomputable section

namespace Perennial

open Iris

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
  named : m'.named = m.named
  ok : m'.ok = m.ok
  maps : m'.maps = m.maps
  hi : m'.hi ≤ max m.hi (off + data.length)
  size : m.size ≤ m'.size
  len : bs'.length = m'.size
  pre : ∀ i < cfLo m off, bs'[i]? = bs[i]?
  suf : off + data.length ≤ m.size → ∀ i, off + data.length ≤ i → bs'[i]? = bs[i]?

theorem narrow_refl {m : OsMeta} {bs : List (w8 × Bool)} (off : Nat) (data : List w8)
    (hlen : bs.length = m.size) : Narrow m bs off data m bs :=
  ⟨rfl, rfl, rfl, rfl, by omega, Nat.le_refl _, hlen, fun _ _ => rfl, fun _ _ _ => rfl⟩

section fin
variable {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8} {k : Nat}

theorem pwSize_ge (sz off k : Nat) : sz ≤ pwSize sz off k := by
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
  have hP := pwSize_ge m.size off k
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

theorem narrow_fin {m' : OsMeta} {bs' : List (w8 × Bool)} (hN : Narrow m bs off data m' bs')
    (hk : k ≤ data.length) :
    Narrow m bs off data (finMeta m' off data k) (finBytes m' bs' off data k) := by
  have hs := hN.size
  refine ⟨hN.lo, hN.named, hN.ok, hN.maps, ?_, ?_, finBytes_length hN.len hk, ?_, ?_⟩
  · show max m'.hi (off + data.length) ≤ _
    have := hN.hi; omega
  · show m.size ≤ pwSize m'.size off k
    have := pwSize_ge m'.size off k; omega
  · intro i hi
    rw [finBytes_pre hN.len i (by unfold cfLo at hi ⊢; omega)]
    exact hN.pre i hi
  · intro hs' i hi
    rw [finBytes_suf hN.len hk (by omega) i hi]
    exact hN.suf hs' i hi

end fin

/-- A crash of a narrowing of `m`, `bs`, idle or with the write's next attempt in flight, leaves
a file a crash of the first attempt in flight may leave. -/
theorem crashOk_narrow {Good : Option OsFile → Prop} {m m' : OsMeta}
    {bs bs' : List (w8 × Bool)} {off : Nat} {data : List w8}
    (hW : CrashOk Good (cfWriting m bs off data)) (hlen : bs.length = m.size)
    (hN : Narrow m bs off data m' bs') :
    CrashOk Good (some (m', bs', none)) ∧ ∀ t, CrashOk Good (some (m', bs', some (t, off, data))) := by
  -- the clean bytes the first attempt's crash keeps are where a run of `bs'` has them
  have hcov : ∀ (rs1 : List (Nat × DFrac × List (w8 × Bool))),
      (∀ i, (i < cfLo m off ∨ (off + data.length ≤ m.size ∧ off + data.length ≤ i)) →
        i < bs.length → ∃ r' ∈ rs1, ∃ k', r'.2.2[k']? = bs[i]? ∧ r'.1 + k' = i) →
      ∀ r ∈ cRuns (cfWriting m bs off data), ∀ k x, r.2.2[k]? = some x → x.2 = true →
        ∃ r' ∈ rs1, ∃ k', r'.2.2[k']? = some x ∧ r'.1 + k' = r.1 + k := by
    intro rs1 H r hr k x hk _
    simp only [cRuns, List.mem_cons, List.not_mem_nil, or_false] at hr
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
  refine ⟨fun fo h => hW fo ?_, fun t fo h => hW fo ?_⟩
  · refine fileCrashedR_mono (m1 := m') (rs1 := cRuns (some (m', bs', none)))
      (Nat.le_of_eq hN.lo.symm) (by have := hN.hi; show _ ≤ max m.hi _; omega)
      (fun h => by show m.named = false; rw [← hN.named]; exact h) (hcov _ ?_) h
    intro i hi hib
    refine ⟨(0, DFrac.own (1 : Qp).half, bs'), List.mem_singleton_self _, i, ?_, by simp⟩
    rcases hi with hi | ⟨hs, hi⟩
    · exact hN.pre i hi
    · exact hN.suf hs i hi
  · refine fileCrashedR_mono (m1 := pwMeta m' off data.length)
      (rs1 := cRuns (some (m', bs', some (t, off, data))))
      (Nat.le_of_eq hN.lo.symm) (by have := hN.hi; show max m'.hi _ ≤ max m.hi _; omega)
      (fun h => by show m.named = false; rw [← hN.named]; exact h) (hcov _ ?_) h
    intro i hi hib
    have hsz := hN.size
    rcases hi with hi | ⟨hs, hi⟩
    · refine ⟨(0, DFrac.own (1 : Qp).half, bs'.take (cfLo m' off)), List.mem_cons_self, i, ?_,
        by simp⟩
      rw [List.getElem?_take_of_lt (by unfold cfLo at hi ⊢; omega)]
      exact hN.pre i hi
    · refine ⟨(cfHi m' off data.length, DFrac.own (1 : Qp).half, bs'.drop (cfHi m' off data.length)),
        List.mem_cons_of_mem _ (List.mem_singleton_self _), i - cfHi m' off data.length, ?_, ?_⟩
      · simp only [List.getElem?_drop]
        rw [show cfHi m' off data.length + (i - cfHi m' off data.length) = i by
          unfold cfHi; omega]
        exact hN.suf hs i hi
      · show cfHi m' off data.length + (i - cfHi m' off data.length) = i
        unfold cfHi; omega

end Perennial
