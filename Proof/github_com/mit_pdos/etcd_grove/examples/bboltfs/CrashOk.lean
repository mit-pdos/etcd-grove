/- Lean-first (no Rocq counterpart). minibolt's crash obligations, as pure lemmas: `CrashOkQ (P1 p) p
Good s` for the states `s` of the database file that `BootMinibolt`'s code passes through,
reduced to statements on images (`idleImg`, `writingImg`), which `CrashImg.lean` proves for `init`'s and `commit`'s states.

The core is what P1 says of a crash image's valid meta slot, in the terms the client holds
(`seen_idle_slot`, `seen_writing_slot`): the slot is the durable image's (`D`, which agrees with
the durable bytes the `OsMeta` knows, `m.dur`, and with the clean bytes), or the bytes the client
holds (each of its bytes not clean, when no write is in flight), or the client's write in flight
over them. Changes in flight by others on the file are excluded by `CrashSeenR`: they hold none of
the bytes the client holds, so (on a file the client holds whole) they write nothing.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.CrashGood
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.BootP1
public import Proof.os.CrashSt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- What the crashed state holds of a file the client holds as `m`, and the bytes `bs` from 0
(all of them): the file `f`, its bytes `bs`, the durable bytes `m.dur` knows and the clean ones. -/
theorem seen_file {Q : OsState → OsState → Prop} {p : GoString} {m : OsMeta} {dq : DFrac}
    {bs : List (w8 × Bool)} {ts : List (Nat × TokInfo)} {fo : Option OsFile}
    (hwf : bs.length = m.size) (h : CrashSeenR Q p (some m) [(0, dq, bs)] ts fo) :
    ∃ (st st' : OsState) (f : OsFile), OsCrash st st' ∧ Q st st' ∧ st'.files !! p = some fo ∧
      st.file p = some f ∧ f.cur = bs.map Prod.fst ∧
      (∀ (j : Nat) (d : w8), m.dur[j]? = some (some d) → f.durable[j]? = some d) ∧
      f.durable.length ≤ m.durHi ∧
      (∀ j (hj : j < bs.length), bs[j].2 = true → CleanPhys f j) ∧
      (∀ j (hj : j < bs.length), bs[j].2 = true → f.durable[j]? = some bs[j].1) ∧
      ∀ t c, st.inflight !! t = some c → c.path = p → ∃ ti, ti.c = c ∧ ((t, ti) ∈ ts ∨
        (∀ off data, c.kind = .write off data → data = [])) := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQ, hst', hm, hxs, -, htok⟩ := h
  obtain ⟨f, hfp, hmo⟩ := hcoh.meta_some p m hm
  have hf : st.file p = some f := file_eq_some.2 hfp
  have hb : ∀ k (hk : k < bs.length), f.cur[k]? = some bs[k].1 ∧
      (bs[k].2 = true → CleanPhys f k) := by
    intro k hk
    have := hxs (0, dq, bs) List.mem_cons_self k hk
    simp only [Nat.zero_add] at this
    obtain ⟨f1, h1, h2, h3⟩ := hcoh.bytes p k _ this
    rw [hf] at h1; cases h1
    exact ⟨h2, fun hc => (h3 hc).1⟩
  have hcur : f.cur = bs.map Prod.fst := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < bs.length
    · rw [(hb k hk).1, List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
    · rw [List.getElem?_eq_none (by have := hmo.size; omega),
        List.getElem?_eq_none (by simp; omega)]
  refine ⟨st, st', f, hcr, hQ, hst', hf, hcur, fun j d h => hmo.dur j d h, hmo.durLen,
    fun j hj hc => (hb j hj).2 hc, fun j hj hc => ?_, ?_⟩
  · have h4 := ((hb j hj).2 hc).2.2.2
    rw [h4]; exact (hb j hj).1
  · intro t c ht hcp
    obtain ⟨ti, hti, rfl⟩ := coh_tok hcoh ht
    refine ⟨ti, rfl, ?_⟩
    rcases htok t ti hti hcp with hin | ⟨hq, hd⟩
    · exact Or.inl hin
    · refine Or.inr fun off data hk => ?_
      have hsz : st.size ti.c.path = bs.length := by
        rw [hcp, size_of_file hf, hcur, List.length_map]
      refine Classical.byContradiction fun hne => ?_
      have hlen : 0 < data.length := List.length_pos_iff.2 hne
      by_cases ho : off < bs.length
      · apply hd (0, dq, bs) List.mem_cons_self off ho
        simp only [affRange, affLo, affHi, hk, hsz, Nat.zero_add, List.mem_range'_1]
        omega
      · apply hq
        apply hcoh.tok_q t ti hti
        simp only [Reaches, hk, hsz]
        omega

/-- What a crash may leave of a file the client holds whole as `m`, `bs`, with no write in flight
(`idleImg`): an image within `m`'s size bounds, with the clean bytes of `bs`, whose valid meta
slots are the durable image `D`'s (which agrees with `m.dur` and the clean bytes, and is at most
`m.durHi` long) or `bs`'s, if no byte of the slot is clean there. -/
def idleImg (m : OsMeta) (bs : List (w8 × Bool)) (img D : List w8) : Prop :=
  m.lo ≤ img.length ∧ img.length ≤ m.hi ∧
  (∀ (k : Nat) (x : w8 × Bool), bs[k]? = some x → x.2 = true → img[k]? = some x.1) ∧
  (∀ (j : Nat) (d : w8), m.dur[j]? = some (some d) → D[j]? = some d) ∧ D.length ≤ m.durHi ∧
  (∀ j (hj : j < bs.length), bs[j].2 = true → D[j]? = some bs[j].1) ∧
  ∀ i < 2, 4096 * i + 80 ≤ img.length → metaValid (fileMeta img i) →
    metaSlot img i = metaSlot D i ∨
    ((∀ k < 64, ∀ x, bs[4096 * i + 16 + k]? = some x → x.2 = false) ∧
      metaSlot img i = metaSlot (bs.map Prod.fst) i)

/-- What the crashed state holds of a file the client holds as `m`, `bs` with its write of `data`
at `off` in flight (token `t`): the file `f`, its bytes `bs`, the durable bytes `m.dur` knows and
the clean ones outside the write's range, and the write the only change in flight on it. -/
theorem seen_writing {Q : OsState → OsState → Prop} {p : GoString} {m : OsMeta}
    {bs : List (w8 × Bool)} {t off : Nat} {data : List w8} {fo : Option OsFile}
    (hwf : bs.length = m.size)
    (h : CrashSeenR Q p (cMeta (some (m, bs, some (t, off, data))))
      (cRuns (some (m, bs, some (t, off, data)))) (cToks p (some (m, bs, some (t, off, data)))) fo) :
    ∃ (st st' : OsState) (f : OsFile), OsCrash st st' ∧ Q st st' ∧ st'.files !! p = some fo ∧
      st.file p = some f ∧ f.cur = bs.map Prod.fst ∧
      (∀ (j : Nat) (d : w8), m.dur[j]? = some (some d) → f.durable[j]? = some d) ∧
      f.durable.length ≤ m.durHi ∧
      (∀ j (hj : j < bs.length), (j < cfLo m off ∨ cfHi m off data.length ≤ j) → bs[j].2 = true →
        f.durable[j]? = some bs[j].1) ∧
      (∀ j (hj : j < bs.length), bs[j].2 = true → f.dirty j = false ∧ f.lost j = false) ∧
      ∀ t' c, st.inflight !! t' = some c → c.path = p → c = ⟨p, .write off data⟩ := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQ, hst', hm, hxs, hts, -⟩ := h
  simp only [cMeta, cRuns, cToks] at hm hxs hts
  obtain ⟨f, hfp, hmo⟩ := hcoh.meta_some p _ hm
  have hf : st.file p = some f := file_eq_some.2 hfp
  have hsz : f.cur.length = bs.length := by rw [hwf, ← hmo.size]; rfl
  have hti := hts _ List.mem_cons_self
  -- the bytes outside the write's range, from the runs
  have hb : ∀ k (hk : k < bs.length), (k < cfLo m off ∨ cfHi m off data.length ≤ k) →
      f.cur[k]? = some bs[k].1 ∧ (bs[k].2 = true → CleanPhys f k) := by
    intro k hk hout
    have hx : Γb !! (p, k) = some bs[k] := by
      rcases hout with hlt | hge
      · have := hxs _ List.mem_cons_self k (by rw [List.length_take]; omega)
        simpa [List.getElem_take] using this
      · have := hxs _ (List.mem_cons_of_mem _ List.mem_cons_self) (k - cfHi m off data.length)
          (by rw [List.length_drop]; omega)
        simp only [List.getElem_drop] at this
        have e : cfHi m off data.length + (k - cfHi m off data.length) = k := by omega
        simp only [e] at this
        exact this
    obtain ⟨f1, h1, h2, h3⟩ := hcoh.bytes p k _ hx
    rw [hf] at h1; cases h1
    exact ⟨h2, fun hc => (h3 hc).1⟩
  -- the bytes in it, from the token
  have hsize : st.size p = bs.length := by rw [size_of_file hf, hsz]
  have hin : ∀ k (hk : k < bs.length), cfLo m off ≤ k → k < cfHi m off data.length →
      f.cur[k]? = some bs[k].1 := by
    intro k hk h1 h2
    obtain ⟨f1, h1', hsv⟩ := hcoh.tok_saved _ _ hti
    rw [hf] at h1'; cases h1'
    have hj : k - cfLo m off < (cfRange m bs off data.length).length := by
      simp only [cfRange, List.length_take, List.length_drop]; omega
    have e1 := congrArg (fun l => l[k - cfLo m off]?) hsv
    simp only [List.getElem?_map, cfRange] at e1
    simp only [affRange, affLo, affHi, hsize] at e1
    rw [List.getElem?_take, if_pos (by simp only [cfHi, cfLo] at h1 h2 hj ⊢; omega),
      List.getElem?_drop, show cfLo m off + (k - cfLo m off) = k by omega,
      List.getElem?_eq_getElem hk, List.getElem?_range' (by simp only [cfHi, cfLo] at h1 h2 ⊢; omega)] at e1
    simp only [Option.map_some, Option.some.injEq] at e1
    rw [show min off bs.length + 1 * (k - cfLo m off) = k by simp only [cfLo] at h1 ⊢; omega] at e1
    rw [List.getElem?_eq_getElem (by omega), e1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  have hcur : f.cur = bs.map Prod.fst := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < bs.length
    · rw [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some]
      by_cases hr : cfLo m off ≤ k ∧ k < cfHi m off data.length
      · exact hin k hk hr.1 hr.2
      · exact (hb k hk (by omega)).1
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  refine ⟨st, st', f, hcr, hQ, hst', hf, hcur, fun j d h => hmo.dur j d h, hmo.durLen,
    fun j hj hout hc => ?_, fun j hj hc => ?_, ?_⟩
  · have h4 := ((hb j hj hout).2 hc).2.2.2
    rw [h4]; exact (hb j hj hout).1
  · by_cases hr : cfLo m off ≤ j ∧ j < cfHi m off data.length
    · have hcl : ((cfRange m bs off data.length).map Prod.snd)[j - cfLo m off]? = some true := by
        simp only [List.getElem?_map, cfRange]
        rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop,
          show cfLo m off + (j - cfLo m off) = j by omega, List.getElem?_eq_getElem hj]
        simp [hc]
      obtain ⟨-, f1, h1, c1, c2, -⟩ := hcoh.tok_clean _ _ hti _ hcl
      simp only at h1 c1 c2
      rw [hf] at h1; cases h1
      simp only [affLo, hsize] at c1 c2
      rw [show min off bs.length + (j - cfLo m off) = j by simp only [cfLo] at hr ⊢; omega] at c1 c2
      exact ⟨c1, c2⟩
    · obtain ⟨c1, c2, -⟩ := (hb j hj (by omega)).2 hc
      exact ⟨c1, c2⟩
  · intro t' c ht' hcp
    by_cases he : t' = t
    · subst he
      have := hcoh.toks t'
      rw [hti, ht'] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact this.symm
    · exact absurd hcp (hcoh.tok_alone t _ hti rfl t' c he ht')

/-- **The idle obligation**: a state without a write in flight is crash-safe under P1 if every
`idleImg` is good, or the file may vanish (it was created since boot) . -/
theorem crashOkQ_idle {p : GoString} {m : OsMeta} {bs : List (w8 × Bool)}
    (hwf : bs.length = m.size) (H : ∀ img D, idleImg m bs img D → goodImg img) :
    CrashOkQ (P1 p) p Good (some (m, bs, none)) := by
  intro fo hfc hseen
  rcases hfc with ⟨rfl, -⟩ | ⟨img, rfl, hlo, hhi, hcl⟩
  · trivial
  obtain ⟨st, st', f, -, hP, hst', hf, hcur, hdur, hdl, hcp, hclean, htok⟩ := seen_file hwf hseen
  refine H img f.durable ⟨hlo, hhi, fun k x hk hc => ?_, hdur, hdl, hclean,
    fun i hi hlen hv => ?_⟩
  · simpa using hcl _ List.mem_cons_self k x hk hc
  have hnc : ∀ k, f.dirty k = true ∨ f.lost k = true → ∀ x, bs[k]? = some x → x.2 = false := by
    intro k hk x hx
    obtain ⟨hkl, rfl⟩ := List.getElem?_eq_some_iff.1 hx
    cases hc : bs[k].2
    · rfl
    · have := hcp k hkl hc
      rcases hk with hk | hk
      · rw [this.1] at hk; cases hk
      · rw [this.2.1] at hk; cases hk
  rcases hP f img i hf hst' hi hlen hv with h1 | ⟨hdl2, h2⟩ | ⟨t, off, data, ht, hne, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨fun k hk => hnc _ (hdl2 k hk), by rw [h2, hcur]⟩
  · obtain ⟨ti, hc, hin | hnil⟩ := htok t _ ht rfl
    · simp [cToks] at hin
    · exact absurd (hnil off data rfl) hne

/-- What a crash may leave of a file the client holds as `m`, `bs` with its write of `data` at
`off` in flight (`writingImg`): an image within the write's size bounds, with the clean bytes of
`bs` outside the write's range, whose valid meta slots are the durable image `D`'s (which agrees
with `m.dur` and those clean bytes), or `bs`'s (if no byte of the slot is clean in `bs`: P1's
second case, and a taken byte flagged clean is clean, `OsCoh.tok_clean`), or `bs`'s after the write. -/
def writingImg (m : OsMeta) (bs : List (w8 × Bool)) (off : Nat) (data : List w8)
    (img D : List w8) : Prop :=
  m.lo ≤ img.length ∧ img.length ≤ max m.hi (off + data.length) ∧
  (∀ (k : Nat) (x : w8 × Bool), bs[k]? = some x → x.2 = true →
    (k < cfLo m off ∨ cfHi m off data.length ≤ k) → img[k]? = some x.1) ∧
  (∀ (j : Nat) (d : w8), m.dur[j]? = some (some d) → D[j]? = some d) ∧ D.length ≤ m.durHi ∧
  (∀ j (hj : j < bs.length), (j < cfLo m off ∨ cfHi m off data.length ≤ j) → bs[j].2 = true →
    D[j]? = some bs[j].1) ∧
  ∀ i < 2, 4096 * i + 80 ≤ img.length → metaValid (fileMeta img i) →
    metaSlot img i = metaSlot D i ∨
    ((∀ k < 64, ∀ x, bs[4096 * i + 16 + k]? = some x → x.2 = false) ∧
      metaSlot img i = metaSlot (bs.map Prod.fst) i) ∨
    metaSlot img i = metaSlot (writeBytes (bs.map Prod.fst) off data) i

/-- **The writing obligation**: a state with the client's write in flight is crash-safe under P1
if every `writingImg` is good. -/
theorem crashOkQ_writing {p : GoString} {m : OsMeta} {bs : List (w8 × Bool)} {t off : Nat}
    {data : List w8} (hwf : bs.length = m.size)
    (H : ∀ img D, writingImg m bs off data img D → goodImg img) :
    CrashOkQ (P1 p) p Good (some (m, bs, some (t, off, data))) := by
  intro fo hfc hseen
  rcases hfc with ⟨rfl, -⟩ | ⟨img, rfl, hlo, hhi, hcl⟩
  · trivial
  obtain ⟨st, st', f, -, hP, hst', hf, hcur, hdur, hdl, hclean, hcp, hone⟩ := seen_writing hwf hseen
  refine H img f.durable ⟨hlo, hhi, fun k x hk hc hout => ?_, hdur, hdl, hclean,
    fun i hi hlen hv => ?_⟩
  · simp only [cRuns] at hcl
    rcases hout with hlt | hge
    · have := hcl _ List.mem_cons_self k x (by rw [List.getElem?_take, if_pos hlt]; exact hk) hc
      simpa using this
    · have := hcl _ (List.mem_cons_of_mem _ List.mem_cons_self) (k - cfHi m off data.length) x
        (by rw [List.getElem?_drop, show cfHi m off data.length + (k - cfHi m off data.length) = k
          by omega]; exact hk) hc
      rwa [show cfHi m off data.length + (k - cfHi m off data.length) = k by omega] at this
  have hnc : ∀ k, f.dirty k = true ∨ f.lost k = true → ∀ x, bs[k]? = some x → x.2 = false := by
    intro k hk x hx
    obtain ⟨hkl, rfl⟩ := List.getElem?_eq_some_iff.1 hx
    cases hc : bs[k].2
    · rfl
    · have := hcp k hkl hc
      rcases hk with hk | hk
      · rw [this.1] at hk; cases hk
      · rw [this.2] at hk; cases hk
  rcases hP f img i hf hst' hi hlen hv with h1 | ⟨hdl2, h2⟩ | ⟨t', off', data', ht, -, h3⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨fun k hk => hnc _ (hdl2 k hk), by rw [h2, hcur]⟩)
  · have := hone t' _ ht rfl
    simp only [OsChange.mk.injEq, OsChangeKind.write.injEq] at this
    obtain ⟨-, rfl, rfl⟩ := this
    exact Or.inr (Or.inr (by rw [h3, hcur]))

/-- **The truncating obligation**: a state with the client's growing truncate to `sz` in flight
is crash-safe under P1 if every `idleImg` of the size bound it widens (`ftMeta`) is good: the
truncate is no write, so P1's third case does not apply. -/
theorem crashOkS_trunc {p : GoString} (s : CSt) {t sz : Nat} (hb : s.busy = .trunc t sz)
    (hwf : s.bs.length = s.m.size)
    (H : ∀ img D, idleImg (ftMeta s.m sz) s.bs img D → goodImg img) :
    CrashOkS (P1 p) p Good (some s) := by
  have hsub := s.runsSub_whole (DFrac.own (1 : Qp).half) (fun k => by simp [CSt.taken, hb])
  intro fo hfc hseen
  simp only [sMeta, sRuns, sToks, CSt.vmeta, hb] at hfc hseen
  have hfc := fileCrashedR_sub hsub hfc
  have hseen := crashSeenR_sub hsub hseen
  rcases hfc with ⟨rfl, -⟩ | ⟨img, rfl, hlo, hhi, hcl⟩
  · trivial
  obtain ⟨st, st', f, -, hP, hst', hf, hcur, hdur, hdl, hcp, hclean, htok⟩ :=
    seen_file (m := ftMeta s.m sz) hwf hseen
  refine H img f.durable ⟨hlo, hhi, fun k x hk hc => ?_, hdur, hdl, hclean,
    fun i hi hlen hv => ?_⟩
  · simpa using hcl _ List.mem_cons_self k x hk hc
  have hnc : ∀ k, f.dirty k = true ∨ f.lost k = true → ∀ x, s.bs[k]? = some x → x.2 = false := by
    intro k hk x hx
    obtain ⟨hkl, rfl⟩ := List.getElem?_eq_some_iff.1 hx
    cases hc : s.bs[k].2
    · rfl
    · have := hcp k hkl hc
      rcases hk with hk | hk
      · rw [this.1] at hk; cases hk
      · rw [this.2.1] at hk; cases hk
  rcases hP f img i hf hst' hi hlen hv with h1 | ⟨hdl2, h2⟩ | ⟨t', off, data, ht, hne, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨fun k hk => hnc _ (hdl2 k hk), by rw [h2, hcur]⟩
  · obtain ⟨ti, hc, hin | hnil⟩ := htok t' _ ht rfl
    · simp only [CSt.toks, hb, List.mem_singleton, Prod.mk.injEq] at hin
      obtain ⟨-, rfl⟩ := hin
      cases hc
    · exact absurd (hnil off data rfl) hne

/-- **Obligation 1**: the file `OpenFile` creates, empty. -/
theorem crashOkQ_create (p : GoString) : CrashOkQ (P1 p) p Good (some (newMeta, [], none)) := by
  apply crashOkQ_idle rfl
  rintro img D ⟨-, hhi, -⟩
  have h0 : img.length = 0 := by simp only [newMeta] at hhi; omega
  refine ⟨by omega, Or.inl ⟨by omega, fun i _ hle => by omega⟩⟩

end pure

end bboltfs
end EtcdGrove
end Perennial
