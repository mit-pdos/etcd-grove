/-
**What a crash leaves of a sector whose versions are known** (`OsMeta.vk`, `MetaOk.vk`): a sector
with at most two versions since the last successful sync comes back whole as one of them (the
durable one, which `OsMeta.dur` knows, or the page cache's, which the client holds), or, under
`NoTearCrash`, as the client's in-page write in flight landed whole: never a mix of bytes of
different versions. Untrusted.

* `crashSeen_sec`: for a full sector below the size of a file whose `OsMeta` knows its versions, a
  crash (`CrashSeenR`, under a premise that gives `NoTearCrash`) leaves the bytes `m.dur` knows of
  it, the bytes the client holds of it (`ByteSeen`: in its runs, or saved by its token), or those
  bytes with the client's write in flight over them (`wByte`). The client's change in flight is
  none (and then its runs cover the file), or one it holds whole (`q = 1`): an in-page write
  starting inside the file, or a growing truncate.
-/
module

public import GooseLang.Ext.Fs.CrashKept
public import GooseLang.Ext.Fs.NoTear

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris

/-- Byte `b` as the client holds it: in one of its runs `rs`, or saved by the write of `ts` that
took it (from `min off m.size` on). -/
def ByteSeen (m : OsMeta) (rs : List (Nat × DFrac × List (w8 × Bool))) (ts : List (Nat × TokInfo))
    (b : Nat) (y : w8) : Prop :=
  (∃ r ∈ rs, ∃ k x, r.2.2[k]? = some x ∧ r.1 + k = b ∧ x.1 = y) ∨
  (∃ x ∈ ts, ∃ off data, x.2.c.kind = .write off data ∧ min off m.size ≤ b ∧
    x.2.saved[b - min off m.size]? = some y)

/-- Byte `b`, held as `y`, after a write of `data` at `off`. -/
def wByte (off : Nat) (data : List w8) (b : Nat) (y : w8) : w8 :=
  if off ≤ b ∧ b < off + data.length then data.getD (b - off) 0 else y

/-! ## Lists of at most two versions -/

theorem mem_le_two {α : Type} {l : List α} {v : α} (h : l.length ≤ 2) (hv : v ∈ l) :
    l.head? = some v ∨ l.getLast? = some v := by
  match l, h, hv with
  | [a], _, hv => simp only [List.mem_singleton] at hv; subst hv; simp
  | [a, b], _, hv =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> simp

/-! ## A sector across landings that miss it -/

/-- The change of kind `k` leaves sector `n` of a file of size at least `s0` as it is, and the size
at least `s0`: an empty write; a write from inside the file (`off ≤ s0`) that misses the sector;
a truncate to at least `s0`. -/
def KeepsSec (s0 n : Nat) : OsChangeKind → Prop
  | .write off data => data = [] ∨ (off ≤ s0 ∧ secHits off (off + data.length) n = false)
  | .truncate sz => s0 ≤ sz

theorem secHits_mono {lo hi hi' n : Nat} (h : hi' ≤ hi) (hn : secHits lo hi n = false) :
    secHits lo hi' n = false := by
  simp only [secHits, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at hn ⊢; omega

theorem landed_keepsSec {s0 n : Nat} (hn : 512 * (n + 1) ≤ s0) :
    ∀ {ks : List OsChangeKind} {f g : OsFile}, Landed ks f g → s0 ≤ f.size →
      (∀ k ∈ ks, KeepsSec s0 n k) → g.secs n = f.secs n ∧ s0 ≤ g.size := by
  intro ks f g hl
  induction hl with
  | nil f => intro hs _; exact ⟨rfl, hs⟩
  | write off data k ks f g hk _ ih =>
    intro hs hK
    have hw := hK _ List.mem_cons_self
    have hrest := fun k' hk' => hK k' (List.mem_cons_of_mem _ hk')
    have hsz : s0 ≤ (f.landWrite off data k).size := by
      rw [landWrite_size f off data k hk]; split <;> omega
    have hsec : (f.landWrite off data k).secs n = f.secs n := by
      unfold OsFile.landWrite
      split
      · rfl
      · rename_i hk0
        simp only [OsFile.change]
        rcases hw with rfl | ⟨hoff, hmiss⟩
        · simp at hk; omega
        · rw [Nat.min_eq_left (by omega : off ≤ f.size),
            secHits_mono (by omega : off + k ≤ off + data.length) hmiss]
          rfl
    obtain ⟨h1, h2⟩ := ih hsz hrest
    exact ⟨h1.trans hsec, h2⟩
  | trunc sz sz' ks f g h1 h2 _ ih =>
    intro hs hK
    have ht : s0 ≤ sz := hK _ List.mem_cons_self
    have hrest := fun k' hk' => hK k' (List.mem_cons_of_mem _ hk')
    have hsz : s0 ≤ (f.truncate sz').size := by
      simp only [OsFile.truncate, OsFile.change, resized_length]; omega
    have hsec : (f.truncate sz').secs n = f.secs n := by
      simp only [OsFile.truncate, OsFile.change]
      rw [show secHits (min f.size sz') (max f.size sz') n = false by
        simp only [secHits, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]; omega]
      rfl
    obtain ⟨h1, h2⟩ := ih hsz hrest
    exact ⟨h1.trans hsec, h2⟩

/-! ## The bytes of a sector -/

/-- Byte `j` of a sector version. -/
abbrev secByte (v : SecBytes) (j : Nat) : w8 := v.toList.getD j 0

theorem divmod_sec (n j : Nat) (hj : j < 512) : (512 * n + j) / 512 = n ∧ (512 * n + j) % 512 = j := by
  omega

/-- The page cache's version of a sector below the size holds the file's bytes. -/
theorem last_byte (f : OsFile) (n j : Nat) (hj : j < 512) (hb : 512 * n + j < f.size) (y : w8)
    (hy : f.contents[512 * n + j]? = some y) : secByte (f.secs n).last j = y := by
  rw [contents_getElem?, if_pos hb, Option.some.injEq, rawAt_def,
    (divmod_sec n j hj).1, (divmod_sec n j hj).2] at hy
  exact hy

/-- The version of a write landed whole over a sector it hits. -/
theorem landWrite_last (f : OsFile) (off : Nat) (data : List w8) (hd : data ≠ [])
    (hoff : off ≤ f.size) (n : Nat) (hn : secHits off (off + data.length) n = true) (j : Nat)
    (hj : j < 512) (hb : 512 * n + j < f.size) :
    secByte ((f.landWrite off data data.length).secs n).last j =
      wByte off data (512 * n + j) (f.rawAt (512 * n + j)) := by
  have hk : data.length ≠ 0 := fun h => hd (List.eq_nil_of_length_eq_zero h)
  unfold OsFile.landWrite
  rw [if_neg hk, List.take_length]
  simp only [OsFile.change, Nat.min_eq_left hoff, hn, if_true]
  have hl : ({ vers := (f.secs n).vers ++ [secOf (f.written off data) n], dirty := true } :
      Sector).last = secOf (f.written off data) n := by simp [Sector.last]
  rw [hl]
  have h1 := secOf_getD (f.written off data) (512 * n + j)
  rw [(divmod_sec n j hj).1, (divmod_sec n j hj).2] at h1
  simp only [secByte]; rw [h1]
  unfold wByte
  split
  · rename_i hin; exact written_in f off data _ hd hin.1 hin.2
  · rename_i hout; exact (written_out f off data _ hd hb (by omega)).1

/-! ## The crash lemma -/

section seen
variable {Q : OsState → OsState → Prop}

/-- **A crash leaves a sector whose versions are known whole** (see the file header). -/
theorem crashSeen_sec (hQ : ∀ st st', Q st st' → NoTearCrash st st') {i : Ino} {m : OsMeta}
    {rs : List (Nat × DFrac × List (w8 × Bool))} {ts : List (Nat × TokInfo)} {f' : OsFile}
    (h : CrashSeenR Q i m rs ts (some f')) {ns : List Nat} (hvk : m.vk = some ns)
    (hts : (ts = [] ∧ ∀ b < m.size, ∃ r ∈ rs, r.1 ≤ b ∧ b < r.1 + r.2.2.length) ∨
      ∃ t ti, ts = [(t, ti)] ∧ ti.q = 1 ∧ ti.c.ino = i ∧
        ((∃ off data, ti.c.kind = .write off data ∧ inPage off data.length ∧ off ≤ m.size) ∨
         ∃ sz, ti.c.kind = .truncate sz ∧ m.size ≤ sz))
    (n : Nat) (hn : 512 * n + 512 ≤ m.size) :
    (∀ j < 512, ∀ d, m.dur[512 * n + j]? = some (some d) → secByte (f'.secs n).last j = d) ∨
    (∀ j < 512, ∀ y, ByteSeen m rs ts (512 * n + j) y → secByte (f'.secs n).last j = y) ∨
    (∃ t ti off data, ts = [(t, ti)] ∧ ti.c.kind = .write off data ∧
      ∀ j < 512, ∀ y, ByteSeen m rs ts (512 * n + j) y →
        secByte (f'.secs n).last j = wByte off data (512 * n + j) y) := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQst, hfo, hm, hrs, hts', hoth, hwf⟩ := h
  obtain ⟨f, hf, hmo⟩ := hcoh.meta_some i m hm
  have hfile : st.file i = some f := hf
  have hsz : m.size = f.size := hmo.size
  have hsti : st.size i = f.size := by simp [OsState.size, hfile]
  -- the crashed file is a crash of `f`
  obtain ⟨-, -, -, -, -, -, hfiles⟩ := hcr
  have hcf : CrashFile st i f f' := by
    by_cases hN : Named st'.fs.treeDur i
    · obtain ⟨f1, f'', hf1, hc, hf''⟩ := (hfiles i).1 hN
      rw [hf] at hf1; cases hf1; rw [hfo] at hf''; cases hf''; exact hc
    · rw [(hfiles i).2 hN] at hfo; cases hfo
  -- the versions of sector `n`: one or two
  have hlen : (f.secs n).vers.length ≤ 2 := by
    have := hmo.vk ns hvk n; split at this <;> omega
  have hne : (f.secs n).vers ≠ [] := hwf.vers i f n hfile
  obtain ⟨w, hw⟩ : ∃ w, (f.secs n).vers.head? = some w := by
    cases hv : (f.secs n).vers with
    | nil => exact absurd hv hne
    | cons a _ => exact ⟨a, rfl⟩
  -- the durable version's bytes, and the page cache's
  have hdur : ∀ j < 512, ∀ d, m.dur[512 * n + j]? = some (some d) → secByte w j = d := by
    intro j hj d hd
    have := hmo.dur (512 * n + j) d hd w
    rw [(divmod_sec n j hj).1, (divmod_sec n j hj).2] at this
    exact this hw
  have hseen : ∀ j < 512, ∀ y, ByteSeen m rs ts (512 * n + j) y →
      f.contents[512 * n + j]? = some y := by
    intro j hj y hy
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
      have hbf : 512 * n + j < f.size := by omega
      rw [← hay, ← hav, show min off m.size + 1 * (512 * n + j - min off m.size) = 512 * n + j by
        omega, List.getD_eq_getElem?_getD, contents_getElem?, if_pos hbf]
      rfl
  have hcur : ∀ j < 512, ∀ y, ByteSeen m rs ts (512 * n + j) y →
      secByte (f.secs n).last j = y := fun j hj y hy =>
    last_byte f n j hj (by omega) y (hseen j hj y hy)
  obtain ⟨sz, vs, -, hcand, rfl⟩ := hcf
  have hV : ((OsFile.ofDisk vs sz).secs n).last = vs n := by simp [OsFile.ofDisk, Sector.last]
  rw [hV]
  -- a version of the sector: the durable one or the page cache's
  have hver : vs n ∈ (f.secs n).vers →
      (∀ j < 512, ∀ d, m.dur[512 * n + j]? = some (some d) → secByte (vs n) j = d) ∨
      (∀ j < 512, ∀ y, ByteSeen m rs ts (512 * n + j) y → secByte (vs n) j = y) := by
    intro hv
    rcases mem_le_two hlen hv with h1 | h1
    · rw [hw] at h1; cases h1; exact .inl hdur
    · right
      have : (f.secs n).last = vs n := by simp [Sector.last, h1]
      rw [← this]; exact hcur
  -- the changes in flight on the file: the client's, and empty writes
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
  rcases hts with ⟨rfl, hcov⟩ | ⟨t, ti, rfl, hq, hino, hkind⟩
  · -- no change of the client's: every change in flight is an empty write, and lands as nothing
    have hempty : ∀ k ∈ changesOn st i, KeepsSec f.size n k := by
      intro k hk
      obtain ⟨t, c, hc, hci, rfl⟩ := hchg k hk
      obtain ⟨ti, hti, rfl⟩ := htok t c hc
      rcases hoth t ti hti hci with hx | ⟨hq, hav⟩
      · cases hx
      · cases hkd : ti.c.kind with
        | truncate sz =>
          exact absurd (hcoh.tok_q t ti hti (by simp [Reaches, hkd])) hq
        | write off data =>
          simp only [KeepsSec]
          left
          have hnr : ¬ Reaches st ti.c := fun hr => hq (hcoh.tok_q t ti hti hr)
          simp only [Reaches, hkd, hci, hsti, Nat.not_lt] at hnr
          apply List.eq_nil_of_length_eq_zero
          apply Classical.byContradiction; intro hl
          obtain ⟨r, hr, h1, h2⟩ := hcov off (by omega)
          apply hav r hr (off - r.1) (by omega)
          simp only [affRange, affLo, affHi, hkd, hci, hsti, List.mem_range'_1]
          omega
    rcases hcand n with hv | ⟨ks, g, hp, hl, hv⟩
    · rcases hver hv with h1 | h1
      · exact .inl h1
      · exact .inr (.inl h1)
    · obtain ⟨hg, -⟩ := landed_keepsSec (s0 := f.size) (n := n) (by omega) hl (Nat.le_refl _)
        (fun k hk => hempty k (hp.mem_iff.1 hk))
      rw [hv, hg]
      exact .inr (.inl hcur)
  · -- the client's change, the only one in flight on the file
    have hti := hts' _ List.mem_cons_self
    have hct : st.proc.inflight !! t = some ti.c := by
      have := hcoh.toks t; rw [hti] at this; exact this.symm
    have hone : ∀ k ∈ changesOn st i, k = ti.c.kind := by
      intro k hk
      obtain ⟨t', c, hc, hci, rfl⟩ := hchg k hk
      by_cases he : t' = t
      · subst he; rw [hct] at hc; cases hc; rfl
      · exact absurd hci (by rw [← hino]; exact hcoh.tok_alone t ti hti hq t' c he hc)
    rcases hkind with ⟨off, data, hkd, hpg, hoff⟩ | ⟨sz, hkd, hgrow⟩
    · -- an in-page write: a sector it hits by `NoTearCrash`, any other untouched
      have hd : data ≠ [] := fun h => by
        have := hpg.1; rw [h] at this; exact absurd this (by decide)
      by_cases hhit : secHits off (off + data.length) n = true
      · have hci : st.proc.inflight !! t = some ⟨i, .write off data⟩ := by
          rw [hct, show ti.c = ⟨i, .write off data⟩ by rw [← hino, ← hkd]]
        rcases hQ st st' hQst t i off data hci hpg f _ hf hfo n
          (by rw [Nat.min_eq_left (by omega : off ≤ f.size)]; exact hhit) with h1 | h1
        · have hV' : ((OsFile.ofDisk vs sz).secs n).last ∈ (f.secs n).vers := h1
          rw [hV] at hV'
          rcases hver hV' with h2 | h2
          · exact .inl h2
          · exact .inr (.inl h2)
        · right; right
          refine ⟨t, ti, off, data, rfl, hkd, fun j hj y hy => ?_⟩
          have h1' : vs n = ((f.landWrite off data data.length).secs n).last := by rw [← hV]; exact h1
          rw [h1', landWrite_last f off data hd (by omega) n hhit j hj (by omega)]
          have := hseen j hj y hy
          rw [contents_getElem?, if_pos (by omega), Option.some.injEq] at this
          rw [this]
      · have hK : ∀ k ∈ changesOn st i, KeepsSec f.size n k := by
          intro k hk
          rw [hone k hk, hkd]
          exact .inr ⟨by omega, by simpa using hhit⟩
        rcases hcand n with hv | ⟨ks, g, hp, hl, hv⟩
        · rcases hver hv with h1 | h1
          · exact .inl h1
          · exact .inr (.inl h1)
        · obtain ⟨hg, -⟩ := landed_keepsSec (s0 := f.size) (n := n) (by omega) hl (Nat.le_refl _)
            (fun k hk => hK k (hp.mem_iff.1 hk))
          rw [hv, hg]
          exact .inr (.inl hcur)
    · -- a growing truncate: the sectors below the size untouched
      have hK : ∀ k ∈ changesOn st i, KeepsSec f.size n k := by
        intro k hk
        rw [hone k hk, hkd]
        show f.size ≤ sz; omega
      rcases hcand n with hv | ⟨ks, g, hp, hl, hv⟩
      · rcases hver hv with h1 | h1
        · exact .inl h1
        · exact .inr (.inl h1)
      · obtain ⟨hg, -⟩ := landed_keepsSec (s0 := f.size) (n := n) (by omega) hl (Nat.le_refl _)
          (fun k hk => hK k (hp.mem_iff.1 hk))
        rw [hv, hg]
        exact .inr (.inl hcur)

end seen

end Fs
end Perennial

end
