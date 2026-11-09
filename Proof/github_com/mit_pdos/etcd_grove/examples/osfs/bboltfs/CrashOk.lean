/- Lean-first (no Rocq counterpart). minibolt's crash obligations on Fs v2, without P1: `FileOkS
NoTearCrash Good i s` for a state `s` of the database file (`Proof/os/CrashSt.lean`), reduced to a
statement on images (`crashImg`).

A meta slot (64 bytes at offset 16 of page 0 or 1) lies inside one sector (sector `8 i`). While the
file's `OsMeta` knows which sectors have at most two versions since the last successful sync
(`OsMeta.vk`, kept by the writes minibolt makes between syncs, each sector written at most once),
a crash leaves that sector whole (`crashSeen_sec`): as its durable version (the bytes `m.dur`
knows), as the page cache's (the bytes the client holds), or, under the no-tear assumption
(`NoTearCrash`, `GooseLang/Ext/Fs/NoTear.lean`), as the client's write in flight landed over it
(a page cut of a write covers a sector whole or misses it). This replaces v1's P1 (no checksum collision on a torn meta): a slot is never a mix, so
nothing about checksums is assumed.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.CrashGood
public import Proof.os.CrashSt
public import GooseLang.Ext.Fs.CrashSecAny

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Fs github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

/-- The meta slot of page `i` of the bytes `l`: 64 bytes at offset 16. -/
def metaSlot (l : List w8) (i : Nat) : List w8 := ((l.drop (4096 * i)).drop 16).take 64

/-- The client's change in flight is one `crashSeen_sec` covers: a write in flight starts inside
the file. -/
def BusyOk (s : CSt) : Prop :=
  match s.busy with
  | .write _ off _ => off ≤ s.m.size
  | _ => True

/-- What a crash may leave of the database file in the state `s` (`img` its bytes): within the
size bounds of `s`'s `OsMeta` (the token's while a change is in flight), with every clean byte the
client holds (not taken by its write), and, while the `OsMeta` knows the versions of its sectors,
each meta slot inside the file whole: the bytes `m.dur` knows there, the client's, or the client's
with its write in flight over them. -/
def crashImg (s : CSt) (img : List w8) : Prop :=
  s.vmeta.lo ≤ img.length ∧ img.length ≤ s.vmeta.hi ∧
  (∀ k x, s.bs[k]? = some x → x.2 = true → s.taken k = false → img[k]? = some x.1) ∧
  ((∃ ns, s.m.vk = some ns) → ∀ i < 2, 4096 * i + 512 ≤ s.m.size → 4096 * i + 80 ≤ img.length →
    (∀ k < 64, ∀ d, s.m.dur[4096 * i + 16 + k]? = some (some d) → img[4096 * i + 16 + k]? = some d) ∨
    (∀ k < 64, img[4096 * i + 16 + k]? = some (s.bs.getD (4096 * i + 16 + k) (0, false)).1) ∨
    (∃ t off data, s.busy = .write t off data ∧ ∀ k < 64,
      img[4096 * i + 16 + k]? =
        some (wByte off data (4096 * i + 16 + k) (s.bs.getD (4096 * i + 16 + k) (0, false)).1)))

/-- Byte `b` of the state's bytes. -/
def bsB (s : CSt) (b : Nat) : w8 := (s.bs.getD b (0, false)).1

/-- Byte `b` after `k` bytes of the write of `data` at `off` landed: the write's inside them, the
state's below its size outside, zero past it. -/
def landB (s : CSt) (off : Nat) (data : List w8) (k b : Nat) : w8 :=
  if off ≤ b ∧ b < off + k then data.getD (b - off) 0 else if b < s.m.size then bsB s b else 0

/-- Byte `b` after a growing truncate landed: the state's below its size, zero past it. -/
def truncB (s : CSt) (b : Nat) : w8 := if b < s.m.size then bsB s b else 0

/-- Sector `n` is the first of its page, known fresh by `m`, and under the size `sz`. -/
abbrev FreshCovS (s : CSt) (n sz : Nat) : Prop := FreshCov s.m n sz

/-- What a crash to the size `sz` may leave in meta slot `i` (its bytes `L`, as sector `8 i` holds
them) of the state `s` whose `OsMeta` knows the versions (`crashSeen_secAny`): the durable version
unless the sector is known fresh and covered; the page cache's, of a sector with two versions
(its bytes below the size); the write in flight landed in part; the truncate in flight landed. -/
def slotCand (s : CSt) (sz i : Nat) (L : List w8) : Prop :=
  L.length = 64 ∧
  ((¬ FreshCovS s (8 * i) sz ∧
      ∀ k < 64, ∀ d, s.m.DurAt (4096 * i + 16 + k) d → L[k]? = some d) ∨
   ((∃ ns, s.m.vk = some ns ∧ 8 * i ∈ ns) ∧
      ∀ k < 64, 4096 * i + 16 + k < s.m.size → L[k]? = some (bsB s (4096 * i + 16 + k))) ∨
   (∃ t off data k', s.busy = .write t off data ∧ 0 < k' ∧ k' ≤ data.length ∧
      secHits (min off s.m.size) (off + k') (8 * i) = true ∧
      (PageCut off data.length k' ∨ FreshCovS s (8 * i) sz) ∧
      ∀ k < 64, L[k]? = some (landB s off data k' (4096 * i + 16 + k))) ∨
   ((∃ t sz', s.busy = .trunc t sz') ∧
      ∀ k < 64, L[k]? = some (truncB s (4096 * i + 16 + k))))

/-- What a crash may leave of the database file of the state `s` past `crashImg`: no
`FALLOC_FL_KEEP_SIZE` blocks if the `OsMeta` knows fresh sectors, and each meta slot as
`slotCand` says, while the versions are known. -/
def crashRaw (s : CSt) (f : OsFile) : Prop :=
  ((∃ p, s.m.fr = some p) → f.kept = false) ∧
  ((∃ ns, s.m.vk = some ns) → ∀ i < 2, slotCand s f.size i (rawSlot f i))

section pure
variable [GooseExts]

/-- A byte of a state's runs is one of its bytes not taken. -/
theorem CSt.runs_byte (s : CSt) : ∀ r ∈ s.runs, ∀ k x, r.2.2[k]? = some x →
    s.bs[r.1 + k]? = some x ∧ s.taken (r.1 + k) = false := by
  intro r hr k x hx
  simp only [CSt.runs, List.mem_map] at hr
  obtain ⟨⟨y, j⟩, hy, rfl⟩ := hr
  have hyj : s.bs[j]? = some y := List.mem_zipIdx_iff_getElem?.1 hy
  simp only at hx ⊢
  by_cases ht : s.taken j = true
  · simp [ht] at hx
  · simp only [ht, Bool.false_eq_true, if_false] at hx
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx
      exact ⟨by simpa using hyj, by simpa using ht⟩
    | succ k => simp at hx

/-- Every byte of a state below its size is one the client holds (`ByteSeen`): in its runs, or
saved by its write in flight. -/
theorem CSt.byteSeen (s : CSt) (i : Ino) (hl : s.bs.length = s.m.size) (b : Nat) (hb : b < s.m.size) :
    ByteSeen s.vmeta s.runs (s.toks i) b (s.bs.getD b (0, false)).1 := by
  have hbl : b < s.bs.length := by omega
  by_cases ht : s.taken b = true
  · right
    unfold CSt.taken at ht
    split at ht
    · rename_i t off data hbz
      simp only [decide_eq_true_eq] at ht
      refine ⟨(t, ⟨⟨i, .write off data⟩, 1, (cfRange s.m s.bs off data.length).map Prod.fst,
        pwMeta s.m off data.length, (cfRange s.m s.bs off data.length).map Prod.snd⟩),
        by simp [CSt.toks, hbz], off, data, rfl, ?_, ?_⟩
      · simp only [CSt.vmeta, hbz, pwMeta]; simp only [cfLo] at ht; omega
      · simp only [CSt.vmeta, hbz, pwMeta, cfRange, cfLo, cfHi] at ht ⊢
        simp only [List.getElem?_map, List.getElem?_take, List.getElem?_drop]
        rw [if_pos (by omega), show min off s.m.size + (b - min off s.m.size) = b by omega,
          List.getElem?_eq_getElem hbl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl]
        rfl
    · cases ht
  · left
    obtain ⟨r, hr, rfl⟩ := s.runs_getElem b hbl
    refine ⟨_, hr, 0, s.bs[b], ?_, rfl, ?_⟩
    · simp [ht]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl]; rfl

theorem CSt.vmeta_size (s : CSt) : s.vmeta.size = s.m.size := by
  unfold CSt.vmeta; split <;> rfl

theorem CSt.vmeta_vk (s : CSt) : s.vmeta.vk = s.m.vk := by
  unfold CSt.vmeta; split <;> rfl

theorem CSt.vmeta_dur (s : CSt) : s.vmeta.dur = s.m.dur := by
  unfold CSt.vmeta; split <;> rfl

theorem CSt.vmeta_fr (s : CSt) : s.vmeta.fr = s.m.fr := by
  unfold CSt.vmeta; split <;> rfl

theorem CSt.vmeta_dz (s : CSt) : s.vmeta.dz = s.m.dz := by
  unfold CSt.vmeta; split <;> rfl

theorem CSt.vmeta_lo (s : CSt) : s.vmeta.lo = s.m.lo := by
  unfold CSt.vmeta; split <;> rfl

theorem CSt.vmeta_durAt (s : CSt) (b : Nat) (d : w8) : s.vmeta.DurAt b d ↔ s.m.DurAt b d := by
  unfold OsMeta.DurAt; rw [CSt.vmeta_dur, CSt.vmeta_dz]

theorem CSt.freshCov_vmeta (s : CSt) (n sz : Nat) : FreshCov s.vmeta n sz ↔ FreshCov s.m n sz := by
  unfold FreshCov; rw [CSt.vmeta_fr]

/-- The change in flight of a state, as `crashSeen_sec` and `crashSeen_secAny` take it. -/
theorem CSt.toksShape {i : Ino} (s : CSt) (hwf : s.Wf) (hbz : BusyOk s) :
    (s.toks i = [] ∧ ∀ b < s.vmeta.size, ∃ r ∈ s.runs, r.1 ≤ b ∧ b < r.1 + r.2.2.length) ∨
      ∃ t ti, s.toks i = [(t, ti)] ∧ ti.q = 1 ∧ ti.c.ino = i ∧
        ((∃ off data, ti.c.kind = .write off data ∧ off ≤ s.vmeta.size) ∨
         ∃ sz, ti.c.kind = .truncate sz ∧ s.vmeta.size ≤ sz) := by
  have hl : s.bs.length = s.m.size := hwf.1
  unfold BusyOk at hbz
  have hw2 := hwf.2.2.2
  rcases hb : s.busy with _ | ⟨t, off, data⟩ | ⟨t, sz⟩
  · left
    refine ⟨by simp [CSt.toks, hb], fun b hb' => ?_⟩
    rw [CSt.vmeta_size] at hb'
    obtain ⟨r, hr, rfl⟩ := s.runs_getElem b (by omega)
    exact ⟨_, hr, Nat.le_refl _, by simp [CSt.taken, hb]⟩
  · rw [hb] at hbz
    right
    exact ⟨t, ⟨⟨i, .write off data⟩, 1, (cfRange s.m s.bs off data.length).map Prod.fst,
      pwMeta s.m off data.length, (cfRange s.m s.bs off data.length).map Prod.snd⟩,
      by simp [CSt.toks, hb], rfl, rfl,
      .inl ⟨off, data, rfl, by rw [CSt.vmeta_size]; exact hbz⟩⟩
  · rw [hb] at hw2
    right
    exact ⟨t, ⟨⟨i, .truncate sz⟩, 1, [], ftMeta s.m sz, []⟩, by simp [CSt.toks, hb], rfl, rfl,
      .inr ⟨sz, rfl, by rw [CSt.vmeta_size]; exact hw2⟩⟩

/-- The client's token of a state's write in flight is its `busy` write. -/
theorem CSt.toks_write {i : Ino} (s : CSt) {t : Nat} {ti : TokInfo} {off : Nat} {data : List w8}
    (htk : s.toks i = [(t, ti)]) (hkd : ti.c.kind = .write off data) :
    s.busy = .write t off data := by
  unfold CSt.toks at htk
  split at htk
  · cases htk
  · rename_i t' off' data' hb'
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at htk
    obtain ⟨rfl, rfl⟩ := htk
    simp only at hkd; cases hkd; exact hb'
  · rename_i t' sz hb'
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at htk
    obtain ⟨rfl, rfl⟩ := htk
    simp only at hkd; cases hkd

/-- The client's token of a state's truncate in flight is its `busy` truncate. -/
theorem CSt.toks_trunc {i : Ino} (s : CSt) {t : Nat} {ti : TokInfo} {sz : Nat}
    (htk : s.toks i = [(t, ti)]) (hkd : ti.c.kind = .truncate sz) :
    ∃ t' sz', s.busy = .trunc t' sz' := by
  unfold CSt.toks at htk
  split at htk
  · cases htk
  · rename_i t' off' data' hb'
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at htk
    obtain ⟨rfl, rfl⟩ := htk
    simp only at hkd; cases hkd
  · rename_i t' sz' hb'
    exact ⟨t', sz', hb'⟩

/-- What a crash of the state `s` leaves, as `crashImg` says it. -/
theorem crashImg_seen {i : Ino} (s : CSt) (hwf : s.Wf) (hbz : BusyOk s) (f : OsFile)
    (hfc : FileCrashedR s.vmeta s.runs (some f))
    (hseen : CrashSeenR NoTearCrash i s.vmeta s.runs (s.toks i) (some f)) :
    crashImg s f.contents := by
  obtain ⟨hlo, hhi, hcl⟩ := hfc f rfl
  have hl : s.bs.length = s.m.size := hwf.1
  refine ⟨by rw [contents_length]; exact hlo, by rw [contents_length]; exact hhi,
    fun k x hk hc ht => ?_, fun ⟨ns, hns⟩ j hj hsz himg => ?_⟩
  · obtain ⟨hkl, rfl⟩ := List.getElem?_eq_some_iff.1 hk
    obtain ⟨r, hr, rfl⟩ := s.runs_getElem k hkl
    have := hcl _ hr 0 s.bs[k] (by simp [ht]) hc
    simpa using this.1
  -- a meta slot: its sector `8 j`, whole
  have hvk : s.vmeta.vk = some ns := by rw [CSt.vmeta_vk]; exact hns
  have hn : 512 * (8 * j) + 512 ≤ s.vmeta.size := by rw [CSt.vmeta_size]; omega
  have hsec := crashSeen_sec (fun _ _ h => h) hseen hvk (8 * j) hn (CSt.toksShape s hwf hbz)
  -- a byte of the slot, from its sector
  have hbyte : ∀ k < 64, f.contents[4096 * j + 16 + k]? =
      some (secByte (f.secs (8 * j)).last (16 + k)) := by
    intro k hk
    rw [contents_getElem?, if_pos (by rw [contents_length] at himg; omega), rawAt_def,
      show (4096 * j + 16 + k) / 512 = 8 * j by omega, show (4096 * j + 16 + k) % 512 = 16 + k by omega]
  have he : ∀ k, 512 * (8 * j) + (16 + k) = 4096 * j + 16 + k := fun k => by omega
  rcases hsec with h1 | h1 | ⟨t, ti, off, data, htk, hkd, h1⟩
  · left
    intro k hk d hd
    rw [hbyte k hk]
    have := h1 (16 + k) (by omega) d (.inl (by rw [CSt.vmeta_dur, he]; exact hd))
    rw [this]
  · right; left
    intro k hk
    rw [hbyte k hk]
    have := h1 (16 + k) (by omega) _ (by rw [he]; exact CSt.byteSeen s i hl _ (by omega))
    rw [this]
  · right; right
    refine ⟨t, off, data, CSt.toks_write s htk hkd, fun k hk => ?_⟩
    rw [hbyte k hk]
    have := h1 (16 + k) (by omega) _ (by rw [he]; exact CSt.byteSeen s i hl _ (by omega))
    rw [this, he]

/-- What a crash of the state `s` leaves, as `crashRaw` says it. -/
theorem crashRaw_seen {i : Ino} (s : CSt) (hwf : s.Wf) (hbz : BusyOk s) (f : OsFile)
    (hseen : CrashSeenR NoTearCrash i s.vmeta s.runs (s.toks i) (some f)) :
    crashRaw s f := by
  have hl : s.bs.length = s.m.size := hwf.1
  refine ⟨fun ⟨p, hp⟩ => crashSeen_kept hseen (p := p) (by rw [CSt.vmeta_fr]; exact hp),
    fun ⟨ns, hns⟩ j hj => ?_⟩
  have hvk : s.vmeta.vk = some ns := by rw [CSt.vmeta_vk]; exact hns
  have he : ∀ k, 512 * (8 * j) + (16 + k) = 4096 * j + 16 + k := fun k => by omega
  have hraw : ∀ k < 64, (rawSlot f j)[k]? = some (secByte (f.secs (8 * j)).last (16 + k)) := by
    intro k hk
    simp only [rawSlot, List.getElem?_map, List.getElem?_range hk, Option.map_some]
  have hseenB : ∀ b < s.m.size, ByteSeen s.vmeta s.runs (s.toks i) b (bsB s b) :=
    fun b hb => CSt.byteSeen s i hl b hb
  refine ⟨by simp [rawSlot], ?_⟩
  rcases crashSeen_secAny (fun _ _ h => h) hseen hvk (8 * j) (CSt.toksShape s hwf hbz) with
    ⟨hfc, h1⟩ | ⟨hn, h1⟩ | ⟨t, ti, off, data, k', htk, hkd, hoff, hk0, hkl, hhit, hcut, h1⟩ |
      ⟨t, ti, sz, htk, hkd, h1⟩
  · left
    refine ⟨fun h => hfc ((CSt.freshCov_vmeta s _ _).2 h), fun k hk d hd => ?_⟩
    rw [hraw k hk, h1 (16 + k) (by omega) d (by rw [he, CSt.vmeta_durAt]; exact hd)]
  · right; left
    refine ⟨⟨ns, hns, hn⟩, fun k hk hb => ?_⟩
    rw [hraw k hk, h1 (16 + k) (by omega) (by rw [CSt.vmeta_size, he]; exact hb) _
      (by rw [he]; exact hseenB _ hb)]
  · right; right; left
    rw [CSt.vmeta_size] at hoff hhit
    refine ⟨t, off, data, k', CSt.toks_write s htk hkd, hk0, hkl, hhit,
      hcut.imp_right (CSt.freshCov_vmeta s _ _).1, fun k hk => ?_⟩
    rw [hraw k hk]
    obtain ⟨hin, hout, hpast⟩ := h1 (16 + k) (by omega)
    rw [he] at hin hout hpast
    unfold landB
    split
    · rename_i hc; rw [hin hc.1 hc.2]
    · split
      · rename_i hc hb
        rw [hout (by omega) (by rw [CSt.vmeta_size]; exact hb) _ (hseenB _ hb)]
      · rename_i hc hb
        rw [hpast (by omega) (by rw [CSt.vmeta_size]; omega)]
  · right; right; right
    refine ⟨CSt.toks_trunc s htk hkd, fun k hk => ?_⟩
    rw [hraw k hk]
    obtain ⟨hin, hpast⟩ := h1 (16 + k) (by omega)
    rw [he] at hin hpast
    unfold truncB
    split
    · rename_i hb; rw [hin (by rw [CSt.vmeta_size]; exact hb) _ (hseenB _ hb)]
    · rename_i hb; rw [hpast (by rw [CSt.vmeta_size]; omega)]

/-- **The obligation of a state, from its images and slots** (see the file header): every crash
of the state `s` is `Good` if every image `crashImg` and `crashRaw` allow is. -/
theorem fileOkS_crashRaw {i : Ino} (s : CSt) (hwf : s.Wf) (hbz : BusyOk s)
    (H : ∀ f, crashImg s f.contents → crashRaw s f → Good (some f)) :
    FileOkS NoTearCrash Good i s := fun f hfc hseen =>
  H f (crashImg_seen s hwf hbz f hfc hseen) (crashRaw_seen s hwf hbz f hseen)

/-- **The obligation of a state of at least four pages since the last sync, from its images**:
every crash of `s` is `Good` if every image `crashImg` allows is good. -/
theorem fileOkS_crashImg {i : Ino} (s : CSt) (hwf : s.Wf) (hbz : BusyOk s)
    (hlo : 4 * 4096 ≤ s.m.lo)
    (H : ∀ img, crashImg s img → goodImg img) : FileOkS NoTearCrash Good i s :=
  fileOkS_crashRaw s hwf hbz fun f hI _ => ⟨H _ hI, fun hs => by
    have := hI.1; rw [CSt.vmeta_lo, contents_length] at this; omega⟩

end pure

end osfs_bboltfs
end EtcdGrove
end Perennial

end
