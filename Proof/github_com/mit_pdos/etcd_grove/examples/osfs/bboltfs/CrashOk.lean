/- Lean-first (no Rocq counterpart). minibolt's crash obligations on Fs v2, without P1: `FileOkS
NoTearCrash Good i s` for a state `s` of the database file (`Proof/os/CrashSt.lean`), reduced to a
statement on images (`crashImg`).

A meta slot (64 bytes at offset 16 of page 0 or 1) lies inside one sector (sector `8 i`). While the
file's `OsMeta` knows which sectors have at most two versions since the last successful sync
(`OsMeta.vk`, kept by the writes minibolt makes between syncs, each sector written at most once),
a crash leaves that sector whole (`crashSeen_sec`): as its durable version (the bytes `m.dur`
knows), as the page cache's (the bytes the client holds), or, under the no-tear assumption
(`NoTearCrash`, `GooseLang/Ext/Fs/NoTear.lean`), as the client's in-page write in flight landed
whole. This replaces v1's P1 (no checksum collision on a torn meta): a slot is never a mix, so
nothing about checksums is assumed.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.CrashGood
public import Proof.os.CrashSt
public import GooseLang.Ext.Fs.CrashSec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Fs github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

/-- The meta slot of page `i` of the bytes `l`: 64 bytes at offset 16. -/
def metaSlot (l : List w8) (i : Nat) : List w8 := ((l.drop (4096 * i)).drop 16).take 64

/-- The client's change in flight is one `crashSeen_sec` covers: a write in flight lies in one
page and starts inside the file. -/
def BusyOk (s : CSt) : Prop :=
  match s.busy with
  | .write _ off data => inPage off data.length ∧ off ≤ s.m.size
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

/-- **The obligation of a state, from its images** (see the file header): every crash of the
state `s` is `Good` if every image `crashImg` allows is good. -/
theorem fileOkS_crashImg {i : Ino} (s : CSt) (hwf : s.Wf) (hbz : BusyOk s)
    (H : ∀ img, crashImg s img → goodImg img) : FileOkS NoTearCrash Good i s := by
  intro f hfc hseen
  show goodImg f.contents
  obtain ⟨hlo, hhi, hcl⟩ := hfc f rfl
  have hl : s.bs.length = s.m.size := hwf.1
  apply H
  refine ⟨by rw [contents_length]; exact hlo, by rw [contents_length]; exact hhi,
    fun k x hk hc ht => ?_, fun ⟨ns, hns⟩ j hj hsz himg => ?_⟩
  · obtain ⟨hkl, rfl⟩ := List.getElem?_eq_some_iff.1 hk
    obtain ⟨r, hr, rfl⟩ := s.runs_getElem k hkl
    have := hcl _ hr 0 s.bs[k] (by simp [ht]) hc
    simpa using this.1
  -- a meta slot: its sector `8 j`, whole
  have hvk : s.vmeta.vk = some ns := by rw [CSt.vmeta_vk]; exact hns
  have hts : (s.toks i = [] ∧ ∀ b < s.vmeta.size, ∃ r ∈ s.runs, r.1 ≤ b ∧ b < r.1 + r.2.2.length) ∨
      ∃ t ti, s.toks i = [(t, ti)] ∧ ti.q = 1 ∧ ti.c.ino = i ∧
        ((∃ off data, ti.c.kind = .write off data ∧ inPage off data.length ∧ off ≤ s.vmeta.size) ∨
         ∃ sz, ti.c.kind = .truncate sz ∧ s.vmeta.size ≤ sz) := by
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
        by simp [CSt.toks, hb], rfl, rfl, .inl ⟨off, data, rfl, hbz.1, by rw [CSt.vmeta_size]; exact hbz.2⟩⟩
    · rw [hb] at hw2
      right
      exact ⟨t, ⟨⟨i, .truncate sz⟩, 1, [], ftMeta s.m sz, []⟩, by simp [CSt.toks, hb], rfl, rfl, .inr ⟨sz, rfl, by rw [CSt.vmeta_size]; exact hw2⟩⟩
  have hn : 512 * (8 * j) + 512 ≤ s.vmeta.size := by rw [CSt.vmeta_size]; omega
  have hsec := crashSeen_sec (fun _ _ h => h) hseen hvk hts (8 * j) hn
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
    have := h1 (16 + k) (by omega) d (by rw [CSt.vmeta_dur, he]; exact hd)
    rw [this]
  · right; left
    intro k hk
    rw [hbyte k hk]
    have := h1 (16 + k) (by omega) _ (by rw [he]; exact CSt.byteSeen s i hl _ (by omega))
    rw [this]
  · right; right
    have hb : s.busy = .write t off data := by
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
    refine ⟨t, off, data, hb, fun k hk => ?_⟩
    rw [hbyte k hk]
    have := h1 (16 + k) (by omega) _ (by rw [he]; exact CSt.byteSeen s i hl _ (by omega))
    rw [this, he]

end pure

end osfs_bboltfs
end EtcdGrove
end Perennial

end
