/- Lean-first (no Rocq counterpart). minibolt's crash obligations on images (Fs v2): for the
states the database file passes through during `init` and `commit`, every image a crash may leave
(`crashImg`, `CrashOk.lean`) is `goodImg`. Ported from v1's (`old/osfs-v1/.../CrashImg.lean`), with
P1's slot cases replaced by `crashImg`'s (`crashImg_slot`).

**Slots.** While the file's `OsMeta` knows the versions of its sectors (`OsMeta.vk`), a meta slot of
an image is whole: the bytes `m.dur` knows there (`durSlot m i P`: all of them, a slot whose meta
satisfies `P` if valid), the page cache's (`cacheSlot bs i P`), or the client's write in flight
over the page cache's (`writeSlot`); `crashImg_slot` concludes that a valid slot of the image
satisfies `P`. No byte of a slot is ever torn, and nothing about checksums is assumed.

**commit** (`commitClean`, `commitMetaSt`): while the metas and the current root page are clean,
an image has them (`commit_clean_img`); while the meta slot `(T+1) % 2` is written, it is the old
slot or the new meta, whose root page is synced, and the current meta is in slot `T % 2`
(`curInSlot`), untouched: `commitMeta_good`.

**init** (`goodImg_noValid`, `goodImg_init`): every slot the image may take is invalid or, once
the metas are written, `init`'s meta.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.CrashOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.InitLayout
public import Proof.os.CrashWReachNoTear

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Fs
open github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
open github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs renaming initMeta → bInitMeta

section pure
variable [GooseExts]

/-! ## Slots -/

theorem fileMeta_slot (l : List w8) (i : Nat) : fileMeta l i = decode (metaSlot l i) := rfl

theorem metaSlot_length (l : List w8) (i : Nat) :
    (metaSlot l i).length = min 64 (l.length - 4096 * i - 16) := by
  simp only [metaSlot, List.length_take, List.length_drop]

theorem metaSlot_getElem? (l : List w8) (i k : Nat) (hk : k < 64) :
    (metaSlot l i)[k]? = l[4096 * i + 16 + k]? := by
  simp only [metaSlot, List.getElem?_take, if_pos hk, List.getElem?_drop]
  congr 1; omega

theorem metaSlot_ext {a b : List w8} {i : Nat}
    (h : ∀ k < 64, a[4096 * i + 16 + k]? = b[4096 * i + 16 + k]?) : metaSlot a i = metaSlot b i := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 64
  · rw [metaSlot_getElem? _ _ _ hk, metaSlot_getElem? _ _ _ hk]; exact h k hk
  · rw [List.getElem?_eq_none (by rw [metaSlot_length]; omega),
      List.getElem?_eq_none (by rw [metaSlot_length]; omega)]

/-- A slot equal to one an image holds whole is held whole. -/
theorem slot_held {a b : List w8} {i : Nat} (h : metaSlot a i = metaSlot b i)
    (hl : 4096 * i + 80 ≤ a.length) : 4096 * i + 80 ≤ b.length := by
  have e := congrArg List.length h
  rw [metaSlot_length, metaSlot_length] at e
  omega

theorem fileMeta_of_slot {a b : List w8} {i : Nat} (h : metaSlot a i = metaSlot b i) :
    fileMeta a i = fileMeta b i := by
  rw [fileMeta_slot, fileMeta_slot, h]

/-- The zero meta is not valid (its magic is 0). -/
theorem zeroSlot_invalid : ¬ metaValid (decode (List.replicate 64 (0 : w8)) : Meta) := by
  rw [show List.replicate 64 (0 : w8) = zeroBytes 64 from rfl, ← encode_zeroMeta,
    ByteEncoding.decode_encode]
  intro h
  have := congrArg (fun x : w32 => x.toNat) h.1
  simp [zeroMeta] at this

theorem slot_zero_invalid {l : List w8} {i : Nat}
    (h : ∀ k < 64, l[4096 * i + 16 + k]? = some 0) : ¬ metaValid (fileMeta l i) := by
  have : metaSlot l i = List.replicate 64 0 := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 64
    · rw [metaSlot_getElem? _ _ _ hk, h k hk, List.getElem?_replicate, if_pos hk]
    · rw [List.getElem?_eq_none (by rw [metaSlot_length]; omega),
        List.getElem?_eq_none (by simp; omega)]
  rw [fileMeta_slot, this]; exact zeroSlot_invalid


/-- What `m.dur` knows of slot `i`: every byte of it, those of `B`, whose meta satisfies `P` if
valid. -/
def durSlot (m : OsMeta) (i : Nat) (P : Meta → Prop) : Prop :=
  ∃ B : List w8, (∀ k < 64, ∃ b, B[4096 * i + 16 + k]? = some b ∧
      m.dur[4096 * i + 16 + k]? = some (some b)) ∧
    (metaValid (fileMeta B i) → P (fileMeta B i))

/-- The page cache's slot `i` satisfies `P` if valid. -/
def cacheSlot (bs : List (w8 × Bool)) (i : Nat) (P : Meta → Prop) : Prop :=
  metaValid (fileMeta (bs.map Prod.fst) i) → P (fileMeta (bs.map Prod.fst) i)

/-- The slot `i` with the write of `data` at `off` over the page cache's satisfies `P` if valid. -/
def writeSlot (bs : List (w8 × Bool)) (off : Nat) (data : List w8) (i : Nat) (P : Meta → Prop) :
    Prop :=
  ∀ L : List w8, (∀ k < 64, L[4096 * i + 16 + k]? =
      some (wByte off data (4096 * i + 16 + k) (bs.getD (4096 * i + 16 + k) (0, false)).1)) →
    metaValid (fileMeta L i) → P (fileMeta L i)

/-- **A valid slot of a crash image satisfies `P`** if the durable copy, the page cache's and the
write in flight's do, while the versions are known. -/
theorem crashImg_slot {s : CSt} {img : List w8} {i : Nat} {P : Meta → Prop} (h : crashImg s img)
    (hbl : s.bs.length = s.m.size) (hvk : ∃ ns, s.m.vk = some ns) (hi : i < 2)
    (hsz : 4096 * i + 512 ≤ s.m.size) (hl : 4096 * i + 80 ≤ img.length)
    (hd : durSlot s.m i P) (hc : cacheSlot s.bs i P)
    (hw : ∀ t off data, s.busy = .write t off data → writeSlot s.bs off data i P)
    (hv : metaValid (fileMeta img i)) : P (fileMeta img i) := by
  obtain ⟨-, -, -, hs⟩ := h
  rcases hs hvk i hi hsz hl with h1 | h1 | ⟨t, off, data, hb, h1⟩
  · obtain ⟨B, hB, hP⟩ := hd
    have e : metaSlot img i = metaSlot B i := metaSlot_ext fun k hk => by
      obtain ⟨b, h2, h3⟩ := hB k hk
      rw [h1 k hk b h3, h2]
    rw [fileMeta_of_slot e] at hv ⊢; exact hP hv
  · have e : metaSlot img i = metaSlot (s.bs.map Prod.fst) i := metaSlot_ext fun k hk => by
      rw [h1 k hk, List.getElem?_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    rw [fileMeta_of_slot e] at hv ⊢; exact hc hv
  · exact hw t off data hb img h1 hv

/-- A clean byte of the state, not taken by its write in flight, is the image's. -/
theorem crashImg_clean {s : CSt} {img : List w8} (h : crashImg s img) {k : Nat} {b : w8}
    (hk : s.bs[k]? = some (b, true)) (ht : s.taken k = false) : img[k]? = some b :=
  h.2.2.1 k _ hk rfl ht

theorem crashImg_lo {s : CSt} {img : List w8} (h : crashImg s img) : s.m.lo ≤ img.length := by
  have := h.1; unfold CSt.vmeta at this; split at this <;> simpa [pwMeta, ftMeta] using this

/-! ## Good images -/

/-- The bytes `[a, a + n)` of `img` are `bs`'s, all clean there. -/
theorem take_drop_eq {img l : List w8} {a n : Nat}
    (h : ∀ k < n, img[a + k]? = l[a + k]?) (hl : a + n ≤ l.length) :
    (img.drop a).take n = (l.drop a).take n := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take, List.getElem?_drop]
  split
  · exact h k ‹_›
  · rfl

theorem goodImg_noValid {img : List w8} (hl : img.length ≤ 2 ^ 30)
    (h : ∀ i < 2, 4096 * i + 80 ≤ img.length → ¬ metaValid (fileMeta img i)) : goodImg img := by
  refine ⟨hl, ?_⟩
  by_cases h4 : img.length < 4 * 4096
  · exact Or.inl ⟨h4, h⟩
  · refine Or.inr (Or.inl ⟨by omega, ?_, ?_⟩) <;> simp only [imgMetas]
    · rw [fileMeta_take _ _ _ (by omega)]; exact h 0 (by omega) (by omega)
    · rw [fileMeta_take _ _ _ (by omega)]; exact h 1 (by omega) (by omega)

theorem curMeta_take (img : List w8) : curMeta (img.take 8192) = curMeta img := by
  unfold curMeta
  rw [fileMeta_take _ _ 0 (by omega), fileMeta_take _ _ 1 (by omega)]

/-- `curMeta` is a valid meta, if there is one. -/
theorem curMeta_cases (mp : List w8) (h : metaValid (fileMeta mp 0) ∨ metaValid (fileMeta mp 1)) :
    (curMeta mp = fileMeta mp 0 ∧ metaValid (fileMeta mp 0)) ∨
    (curMeta mp = fileMeta mp 1 ∧ metaValid (fileMeta mp 1)) := by
  unfold curMeta
  dsimp only
  split
  · split
    · exact Or.inr ⟨rfl, ‹_›⟩
    · exact Or.inl ⟨rfl, h.resolve_right ‹_›⟩
  · split
    · exact Or.inl ⟨rfl, ‹_›⟩
    · exact Or.inr ⟨rfl, h.resolve_left ‹_›⟩

theorem curMeta_congr {a b : List w8} (h0 : fileMeta a 0 = fileMeta b 0)
    (h1 : fileMeta a 1 = fileMeta b 1) : curMeta a = curMeta b := by
  unfold curMeta; rw [h0, h1]

/-- An image whose current meta `X` is an open database's: valid, its root page committed below
its high water mark, inside the image, and holding what `BootMinibolt` checks. -/
theorem goodImg_cur {img : List w8} {X : Meta} (h16 : 4 * 4096 ≤ img.length)
    (hl : img.length ≤ 2 ^ 30) (hc : curMeta img = X)
    (hv : metaValid (fileMeta img 0) ∨ metaValid (fileMeta img 1))
    (hr : 2 ≤ X.root'.root'.toNat) (hrp : X.root'.root'.toNat < X.pgid'.toNat)
    (hp : (X.pgid'.toNat + 1) * 4096 ≤ 2 ^ 30) (hpi : 4096 * X.pgid'.toNat ≤ img.length)
    (hb : bootOk X.txid'.toNat (pageVal ((img.drop (4096 * X.root'.root'.toNat)).take 4096)))
    (hs : fileMeta img (X.txid'.toNat % 2) = X)
    (ht1 : 1 ≤ X.txid'.toNat) (htp : X.txid'.toNat < X.pgid'.toNat) :
    goodImg img := by
  have hc' : curMeta (imgMetas img) = X := by simp only [imgMetas]; rw [curMeta_take, hc]
  refine ⟨hl, Or.inr (Or.inr ⟨h16, ⟨by simp; omega, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?slot, ⟨?_, ?_⟩⟩)⟩
  case slot =>
    show curMeta (imgMetas img) = fileMeta (imgMetas img) _
    simp only [imgMetas]
    rw [hc', fileMeta_take _ _ _ (by omega)]
    exact hs.symm
  · simp only [imgMetas]
    rw [fileMeta_take _ _ 0 (by omega), fileMeta_take _ _ 1 (by omega)]; exact hv
  all_goals simp only [curRoot, curPgid, hc']
  all_goals assumption

/-! ## init -/

/-- The current meta of an image whose slot 1 is `init`'s meta 1 and whose slot 0 is invalid or
`init`'s meta 0 (txid 0 below 1): `init`'s meta 1. -/
theorem curMeta_init1 {img : List w8} (h1 : fileMeta img 1 = bInitMeta 1)
    (h0 : metaValid (fileMeta img 0) → fileMeta img 0 = bInitMeta 0) :
    curMeta img = bInitMeta 1 := by
  unfold curMeta
  dsimp only
  rw [h1]
  split
  · rw [if_pos (initMeta_valid 1)]
  · rename_i hlt
    split
    · rename_i hv0
      rw [h0 hv0, initMeta_txid, initMeta_txid] at hlt
      exact absurd (by decide) hlt
    · rfl

/-- `init`'s metas, read back from an image whose slots are invalid or `init`'s, slot 0 valid only
if slot 1 is (`init` writes meta 1 first), and whose page 3 is `init`'s root page: a good image,
whose current meta, if any, is `init`'s meta 1 (txid 1). -/
theorem goodImg_init {img : List w8} (h16 : 4 * 4096 ≤ img.length) (hl : img.length ≤ 2 ^ 30)
    (hs : ∀ i < 2, metaValid (fileMeta img i) → fileMeta img i = bInitMeta i)
    (h01 : metaValid (fileMeta img 0) → metaValid (fileMeta img 1))
    (h3 : (img.drop (4096 * 3)).take 4096 = emptyPageBytes (W64 3) (W16 2)) : goodImg img := by
  by_cases hv1 : metaValid (fileMeta img 1)
  · have e1 := hs 1 (by omega) hv1
    have hc := curMeta_init1 e1 (hs 0 (by omega))
    refine goodImg_cur h16 hl hc (Or.inr hv1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [initMeta_root, initMeta_pgid, initMeta_txid]
    · decide
    · decide
    · decide
    · show 4096 * 4 ≤ img.length; omega
    · rw [show (W64 3).toNat = 3 from rfl, h3, initRoot_val]
      exact Or.inl ⟨by decide, rfl⟩
    · exact e1
    · decide
    · decide
  · exact goodImg_noValid hl fun i hi _ hv' => by
      rcases i with _ | _ | i
      · exact hv1 (h01 hv')
      · exact hv1 hv'
      · omega


/-! ## init, before its first sync -/

/-- Meta slot `i` of the image of a file that holds the slot whole is its raw slot. -/
theorem fileMeta_contents {f : OsFile} {i : Nat} (h : 4096 * i + 80 ≤ f.size) :
    fileMeta f.contents i = decode (rawSlot f i) := by
  rw [fileMeta_slot]; congr 1
  apply List.ext_getElem?; intro k
  by_cases hk : k < 64
  · rw [metaSlot_getElem? _ _ _ hk, contents_getElem?, if_pos (by omega), rawAt_def]
    simp only [rawSlot, List.getElem?_map, List.getElem?_range hk, Option.map_some]
    rw [show (4096 * i + 16 + k) / 512 = 8 * i by omega,
      show (4096 * i + 16 + k) % 512 = 16 + k by omega]
  · rw [List.getElem?_eq_none (by rw [metaSlot_length, contents_length]; omega),
      List.getElem?_eq_none (by simp [rawSlot]; omega)]

/-- Sixty-four zero bytes are no valid meta. -/
theorem zeros_invalid {L : List w8} (hl : L.length = 64) (h : ∀ k < 64, L[k]? = some 0) :
    ¬ metaValid (decode L : Meta) := by
  have : L = List.replicate 64 0 := List.ext_getElem? fun k => by
    by_cases hk : k < 64
    · rw [h k hk, List.getElem?_replicate, if_pos hk]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  rw [this]; exact zeroSlot_invalid

/-- A slot of the bytes `durSlot` knows satisfies its predicate, if valid. -/
theorem durSlot_list {m : OsMeta} {i : Nat} {P : Meta → Prop} (hd : durSlot m i P) {L : List w8}
    (hl : L.length = 64) (hL : ∀ k < 64, ∀ d, m.DurAt (4096 * i + 16 + k) d → L[k]? = some d) :
    metaValid (decode L : Meta) → P (decode L) := by
  obtain ⟨B, hB, hP⟩ := hd
  have e : decode L = fileMeta B i := by
    rw [fileMeta_slot]; congr 1
    apply List.ext_getElem?; intro k
    by_cases hk : k < 64
    · obtain ⟨b, h1, h2⟩ := hB k hk
      rw [hL k hk b (.inl h2), metaSlot_getElem? _ _ _ hk, h1]
    · rw [List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (by rw [metaSlot_length]; omega)]
  rw [e]; exact hP

/-- The file as `Open` hands it to `init`: its size and crash bounds at most 1 GiB, one version of
each sector known, fresh sectors known from at most its last page on (and from at least its end),
and the meta slot of every page that holds a byte of it invalid on disk, as `m.dur` knows it. -/
structure initIdle (m : OsMeta) (bs : List (w8 × Bool)) : Prop where
  len : bs.length = m.size
  hi : m.hi ≤ 2 ^ 30
  vk : m.vk = some []
  fr : ∃ p, m.fr = some p ∧ m.size ≤ p ∧ p ≤ pageUp m.size
  dur : ∀ j < 2, 4096 * j < m.size → durSlot m j (fun _ => False)

/-- A state of `init`'s first write (`F` at 0, zero over the meta pages) from `m0`, `nn` bytes of
it written: what a crash of it needs. -/
structure initW1St (m0 : OsMeta) (F : List w8) (nn : Nat) (m : OsMeta) (bs : List (w8 × Bool)) :
    Prop where
  len : bs.length = m.size
  nnle : nn ≤ 16384
  size : m.size = max m0.size nn
  bytes : ∀ b < nn, (bs[b]?).map Prod.fst = some (F.getD b 0)
  dur : m.dur = m0.dur
  dz : m.dz = m0.dz
  fr : m.fr = m0.fr
  vk : ∃ ns, m.vk = some ns ∧ ∀ j < 2, 8 * j ∈ ns → 4096 * j + 512 ≤ nn
  hi : m.hi ≤ max m0.hi 16384
  cut : nn = 16384 ∨ nn % 4096 = 0

theorem initW1St.notOk {m0 : OsMeta} {F : List w8} {nn : Nat} {m : OsMeta} {bs : List (w8 × Bool)}
    (h : initW1St m0 F nn m bs) : initW1St m0 F nn { m with ok := false } bs :=
  ⟨h.len, h.nnle, h.size, h.bytes, h.dur, h.dz, h.fr, h.vk, h.hi, h.cut⟩

/-- The page `pageUp x` is at most a page boundary at or past `x`. -/
theorem pageUp_le {x q : Nat} (h : x ≤ 4096 * q) : pageUp x ≤ 4096 * q := by
  unfold pageUp; omega

/-- **Every meta slot a crash of a state of `init`'s first write may leave is invalid** (under a
size that reaches its page): on disk, as `initIdle` knows it, unless the page is fresh; else
the write's zeros. -/
theorem initW1_dead {m0 : OsMeta} {xs : List (w8 × Bool)} {F : List w8} {nn : Nat} {s : CSt}
    (h0 : initIdle m0 xs) (hF : F.length = 16384) (hFz : ∀ k < 8192, F.getD k 0 = 0)
    (h : initW1St m0 F nn s.m s.bs)
    (hb : s.busy = .idle ∨ ∃ t, s.busy = .write t nn (F.drop nn)) :
    ∀ j < 2, ∀ sz L, 4096 * j < sz → slotCand s sz j L → ¬ metaValid (decode L : Meta) := by
  intro j hj sz L hs hc
  obtain ⟨p, hp, hSp, hpS⟩ := h0.fr
  have hfr : s.m.fr = some p := by rw [h.fr]; exact hp
  obtain ⟨hlen, hc⟩ := hc
  have hz : ∀ b, b < nn → b < 8192 → bsB s b = 0 := by
    intro b hb1 hb2
    have := h.bytes b hb1
    unfold bsB
    cases hx : s.bs[b]? with
    | none => rw [hx] at this; cases this
    | some x =>
      rw [hx] at this; simp only [Option.map_some, Option.some.injEq] at this
      rw [List.getD_eq_getElem?_getD, hx]; simp only [Option.getD_some]
      rw [this, hFz b hb2]
  rcases hc with ⟨hfc, hL⟩ | ⟨⟨ns, hns, hmem⟩, hL⟩ |
      ⟨t, off, data, k', hbz, hk0, hkl, hhit, hcut, hL⟩ | ⟨⟨t, sz', hbz⟩, hL⟩
  · -- the durable copy: the page holds a byte of the file, else it is fresh and covered
    by_cases hS : 4096 * j < m0.size
    · exact fun hv => durSlot_list (h0.dur j hj hS) hlen (fun k hk d hd => hL k hk d (by
        unfold OsMeta.DurAt at hd ⊢; rw [h.dur, h.dz]; exact hd)) hv
    · exact absurd ⟨by omega, ⟨p, hfr, by have := pageUp_le (q := j) (by omega : m0.size ≤ 4096 * j); omega⟩,
        by omega⟩ hfc
  · -- the page cache's, of a sector the write met: its zeros
    obtain ⟨ns', hns', hbd⟩ := h.vk
    rw [hns'] at hns; cases hns
    have hb := hbd j hj hmem
    refine zeros_invalid hlen fun k hk => ?_
    rw [hL k hk (by rw [h.size]; omega), hz _ (by omega) (by omega)]
  · -- the write in flight, landed in part: its zeros, or the page cache's
    rcases hb with hb | ⟨t', hb⟩
    · rw [hb] at hbz; cases hbz
    rw [hb] at hbz; cases hbz
    refine zeros_invalid hlen fun k hk => ?_
    rw [hL k hk]
    unfold landB
    split
    · rename_i hin
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
        show nn + (4096 * j + 16 + k - nn) = 4096 * j + 16 + k by omega, hFz _ (by omega)]
    · rename_i hout
      split
      · rename_i hsz
        by_cases hlt : 4096 * j + 16 + k < nn
        · rw [hz _ hlt (by omega)]
        · exfalso
          rcases hcut with ⟨-, hpc⟩ | ⟨-, ⟨p', hp', hp'j⟩, -⟩
          · simp only [secHits, Bool.and_eq_true, decide_eq_true_eq] at hhit
            simp only [List.length_drop] at hpc hkl
            have := h.nnle
            rcases hpc with h1 | h1 | h1
            · omega
            · omega
            · omega
          · rw [hfr] at hp'; cases hp'
            rw [h.size] at hsz
            omega
      · rfl
  · rcases hb with hb | ⟨t', hb⟩ <;> rw [hb] at hbz <;> cases hbz

/-- **Good from dead slots**: every crash of a state at most 1 GiB since the last sync, whose
`OsMeta` knows its versions and fresh sectors, is `Good` if every meta slot a crash may leave
under a size that reaches its page (`slotCand`) is invalid. -/
theorem fileOkS_slotsDead {i : Ino} (s : CSt) (hwf : s.Wf) (hbz : BusyOk s)
    (hvk : ∃ ns, s.m.vk = some ns) (hfr : ∃ p, s.m.fr = some p) (hhi : s.vmeta.hi ≤ 2 ^ 30)
    (hd : ∀ j < 2, ∀ sz L, 4096 * j < sz → slotCand s sz j L → ¬ metaValid (decode L : Meta)) :
    FileOkS NoTearCrash Good i s := by
  refine fileOkS_crashRaw s hwf hbz fun f hI hR => ?_
  have hraw : ∀ j < 2, 4096 * j < f.size → ¬ metaValid (decode (rawSlot f j) : Meta) :=
    fun j hj hs => hd j hj _ _ hs (hR.2 hvk j hj)
  have hl : f.contents.length ≤ 2 ^ 30 := by have := hI.2.1; omega
  have hl' := hl
  rw [contents_length] at hl'
  refine ⟨⟨hl, ?_⟩, fun _ => ⟨hR.1 hfr, hraw⟩⟩
  by_cases h4 : f.size < 4 * 4096
  · exact .inl ⟨by rw [contents_length]; exact h4, fun j hj hs => by
      rw [contents_length] at hs; rw [fileMeta_contents hs]; exact hraw j hj (by omega)⟩
  · refine .inr (.inl ⟨by rw [contents_length]; omega, ?_, ?_⟩) <;> simp only [imgMetas] <;>
      rw [fileMeta_take _ _ _ (by omega), fileMeta_contents (by omega)]
    · exact hraw 0 (by omega) (by omega)
    · exact hraw 1 (by omega) (by omega)

/-- **`init`'s first write, retried**: every state it reaches from `initIdle` is an `initW1St`. -/
theorem initW1St_of_wreach {m0 : OsMeta} {xs : List (w8 × Bool)} {F : List w8}
    (h0 : initIdle m0 xs) (hF : F.length = 16384) {nn : Nat} {m' : OsMeta}
    {bs' : List (w8 × Bool)} (hR : WReach NoTearCut m0 xs 0 F nn m' bs') :
    initW1St m0 F nn m' bs' := by
  have h64 : F.length < 2 ^ 64 := by rw [hF]; decide
  have hN := hR.narrow h0.len (Nat.zero_le _)
  obtain ⟨hnn, hsz, hby⟩ := hR.exact noTearCut_errno h0.len (Nat.zero_le _) h64
  obtain ⟨hd, hdz, -, -, -⟩ := hR.meta_keep
  obtain ⟨ns', hns', hns⟩ := hR.noTear_vk h0.len (Nat.zero_le _) (by decide) h64 h0.vk
    (fun _ _ h => by simp at h)
  have hcut := hR.noTear_cut (by decide) h64
  rw [hF] at hnn hcut hns
  have hps : pwSize m0.size 0 nn = max m0.size nn := by
    unfold pwSize; split <;> omega
  refine ⟨hN.len, hnn, by rw [hsz, hps], fun b hb => ?_, hd, hdz,
    hR.fr_keep (by decide) (by rw [hF]) h64, ⟨ns', hns', fun j hj hm => ?_⟩,
    by have := hN.hi; rw [hF] at this; omega, by omega⟩
  · rw [hby b (Nat.zero_le _) (by rw [hF]; omega) (by rw [hps]; omega), if_pos (by omega)]
    simp
  · apply Classical.byContradiction; intro hlt
    exact hns (by omega) (8 * j) (by simp only [secHits, Bool.and_eq_true, decide_eq_true_eq]; omega) hm

/-! ## init, after its first sync -/

/-- The slot `init` writes in its phase `ph`: meta 1 first (`false`), then meta 0 (`true`). -/
def initSlot : Bool → Nat
  | false => 1
  | true => 0

/-- The bytes of the other slot (`1 - initSlot ph`) in phase `ph`: zero before meta 1 is synced,
`init`'s meta 1 after. -/
def initOrdByte : Bool → Nat → w8
  | false, _ => 0
  | true, j => initBytes.getD j 0

/-- In phase `ph`, the slot `init` does not write is clean in the page cache, with `initOrdByte`. -/
def initOrd (ph : Bool) (bs : List (w8 × Bool)) : Prop :=
  ∀ k < 64, bs[4096 * (1 - initSlot ph) + 16 + k]? =
    some (initOrdByte ph (4096 * (1 - initSlot ph) + 16 + k), true)

/-- An image with the other slot's `initOrdByte`s has slot 0 valid only if slot 1 is, and that
slot valid only as `init`'s meta. -/
theorem initOrd_img {ph : Bool} {img : List w8}
    (h : ∀ k < 64, img[4096 * (1 - initSlot ph) + 16 + k]? =
      some (initOrdByte ph (4096 * (1 - initSlot ph) + 16 + k))) :
    (metaValid (fileMeta img 0) → metaValid (fileMeta img 1)) ∧
    (metaValid (fileMeta img (1 - initSlot ph)) →
      fileMeta img (1 - initSlot ph) = bInitMeta (1 - initSlot ph)) := by
  cases ph with
  | false =>
    have hz : ¬ metaValid (fileMeta img 0) := slot_zero_invalid (i := 0) fun k hk => by
      have := h k hk
      simp only [initSlot, initOrdByte] at this
      exact this
    exact ⟨fun hv => absurd hv hz, fun hv => absurd hv hz⟩
  | true =>
    have hil := initBytes_length
    simp only [pageBytes] at hil
    have e : fileMeta img 1 = fileMeta initBytes 1 := fileMeta_of_slot (metaSlot_ext fun k hk => by
      have := h k hk
      simp only [initSlot, initOrdByte] at this
      rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl)
    refine ⟨fun _ => by rw [e, initBytes_meta1]; exact initMeta_valid 1, fun _ => ?_⟩
    show fileMeta img 1 = bInitMeta 1
    rw [e, initBytes_meta1]

/-- After the first sync, in phase `ph`: the size at least four pages since the sync, the
versions known, `m.dur` and the page cache's slots invalid or `init`'s metas, `init`'s page 3 and
the slot not being written (`initOrd`) clean in the page cache. -/
structure initMid (ph : Bool) (m : OsMeta) (bs : List (w8 × Bool)) : Prop where
  len : bs.length = m.size
  hi : m.hi ≤ 2 ^ 30
  lo : 4 * 4096 ≤ m.lo
  sz : 4 * 4096 ≤ m.size
  vk : ∃ ns, m.vk = some ns
  dur : ∀ i < 2, durSlot m i (fun X => X = bInitMeta i)
  cache : ∀ i < 2, cacheSlot bs i (fun X => X = bInitMeta i)
  page3 : ∀ k < 4096, bs[4096 * 3 + k]? =
    some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0, true)
  ord : initOrd ph bs

theorem initMid.notOk {ph : Bool} {m : OsMeta} {bs : List (w8 × Bool)} (h : initMid ph m bs) :
    initMid ph { m with ok := false } bs :=
  ⟨h.len, h.hi, h.lo, h.sz, h.vk, h.dur, h.cache, h.page3, h.ord⟩

/-- Page 3 of an image whose page-3 bytes are the page cache's clean ones. -/
theorem initMid_page3 {ph : Bool} {m : OsMeta} {bs : List (w8 × Bool)} (h : initMid ph m bs)
    {img : List w8}
    (himg : ∀ k < 4096, bs[4096 * 3 + k]? = some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0, true) →
      img[4096 * 3 + k]? = some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0)) :
    (img.drop (4096 * 3)).take 4096 = emptyPageBytes (W64 3) (W16 2) := by
  have hlen := emptyPageBytes_length (W64 3) (W16 2)
  simp only [pageBytes] at hlen
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take, List.getElem?_drop]
  split
  · rename_i hk
    rw [himg k hk (h.page3 k hk), List.getElem?_eq_getElem (by omega)]; rfl
  · rw [List.getElem?_eq_none (by omega)]

/-- The data of `init`'s meta write of phase `ph`: a page whose slot is `initBytes`'s slot
`initSlot ph`. -/
def initWData (ph : Bool) (D : List w8) : Prop :=
  D.length = 4096 ∧ ∀ k < 64, D[16 + k]? = initBytes[4096 * initSlot ph + 16 + k]?

/-- The slot of a page of `initWData`: `init`'s meta. -/
theorem initWData_meta {ph : Bool} {D : List w8} (hD : initWData ph D) {L : List w8}
    (hL : ∀ k < 64, L[4096 * initSlot ph + 16 + k]? = some (D.getD (16 + k) 0)) :
    fileMeta L (initSlot ph) = bInitMeta (initSlot ph) := by
  have hil := initBytes_length
  simp only [pageBytes] at hil
  have e : fileMeta L (initSlot ph) = fileMeta initBytes (initSlot ph) :=
    fileMeta_of_slot (metaSlot_ext fun k hk => by
      rw [hL k hk, List.getD_eq_getElem?_getD, hD.2 k hk,
        List.getElem?_eq_getElem (by cases ph <;> simp [initSlot] <;> omega)]
      rfl)
  rw [e]
  cases ph
  · exact initBytes_meta1
  · exact initBytes_meta0

/-- A meta write of phase `ph` (page `initSlot ph`, retried) keeps the bytes of the other slot
and of page 3. -/
theorem initW_keeps {ph : Bool} {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {D : List w8} {nn : Nat}
    (hl : bs.length = m.size) (hR : WReach NoTearCut m bs (4096 * initSlot ph) D nn m' bs')
    (hdl : D.length = 4096) (hsz : 4 * 4096 ≤ m.size) :
    (∀ k < 64, bs'[4096 * (1 - initSlot ph) + 16 + k]? = bs[4096 * (1 - initSlot ph) + 16 + k]?) ∧
    ∀ k, 8192 ≤ k → bs'[k]? = bs[k]? := by
  have hN := hR.narrow hl (by cases ph <;> simp [initSlot] <;> omega)
  refine ⟨fun k hk => ?_, fun k hk => hN.suf (by cases ph <;> simp [initSlot] <;> omega) _
    (by cases ph <;> simp [initSlot] <;> omega)⟩
  cases ph with
  | false => exact hN.pre _ (by simp only [cfLo, initSlot]; omega)
  | true => exact hN.suf (by simp [initSlot]; omega) _ (by simp [initSlot]; omega)

/-- **`init`'s meta write of phase `ph`, retried**, from a synced `initMid ph` state (the versions
known with one each): every state it reaches is `initMid ph`, and lands nothing or the whole page;
with the whole page, the slot written is `init`'s meta. -/
theorem initMid_wreach {ph : Bool} {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {D : List w8}
    {nn : Nat} (h : initMid ph m bs) (hvk : m.vk = some []) (hD : initWData ph D)
    (hR : WReach NoTearCut m bs (4096 * initSlot ph) D nn m' bs') :
    initMid ph m' bs' ∧ (nn = 0 ∨ nn = 4096) ∧
      (nn = 4096 → ∀ k < 64, (bs'[4096 * initSlot ph + 16 + k]?).map Prod.fst =
        some (D.getD (16 + k) 0)) := by
  have hdl := hD.1
  have h64 : D.length < 2 ^ 64 := by rw [hdl]; decide
  have hsz0 := h.sz
  have hoff : 4096 * initSlot ph ≤ m.size := by cases ph <;> simp [initSlot] <;> omega
  have hN := hR.narrow h.len hoff
  obtain ⟨hnn, hsz, hby⟩ := hR.exact noTearCut_errno h.len hoff h64
  obtain ⟨hd, hdz, -, -, hlo⟩ := hR.meta_keep
  obtain ⟨ns', hns', -⟩ := hR.noTear_vk h.len hoff (by cases ph <;> simp [initSlot]) h64 hvk
    (fun _ _ h => by simp at h)
  have hcut := hR.noTear_cut (by cases ph <;> simp [initSlot]) h64
  rw [hdl] at hnn hcut
  have hnn' : nn = 0 ∨ nn = 4096 := by
    rcases hcut with h1 | h1
    · exact .inr h1
    · cases ph <;> simp [initSlot] at h1 <;> omega
  have hps : pwSize m.size (4096 * initSlot ph) nn = m.size := by
    unfold pwSize; split
    · rfl
    · cases ph <;> simp [initSlot] <;> omega
  obtain ⟨ho, h3⟩ := initW_keeps h.len hR hdl hsz0
  have hslot : ∀ k < 64, bs'[4096 * initSlot ph + 16 + k]? =
      if nn = 4096 then some (D.getD (16 + k) 0, false)
      else bs[4096 * initSlot ph + 16 + k]? := by
    intro k hk
    rw [hby _ (by omega) (by omega) (by rw [hps]; cases ph <;> simp [initSlot] <;> omega)]
    rcases hnn' with rfl | rfl
    · rw [if_neg (by omega), if_neg (by omega)]
    · rw [if_pos (by omega), if_pos rfl]
      congr 3; omega
  refine ⟨⟨hN.len, by have := hN.hi; have := h.hi; rw [hdl] at *; cases ph <;> simp [initSlot] at * <;> omega,
    by rw [hlo]; exact h.lo, by have := hN.size; omega, ⟨ns', hns'⟩,
    fun i hi => ?_, fun i hi hv => ?_, fun k hk => ?_, fun k hk => ?_⟩, hnn', fun h4 k hk => ?_⟩
  · obtain ⟨B, hB, hP⟩ := h.dur i hi
    exact ⟨B, fun k hk => by rw [hd]; exact hB k hk, hP⟩
  · -- the page cache's slot `i`: the old one, or the write's
    have hlen' : bs'.length = m.size := by rw [hN.len, hsz, hps]
    by_cases hi' : i = initSlot ph
    · subst hi'
      by_cases h4 : nn = 4096
      · have e := initWData_meta hD (L := bs'.map Prod.fst) fun k hk => by
          rw [List.getElem?_map, hslot k hk, if_pos h4]; rfl
        exact e
      · have e : fileMeta (bs'.map Prod.fst) (initSlot ph) = fileMeta (bs.map Prod.fst) (initSlot ph) :=
          fileMeta_of_slot (metaSlot_ext fun k hk => by
            rw [List.getElem?_map, List.getElem?_map, hslot k hk, if_neg h4])
        rw [e] at hv ⊢; exact h.cache _ hi hv
    · have hio : i = 1 - initSlot ph := by cases ph <;> simp [initSlot] at hi' ⊢ <;> omega
      subst hio
      have e : fileMeta (bs'.map Prod.fst) (1 - initSlot ph) =
          fileMeta (bs.map Prod.fst) (1 - initSlot ph) :=
        fileMeta_of_slot (metaSlot_ext fun k hk => by
          rw [List.getElem?_map, List.getElem?_map, ho k hk])
      rw [e] at hv ⊢; exact h.cache _ hi hv
  · rw [h3 _ (by omega)]; exact h.page3 k hk
  · rw [ho k hk]; exact h.ord k hk
  · rw [hslot k hk, if_pos h4]; rfl

/-- A successful sync of the whole file, with `init`'s page 3, slots invalid or `init`'s metas,
and the other slot of phase `ph` as `initOrd` says, leaves an `initMid ph` state, all clean, the
versions known with one each. -/
theorem initMid_synced {ph : Bool} {m : OsMeta} {bs : List (w8 × Bool)} (hok : m.ok = true)
    (hl : bs.length = m.size) (hlo : 4 * 4096 ≤ m.size) (hhi : m.size ≤ 2 ^ 30)
    (hs : ∀ i < 2, metaValid (fileMeta (bs.map Prod.fst) i) →
      fileMeta (bs.map Prod.fst) i = bInitMeta i)
    (h3 : ∀ k < 4096, (bs[4096 * 3 + k]?).map Prod.fst =
      some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0))
    (hord : initOrd ph (bs.map fun x => (x.1, true))) :
    initMid ph (m.synced 0 bs) (bs.map fun x => (x.1, true)) ∧ (m.synced 0 bs).vk = some [] := by
  have hfst : (bs.map fun x => (x.1, true)).map Prod.fst = bs.map Prod.fst := by
    rw [List.map_map]; rfl
  refine ⟨⟨by simp [OsMeta.synced, hl], by simp [OsMeta.synced]; omega,
    by simp [OsMeta.synced]; omega, by simp [OsMeta.synced]; omega,
    ⟨[], by simp [OsMeta.synced, hok]⟩, fun i hi => ?_, fun i hi hv => ?_, fun k hk => ?_, hord⟩,
    by simp [OsMeta.synced, hok]⟩
  · refine ⟨bs.map Prod.fst, fun k hk => ?_, hs i hi⟩
    have hkl : 4096 * i + 16 + k < bs.length := by omega
    refine ⟨bs[4096 * i + 16 + k].1, by rw [List.getElem?_map, List.getElem?_eq_getElem hkl]; rfl, ?_⟩
    simp only [OsMeta.synced, hok, if_true, durOf, List.replicate_zero, List.nil_append,
      List.getElem?_map, List.getElem?_eq_getElem hkl, Option.map_some, Nat.sub_zero]
  · unfold cacheSlot at *; rw [hfst] at hv ⊢; exact hs i hi hv
  · have := h3 k hk
    rw [List.getElem?_map]
    cases hx : bs[4096 * 3 + k]? with
    | none => rw [hx] at this; cases this
    | some x => rw [hx] at this; simp only [Option.map_some, Option.some.injEq] at this ⊢; rw [this]

/-! ## commit -/

/-- What a commit's crash images need of the state while the metas and the current root page are
clean (every step before the meta write): `bs`'s meta pages `mp` are an open database's, whose
current meta's root page holds what `BootMinibolt` checks, and the size since the last sync covers
the high water mark. -/
structure commitClean (m : OsMeta) (bs : List (w8 × Bool)) : Prop where
  hi : m.hi ≤ 2 ^ 30
  lo : 4 * 4096 ≤ m.lo
  ok : metaPagesOk ((bs.map Prod.fst).take 8192)
  slot : curInSlot ((bs.map Prod.fst).take 8192)
  pg : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ m.lo
  boot : bootOk (curMeta ((bs.map Prod.fst).take 8192)).txid'.toNat
    (pageVal (((bs.map Prod.fst).drop (4096 * curRoot ((bs.map Prod.fst).take 8192))).take 4096))
  metas : ∀ k < 8192, ∃ b, bs[k]? = some (b, true)
  root : ∀ k < 4096, ∃ b, bs[4096 * curRoot ((bs.map Prod.fst).take 8192) + k]? = some (b, true)
  tx : txOk ((bs.map Prod.fst).take 8192)

theorem commit_clean_img {m : OsMeta} {bs : List (w8 × Bool)} (h : commitClean m bs)
    {img : List w8} (hlo : m.lo ≤ img.length) (hhi : img.length ≤ 2 ^ 30)
    (hcl : ∀ k b, bs[k]? = some (b, true) →
      (k < 8192 ∨ (4096 * curRoot ((bs.map Prod.fst).take 8192) ≤ k ∧
        k < 4096 * curRoot ((bs.map Prod.fst).take 8192) + 4096)) → img[k]? = some b) :
    goodImg img := by
  have hok := h.ok
  have hpg := h.pg
  have hboot := h.boot
  have hroot := h.root
  have hlo4 := h.lo
  have hslot := h.slot
  have htx := h.tx
  have hlen : ((bs.map Prod.fst).take 8192).length = 8192 := hok.1
  have hbl : 8192 ≤ (bs.map Prod.fst).length := by rw [List.length_take] at hlen; omega
  generalize hmp : (bs.map Prod.fst).take 8192 = mp at hok hpg hboot hroot hcl hslot htx
  have hmeta : ∀ k < 8192, img[k]? = (bs.map Prod.fst)[k]? := by
    intro k hk
    obtain ⟨b, hb⟩ := h.metas k hk
    rw [hcl k b hb (.inl hk), List.getElem?_map, hb]; rfl
  have hR : ∀ k < 4096, img[4096 * curRoot mp + k]? = (bs.map Prod.fst)[4096 * curRoot mp + k]? := by
    intro k hk
    obtain ⟨b, hb⟩ := hroot k hk
    rw [hcl _ b hb (.inr ⟨by omega, by omega⟩), List.getElem?_map, hb]; rfl
  have htake : img.take 8192 = mp := by
    rw [← hmp]
    apply List.ext_getElem?
    intro k
    simp only [List.getElem?_take]
    split
    · exact hmeta k ‹_›
    · rfl
  refine ⟨hhi, Or.inr (Or.inr ⟨by omega, ?_, ?_, ?_⟩)⟩
  · simp only [imgMetas, htake]; exact hok
  · simp only [imgMetas, htake]; omega
  · simp only [imgMetas, htake]
    obtain ⟨b4, hb4⟩ := hroot 4095 (by omega)
    have h4 := (List.getElem?_eq_some_iff.1 hb4).1
    rw [take_drop_eq hR (by simp only [List.length_map]; omega)]
    exact ⟨hboot, hslot, htx⟩

/-- The current meta of an image whose slot `s` is the old current meta `M` and whose other slot
is invalid, the old one, or the new meta `N` (with a larger txid): `M` or `N`. -/
theorem commit_cur {img mp : List w8} {M N : Meta} {s : Nat} (hs : s < 2)
    (hM : fileMeta img s = M) (hMv : metaValid M) (hmp : curMeta mp = M) (hmps : fileMeta mp s = M)
    (h' : metaValid (fileMeta img (1 - s)) →
      fileMeta img (1 - s) = fileMeta mp (1 - s) ∨ fileMeta img (1 - s) = N)
    (hNv : metaValid N) (htx : uint.Z M.txid' < uint.Z N.txid') :
    curMeta img = M ∨ curMeta img = N := by
  by_cases hv : metaValid (fileMeta img (1 - s))
  · rcases h' hv with e | e
    · left
      rw [← hmp]
      rcases s with _ | _ | s
      · exact curMeta_congr (hM.trans hmps.symm) e
      · exact curMeta_congr e (hM.trans hmps.symm)
      · omega
    · right
      unfold curMeta
      dsimp only
      rcases s with _ | _ | s
      · simp only [Nat.sub_zero] at e
        rw [hM, e, if_pos htx, if_pos hNv]
      · simp only [Nat.sub_self] at e
        rw [hM, e, if_neg (by omega), if_pos hNv]
      · omega
  · left
    have hvs : metaValid (fileMeta img 0) ∨ metaValid (fileMeta img 1) := by
      rcases s with _ | _ | s
      · exact Or.inl (hM ▸ hMv)
      · exact Or.inr (hM ▸ hMv)
      · omega
    rcases curMeta_cases img hvs with ⟨e, v⟩ | ⟨e, v⟩
    · rcases s with _ | _ | s
      · exact e.trans hM
      · exact absurd v hv
      · omega
    · rcases s with _ | _ | s
      · exact absurd v hv
      · exact e.trans hM
      · omega

/-- What a commit's crash images need of the state while it writes the meta slot `1 - s` (from
the old meta pages `mp`, whose current meta `M` is in slot `s`, to the new meta `N`): slot `s`,
`M`'s root page and `N`'s root page (synced, holding `N`'s txid) clean, and the durable copy of slot
`1 - s` the old or the new meta. -/
structure commitMetaSt (m : OsMeta) (bs : List (w8 × Bool)) (mp : List w8) (N : Meta)
    (s : Nat) : Prop where
  s2 : s < 2
  sTx : s = (curMeta mp).txid'.toNat % 2
  hi : m.hi ≤ 2 ^ 30
  lo : 4 * 4096 ≤ m.lo
  ok : metaPagesOk mp
  slot : curMeta mp = fileMeta mp s
  pg : 4096 * curPgid mp ≤ m.lo
  boot : bootOk (curMeta mp).txid'.toNat
    (pageVal (((bs.map Prod.fst).drop (4096 * curRoot mp)).take 4096))
  root : ∀ k < 4096, ∃ b, bs[4096 * curRoot mp + k]? = some (b, true)
  metaS : ∀ k < 64, ∃ b, mp[4096 * s + 16 + k]? = some b ∧ bs[4096 * s + 16 + k]? = some (b, true)
  tx : txOk mp
  nValid : metaValid N
  nTx : uint.Z (curMeta mp).txid' < uint.Z N.txid'
  nTxS : N.txid'.toNat = (curMeta mp).txid'.toNat + 1
  nRoot : 2 ≤ N.root'.root'.toNat
  nRootPg : N.root'.root'.toNat < N.pgid'.toNat
  nTxPg : N.txid'.toNat < N.pgid'.toNat
  nPg : (N.pgid'.toNat + 1) * 4096 ≤ 2 ^ 30
  nPgLo : 4096 * N.pgid'.toNat ≤ m.lo
  nBoot : bootOk N.txid'.toNat
    (pageVal (((bs.map Prod.fst).drop (4096 * N.root'.root'.toNat)).take 4096))
  nPage : ∀ k < 4096, ∃ b, bs[4096 * N.root'.root'.toNat + k]? = some (b, true)

theorem commitMeta_good {m : OsMeta} {bs : List (w8 × Bool)} {mp : List w8} {N : Meta} {s : Nat}
    (h : commitMetaSt m bs mp N s) {img : List w8} (hlo : m.lo ≤ img.length)
    (hhi : img.length ≤ 2 ^ 30)
    (hcl : ∀ k b, bs[k]? = some (b, true) → (4096 * s + 16 ≤ k ∧ k < 4096 * s + 80 ∨
      (4096 * curRoot mp ≤ k ∧ k < 4096 * curRoot mp + 4096) ∨
      (4096 * N.root'.root'.toNat ≤ k ∧ k < 4096 * N.root'.root'.toNat + 4096)) → img[k]? = some b)
    (h' : metaValid (fileMeta img (1 - s)) →
      fileMeta img (1 - s) = fileMeta mp (1 - s) ∨ fileMeta img (1 - s) = N) :
    goodImg img := by
  have hok := h.ok
  have hMv : metaValid (curMeta mp) := by
    rcases curMeta_cases mp hok.2.1 with ⟨e, v⟩ | ⟨e, v⟩ <;> rw [e] <;> exact v
  have hs2 := h.s2
  have hM : fileMeta img s = curMeta mp := by
    rw [h.slot]
    apply fileMeta_of_slot
    apply metaSlot_ext
    intro k hk
    obtain ⟨b, h1, h2⟩ := h.metaS k hk
    rw [hcl _ b h2 (.inl ⟨by omega, by omega⟩), h1]
  have hpage : ∀ r, (∀ k < 4096, ∃ b, bs[4096 * r + k]? = some (b, true)) →
      (∀ k, 4096 * r ≤ k → k < 4096 * r + 4096 → ∀ b, bs[k]? = some (b, true) → img[k]? = some b) →
      (img.drop (4096 * r)).take 4096 = ((bs.map Prod.fst).drop (4096 * r)).take 4096 := by
    intro r hr himg
    obtain ⟨b4, hb4⟩ := hr 4095 (by omega)
    have h4 := (List.getElem?_eq_some_iff.1 hb4).1
    refine take_drop_eq (fun k hk => ?_) (by simp only [List.length_map]; omega)
    obtain ⟨b, hb⟩ := hr k hk
    rw [himg _ (by omega) (by omega) b hb, List.getElem?_map, hb]; rfl
  rcases commit_cur hs2 hM hMv rfl h.slot.symm h' h.nValid h.nTx with hc | hc
  · refine goodImg_cur (by have := h.lo; omega) hhi hc
      (by rcases s with _ | _ | s
          · exact Or.inl (hM ▸ hMv)
          · exact Or.inr (hM ▸ hMv)
          · omega) hok.2.2.1 hok.2.2.2.1 hok.2.2.2.2 (by have := h.pg; unfold curPgid at this; omega) ?_
      (by rw [← h.sTx]; exact hM) h.tx.1 (by have := h.tx.2; unfold curPgid at this; omega)
    show bootOk _ (pageVal ((img.drop (4096 * curRoot mp)).take 4096))
    rw [hpage _ h.root (fun k h1 h2 b hb => hcl k b hb (.inr (.inl ⟨h1, h2⟩)))]
    exact h.boot
  · have hvN : metaValid (fileMeta img 0) ∨ metaValid (fileMeta img 1) := by
      rcases s with _ | _ | s
      · exact Or.inl (hM ▸ hMv)
      · exact Or.inr (hM ▸ hMv)
      · omega
    have hN' : fileMeta img (1 - s) = N := by
      rcases curMeta_cases img hvN with ⟨e, v⟩ | ⟨e, v⟩
      · rcases s with _ | _ | s
        · exact absurd (hM.symm.trans (e.symm.trans hc)) (fun e' => by
            have := h.nTx; rw [e'] at this; omega)
        · exact e.symm.trans hc
        · omega
      · rcases s with _ | _ | s
        · exact e.symm.trans hc
        · exact absurd (hM.symm.trans (e.symm.trans hc)) (fun e' => by
            have := h.nTx; rw [e'] at this; omega)
        · omega
    refine goodImg_cur (by have := h.lo; omega) hhi hc hvN h.nRoot h.nRootPg h.nPg
      (by have := h.nPgLo; omega) ?_ (by
        rw [h.nTxS, show ((curMeta mp).txid'.toNat + 1) % 2 = 1 - s by have := h.sTx; omega]
        exact hN') (by rw [h.nTxS]; omega) h.nTxPg
    rw [hpage _ h.nPage (fun k h1 h2 b hb => hcl k b hb (.inr (.inr ⟨h1, h2⟩)))]
    exact h.nBoot

end pure

/-! ## As obligations on the states of the crash invariant (`Proof/os/CrashSt.lean`) -/

section states
variable [GooseExts] {i : Ino} (s : CSt) (hwf : s.Wf)
include hwf

/-- **`init`'s first write's obligation**: a state of it, idle or with its next attempt in flight
(the data's rest), nothing frozen. -/
theorem initW1_okS {m0 : OsMeta} {xs : List (w8 × Bool)} {F : List w8} {nn : Nat}
    (h0 : initIdle m0 xs) (hF : F.length = 16384) (hFz : ∀ k < 8192, F.getD k 0 = 0)
    (hst : initW1St m0 F nn s.m s.bs) (hfa : s.fa = 0) (hfb : s.fb = 0)
    (hb : s.busy = .idle ∨ ∃ t, s.busy = .write t nn (F.drop nn) ∧ nn < 16384) :
    FileOkS NoTearCrash Good i s := by
  obtain ⟨p, hp, -, -⟩ := h0.fr
  obtain ⟨ns, hns, -⟩ := hst.vk
  have hsz := hst.size
  refine fileOkS_slotsDead s hwf ?_ ⟨ns, hns⟩ ⟨p, by rw [hst.fr]; exact hp⟩ ?_
    (initW1_dead h0 hF hFz hst (hb.imp_right fun ⟨t, h1, _⟩ => ⟨t, h1⟩))
  · unfold BusyOk
    rcases hb with hb | ⟨t, hb, -⟩ <;> rw [hb]
    · trivial
    · show nn ≤ s.m.size; omega
  · have h1 := hst.hi; have h2 := h0.hi; have h3 := hst.nnle
    unfold CSt.vmeta
    rcases hb with hb | ⟨t, hb, -⟩ <;> rw [hb]
    · dsimp only; omega
    · simp only [pwMeta, List.length_drop, hF]; omega

/-- `init`'s idle states after the first sync (the meta writes', their failures, the syncs'). -/
theorem initMid_okS {ph : Bool} (hb : s.busy = .idle) (h : initMid ph s.m s.bs) :
    FileOkS NoTearCrash Good i s := by
  have hs2 := h.sz
  refine fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; trivial) h.lo fun img hI => ?_
  have hlo := crashImg_lo hI
  have hlo' := h.lo
  have hcl : ∀ k b, s.bs[k]? = some (b, true) → img[k]? = some b := fun k b hk =>
    crashImg_clean hI hk (CSt.taken_out _ _ fun _ _ _ h' => by rw [hb] at h'; cases h')
  have ho := initOrd_img (ph := ph) (img := img) fun k hk => hcl _ _ (h.ord k hk)
  refine goodImg_init (by omega)
    (by have h1 := hI.2.1; have := h.hi; unfold CSt.vmeta at h1; rw [hb] at h1; dsimp only at h1; omega)
    (fun j hj hv => crashImg_slot hI hwf.1 h.vk hj (by omega) (by omega) (h.dur j hj) (h.cache j hj)
      (fun _ _ _ h' => by rw [hb] at h'; cases h') hv) ho.1
    (initMid_page3 h fun k _ hk => hcl _ _ hk)

/-- `init`'s meta write of phase `ph` in flight (the whole page `D`, nothing of it landed). -/
theorem initMidW_okS {ph : Bool} {t : Nat} {D : List w8}
    (hb : s.busy = .write t (4096 * initSlot ph) D) (h : initMid ph s.m s.bs)
    (hD : initWData ph D) : FileOkS NoTearCrash Good i s := by
  have hs2 := h.sz
  have hdl := hD.1
  refine fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; cases ph <;> simp [initSlot] <;> omega)
    h.lo fun img hI => ?_
  have hlo := crashImg_lo hI
  have hlo' := h.lo
  -- the other slot and page 3: clean bytes the write misses
  have hcl : ∀ k b, s.bs[k]? = some (b, true) →
      (k < 4096 * initSlot ph ∨ 4096 * initSlot ph + 4096 ≤ k) → img[k]? = some b :=
    fun k b hk hm => crashImg_clean hI hk (CSt.taken_out _ _ fun _ _ _ h' => by
      rw [hb] at h'; cases h'
      simp only [cfLo, cfHi]
      cases ph <;> simp [initSlot] at hm ⊢ <;> omega)
  have ho := initOrd_img (ph := ph) (img := img) fun k hk => hcl _ _ (h.ord k hk)
    (by cases ph <;> simp [initSlot] <;> omega)
  refine goodImg_init (by omega)
    (by have h1 := hI.2.1; have := h.hi; unfold CSt.vmeta at h1; rw [hb] at h1
        simp only [pwMeta] at h1; cases ph <;> simp [initSlot] at h1 <;> omega)
    (fun j hj hv => ?_) ho.1
    (initMid_page3 h fun k _ hk => hcl _ _ hk (.inr (by cases ph <;> simp [initSlot] <;> omega)))
  by_cases hjs : j = initSlot ph
  · subst hjs
    refine crashImg_slot hI hwf.1 h.vk hj (by omega) (by omega) (h.dur _ hj) (h.cache _ hj)
      (fun t' off data h' => ?_) hv
    rw [hb] at h'; cases h'
    intro L hL _
    exact initWData_meta hD fun k hk => by
      rw [hL k hk]; unfold wByte
      rw [if_pos ⟨by omega, by omega⟩]
      congr 2; omega
  · have hjo : j = 1 - initSlot ph := by cases ph <;> simp [initSlot] at hjs ⊢ <;> omega
    subst hjo
    exact ho.2 hv

/-- A commit's idle states before the meta write. -/
theorem commitClean_okS (hb : s.busy = .idle) (h : commitClean s.m s.bs) :
    FileOkS NoTearCrash Good i s :=
  fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; trivial) h.lo fun img hI =>
    commit_clean_img h (crashImg_lo hI)
      (by have h1 := hI.2.1; have h2 := h.hi; unfold CSt.vmeta at h1; rw [hb] at h1; dsimp only at h1; omega)
      (fun k b hb' _ => crashImg_clean hI hb' (CSt.taken_out _ _ fun _ _ _ h => by rw [hb] at h; cases h))

/-- A commit's writes before the meta write (the data page), in flight: they miss the metas and
the current root page. -/
theorem commitClean_write_okS {t off : Nat} {data : List w8} (hb : s.busy = .write t off data)
    (h : commitClean s.m s.bs) (hoff : off ≤ s.m.size) (hdl : off + data.length ≤ 2 ^ 30)
    (hmiss : ∀ k, (k < 8192 ∨ (4096 * curRoot ((s.bs.map Prod.fst).take 8192) ≤ k ∧
        k < 4096 * curRoot ((s.bs.map Prod.fst).take 8192) + 4096)) →
      k < cfLo s.m off ∨ cfHi s.m off data.length ≤ k) :
    FileOkS NoTearCrash Good i s :=
  fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; exact hoff) h.lo fun img hI =>
    commit_clean_img h (crashImg_lo hI)
      (by have h1 := hI.2.1; have h2 := h.hi; unfold CSt.vmeta at h1; rw [hb] at h1
          simp only [pwMeta] at h1; omega)
      (fun k b hb' hk => crashImg_clean hI hb' (CSt.taken_out _ _ fun _ _ _ h' => by
        rw [hb] at h'; cases h'; exact hmiss k hk))

/-- A commit's growing truncate in flight. -/
theorem commitClean_trunc_okS {t sz : Nat} (hb : s.busy = .trunc t sz) (h : commitClean s.m s.bs)
    (hsz : sz ≤ 2 ^ 30) : FileOkS NoTearCrash Good i s :=
  fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; trivial) h.lo fun img hI =>
    commit_clean_img h (crashImg_lo hI)
      (by have h1 := hI.2.1; have h2 := h.hi; unfold CSt.vmeta at h1; rw [hb] at h1
          simp only [ftMeta] at h1; omega)
      (fun k b hb' _ => crashImg_clean hI hb' (CSt.taken_out _ _ fun _ _ _ h => by rw [hb] at h; cases h))

/-- A commit's meta write in flight (the new meta page `data` at page `1 - sl`), while the
versions are known: the slot written is the durable copy's, the page cache's or the write's, each
the old meta or the new one. -/
theorem commitMetaW_okS {t sl : Nat} {data : List w8} {mp : List w8} {N : Meta}
    (hb : s.busy = .write t (4096 * (1 - sl)) data) (h : commitMetaSt s.m s.bs mp N sl)
    (hvk : ∃ ns, s.m.vk = some ns) (hsz : 4 * 4096 ≤ s.m.size)
    (hdl : data.length = 4096) (hR : 2 ≤ curRoot mp)
    (hd : durSlot s.m (1 - sl) (fun X => X = fileMeta mp (1 - sl) ∨ X = N))
    (hc : cacheSlot s.bs (1 - sl) (fun X => X = fileMeta mp (1 - sl) ∨ X = N))
    (hw : writeSlot s.bs (4096 * (1 - sl)) data (1 - sl)
      (fun X => X = fileMeta mp (1 - sl) ∨ X = N)) :
    FileOkS NoTearCrash Good i s := by
  have hs2 := h.s2
  have hNR := h.nRoot
  refine fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; omega) h.lo fun img hI => ?_
  have hlo := crashImg_lo hI
  have hlo4 := h.lo
  refine commitMeta_good h hlo
    (by have h1 := hI.2.1; have h2 := h.hi; unfold CSt.vmeta at h1; rw [hb] at h1
        simp only [pwMeta] at h1; rcases sl with _ | _ | sl <;> omega)
    (fun k b hb' hk => crashImg_clean hI hb' (CSt.taken_out _ _ fun _ _ _ h' => by
      rw [hb] at h'; cases h'
      simp only [cfLo, cfHi]
      rcases sl with _ | _ | sl <;> omega))
    (fun hv => crashImg_slot hI hwf.1 hvk (by omega) (by rcases sl with _ | _ | sl <;> omega)
      (by rcases sl with _ | _ | sl <;> omega) hd hc
      (fun _ _ _ h' => by rw [hb] at h'; cases h'; exact hw) hv)

/-- A commit's idle states after the meta write (or its failure, or a failed sync of it), while
the versions are known. -/
theorem commitMetaIdle_okS {mp : List w8} {N : Meta} {sl : Nat} (hb : s.busy = .idle)
    (h : commitMetaSt s.m s.bs mp N sl) (hvk : ∃ ns, s.m.vk = some ns) (hsz : 4 * 4096 ≤ s.m.size)
    (hd : durSlot s.m (1 - sl) (fun X => X = fileMeta mp (1 - sl) ∨ X = N))
    (hc : cacheSlot s.bs (1 - sl) (fun X => X = fileMeta mp (1 - sl) ∨ X = N)) :
    FileOkS NoTearCrash Good i s := by
  have hs2 := h.s2
  refine fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; trivial) h.lo fun img hI => ?_
  have hlo := crashImg_lo hI
  have hlo4 := h.lo
  refine commitMeta_good h hlo
    (by have h1 := hI.2.1; have h2 := h.hi; unfold CSt.vmeta at h1; rw [hb] at h1; dsimp only at h1; omega)
    (fun k b hb' _ => crashImg_clean hI hb' (CSt.taken_out _ _ fun _ _ _ h' => by
      rw [hb] at h'; cases h'))
    (fun hv => crashImg_slot hI hwf.1 hvk (by omega) (by rcases sl with _ | _ | sl <;> omega)
      (by rcases sl with _ | _ | sl <;> omega) hd hc
      (fun _ _ _ h' => by rw [hb] at h'; cases h') hv)

end states

/-- The namespace of the database file's crash invariant. -/
def dbCrashN : Namespace := nroot .@ "minibolt_crash"

/-- minibolt's obligation on the states of its file: every crash of the state is `Good`. -/
abbrev dbOk [GooseExts] : CState → Prop
  | none => True
  | some (i, s) => FileOkS NoTearCrash Good i s

end osfs_bboltfs
end EtcdGrove
end Perennial

end
