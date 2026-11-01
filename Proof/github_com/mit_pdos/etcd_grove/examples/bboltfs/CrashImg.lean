/- Lean-first (no Rocq counterpart). minibolt's crash obligations on images: for the states the
database file passes through during `init` and `commit`, every image a crash may leave
(`idleImg`, `writingImg`, `CrashOk.lean`) is `goodImg`.

**Slots.** A valid meta slot of the image is the durable image's, or the page cache's (idle: only
if no byte of the slot is clean), or the write's in flight. `durOk m i P` says what the durable
copy of slot `i` may be (`m.dur` knows it, or the durable image is too short to hold it,
`m.durHi`), `cacheOk bs i P` what the page cache's may be (a clean byte, or a meta satisfying
`P`); `idleImg_slot`/`writingImg_slot` conclude that a valid slot of the image satisfies `P`.

**init** (`initIdle`, `initWriting`): every slot the image may take is invalid (the old slots
were invalid, the first write zeroes them) or, once the metas are written, `init`'s meta (`P :=
(· = bInitMeta i)`), whose root page 3 is synced: `goodImg_noValid`, `goodImg_init`.

**commit** (`commitClean`, `commitMeta`): while the metas and the current root page are clean,
an image has them (`commit_clean`); while the meta slot `(T+1) % 2` is written, it is the old
slot or the new meta, whose root page is synced, and the current meta is in slot `T % 2`
(`curInSlot`), untouched: `commit_metas`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.CrashOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.InitLayout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open github_com.mit_pdos.etcd_grove.examples.bboltfs
open github_com.mit_pdos.etcd_grove.examples.bboltfs renaming initMeta → bInitMeta

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

/-- What the durable copy of slot `i` may be: the durable image is too short to hold it, or
`m.dur` knows it as `B`'s slot, which satisfies `P` if valid. -/
def durOk (m : OsMeta) (i : Nat) (P : Meta → Prop) : Prop :=
  m.durHi < 4096 * i + 80 ∨
  ∃ B : List w8, (∀ k < 64, ∃ b, B[4096 * i + 16 + k]? = some b ∧
      m.dur[4096 * i + 16 + k]? = some (some b)) ∧
    (metaValid (fileMeta B i) → P (fileMeta B i))

/-- `durOk` from durable bytes `m.dur` knows: those of `B`, up to the durable image's bound. -/
theorem durOk_of {m : OsMeta} {i : Nat} {P : Meta → Prop} (B : List w8)
    (hB : ∀ j b, B[j]? = some b → j < m.durHi → m.dur[j]? = some (some b))
    (hlen : m.durHi ≤ B.length)
    (hP : 4096 * i + 80 ≤ B.length → metaValid (fileMeta B i) → P (fileMeta B i)) :
    durOk m i P := by
  by_cases h : m.durHi < 4096 * i + 80
  · exact Or.inl h
  · refine Or.inr ⟨B, fun k hk => ?_, hP (by omega)⟩
    obtain ⟨b, hb⟩ : ∃ b, B[4096 * i + 16 + k]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    exact ⟨b, hb, hB _ _ hb (by omega)⟩

/-- What the page cache's slot `i` may be, idle: it has a clean byte (so a crash keeps no torn
copy of it), or it satisfies `P` if valid. -/
def cacheOk (bs : List (w8 × Bool)) (i : Nat) (P : Meta → Prop) : Prop :=
  4096 * i + 80 ≤ bs.length →
    (∃ k < 64, ∃ x, bs[4096 * i + 16 + k]? = some x ∧ x.2 = true) ∨
    (metaValid (fileMeta (bs.map Prod.fst) i) → P (fileMeta (bs.map Prod.fst) i))

theorem durOk_slot {m : OsMeta} {i : Nat} {P : Meta → Prop} {img D : List w8}
    (hD : ∀ (j : Nat) (d : w8), m.dur[j]? = some (some d) → D[j]? = some d)
    (hDl : D.length ≤ m.durHi) (h : durOk m i P) (heq : metaSlot img i = metaSlot D i)
    (hl : 4096 * i + 80 ≤ img.length) (hv : metaValid (fileMeta img i)) : P (fileMeta img i) := by
  rcases h with h | ⟨B, hB, hP⟩
  · have := slot_held heq hl; omega
  · have e : metaSlot D i = metaSlot B i := metaSlot_ext fun k hk => by
      obtain ⟨b, h1, h2⟩ := hB k hk
      rw [h1, hD _ _ h2]
    rw [fileMeta_of_slot (heq.trans e)] at hv ⊢
    exact hP hv

theorem idleImg_slot {m : OsMeta} {bs : List (w8 × Bool)} {img D : List w8} {i : Nat}
    {P : Meta → Prop} (h : idleImg m bs img D) (hd : durOk m i P) (hc : cacheOk bs i P)
    (hi : i < 2) (hl : 4096 * i + 80 ≤ img.length) (hv : metaValid (fileMeta img i)) :
    P (fileMeta img i) := by
  obtain ⟨-, -, -, hD, hDl, -, hs⟩ := h
  rcases hs i hi hl hv with heq | ⟨hnc, heq⟩
  · exact durOk_slot hD hDl hd heq hl hv
  · have hb := slot_held heq hl
    rw [List.length_map] at hb
    rcases hc hb with ⟨k, hk, x, hx, hxc⟩ | hP
    · rw [hnc k hk x hx] at hxc; cases hxc
    · rw [fileMeta_of_slot heq] at hv ⊢; exact hP hv

theorem writingImg_slot {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8}
    {img D : List w8} {i : Nat} {P : Meta → Prop} (h : writingImg m bs off data img D)
    (hd : durOk m i P)
    (hc : 4096 * i + 80 ≤ bs.length → metaValid (fileMeta (bs.map Prod.fst) i) →
      P (fileMeta (bs.map Prod.fst) i))
    (hw : metaValid (fileMeta (writeBytes (bs.map Prod.fst) off data) i) →
      P (fileMeta (writeBytes (bs.map Prod.fst) off data) i))
    (hi : i < 2) (hl : 4096 * i + 80 ≤ img.length) (hv : metaValid (fileMeta img i)) :
    P (fileMeta img i) := by
  obtain ⟨-, -, -, hD, hDl, -, hs⟩ := h
  rcases hs i hi hl hv with heq | heq | heq
  · exact durOk_slot hD hDl hd heq hl hv
  · have hb := slot_held heq hl
    rw [List.length_map] at hb
    rw [fileMeta_of_slot heq] at hv ⊢; exact hc hb hv
  · rw [fileMeta_of_slot heq] at hv ⊢; exact hw hv

/-- A clean byte of `bs` is the image's, idle... -/
theorem idleImg_clean {m : OsMeta} {bs : List (w8 × Bool)} {img D : List w8}
    (h : idleImg m bs img D) {k : Nat} {b : w8} (hk : bs[k]? = some (b, true)) : img[k]? = some b :=
  h.2.2.1 k _ hk rfl

/-- ... and outside the write's range, with a write in flight. -/
theorem writingImg_clean {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8}
    {img D : List w8} (h : writingImg m bs off data img D) {k : Nat} {b : w8}
    (hk : bs[k]? = some (b, true)) (hout : k < cfLo m off ∨ cfHi m off data.length ≤ k) :
    img[k]? = some b :=
  h.2.2.1 k _ hk rfl hout

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

/-! ## Good images -/

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
    (hb : bootOk X.txid'.toNat (pageVal ((img.drop (4096 * X.root'.root'.toNat)).take 4096))) :
    goodImg img := by
  have hc' : curMeta (imgMetas img) = X := by simp only [imgMetas]; rw [curMeta_take, hc]
  refine ⟨hl, Or.inr (Or.inr ⟨h16, ⟨by simp; omega, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩)⟩
  · simp only [imgMetas]
    rw [fileMeta_take _ _ 0 (by omega), fileMeta_take _ _ 1 (by omega)]; exact hv
  all_goals simp only [curRoot, curPgid, hc']
  all_goals assumption

/-! ## init -/

/-- `init`'s metas, read back from an image whose slots are invalid or `init`'s and whose page 3
is `init`'s root page: a good image. -/
theorem goodImg_init {img : List w8} (h16 : 4 * 4096 ≤ img.length) (hl : img.length ≤ 2 ^ 30)
    (hs : ∀ i < 2, metaValid (fileMeta img i) → fileMeta img i = bInitMeta i)
    (h3 : (img.drop (4096 * 3)).take 4096 = emptyPageBytes (W64 3) (W16 2)) : goodImg img := by
  by_cases hv : metaValid (fileMeta img 0) ∨ metaValid (fileMeta img 1)
  · have hX : ∃ i < 2, curMeta img = bInitMeta i := by
      rcases curMeta_cases img hv with ⟨e, v⟩ | ⟨e, v⟩
      · exact ⟨0, by omega, e.trans (hs 0 (by omega) v)⟩
      · exact ⟨1, by omega, e.trans (hs 1 (by omega) v)⟩
    obtain ⟨i, hi, hc⟩ := hX
    refine goodImg_cur h16 hl hc hv ?_ ?_ ?_ ?_ ?_ <;>
      simp only [initMeta_root, initMeta_pgid, initMeta_txid]
    · decide
    · decide
    · decide
    · show 4096 * 4 ≤ img.length; omega
    · rw [show (W64 3).toNat = 3 from rfl, h3, initRoot_val]
      refine Or.inl ⟨?_, rfl⟩
      rcases i with _ | _ | i
      · decide
      · decide
      · omega
  · exact goodImg_noValid hl fun i hi _ hv' => hv (by
      rcases i with _ | _ | i
      · exact Or.inl hv'
      · exact Or.inr hv'
      · omega)

/-- The durable copy and the page cache of every slot are invalid (or not held whole, or with a
clean byte): `init`'s states before its metas are written. -/
structure initIdle (m : OsMeta) (bs : List (w8 × Bool)) : Prop where
  hi : m.hi ≤ 2 ^ 30
  dur : ∀ i < 2, durOk m i (fun _ => False)
  cache : ∀ i < 2, cacheOk bs i (fun _ => False)

theorem initIdle_good {m : OsMeta} {bs : List (w8 × Bool)} (h : initIdle m bs) :
    ∀ img D, idleImg m bs img D → goodImg img := by
  intro img D hI
  refine goodImg_noValid (by have := hI.2.1; have := h.hi; omega) fun i hi hl hv => ?_
  exact idleImg_slot hI (h.dur i hi) (h.cache i hi) hi hl hv

/-- `init`'s first write in flight: the data zeroes both slots. -/
theorem initW1_good {m : OsMeta} {bs : List (w8 × Bool)} {data : List w8}
    (hhi : m.hi ≤ 2 ^ 30) (hdl : data.length ≤ 2 ^ 30)
    (hdur : ∀ i < 2, durOk m i (fun _ => False))
    (hcache : ∀ i < 2, 4096 * i + 80 ≤ bs.length → ¬ metaValid (fileMeta (bs.map Prod.fst) i))
    (hz : ∀ k < 8192, data[k]? = some 0) :
    ∀ img D, writingImg m bs 0 data img D → goodImg img := by
  intro img D hW
  have hne : data ≠ [] := by
    intro h; have := hz 0 (by omega); rw [h] at this; cases this
  refine goodImg_noValid (by have := hW.2.1; omega) fun i hi hl hv => ?_
  refine writingImg_slot hW (hdur i hi) (fun hb hv' => hcache i hi hb hv') (fun hv' => ?_) hi hl hv
  refine slot_zero_invalid (fun k hk => ?_) hv'
  unfold writeBytes
  rw [if_neg hne]
  simp only [List.take_zero, List.nil_append, Nat.zero_add]
  have hk' := hz (4096 * i + 16 + k) (by omega)
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk').1]
  exact hk'

/-- After the first sync, before the metas are written: the slots are zero on disk, `m.dur`
knows them, and `init`'s pages 2–3 are clean in the page cache. The meta write in flight, or
after it (idle, with `cacheOk` for `init`'s metas), leaves good images. -/
structure initMid (m : OsMeta) (bs : List (w8 × Bool)) : Prop where
  hi : m.hi ≤ 2 ^ 30
  lo : 4 * 4096 ≤ m.lo
  dur : ∀ i < 2, durOk m i (fun X => X = bInitMeta i)
  page3 : ∀ k < 4096, bs[4096 * 3 + k]? =
    some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0, true)

theorem initMid_page3 {m : OsMeta} {bs : List (w8 × Bool)} (h : initMid m bs) {img : List w8}
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

theorem initMid_idle_good {m : OsMeta} {bs : List (w8 × Bool)} (h : initMid m bs)
    (hc : ∀ i < 2, cacheOk bs i (fun X => X = bInitMeta i)) :
    ∀ img D, idleImg m bs img D → goodImg img := by
  intro img D hI
  have hlo := hI.1
  have hlo' := h.lo
  refine goodImg_init (by have := h.lo; omega) (by have := hI.2.1; have := h.hi; omega)
    (fun i hi hv => idleImg_slot hI (h.dur i hi) (hc i hi) hi (by omega) hv) ?_
  exact initMid_page3 h fun k _ hb => idleImg_clean hI hb

theorem initW2_good {m : OsMeta} {bs : List (w8 × Bool)} {data : List w8} (h : initMid m bs)
    (hdl : data.length ≤ 4096 * 3) (hsz : 4 * 4096 ≤ m.size)
    (hc : ∀ i < 2, 4096 * i + 80 ≤ bs.length → metaValid (fileMeta (bs.map Prod.fst) i) →
      fileMeta (bs.map Prod.fst) i = bInitMeta i)
    (hw : ∀ i < 2, metaValid (fileMeta (writeBytes (bs.map Prod.fst) 0 data) i) →
      fileMeta (writeBytes (bs.map Prod.fst) 0 data) i = bInitMeta i) :
    ∀ img D, writingImg m bs 0 data img D → goodImg img := by
  intro img D hW
  have hlo := hW.1
  have hlo' := h.lo
  refine goodImg_init (by have := h.lo; omega)
    (by have := hW.2.1; have := h.hi; omega)
    (fun i hi hv => writingImg_slot hW (h.dur i hi) (hc i hi) (hw i hi) hi (by omega) hv) ?_
  exact initMid_page3 h fun k _ hb => writingImg_clean hW hb
    (.inr (by simp only [cfHi]; omega))

/-! ## commit -/

/-- The current meta of the meta pages `mp` is in slot `txid % 2`, where `commit` never writes. -/
def curInSlot (mp : List w8) : Prop :=
  curMeta mp = fileMeta mp ((curMeta mp).txid'.toNat % 2)

/-- What a commit's crash images need of the state while the metas and the current root page are
clean (every step before the meta write): `bs`'s meta pages `mp` are an open database's, whose
current meta's root page holds what `BootMinibolt` checks, and the size since the last sync covers
the high water mark. -/
structure commitClean (m : OsMeta) (bs : List (w8 × Bool)) : Prop where
  hi : m.hi ≤ 2 ^ 30
  lo : 4 * 4096 ≤ m.lo
  ok : metaPagesOk ((bs.map Prod.fst).take 8192)
  pg : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ m.lo
  boot : bootOk (curMeta ((bs.map Prod.fst).take 8192)).txid'.toNat
    (pageVal (((bs.map Prod.fst).drop (4096 * curRoot ((bs.map Prod.fst).take 8192))).take 4096))
  metas : ∀ k < 8192, ∃ b, bs[k]? = some (b, true)
  root : ∀ k < 4096, ∃ b, bs[4096 * curRoot ((bs.map Prod.fst).take 8192) + k]? = some (b, true)

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
  have hlen : ((bs.map Prod.fst).take 8192).length = 8192 := hok.1
  have hbl : 8192 ≤ (bs.map Prod.fst).length := by rw [List.length_take] at hlen; omega
  generalize hmp : (bs.map Prod.fst).take 8192 = mp at hok hpg hboot hroot hcl
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
    exact hboot

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
structure commitMeta (m : OsMeta) (bs : List (w8 × Bool)) (mp : List w8) (N : Meta)
    (s : Nat) : Prop where
  s2 : s < 2
  hi : m.hi ≤ 2 ^ 30
  lo : 4 * 4096 ≤ m.lo
  ok : metaPagesOk mp
  slot : curMeta mp = fileMeta mp s
  pg : 4096 * curPgid mp ≤ m.lo
  boot : bootOk (curMeta mp).txid'.toNat
    (pageVal (((bs.map Prod.fst).drop (4096 * curRoot mp)).take 4096))
  root : ∀ k < 4096, ∃ b, bs[4096 * curRoot mp + k]? = some (b, true)
  metaS : ∀ k < 64, ∃ b, mp[4096 * s + 16 + k]? = some b ∧ bs[4096 * s + 16 + k]? = some (b, true)
  nValid : metaValid N
  nTx : uint.Z (curMeta mp).txid' < uint.Z N.txid'
  nRoot : 2 ≤ N.root'.root'.toNat
  nRootPg : N.root'.root'.toNat < N.pgid'.toNat
  nPg : (N.pgid'.toNat + 1) * 4096 ≤ 2 ^ 30
  nPgLo : 4096 * N.pgid'.toNat ≤ m.lo
  nBoot : bootOk N.txid'.toNat
    (pageVal (((bs.map Prod.fst).drop (4096 * N.root'.root'.toNat)).take 4096))
  nPage : ∀ k < 4096, ∃ b, bs[4096 * N.root'.root'.toNat + k]? = some (b, true)
  dur : durOk m (1 - s) (fun X => X = fileMeta mp (1 - s) ∨ X = N)

theorem commitMeta_good {m : OsMeta} {bs : List (w8 × Bool)} {mp : List w8} {N : Meta} {s : Nat}
    (h : commitMeta m bs mp N s) {img : List w8} (hlo : m.lo ≤ img.length)
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
    show bootOk _ (pageVal ((img.drop (4096 * curRoot mp)).take 4096))
    rw [hpage _ h.root (fun k h1 h2 b hb => hcl k b hb (.inr (.inl ⟨h1, h2⟩)))]
    exact h.boot
  · have hvN : metaValid (fileMeta img 0) ∨ metaValid (fileMeta img 1) := by
      rcases s with _ | _ | s
      · exact Or.inl (hM ▸ hMv)
      · exact Or.inr (hM ▸ hMv)
      · omega
    refine goodImg_cur (by have := h.lo; omega) hhi hc hvN h.nRoot h.nRootPg h.nPg
      (by have := h.nPgLo; omega) ?_
    rw [hpage _ h.nPage (fun k h1 h2 b hb => hcl k b hb (.inr (.inr ⟨h1, h2⟩)))]
    exact h.nBoot

/-- The meta write in flight (`data`, the new meta page, at `4096 * (1 - s)`): good images. -/
theorem commitMetaW_good {m : OsMeta} {bs : List (w8 × Bool)} {mp : List w8} {N : Meta} {s : Nat}
    {data : List w8} (h : commitMeta m bs mp N s) (hdl : data.length = 4096)
    (hhi : 4096 * (1 - s) + 4096 ≤ 2 ^ 30)
    (hR : 2 ≤ curRoot mp)
    (hc : 4096 * (1 - s) + 80 ≤ bs.length → metaValid (fileMeta (bs.map Prod.fst) (1 - s)) →
      fileMeta (bs.map Prod.fst) (1 - s) = fileMeta mp (1 - s) ∨
        fileMeta (bs.map Prod.fst) (1 - s) = N)
    (hw : fileMeta (writeBytes (bs.map Prod.fst) (4096 * (1 - s)) data) (1 - s) = N) :
    ∀ img D, writingImg m bs (4096 * (1 - s)) data img D → goodImg img := by
  intro img D hW
  have hs2 := h.s2
  have hlo := hW.1
  have hhi' := hW.2.1
  have hNR := h.nRoot
  refine commitMeta_good h hlo (by have := h.hi; omega) (fun k b hb hk => ?_) (fun hv => ?_)
  · refine writingImg_clean hW hb ?_
    simp only [cfLo, cfHi]
    rcases s with _ | _ | s <;> omega
  · exact writingImg_slot hW h.dur hc (fun _ => .inr hw) (by omega) (by
      have := h.lo; rcases s with _ | _ | s <;> omega) hv

/-- After the meta write, or its failure, or a failed sync of it (idle): good images, if each
slot of the page cache with no clean byte is the old or the new meta. -/
theorem commitMetaIdle_good {m : OsMeta} {bs : List (w8 × Bool)} {mp : List w8} {N : Meta}
    {s : Nat} (h : commitMeta m bs mp N s)
    (hc : cacheOk bs (1 - s) (fun X => X = fileMeta mp (1 - s) ∨ X = N)) :
    ∀ img D, idleImg m bs img D → goodImg img := by
  intro img D hI
  have hs2 := h.s2
  have hlo := hI.1
  refine commitMeta_good h hlo (by have := hI.2.1; have := h.hi; omega)
    (fun k b hb _ => idleImg_clean hI hb) (fun hv => ?_)
  exact idleImg_slot hI h.dur hc (by omega) (by have := h.lo; rcases s with _ | _ | s <;> omega) hv

end pure

end bboltfs
end EtcdGrove
end Perennial
