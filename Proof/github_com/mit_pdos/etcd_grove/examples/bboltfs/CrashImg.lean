/- Lean-first (no Rocq counterpart). minibolt's crash obligations on images: for the states the
database file passes through during `init` and `commit`, every image a crash may leave
(`idleImg`, `writingImg`, `CrashOk.lean`) is `goodImg`.

**Slots.** A valid meta slot of the image is the durable image's, or the page cache's (only
if no byte of the slot is clean, in flight too), or the write's in flight. `durOk m i P` says what the durable
copy of slot `i` may be (`m.dur` knows it, or the durable image is too short to hold it,
`m.durHi`), `cacheOk bs i P` what the page cache's may be (a clean byte, or a meta satisfying
`P`); `idleImg_slot`/`writingImg_slot` conclude that a valid slot of the image satisfies `P`.

**init** (`initIdle`, then `initMid ph`): every slot the image may take is invalid (the old
slots were invalid, the first write zeroes them) or, once the metas are written, `init`'s meta
(`P := (· = bInitMeta i)`), whose root page 3 is synced: `goodImg_noValid`, `goodImg_init`. Meta 1
is written and synced (phase `false`, slot 0 clean and zero) before meta 0 (phase `true`, slot 1
clean and `init`'s): a valid slot 0 comes with a valid slot 1 (`initOrd`), so the current meta is
meta 1, txid 1, never txid 0.

**commit** (`commitClean`, `commitMetaSt`): while the metas and the current root page are clean,
an image has them (`commit_clean`); while the meta slot `(T+1) % 2` is written, it is the old
slot or the new meta, whose root page is synced, and the current meta is in slot `T % 2`
(`curInSlot`), untouched: `commit_metas`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.CrashOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.InitLayout
public import Proof.os.CrashWReach

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

/-- `cacheOk` of every state a retried write covering slot `i` reaches, from a state whose bytes
of the slot are all clean: a partly written slot keeps a clean old byte, or is all the new data,
which satisfies `P` if valid. -/
theorem cacheOk_wreach {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {off : Nat} {data : List w8}
    {i : Nat} {P : Meta → Prop} (h : WReach m bs off data m' bs') (hl : bs.length = m.size)
    (ha : off ≤ 4096 * i + 16) (haw : 4096 * i + 80 ≤ off + data.length)
    (hcl : ∀ k < 64, ∀ x, bs[4096 * i + 16 + k]? = some x → x.2 = true)
    (hP : ∀ L : List w8, (∀ k < 64, L[4096 * i + 16 + k]? =
        some (data.getD (4096 * i + 16 + k - off) 0)) →
      metaValid (fileMeta L i) → P (fileMeta L i)) :
    cacheOk bs' i P := by
  intro hlen
  rcases h.torn hl (a := 4096 * i + 16) (w := 64) (by omega) ha (by omega) (by omega) with
    ⟨hin, heq⟩ | ⟨-, ⟨j, hj, hjl, heq⟩ | hall⟩
  · obtain ⟨x, hx⟩ : ∃ x, bs[4096 * i + 16 + 0]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    exact .inl ⟨0, by omega, x, by rw [heq 0 (by omega)]; exact hx, hcl 0 (by omega) x hx⟩
  · obtain ⟨x, hx⟩ : ∃ x, bs[4096 * i + 16 + j]? = some x :=
      ⟨_, List.getElem?_eq_getElem hjl⟩
    exact .inl ⟨j, hj, x, by rw [heq]; exact hx, hcl j hj x hx⟩
  · exact .inr (hP _ fun k hk => by rw [List.getElem?_map, hall k hk]; rfl)

/-- `hP` of `cacheOk_wreach` from the write's slot (`writeBytes`). -/
theorem slot_data_write {bs : List w8} {off : Nat} {data : List w8} {i : Nat} {L : List w8}
    (ha : off ≤ 4096 * i + 16) (haw : 4096 * i + 80 ≤ off + data.length)
    (hL : ∀ k < 64, L[4096 * i + 16 + k]? = some (data.getD (4096 * i + 16 + k - off) 0)) :
    fileMeta L i = fileMeta (writeBytes bs off data) i := by
  have hne : data ≠ [] := by intro h; simp [h] at haw; omega
  refine fileMeta_of_slot (metaSlot_ext fun k hk => ?_)
  rw [hL k hk, writeBytes_getElem? _ _ _ hne, if_neg (by omega), if_pos (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

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
    (hd : durOk m i P) (hc : cacheOk bs i P)
    (hw : metaValid (fileMeta (writeBytes (bs.map Prod.fst) off data) i) →
      P (fileMeta (writeBytes (bs.map Prod.fst) off data) i))
    (hi : i < 2) (hl : 4096 * i + 80 ≤ img.length) (hv : metaValid (fileMeta img i)) :
    P (fileMeta img i) := by
  obtain ⟨-, -, -, hD, hDl, -, hs⟩ := h
  rcases hs i hi hl hv with heq | ⟨hnc, heq⟩ | heq
  · exact durOk_slot hD hDl hd heq hl hv
  · have hb := slot_held heq hl
    rw [List.length_map] at hb
    rcases hc hb with ⟨k, hk, x, hx, hxc⟩ | hP
    · rw [hnc k hk x hx] at hxc; cases hxc
    · rw [fileMeta_of_slot heq] at hv ⊢; exact hP hv
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

/-- A retried write keeps what `m.dur` knows and its bound. -/
theorem wreach_dur {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {off : Nat} {data : List w8}
    (h : WReach m bs off data m' bs') : m'.dur = m.dur ∧ m'.durHi = m.durHi := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | step k _ _ ih => exact ih

theorem durOk_congr {m m' : OsMeta} {i : Nat} {P : Meta → Prop} (h1 : m'.dur = m.dur)
    (h2 : m'.durHi = m.durHi) (h : durOk m i P) : durOk m' i P := by
  unfold durOk; rw [h1, h2]; exact h

/-- `init`'s first write, retried: every state it reaches is `initIdle`, from one whose bytes of
the slots are clean (the file as `Open` found it), since the data zeroes the slots. -/
theorem initIdle_wreach {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {data : List w8}
    (h : initIdle m bs) (hl : bs.length = m.size) (hR : WReach m bs 0 data m' bs')
    (hcl : ∀ i < 2, ∀ k < 64, ∀ x, bs[4096 * i + 16 + k]? = some x → x.2 = true)
    (hdl : 8192 ≤ data.length) (hdl' : data.length ≤ 2 ^ 30)
    (hz : ∀ k < 8192, data[k]? = some 0) : initIdle m' bs' := by
  obtain ⟨hd1, hd2⟩ := wreach_dur hR
  refine ⟨by have := (hR.narrow hl).hi; have := h.hi; omega,
    fun i hi => durOk_congr hd1 hd2 (h.dur i hi), fun i hi => ?_⟩
  refine cacheOk_wreach hR hl (by omega) (by omega) (hcl i hi) fun L hL hv => ?_
  refine slot_zero_invalid (fun k hk => ?_) hv
  rw [hL k hk, List.getD_eq_getElem?_getD, Nat.sub_zero, hz _ (by omega)]; rfl

/-- `init`'s first write in flight: the data zeroes both slots. -/
theorem initW1_good {m : OsMeta} {bs : List (w8 × Bool)} {data : List w8}
    (hhi : m.hi ≤ 2 ^ 30) (hdl : data.length ≤ 2 ^ 30)
    (hdur : ∀ i < 2, durOk m i (fun _ => False))
    (hcache : ∀ i < 2, cacheOk bs i (fun _ => False))
    (hz : ∀ k < 8192, data[k]? = some 0) :
    ∀ img D, writingImg m bs 0 data img D → goodImg img := by
  intro img D hW
  have hne : data ≠ [] := by
    intro h; have := hz 0 (by omega); rw [h] at this; cases this
  refine goodImg_noValid (by have := hW.2.1; omega) fun i hi hl hv => ?_
  refine writingImg_slot hW (hdur i hi) (hcache i hi) (fun hv' => ?_) hi hl hv
  refine slot_zero_invalid (fun k hk => ?_) hv'
  unfold writeBytes
  rw [if_neg hne]
  simp only [List.take_zero, List.nil_append, Nat.zero_add]
  have hk' := hz (4096 * i + 16 + k) (by omega)
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk').1]
  exact hk'

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

/-- An image with the other slot's `initOrdByte`s has slot 0 valid only if slot 1 is. -/
theorem initOrd_img {ph : Bool} {img : List w8}
    (h : ∀ k < 64, img[4096 * (1 - initSlot ph) + 16 + k]? =
      some (initOrdByte ph (4096 * (1 - initSlot ph) + 16 + k))) :
    metaValid (fileMeta img 0) → metaValid (fileMeta img 1) := by
  cases ph with
  | false =>
    intro hv
    refine absurd hv (slot_zero_invalid (i := 0) fun k hk => ?_)
    have := h k hk
    simp only [initSlot, initOrdByte] at this
    exact this
  | true =>
    intro _
    have hil := initBytes_length
    simp only [pageBytes] at hil
    have e : fileMeta img 1 = fileMeta initBytes 1 := fileMeta_of_slot (metaSlot_ext fun k hk => by
      have := h k hk
      simp only [initSlot, initOrdByte] at this
      rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl)
    rw [e, initBytes_meta1]; exact initMeta_valid 1

theorem initOrd_clean {ph : Bool} {bs : List (w8 × Bool)} {img : List w8} (h : initOrd ph bs)
    (himg : ∀ k b, bs[k]? = some (b, true) → 4096 * (1 - initSlot ph) + 16 ≤ k →
      k < 4096 * (1 - initSlot ph) + 80 → img[k]? = some b) :
    metaValid (fileMeta img 0) → metaValid (fileMeta img 1) :=
  initOrd_img fun k hk => himg _ _ (h k hk) (by omega) (by omega)

/-- After the first sync, before the metas are written, in phase `ph`: the slots are zero or
`init`'s on disk, `m.dur` knows them, `init`'s page 3 and the slot not being written
(`initOrd`) are clean in the page cache. A meta write in flight, or after it (idle, with
`cacheOk` for `init`'s metas), leaves good images. -/
structure initMid (ph : Bool) (m : OsMeta) (bs : List (w8 × Bool)) : Prop where
  hi : m.hi ≤ 2 ^ 30
  lo : 4 * 4096 ≤ m.lo
  dur : ∀ i < 2, durOk m i (fun X => X = bInitMeta i)
  page3 : ∀ k < 4096, bs[4096 * 3 + k]? =
    some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0, true)
  ord : initOrd ph bs

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

/-- A meta write of phase `ph` (page `initSlot ph`, retried) keeps the bytes of the other slot
and of page 3. -/
theorem initW_keeps {ph : Bool} {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {data : List w8}
    (hl : bs.length = m.size) (hR : WReach m bs (4096 * initSlot ph) data m' bs')
    (hdl : data.length = 4096) (hsz : 4 * 4096 ≤ m.size) :
    (∀ k < 64, bs'[4096 * (1 - initSlot ph) + 16 + k]? = bs[4096 * (1 - initSlot ph) + 16 + k]?) ∧
    ∀ k, 8192 ≤ k → bs'[k]? = bs[k]? := by
  have hN := hR.narrow hl
  refine ⟨fun k hk => ?_, fun k hk => hN.suf (by cases ph <;> simp [initSlot] <;> omega) _
    (by cases ph <;> simp [initSlot] <;> omega)⟩
  cases ph with
  | false => exact hN.pre _ (by simp only [cfLo, initSlot]; omega)
  | true => exact hN.suf (by simp [initSlot]; omega) _ (by simp [initSlot]; omega)

/-- `init`'s meta write of phase `ph`, retried: every state it reaches is `initMid ph`. -/
theorem initMid_wreach {ph : Bool} {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {data : List w8}
    (h : initMid ph m bs) (hl : bs.length = m.size)
    (hR : WReach m bs (4096 * initSlot ph) data m' bs')
    (hdl : data.length = 4096) (hsz : 4 * 4096 ≤ m.size) : initMid ph m' bs' := by
  obtain ⟨hd1, hd2⟩ := wreach_dur hR
  have hN := hR.narrow hl
  obtain ⟨ho, h3⟩ := initW_keeps hl hR hdl hsz
  refine ⟨by have := hN.hi; have := h.hi; cases ph <;> simp [initSlot] at this ⊢ <;> omega,
    by rw [hN.lo]; exact h.lo, fun i hi => durOk_congr hd1 hd2 (h.dur i hi), fun k hk => ?_,
    fun k hk => ?_⟩
  · rw [h3 _ (by omega)]; exact h.page3 k hk
  · rw [ho k hk]; exact h.ord k hk

/-- A successful sync of the whole file, with `init`'s page 3, slots that are invalid or
`init`'s metas, and the other slot of phase `ph` as `initOrd` says (all of `init`'s syncs), leaves
an `initMid ph` state, all clean. -/
theorem initMid_synced {ph : Bool} {m : OsMeta} {bs : List (w8 × Bool)} (hok : m.ok = true)
    (hl : bs.length = m.size) (hlo : 4 * 4096 ≤ m.size) (hhi : m.size ≤ 2 ^ 30)
    (hs : ∀ i < 2, metaValid (fileMeta (bs.map Prod.fst) i) →
      fileMeta (bs.map Prod.fst) i = bInitMeta i)
    (h3 : ∀ k < 4096, (bs[4096 * 3 + k]?).map Prod.fst =
      some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0))
    (hord : initOrd ph (bs.map fun x => (x.1, true))) :
    initMid ph (m.synced 0 bs) (syncedBytes m bs) ∧
      ∀ i < 2, cacheOk (syncedBytes m bs) i (fun X => X = bInitMeta i) := by
  have hsb : syncedBytes m bs = bs.map (fun x => (x.1, true)) := by simp [syncedBytes, hok]
  refine ⟨⟨by simp [OsMeta.synced]; omega, by simp [OsMeta.synced]; omega, fun i hi => ?_,
    fun k hk => ?_, by rw [hsb]; exact hord⟩, fun i hi hlen => ?_⟩
  · refine durOk_of (bs.map Prod.fst) (fun j b hb _ => ?_) (by simp [OsMeta.synced, hl])
      (fun _ hv => hs i hi hv)
    simp only [OsMeta.synced, hok, if_true, durOf, List.replicate_zero, List.nil_append,
      List.getElem?_map] at hb ⊢
    cases hx : bs[j]? with
    | none => rw [hx] at hb; cases hb
    | some x => rw [hx] at hb; simp only [Option.map_some, Option.some.injEq] at hb ⊢; rw [hb]
  · have := h3 k hk
    rw [hsb, List.getElem?_map]
    cases hx : bs[4096 * 3 + k]? with
    | none => rw [hx] at this; cases this
    | some x => rw [hx] at this; simp only [Option.map_some, Option.some.injEq] at this ⊢; rw [this]
  · rw [hsb] at hlen ⊢
    simp only [List.length_map] at hlen
    exact .inl ⟨0, by omega, _, by rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)]; rfl, rfl⟩

theorem initMid_idle_good {ph : Bool} {m : OsMeta} {bs : List (w8 × Bool)} (h : initMid ph m bs)
    (hc : ∀ i < 2, cacheOk bs i (fun X => X = bInitMeta i)) :
    ∀ img D, idleImg m bs img D → goodImg img := by
  intro img D hI
  have hlo := hI.1
  have hlo' := h.lo
  refine goodImg_init (by have := h.lo; omega) (by have := hI.2.1; have := h.hi; omega)
    (fun i hi hv => idleImg_slot hI (h.dur i hi) (hc i hi) hi (by omega) hv)
    (initOrd_clean h.ord fun k b hb _ _ => idleImg_clean hI hb) ?_
  exact initMid_page3 h fun k _ hb => idleImg_clean hI hb

theorem initW_good {ph : Bool} {m : OsMeta} {bs : List (w8 × Bool)} {data : List w8}
    (h : initMid ph m bs) (hdl : data.length = 4096) (hsz : 4 * 4096 ≤ m.size)
    (hc : ∀ i < 2, cacheOk bs i (fun X => X = bInitMeta i))
    (hw : ∀ i < 2, metaValid (fileMeta (writeBytes (bs.map Prod.fst) (4096 * initSlot ph) data) i) →
      fileMeta (writeBytes (bs.map Prod.fst) (4096 * initSlot ph) data) i = bInitMeta i) :
    ∀ img D, writingImg m bs (4096 * initSlot ph) data img D → goodImg img := by
  intro img D hW
  have hlo := hW.1
  have hlo' := h.lo
  refine goodImg_init (by have := h.lo; omega)
    (by have := hW.2.1; have := h.hi; cases ph <;> simp [initSlot] at this ⊢ <;> omega)
    (fun i hi hv => writingImg_slot hW (h.dur i hi) (hc i hi) (hw i hi) hi (by omega) hv)
    (initOrd_clean h.ord fun k b hb h1 h2 => writingImg_clean hW hb (by
      cases ph
      · exact .inl (by simp only [cfLo, initSlot] at h1 h2 ⊢; omega)
      · exact .inr (by simp only [cfHi, initSlot] at h1 h2 ⊢; omega))) ?_
  exact initMid_page3 h fun k _ hb => writingImg_clean hW hb
    (.inr (by simp only [cfHi]; cases ph <;> simp [initSlot] <;> omega))

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
  dur : durOk m (1 - s) (fun X => X = fileMeta mp (1 - s) ∨ X = N)

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

/-- The meta write in flight (`data`, the new meta page, at `4096 * (1 - s)`): good images. -/
theorem commitMetaW_good {m : OsMeta} {bs : List (w8 × Bool)} {mp : List w8} {N : Meta} {s : Nat}
    {data : List w8} (h : commitMetaSt m bs mp N s) (hdl : data.length = 4096)
    (hhi : 4096 * (1 - s) + 4096 ≤ 2 ^ 30)
    (hR : 2 ≤ curRoot mp)
    (hc : cacheOk bs (1 - s) (fun X => X = fileMeta mp (1 - s) ∨ X = N))
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
    {s : Nat} (h : commitMetaSt m bs mp N s)
    (hc : cacheOk bs (1 - s) (fun X => X = fileMeta mp (1 - s) ∨ X = N)) :
    ∀ img D, idleImg m bs img D → goodImg img := by
  intro img D hI
  have hs2 := h.s2
  have hlo := hI.1
  refine commitMeta_good h hlo (by have := hI.2.1; have := h.hi; omega)
    (fun k b hb _ => idleImg_clean hI hb) (fun hv => ?_)
  exact idleImg_slot hI h.dur hc (by omega) (by have := h.lo; rcases s with _ | _ | s <;> omega) hv

/-! ### As obligations on the states of the crash invariant (`Proof/os/CrashSt.lean`) -/

section states
variable {p : GoString} (s : CSt) (hl : s.bs.length = s.m.size)
include hl

/-- `init`'s idle states (Open's, W1's narrowings, S1 and its failure). -/
theorem initIdle_okS (hb : s.busy = .idle) (h : initIdle s.m s.bs) :
    CrashOkS (P1 p) p Good (some s) :=
  crashOkS_idle s hb (crashOkQ_idle hl (initIdle_good h))

/-- `init`'s first write in flight. -/
theorem initW1_okS {t : Nat} {data : List w8} (hb : s.busy = .write t 0 data)
    (hhi : s.m.hi ≤ 2 ^ 30) (hdl : data.length ≤ 2 ^ 30)
    (hdur : ∀ i < 2, durOk s.m i (fun _ => False))
    (hcache : ∀ i < 2, cacheOk s.bs i (fun _ => False))
    (hz : ∀ k < 8192, data[k]? = some 0) : CrashOkS (P1 p) p Good (some s) :=
  crashOkS_write s hb hl (crashOkQ_writing hl (initW1_good hhi hdl hdur hcache hz))

/-- `init`'s idle states after S1 (the meta writes' narrowings, S2, S3, failures). -/
theorem initMid_okS {ph : Bool} (hb : s.busy = .idle) (h : initMid ph s.m s.bs)
    (hc : ∀ i < 2, cacheOk s.bs i (fun X => X = bInitMeta i)) : CrashOkS (P1 p) p Good (some s) :=
  crashOkS_idle s hb (crashOkQ_idle hl (initMid_idle_good h hc))

/-- `init`'s meta write of phase `ph` in flight. -/
theorem initW_okS {ph : Bool} {t : Nat} {data : List w8}
    (hb : s.busy = .write t (4096 * initSlot ph) data) (h : initMid ph s.m s.bs)
    (hdl : data.length = 4096) (hsz : 4 * 4096 ≤ s.m.size)
    (hc : ∀ i < 2, cacheOk s.bs i (fun X => X = bInitMeta i))
    (hw : ∀ i < 2,
      metaValid (fileMeta (writeBytes (s.bs.map Prod.fst) (4096 * initSlot ph) data) i) →
      fileMeta (writeBytes (s.bs.map Prod.fst) (4096 * initSlot ph) data) i = bInitMeta i) :
    CrashOkS (P1 p) p Good (some s) :=
  crashOkS_write s hb hl (crashOkQ_writing hl (initW_good h hdl hsz hc hw))

/-- A commit's idle states before the meta write. -/
theorem commitClean_okS (hb : s.busy = .idle) (h : commitClean s.m s.bs) :
    CrashOkS (P1 p) p Good (some s) :=
  crashOkS_idle s hb (crashOkQ_idle hl fun img D hI =>
    commit_clean_img h hI.1 (by have := hI.2.1; have := h.hi; omega)
      (fun k b hb' _ => idleImg_clean hI hb'))

/-- A commit's writes before the meta write (the data page), in flight: they miss the metas and
the current root page. -/
theorem commitClean_write_okS {t off : Nat} {data : List w8} (hb : s.busy = .write t off data)
    (h : commitClean s.m s.bs) (hdl : off + data.length ≤ 2 ^ 30)
    (hmiss : ∀ k, (k < 8192 ∨ (4096 * curRoot ((s.bs.map Prod.fst).take 8192) ≤ k ∧
        k < 4096 * curRoot ((s.bs.map Prod.fst).take 8192) + 4096)) →
      k < cfLo s.m off ∨ cfHi s.m off data.length ≤ k) :
    CrashOkS (P1 p) p Good (some s) :=
  crashOkS_write s hb hl (crashOkQ_writing hl fun img D hW =>
    commit_clean_img h hW.1 (by have := hW.2.1; have := h.hi; omega)
      (fun k b hb' hk => writingImg_clean hW hb' (hmiss k hk)))

/-- A commit's growing truncate in flight. -/
theorem commitClean_trunc_okS {t sz : Nat} (hb : s.busy = .trunc t sz) (h : commitClean s.m s.bs)
    (hsz : sz ≤ 2 ^ 30) : CrashOkS (P1 p) p Good (some s) :=
  crashOkS_trunc s hb hl fun img D hI =>
    commit_clean_img h hI.1 (by have := hI.2.1; have := h.hi; simp only [ftMeta] at *; omega)
      (fun k b hb' _ => idleImg_clean hI hb')

/-- A commit's meta write in flight. -/
theorem commitMetaW_okS {t sl : Nat} {data : List w8} {mp : List w8} {N : Meta}
    (hb : s.busy = .write t (4096 * (1 - sl)) data) (h : commitMetaSt s.m s.bs mp N sl)
    (hdl : data.length = 4096) (hhi : 4096 * (1 - sl) + 4096 ≤ 2 ^ 30) (hR : 2 ≤ curRoot mp)
    (hc : cacheOk s.bs (1 - sl) (fun X => X = fileMeta mp (1 - sl) ∨ X = N))
    (hw : fileMeta (writeBytes (s.bs.map Prod.fst) (4096 * (1 - sl)) data) (1 - sl) = N) :
    CrashOkS (P1 p) p Good (some s) :=
  crashOkS_write s hb hl (crashOkQ_writing hl (commitMetaW_good h hdl hhi hR hc hw))

/-- A commit's idle states after the meta write (or its failure, or a failed sync of it). -/
theorem commitMetaIdle_okS {mp : List w8} {N : Meta} {sl : Nat} (hb : s.busy = .idle)
    (h : commitMetaSt s.m s.bs mp N sl)
    (hc : cacheOk s.bs (1 - sl) (fun X => X = fileMeta mp (1 - sl) ∨ X = N)) :
    CrashOkS (P1 p) p Good (some s) :=
  crashOkS_idle s hb (crashOkQ_idle hl (commitMetaIdle_good h hc))

end states

section obligations
variable {p : GoString}

/-- A failed sync leaves `initIdle`/`initMid` as they were (they ignore `ok`). -/
theorem initIdle_notOk {m : OsMeta} {bs : List (w8 × Bool)} (h : initIdle m bs) :
    initIdle { m with ok := false } bs := ⟨h.hi, h.dur, h.cache⟩

theorem initMid_notOk {ph : Bool} {m : OsMeta} {bs : List (w8 × Bool)} (h : initMid ph m bs) :
    initMid ph { m with ok := false } bs := ⟨h.hi, h.lo, h.dur, h.page3, h.ord⟩

/-- **`init`'s first write's obligation** (`os.File.WriteAt.specCrashS`): every state it reaches,
idle or with the next attempt in flight, from an `initIdle` state whose slots are clean. -/
theorem initW1_obl {m : OsMeta} {xs : List (w8 × Bool)} {F : List w8} (h : initIdle m xs)
    (hl : xs.length = m.size)
    (hcl : ∀ i < 2, ∀ k < 64, ∀ x, xs[4096 * i + 16 + k]? = some x → x.2 = true)
    (hF : 8192 ≤ F.length) (hF' : F.length ≤ 2 ^ 30) (hz : ∀ k < 8192, F[k]? = some 0)
    (fa fb : Nat) :
    ∀ m' bs', WReach m xs 0 F m' bs' →
      CrashOkS (P1 p) p Good (some ⟨m', bs', fa, fb, .idle⟩) ∧
      ∀ t, CrashOkS (P1 p) p Good (some ⟨m', bs', fa, fb, .write t 0 F⟩) := by
  intro m' bs' hR
  have hI := initIdle_wreach h hl hR hcl hF hF' hz
  have hl' := (hR.narrow hl).len
  exact ⟨initIdle_okS ⟨m', bs', fa, fb, .idle⟩ hl' rfl hI, fun t =>
    initW1_okS ⟨m', bs', fa, fb, .write t 0 F⟩ hl' rfl hI.hi hF' hI.dur hI.cache hz⟩

/-- The slot `initSlot ph` of the data `D` of `init`'s meta write is `initBytes`'s. -/
def initWData (ph : Bool) (D : List w8) : Prop :=
  D.length = 4096 ∧ ∀ k < 64, D[16 + k]? = initBytes[4096 * initSlot ph + 16 + k]?

/-- A slot equal to `initBytes`'s slot `initSlot ph` is `init`'s meta there. -/
theorem initWData_meta {ph : Bool} {D : List w8} (hD : initWData ph D) {L : List w8}
    (hL : ∀ k < 64, L[4096 * initSlot ph + 16 + k]? = D[16 + k]?) :
    fileMeta L (initSlot ph) = bInitMeta (initSlot ph) := by
  have e : fileMeta L (initSlot ph) = fileMeta initBytes (initSlot ph) :=
    fileMeta_of_slot (metaSlot_ext fun k hk => by rw [hL k hk, hD.2 k hk])
  rw [e]
  cases ph
  · exact initBytes_meta1
  · exact initBytes_meta0

/-- `init`'s meta write of phase `ph`, retried, from an `initMid ph` state whose slot
`initSlot ph` is clean, with data `D` (`initWData`): every state it reaches is `initMid ph`, with
`cacheOk` for `init`'s metas (a torn slot keeps a clean old byte; the other slot is clean). -/
theorem initW_reach {ph : Bool} {m : OsMeta} {bs : List (w8 × Bool)} {D : List w8}
    (h : initMid ph m bs) (hl : bs.length = m.size)
    (hcl : ∀ k < 64, ∀ x, bs[4096 * initSlot ph + 16 + k]? = some x → x.2 = true)
    (hD : initWData ph D) (hsz : 4 * 4096 ≤ m.size) {m' : OsMeta} {bs' : List (w8 × Bool)}
    (hR : WReach m bs (4096 * initSlot ph) D m' bs') :
    initMid ph m' bs' ∧ ∀ i < 2, cacheOk bs' i (fun X => X = bInitMeta i) := by
  have hM := initMid_wreach h hl hR hD.1 hsz
  refine ⟨hM, fun i hi => ?_⟩
  have hw : cacheOk bs' (initSlot ph) (fun X => X = bInitMeta (initSlot ph)) :=
    cacheOk_wreach hR hl (by omega) (by rw [hD.1]; omega) hcl fun L hL _ =>
      initWData_meta hD fun k hk => by
        rw [hL k hk, List.getD_eq_getElem?_getD,
          show 4096 * initSlot ph + 16 + k - 4096 * initSlot ph = 16 + k by omega,
          List.getElem?_eq_getElem (by rw [hD.1]; omega)]
        rfl
  have ho : cacheOk bs' (1 - initSlot ph) (fun X => X = bInitMeta (1 - initSlot ph)) :=
    fun _ => .inl ⟨0, by omega, _, hM.ord 0 (by omega), rfl⟩
  cases ph <;> rcases i with _ | _ | i
  · exact ho
  · exact hw
  · omega
  · exact hw
  · exact ho
  · omega

/-- **`init`'s meta write's obligation** (phase `ph`): every state it reaches, from an
`initMid ph` state whose slot `initSlot ph` is clean, with data `D` (`initWData`). -/
theorem initW_obl {ph : Bool} {m : OsMeta} {bs : List (w8 × Bool)} {D : List w8}
    (h : initMid ph m bs) (hl : bs.length = m.size)
    (hcl : ∀ k < 64, ∀ x, bs[4096 * initSlot ph + 16 + k]? = some x → x.2 = true)
    (hD : initWData ph D) (hsz : 4 * 4096 ≤ m.size) (fa fb : Nat) :
    ∀ m' bs', WReach m bs (4096 * initSlot ph) D m' bs' →
      CrashOkS (P1 p) p Good (some ⟨m', bs', fa, fb, .idle⟩) ∧
      ∀ t, CrashOkS (P1 p) p Good (some ⟨m', bs', fa, fb, .write t (4096 * initSlot ph) D⟩) := by
  intro m' bs' hR
  obtain ⟨hM, hc⟩ := initW_reach h hl hcl hD hsz hR
  have hN := hR.narrow hl
  have hsz' : 4 * 4096 ≤ m'.size := by have := hN.size; omega
  refine ⟨initMid_okS ⟨m', bs', fa, fb, .idle⟩ hN.len rfl hM hc, fun t =>
    initW_okS ⟨m', bs', fa, fb, .write t (4096 * initSlot ph) D⟩ hN.len rfl hM hD.1 hsz' hc
      fun i hi hv => ?_⟩
  have hne : D ≠ [] := by intro e; have := hD.1; rw [e] at this; cases this
  have hlen : (bs'.map Prod.fst).length = m'.size := by rw [List.length_map, hN.len]
  by_cases hi0 : i = initSlot ph
  · subst hi0
    exact initWData_meta hD fun k hk => by
      rw [writeBytes_getElem? _ _ _ hne, if_neg (by omega), if_pos (by rw [hD.1]; omega),
        show 4096 * initSlot ph + 16 + k - 4096 * initSlot ph = 16 + k by omega]
  · have hi1 : i = 1 - initSlot ph := by cases ph <;> simp [initSlot] at hi0 ⊢ <;> omega
    subst hi1
    have hslot : ∀ k < 64, (writeBytes (bs'.map Prod.fst) (4096 * initSlot ph) D)[4096 * (1 - initSlot ph) + 16 + k]? =
        some (initOrdByte ph (4096 * (1 - initSlot ph) + 16 + k)) := by
      intro k hk
      have ho := hM.ord k hk
      rw [writeBytes_getElem? _ _ _ hne]
      cases ph
      · rw [if_pos (by simp only [initSlot]; omega),
          if_pos (by rw [hlen]; simp only [initSlot]; omega), List.getElem?_map, ho]; rfl
      · rw [if_neg (by simp only [initSlot]; omega),
          if_neg (by rw [hD.1]; simp only [initSlot]; omega), List.getElem?_map, ho]; rfl
    cases ph
    · exact absurd hv (by
        refine slot_zero_invalid (i := 0) fun k hk => ?_
        have := hslot k hk; simp only [initSlot, initOrdByte] at this; exact this)
    · have hil := initBytes_length
      simp only [pageBytes] at hil
      have e : fileMeta (writeBytes (bs'.map Prod.fst) (4096 * initSlot true) D) 1 =
          fileMeta initBytes 1 := fileMeta_of_slot (metaSlot_ext fun k hk => by
        have := hslot k hk
        simp only [initSlot, initOrdByte] at this ⊢
        rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        rfl)
      simp only [initSlot] at e ⊢
      rw [e, initBytes_meta1]

/-- After a successful meta write of phase `ph` (its data `D` read back): the slots are invalid or
`init`'s metas, page 3 is `init`'s, and slot 1 is `init`'s meta 1 (`initOrd true`, for the next
sync), in both phases. -/
theorem initW_done {ph : Bool} {m : OsMeta} {bs : List (w8 × Bool)} {D : List w8}
    (hD : initWData ph D) (hM : initMid ph m bs)
    (hd : ∀ i < D.length, (bs[4096 * initSlot ph + i]?).map Prod.fst = D[i]?) :
    (∀ i < 2, metaValid (fileMeta (bs.map Prod.fst) i) →
      fileMeta (bs.map Prod.fst) i = bInitMeta i) ∧
    (∀ k < 4096, (bs[4096 * 3 + k]?).map Prod.fst =
      some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0)) ∧
    initOrd true (bs.map fun x => (x.1, true)) := by
  have hil := initBytes_length
  simp only [pageBytes] at hil
  have hcl : ∀ {j : Nat} {b : w8}, (bs[j]?).map Prod.fst = some b →
      (bs.map fun x => (x.1, true))[j]? = some (b, true) := by
    intro j b h
    rw [List.getElem?_map]
    cases hx : bs[j]? with
    | none => rw [hx] at h; cases h
    | some x => rw [hx] at h; simp only [Option.map_some, Option.some.injEq] at h ⊢; rw [h]
  have hw : fileMeta (bs.map Prod.fst) (initSlot ph) = bInitMeta (initSlot ph) :=
    initWData_meta hD fun k hk => by
      rw [List.getElem?_map, Nat.add_assoc, hd _ (by rw [hD.1]; omega)]
  have h1 : ∀ k < 64, (bs[4096 + 16 + k]?).map Prod.fst = some (initBytes.getD (4096 + 16 + k) 0) := by
    intro k hk
    cases ph
    · rw [show 4096 + 16 + k = 4096 * initSlot false + (16 + k) by simp [initSlot]; omega,
        hd _ (by rw [hD.1]; omega), hD.2 k hk, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp only [initSlot]; omega)]
      simp only [initSlot, ← Nat.add_assoc]
      rw [List.getElem?_eq_getElem (by omega)]
      rfl
    · have := hM.ord k hk
      simp only [initSlot, initOrdByte] at this
      rw [this]; rfl
  refine ⟨fun i hi hv => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have e1 : fileMeta (bs.map Prod.fst) 1 = bInitMeta 1 := by
      rw [← initBytes_meta1]
      refine fileMeta_of_slot (metaSlot_ext fun k hk => ?_)
      rw [List.getElem?_map, h1 k hk, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    rcases i with _ | _ | i
    · cases ph
      · refine absurd hv (slot_zero_invalid fun k hk => ?_)
        have := hM.ord k hk
        simp only [initSlot, initOrdByte] at this
        rw [List.getElem?_map, this]; rfl
      · exact hw
    · exact e1
    · omega
  · have := hM.page3 k hk
    rw [this]; rfl
  · exact hcl (h1 k hk)

/-- **`init`'s syncs' obligation** (success; `syscall.Fdatasync.specCrashS` with `H = F = []`):
the file synced whole, with `init`'s page 3, slots invalid or `init`'s metas, and the other slot of
phase `ph` as `initOrd` says. On failure, the state is the write's last (`initIdle_notOk`,
`initMid_notOk`). -/
theorem initSync_ok {ph : Bool} {m : OsMeta} {bs : List (w8 × Bool)} (hok : m.ok = true)
    (hl : bs.length = m.size) (hlo : 4 * 4096 ≤ m.size) (hhi : m.size ≤ 2 ^ 30)
    (hs : ∀ i < 2, metaValid (fileMeta (bs.map Prod.fst) i) →
      fileMeta (bs.map Prod.fst) i = bInitMeta i)
    (h3 : ∀ k < 4096, (bs[4096 * 3 + k]?).map Prod.fst =
      some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0))
    (hord : initOrd ph (bs.map fun x => (x.1, true))) :
    CrashOkS (P1 p) p Good (some (csSynced false m [] [] bs 0 0)) := by
  obtain ⟨hM, hc⟩ := initMid_synced hok hl hlo hhi hs h3 hord
  have e : m.syncedKeep 0 bs 0 [] = m.synced 0 bs := by
    simp only [OsMeta.syncedKeep, durOf, List.replicate_zero, List.nil_append, List.map_nil]
    rw [show ∀ a : List (Option w8), durOverlay a [] = a from fun a => by cases a <;> rfl]
  simp only [csSynced, List.nil_append]
  rw [e]
  refine initMid_okS ⟨m.synced 0 bs, syncedBytes m bs, 0, 0, .idle⟩ ?_ rfl hM hc
  simp [syncedBytes, OsMeta.synced, hok, hl]

end obligations

end pure

end bboltfs
end EtcdGrove
end Perennial
