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

/-- A commit's idle states before the meta write. -/
theorem commitClean_okS (hb : s.busy = .idle) (h : commitClean s.m s.bs) :
    FileOkS NoTearCrash Good i s :=
  fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; trivial) fun img hI =>
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
  fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; exact hoff) fun img hI =>
    commit_clean_img h (crashImg_lo hI)
      (by have h1 := hI.2.1; have h2 := h.hi; unfold CSt.vmeta at h1; rw [hb] at h1
          simp only [pwMeta] at h1; omega)
      (fun k b hb' hk => crashImg_clean hI hb' (CSt.taken_out _ _ fun _ _ _ h' => by
        rw [hb] at h'; cases h'; exact hmiss k hk))

/-- A commit's growing truncate in flight. -/
theorem commitClean_trunc_okS {t sz : Nat} (hb : s.busy = .trunc t sz) (h : commitClean s.m s.bs)
    (hsz : sz ≤ 2 ^ 30) : FileOkS NoTearCrash Good i s :=
  fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; trivial) fun img hI =>
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
  refine fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; omega) fun img hI => ?_
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
  refine fileOkS_crashImg s hwf (by unfold BusyOk; rw [hb]; trivial) fun img hI => ?_
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

end osfs_bboltfs
end EtcdGrove
end Perennial

end
