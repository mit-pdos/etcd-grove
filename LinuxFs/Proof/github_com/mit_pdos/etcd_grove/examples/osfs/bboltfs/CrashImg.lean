/- Lean-first (no Rocq counterpart). minibolt's crash obligations on images (the per-byte model):
for the states the database file passes through during `init` and `commit`, every file a crash may
leave (`CrashImg`, `CrashOk.lean`) is `Good`.

**Slots.** What a state knows of a meta slot's bytes (`SlotK`): clean, holding `X`; or written over
clean bytes holding `X`, with `D`, at one first stamp (a write's attempts after its first write
the same bytes again, at later stamps). By P1, a slot of a crash image that validates is the slot
as of one stamp, so `X` or `D` (`slotK_valid`): no torn slot, and nothing about checksums beyond P1.

**init** (`noValid_okS`, `initMid_okS`): before its first sync every slot a crash may leave is the
old file's (invalid, the file being one `Open` redoes `init` on) or zeros; after it, each slot
invalid or `init`'s meta, slot 0 only after slot 1.

**commit** (`commitClean_okS`, `commitMeta_okS`): while the metas and the current root page are
clean, an image has them; while slot `(T+1) % 2` is written, it is the old slot or the new meta,
whose root page is synced, and the current meta is in slot `T % 2`, untouched.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.CrashOk
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.InitLayout

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



/-! ## A crash image, byte by byte (`CrashImg`) -/

theorem valAt_one (x : w8) (n : Nat) : valAt [(x, 0)] n = x := by
  simp [valAt]

theorem getLast_val {l : Cands} {d : w8} (hl : l ≠ []) (h : ∀ e ∈ l, e.1 = d) :
    (l.getLast?.map (·.1)).getD 0 = d := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (List.getLast?_isSome.2 hl)
  rw [he]
  exact h e (List.mem_of_getLast? he)

/-- **A byte written at `N` over a clean one**, and maybe again later with the same value: as of
a stamp below `N` the old value, from `N` on the new one. -/
theorem valAt_two (x d : w8) (N : Nat) (L : Cands) (hN : 0 < N)
    (hL : ∀ e ∈ L, e.1 = d ∧ N < e.2) (n : Nat) :
    valAt ((x, 0) :: (d, N) :: L) n = if n < N then x else d := by
  unfold valAt
  by_cases h : n < N
  · rw [if_pos h]
    have hf : L.filter (fun q => decide (q.2 ≤ n)) = [] :=
      List.filter_eq_nil_iff.2 fun e he => by have := (hL e he).2; simp; omega
    simp [List.filter_cons, show ¬ N ≤ n by omega, hf]
  · rw [if_neg h]
    simp only [List.filter_cons, Nat.zero_le, decide_true, if_true, show N ≤ n by omega]
    rw [List.getLast?_cons_cons]
    exact getLast_val (by simp) fun e he => by
      rcases List.mem_cons.1 he with rfl | he
      · rfl
      · exact (hL e (List.mem_filter.1 he).1).1

/-- Meta slot `j`'s bytes as the state `s` knows them: clean, holding `X`; or written over clean
ones holding `X`, with `D`, at one first stamp `N` (each later candidate `D`'s byte again). -/
def SlotK (s : CSt) (j : Nat) (X D : List w8) : Prop :=
  X.length = 64 ∧ D.length = 64 ∧
  ((∀ k < 64, s.kc (4096 * j + 16 + k) = some [(X.getD k 0, 0)]) ∨
   ∃ N, 0 < N ∧ ∀ k < 64, ∃ L, s.kc (4096 * j + 16 + k) =
     some ((X.getD k 0, 0) :: (D.getD k 0, N) :: L) ∧ ∀ e ∈ L, e.1 = D.getD k 0 ∧ N < e.2)

theorem rawSlot_ext {f : OsFile} {j : Nat} {X : List w8} (hX : X.length = 64)
    (h : ∀ k < 64, f.cache (4096 * j + 16 + k) = X.getD k 0) : rawSlot f j = X := by
  apply List.ext_getElem (by simp [rawSlot, hX])
  intro k h1 h2
  simp only [rawSlot, List.getElem_map, List.getElem_range]
  rw [h k (by simpa [rawSlot] using h1), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rfl

/-- **A valid meta slot of a crash image is one the state knows of**: the clean one, or the one
written over it (P1: the slot as of one stamp). -/
theorem slotK_valid {s : CSt} {f : OsFile} {j : Nat} {X D : List w8} (hI : CrashImg s f)
    (hK : SlotK s j X D) (hj : j < 2) (hsz : 4096 * j < f.size)
    (hv : metaValid (decode (rawSlot f j) : Meta)) : rawSlot f j = X ∨ rawSlot f j = D := by
  obtain ⟨hX, hD, hK⟩ := hK
  have hsome : ∀ k < 64, (s.kc (4096 * j + 16 + k)).isSome := by
    intro k hk
    rcases hK with h | ⟨N, -, h⟩
    · rw [h k hk]; rfl
    · obtain ⟨L, hL, -⟩ := h k hk; rw [hL]; rfl
  obtain ⟨n, hn⟩ := hI.slot j hj hsz hv hsome
  rcases hK with h | ⟨N, hN, h⟩
  · left
    exact rawSlot_ext hX fun k hk => by rw [hn k hk _ (h k hk), valAt_one]
  · by_cases hnN : n < N
    · left
      refine rawSlot_ext hX fun k hk => ?_
      obtain ⟨L, hL, hLd⟩ := h k hk
      rw [hn k hk _ hL, valAt_two _ _ _ _ hN hLd, if_pos hnN]
    · right
      refine rawSlot_ext hD fun k hk => ?_
      obtain ⟨L, hL, hLd⟩ := h k hk
      rw [hn k hk _ hL, valAt_two _ _ _ _ hN hLd, if_neg hnN]

/-- A slot the state knows as the same bytes whichever way (clean, or written over with the same
bytes) is the crash image's raw slot, in a page that holds a byte of the file. -/
theorem slotK_same {s : CSt} {f : OsFile} {j : Nat} {X : List w8} (hI : CrashImg s f)
    (hK : SlotK s j X X) (hsz : 4096 * j < f.size) (hlo : 4096 * j + 80 ≤ s.vmeta.lo) :
    rawSlot f j = X := by
  obtain ⟨hX, -, hK⟩ := hK
  refine rawSlot_ext hX fun k hk => ?_
  have hpg : pageIn f.size (4096 * j + 16 + k) = true := by unfold pageIn; simp; omega
  rcases hK with h | ⟨N, -, h⟩
  · obtain ⟨q, hq⟩ | ⟨h0, -⟩ := hI.byte _ _ hpg (h k hk)
    rotate_left; · omega
    simp only [List.mem_singleton, Prod.mk.injEq] at hq; exact hq.1
  · obtain ⟨L, hL, hLd⟩ := h k hk
    obtain ⟨q, hq⟩ | ⟨h0, -⟩ := hI.byte _ _ hpg hL
    rotate_left; · omega
    rcases List.mem_cons.1 hq with e | hq
    · simp only [Prod.mk.injEq] at e; exact e.1
    rcases List.mem_cons.1 hq with e | hq
    · simp only [Prod.mk.injEq] at e; exact e.1
    · exact (hLd _ hq).1

/-- A meta slot of a crash image that holds it whole is its raw slot. -/
theorem fileMeta_contents {f : OsFile} {j : Nat} (h : 4096 * j + 80 ≤ f.size) :
    fileMeta f.contents j = decode (rawSlot f j) := by
  rw [fileMeta_slot]; congr 1
  apply List.ext_getElem?; intro k
  by_cases hk : k < 64
  · rw [metaSlot_getElem? _ _ _ hk, contents_getElem?, if_pos (by omega)]
    simp only [rawSlot, List.getElem?_map, List.getElem?_range hk, Option.map_some]
  · rw [List.getElem?_eq_none (by rw [metaSlot_length, contents_length]; omega),
      List.getElem?_eq_none (by simp [rawSlot]; omega)]

/-- A clean byte the state knows is the crash image's. -/
theorem crashImg_clean {s : CSt} {f : OsFile} (hI : CrashImg s f) {b : Nat} {x : w8}
    (hk : s.kc b = some [(x, 0)]) (hb : b < f.size) (hlo : b < s.vmeta.lo) :
    f.contents[b]? = some x := by
  obtain ⟨q, hq⟩ | ⟨h0, -⟩ := hI.byte b _ (by unfold pageIn; simp; omega) hk
  rotate_left; · omega
  simp only [List.mem_singleton, Prod.mk.injEq] at hq
  rw [contents_getElem?, if_pos hb, hq.1]

/-- An idle state knows its bytes below the size; a busy one those its change misses. -/
theorem kc_below {s : CSt} {b : Nat} {x : ByteG} (hb : b < s.m.size) (hx : s.bs[b]? = some x)
    (hout : match s.busy with
      | .idle => True
      | .write _ off data _ => ¬ inRange (min off s.m.size) (off + data.length) b = true
      | .trunc _ sz _ => ¬ inRange (min s.m.size sz) (max s.m.size sz) b = true) :
    s.kc b = some x.2 := by
  have hbase : s.baseC b = some x.2 := by
    unfold CSt.baseC; rw [if_pos hb, hx]; rfl
  unfold CSt.kc
  split <;> rename_i hbz <;> rw [hbz] at hout
  · exact hbase
  · rw [if_neg hout]; exact hbase
  · rw [if_neg hout]; exact hbase

/-- A durable byte an idle state holds, known clean. -/
theorem kc_idle_dur {s : CSt} (hb0 : s.busy = .idle) {b : Nat} {x : w8} (hb : b < s.m.size)
    (hx : s.bs[b]? = some (durB x)) : s.kc b = some [(x, 0)] :=
  kc_below hb hx (by rw [hb0]; trivial)

/-- The bytes of the image from `a` on are the ones `l` holds there. -/
theorem image_take_drop {s : CSt} {f : OsFile} (hI : CrashImg s f) {a n : Nat} {l : List w8}
    (hl : a + n ≤ l.length) (hn : a + n ≤ f.size) (hlo : a + n ≤ s.vmeta.lo)
    (h : ∀ k < n, s.kc (a + k) = some [(l.getD (a + k) 0, 0)]) :
    (f.contents.drop a).take n = (l.drop a).take n := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take, List.getElem?_drop]
  split
  · rename_i hk
    rw [crashImg_clean hI (h k hk) (by omega) (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  · rfl

/-! ## commit -/

/-- What a commit's crash images need of the state while the metas and the current root page are
clean (every step before the meta write): `bs`'s meta pages `mp` are an open database's, whose
current meta's root page holds what `BootMinibolt` checks, and the size since the last sync covers
the high water mark. -/
structure commitClean (m : OsMeta) (bs : List ByteG) : Prop where
  hi : m.hi ≤ 2 ^ 30
  lo : 4 * 4096 ≤ m.lo
  ok : metaPagesOk ((bs.map Prod.fst).take 8192)
  slot : curInSlot ((bs.map Prod.fst).take 8192)
  pg : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ m.lo
  boot : bootOk (curMeta ((bs.map Prod.fst).take 8192)).txid'.toNat
    (pageVal (((bs.map Prod.fst).drop (4096 * curRoot ((bs.map Prod.fst).take 8192))).take 4096))
  metas : ∀ k < 8192, ∃ b, bs[k]? = some (durB b)
  root : ∀ k < 4096, ∃ b, bs[4096 * curRoot ((bs.map Prod.fst).take 8192) + k]? = some (durB b)
  tx : txOk ((bs.map Prod.fst).take 8192)
  /-- The committed pages (the frozen ones, past the meta pages) durable. -/
  frz : ∀ k, 8192 ≤ k → k < 4096 * curPgid ((bs.map Prod.fst).take 8192) → ∃ b, bs[k]? = some (durB b)

theorem commit_clean_img {m : OsMeta} {bs : List ByteG} (h : commitClean m bs)
    {img : List w8} (hlo : m.lo ≤ img.length) (hhi : img.length ≤ 2 ^ 30)
    (hcl : ∀ k b, bs[k]? = some (durB b) →
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
structure commitMetaSt (m : OsMeta) (bs : List ByteG) (mp : List w8) (N : Meta)
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
  root : ∀ k < 4096, ∃ b, bs[4096 * curRoot mp + k]? = some (durB b)
  metaS : ∀ k < 64, ∃ b, mp[4096 * s + 16 + k]? = some b ∧ bs[4096 * s + 16 + k]? = some (durB b)
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
  nPage : ∀ k < 4096, ∃ b, bs[4096 * N.root'.root'.toNat + k]? = some (durB b)
  frz : ∀ k, 8192 ≤ k → k < 4096 * curPgid mp → ∃ b, bs[k]? = some (durB b)

theorem commitMeta_good {m : OsMeta} {bs : List ByteG} {mp : List w8} {N : Meta} {s : Nat}
    (h : commitMetaSt m bs mp N s) {img : List w8} (hlo : m.lo ≤ img.length)
    (hhi : img.length ≤ 2 ^ 30)
    (hcl : ∀ k b, bs[k]? = some (durB b) → (4096 * s + 16 ≤ k ∧ k < 4096 * s + 80 ∨
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
  have hpage : ∀ r, (∀ k < 4096, ∃ b, bs[4096 * r + k]? = some (durB b)) →
      (∀ k, 4096 * r ≤ k → k < 4096 * r + 4096 → ∀ b, bs[k]? = some (durB b) → img[k]? = some b) →
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
variable [GooseExts] {i : Ino}

/-- The change in flight of `s` leaves byte `b` alone. -/
def _root_.Perennial.CSt.Misses (s : CSt) (b : Nat) : Prop :=
  match s.busy with
  | .idle => True
  | .write _ off data _ => ¬ inRange (min off s.m.size) (off + data.length) b = true
  | .trunc _ sz _ => ¬ inRange (min s.m.size sz) (max s.m.size sz) b = true

/-- A durable byte of the state, which its change in flight misses, is known clean. -/
theorem kc_dur {s : CSt} {b : Nat} {x : w8} (hb : b < s.m.size) (hx : s.bs[b]? = some (durB x))
    (hm : s.Misses b) : s.kc b = some [(x, 0)] :=
  kc_below hb hx hm

/-- **No slot of a crash image of `s` validates**: every crash leaves a good image (with no
valid meta: `Open` redoes `init`), whose slots past the size do not validate either. -/
theorem noValid_okS (s : CSt) (hwf : s.Wf) (hbz : BusyOk s) (hhi : s.vmeta.hi ≤ 2 ^ 30)
    (hs : ∀ j < 2, ∃ X D, SlotK s j X D ∧ ¬ metaValid (decode X : Meta) ∧
      ¬ metaValid (decode D : Meta)) :
    FileOkS P1 Good i s := by
  refine fileOkS_of s hwf hbz fun f hI => ?_
  have hinv : ∀ j < 2, 4096 * j < f.size → ¬ metaValid (decode (rawSlot f j) : Meta) := by
    intro j hj hsz hv
    obtain ⟨X, D, hK, hX, hD⟩ := hs j hj
    rcases slotK_valid hI hK hj hsz hv with e | e <;> rw [e] at hv
    · exact hX hv
    · exact hD hv
  refine ⟨goodImg_noValid (by rw [contents_length]; exact Nat.le_trans hI.hi hhi) fun j hj hl => ?_,
    fun _ j hj hsz => hinv j hj hsz⟩
  rw [contents_length] at hl
  rw [fileMeta_contents hl]; exact hinv j hj (by omega)

/-- **`init`'s states after its first sync**: four pages or more, each slot invalid or `init`'s
meta, slot 0 valid only once slot 1 surely is (`init` writes meta 1 first), page 3 `init`'s root
page. -/
theorem initMid_okS (s : CSt) (hwf : s.Wf) (hbz : BusyOk s) (hlo : 4 * 4096 ≤ s.vmeta.lo)
    (hhi : s.vmeta.hi ≤ 2 ^ 30)
    (hs : ∀ j < 2, ∃ X D, SlotK s j X D ∧
      (metaValid (decode X : Meta) → (decode X : Meta) = bInitMeta j) ∧
      (metaValid (decode D : Meta) → (decode D : Meta) = bInitMeta j))
    (h01 : (∃ X D, SlotK s 0 X D ∧ ¬ metaValid (decode X : Meta) ∧ ¬ metaValid (decode D : Meta)) ∨
      (∃ X, SlotK s 1 X X ∧ metaValid (decode X : Meta)))
    (hp3 : ∀ k < 4096, s.kc (4096 * 3 + k) = some [((emptyPageBytes (W64 3) (W16 2)).getD k 0, 0)]) :
    FileOkS P1 Good i s := by
  refine fileOkS_of s hwf hbz fun f hI => ?_
  have h16 : 4 * 4096 ≤ f.size := Nat.le_trans hlo hI.lo
  have hslot : ∀ j < 2, metaValid (fileMeta f.contents j) → fileMeta f.contents j = bInitMeta j := by
    intro j hj hv
    obtain ⟨X, D, hK, hX, hD⟩ := hs j hj
    rw [fileMeta_contents (f := f) (j := j) (by omega)] at hv ⊢
    rcases slotK_valid hI hK hj (by omega) hv with e | e <;> rw [e] at hv ⊢
    · exact hX hv
    · exact hD hv
  have h01' : metaValid (fileMeta f.contents 0) → metaValid (fileMeta f.contents 1) := by
    intro hv0
    rcases h01 with ⟨X, D, hK, hX, hD⟩ | ⟨X, hK, hX⟩
    · exfalso
      rw [fileMeta_contents (f := f) (j := 0) (by omega)] at hv0
      rcases slotK_valid hI hK (by omega) (by omega) hv0 with e | e <;> rw [e] at hv0
      · exact hX hv0
      · exact hD hv0
    · rw [fileMeta_contents (f := f) (j := 1) (by omega), slotK_same hI hK (by omega) (by omega)]
      exact hX
  have h3 : (f.contents.drop (4096 * 3)).take 4096 = emptyPageBytes (W64 3) (W16 2) := by
    have hl := emptyPageBytes_length (W64 3) (W16 2)
    simp only [pageBytes] at hl
    apply List.ext_getElem?
    intro k
    simp only [List.getElem?_take, List.getElem?_drop]
    split
    · rename_i hk
      rw [crashImg_clean hI (hp3 k hk) (by omega) (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    · rename_i hk; rw [List.getElem?_eq_none (by omega)]
  exact ⟨goodImg_init (by rw [contents_length]; exact h16)
    (by rw [contents_length]; exact Nat.le_trans hI.hi hhi) hslot h01' h3,
    fun hsm => absurd hsm (by omega)⟩

/-- **A commit's states before its meta write**: the metas and the current root page clean, and
missed by the change in flight. -/
theorem commitClean_okS (s : CSt) (hwf : s.Wf) (hbz : BusyOk s) {M : OsMeta}
    (h : commitClean M s.bs)
    (hlo : M.lo ≤ s.vmeta.lo) (hhi : s.vmeta.hi ≤ 2 ^ 30)
    (hmiss : ∀ k, (k < 8192 ∨ (4096 * curRoot ((s.bs.map Prod.fst).take 8192) ≤ k ∧
        k < 4096 * curRoot ((s.bs.map Prod.fst).take 8192) + 4096)) → s.Misses k) :
    FileOkS P1 Good i s := by
  refine fileOkS_of s hwf hbz fun f hI => ?_
  have hlo' := Nat.le_trans hlo hI.lo
  have h16 := h.lo
  have hpg := h.pg
  have hrp := h.ok.2.2.2.1
  refine ⟨commit_clean_img h (by rw [contents_length]; exact hlo')
    (by rw [contents_length]; exact Nat.le_trans hI.hi hhi) (fun k b hb hk => ?_),
    fun hsm => absurd hsm (by omega)⟩
  have hkl : k < s.bs.length := (List.getElem?_eq_some_iff.1 hb).1
  have hl : s.bs.length = s.m.size := hwf.1
  refine crashImg_clean hI (kc_dur (by omega) hb (hmiss k hk)) ?_ ?_ <;>
  · unfold curRoot curPgid at *
    rcases hk with hk | ⟨-, hk⟩ <;> omega

/-- **A commit's states while (and after) it writes the meta slot `1 - sl`**: slot `sl`, the old
and the new current root pages clean and missed, and slot `1 - sl` as the state knows it the old
meta or the new one, if valid. -/
theorem commitMeta_okS (s : CSt) (hwf : s.Wf) (hbz : BusyOk s) {mp : List w8} {N : Meta}
    {sl : Nat} {M : OsMeta} (h : commitMetaSt M s.bs mp N sl)
    (hlo : M.lo ≤ s.vmeta.lo) (hhi : s.vmeta.hi ≤ 2 ^ 30)
    (hmiss : ∀ k, (4096 * sl + 16 ≤ k ∧ k < 4096 * sl + 80 ∨
      (4096 * curRoot mp ≤ k ∧ k < 4096 * curRoot mp + 4096) ∨
      (4096 * N.root'.root'.toNat ≤ k ∧ k < 4096 * N.root'.root'.toNat + 4096)) → s.Misses k)
    (hK : ∃ X D, SlotK s (1 - sl) X D ∧
      (metaValid (decode X : Meta) → (decode X : Meta) = fileMeta mp (1 - sl) ∨ (decode X : Meta) = N) ∧
      (metaValid (decode D : Meta) → (decode D : Meta) = fileMeta mp (1 - sl) ∨ (decode D : Meta) = N)) :
    FileOkS P1 Good i s := by
  refine fileOkS_of s hwf hbz fun f hI => ?_
  have hlo' := Nat.le_trans hlo hI.lo
  have h16 := h.lo
  have hpg := h.pg
  have hrp := h.ok.2.2.2.1
  have hs2 := h.s2
  have hnr := h.nRootPg
  have hnp := h.nPgLo
  refine ⟨commitMeta_good h (by rw [contents_length]; exact hlo')
    (by rw [contents_length]; exact Nat.le_trans hI.hi hhi) (fun k b hb hk => ?_) (fun hv => ?_),
    fun hsm => absurd hsm (by omega)⟩
  · have hkl : k < s.bs.length := (List.getElem?_eq_some_iff.1 hb).1
    have hl : s.bs.length = s.m.size := hwf.1
    refine crashImg_clean hI (kc_dur (by omega) hb (hmiss k hk)) ?_ ?_ <;>
    · unfold curRoot curPgid at *
      rcases hk with hk | ⟨-, hk⟩ | ⟨-, hk⟩ <;> omega
  · obtain ⟨X, D, hK, hX, hD⟩ := hK
    rw [fileMeta_contents (f := f) (j := 1 - sl) (by omega)] at hv ⊢
    rcases slotK_valid hI hK (by omega) (by omega) hv with e | e <;> rw [e] at hv ⊢
    · exact hX hv
    · exact hD hv

end states

/-- The namespace of the database file's crash invariant. -/
def dbCrashN : Namespace := nroot .@ "minibolt_crash"

/-- minibolt's obligation on the states of its file: every crash of the state is `Good`. -/
abbrev dbOk [GooseExts] : CState → Prop
  | none => True
  | some (i, s) => FileOkS P1 Good i s

end osfs_bboltfs
end EtcdGrove
end Perennial

end
