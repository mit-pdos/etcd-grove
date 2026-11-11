/-
`DB.grow` (U4e, `notes/bbolt-proof-plan.md`): the writer side after the file grew, pure part
(`WDb.grown`, `growWb`, `wdbOK'_grown`), and the three facts `wdbOK'` does not give that the
proof needs (`sorry`s, reported to the maintainer: shared-statement gaps).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.RemapEnd
public import Proof.go_etcd_io.bbolt.Txn.WJoin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section pure
variable [GooseExts]

/-- The slots' bytes after the file grew from `size` (zeros past it): a slot inside the old file
keeps its bytes, the partial one its first `size - 4096·s` bytes, the rest zeros. -/
def growWb (wb : Nat → List w8) (size : Nat) : Nat → List w8 :=
  fun s => if 4096 * (s + 1) ≤ size then wb s
    else (wb s).take (size - 4096 * s) ++ List.replicate (4096 - (size - 4096 * s)) (0 : w8)

/-- The writer side after the file changed to `m'` (the same mappings), with the slots' bytes
`wb'`; its `W` slots `wSlots` of the new bound. -/
def WDb.grown (w : WDb) (m' : OsMeta) (wb' : Nat → List w8) : WDb :=
  { w with m := m', W := wSlots (max (mapLen w.ms) m'.size / 4096) w.C w.fl, wb := wb' }

/-- The bytes of the extent from `f`, read from `wb'` that agrees with `wb` below `n`, when the
extent ends below `n` and `f`'s bytes hold a page header. -/
theorem extentBytes_congr_lt (wb wb' : Nat → List w8) (f n : Nat)
    (hlt : f + (1 + pageOverflow (extentBytes wb f)) ≤ n) (h16 : 16 ≤ (wb f).length)
    (hag : ∀ s, s < n → wb' s = wb s) : extentBytes wb' f = extentBytes wb f := by
  have hov : pageOverflow (extentBytes wb f) = pageOverflow (wb f) := by
    unfold pageOverflow pageHdr bytesAt
    congr 3
    unfold extentBytes
    rw [show 1 + pageOverflow (wb f) = (pageOverflow (wb f)) + 1 by omega, List.range'_succ,
      List.flatMap_cons, List.drop_zero, List.drop_zero,
      List.take_append_of_le_length h16]
  rw [hov] at hlt
  have hf' : wb' f = wb f := hag f (by omega)
  unfold extentBytes
  rw [hf']
  simp only [List.flatMap]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  rw [List.mem_range'] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  exact hag _ (by omega)

/-- `flClause` with the slots' bytes changed only from the high-water mark on. -/
theorem flClause_wb (fr : Bool) (w : WDb) (wb' : Nat → List w8) (h : flClause fr w)
    (h16 : ∀ f, w.C.flpg = some f → 16 ≤ (w.wb f).length)
    (hag : ∀ s, s < w.C.hwm → wb' s = w.wb s) : flClause fr { w with wb := wb' } := by
  cases fr
  · simp only [flClause] at h ⊢
    intro f hf
    have hlt := (h f hf f hf).2.1
    rw [extentBytes_congr_lt w.wb wb' f _ hlt (h16 f hf) hag]
    exact h f hf
  · simp only [flClause, WDb.wtxid] at h ⊢
    intro f hf
    have hlt := ((h f hf).2 f hf).2.1
    have hf' : wb' f = w.wb f := hag f (by omega)
    rw [extentBytes_congr_lt w.wb wb' f _ hlt (h16 f hf) hag, hf']
    exact h f hf

/-- **The writer side's facts after the file grew** to `m'` (the same mappings, at least the
old size), with slots' bytes `wb'` that keep the old file's whole pages. -/
theorem wdbOK'_grown (fr : Bool) (w : WDb) (hok : wdbOK' fr w) (b : Loc) (L : Nat)
    (hms : w.ms = some (b, L)) (m' : OsMeta) (wb' : Nat → List w8)
    (hsz : w.m.size ≤ m'.size) (hmaps : m'.maps = w.m.maps)
    (h16 : ∀ f, w.C.flpg = some f → 16 ≤ (w.wb f).length)
    (hag : ∀ s, 4096 * (s + 1) ≤ w.m.size → wb' s = w.wb s)
    (hlen : ∀ s, 4096 * (s + 1) ≤ m'.size → w.m.size < 4096 * (s + 1) → (wb' s).length = 4096)
    (h10 : L ≤ 0x1000000 → m'.size ≤ L) (h13 : m'.size < 2 ^ 63)
    (h14 : m'.size ≤ L ∨ m'.size % 4096 = 0)
    (hpart' : ∀ s, 4096 * s < m'.size → m'.size < 4096 * (s + 1) →
      m'.size - 4096 * s ≤ (wb' s).length) :
    wdbOK' fr (w.grown m' wb') := by
  have hk3 := hok.2.2.1
  have hag' : ∀ s, s < w.C.hwm → wb' s = w.wb s := fun s hs => hag s (by omega)
  have hc := flClause_congr fr { w with wb := wb' } (w.grown m' wb') rfl rfl rfl
    (flClause_wb fr w wb' (wdbOK'_flClause fr w hok) h16 hag')
  have hmW := wdbOK'_mem_W fr w hok
  obtain ⟨hk1, _, _, _, hk5, -, hk7, hk8, hk9, _, hk11, hk12, _, _, hk15, _, hk17⟩ := hok
  refine ⟨?_, ?_, ?_, ?_, hk5, hc, hk7, hk8, hk9, ?_, hk11, hk12, h13, ?_, ?_, hpart', hk17⟩
  · intro b' l' h
    simp only [WDb.grown, hmaps] at h ⊢
    exact hk1 b' l' h
  · intro h; simp [WDb.grown, hms] at h
  · simp only [WDb.grown]; omega
  · intro s
    simp only [WDb.grown]
    exact mem_W_of_wSlots _ _ _ s
  · intro b' l' h hl
    simp only [WDb.grown, hms, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact h10 hl
  · intro b' l' h
    simp only [WDb.grown, hms, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact h14
  · intro s hs hle
    simp only [WDb.grown] at hs hle ⊢
    by_cases hin : 4096 * (s + 1) ≤ w.m.size
    · rw [hag s hin]
      obtain ⟨a, -, c⟩ := (mem_wSlots _ _ _ s).1 hs
      refine hk15 s ((hmW s).2 ⟨a, ?_, c⟩) hin
      have := Nat.le_max_right (mapLen w.ms) w.m.size
      have : s < w.m.size / 4096 := by omega
      omega
    · exact hlen s hle (by omega)

/-- `wdbOK'` after a change of the file's `OsMeta` keeping its size and mappings. -/
theorem wdbOK'_setM (fr : Bool) (w : WDb) (hok : wdbOK' fr w) (m' : OsMeta)
    (hsz : m'.size = w.m.size) (hmaps : m'.maps = w.m.maps) :
    wdbOK' fr { w with m := m' } := by
  have hc := flClause_congr fr w { w with m := m' } rfl rfl rfl (wdbOK'_flClause fr w hok)
  obtain ⟨hk1, hk2, hk3, hk4, hk5, -, hk7, hk8, hk9, hk10, hk11, hk12, hk13, hk14, hk15, hk16,
    hk17⟩ := hok
  refine ⟨?_, ?_, ?_, ?_, hk5, hc, hk7, hk8, hk9, ?_, hk11, hk12, ?_, ?_, ?_, ?_, hk17⟩ <;>
    simp only [hsz, hmaps] <;> assumption

omit [GooseExts] in
/-- `growWb`'s length at a slot reaching past the old end. -/
theorem growWb_length (wb : Nat → List w8) (size s : Nat) (hs : size < 4096 * (s + 1))
    (hp : 4096 * s < size → size - 4096 * s ≤ (wb s).length) :
    (growWb wb size s).length = 4096 := by
  simp only [growWb, Nat.not_le.2 hs, ↓reduceIte, List.length_append, List.length_take,
    List.length_replicate]
  by_cases h : 4096 * s < size
  · have := hp h; omega
  · omega

/-! ## Facts of `wdbOK'` for `DB.grow` (U4e's three gaps, closed by maintainer 13) -/

/-- **The synced freelist page's bytes hold a header** (at `fr = false` `Txn/WJoin.wb_header`; at
`fr = true` `flClause true` carries it). -/
theorem wdbOK'_flHdr (fr : Bool) (w : WDb) (hok : wdbOK' fr w) :
    ∀ f, w.C.flpg = some f → 16 ≤ (w.wb f).length := by
  cases fr
  · exact wb_header w hok
  · exact fun f hf => (wdbOK'_flClause true w hok f hf).1

/-- **The file's partial last page belongs to the writer, its bytes covering the file's part**
(`DB.grow` makes it a whole `W` page). The mapping ends on a page (`hal`: `mapFields` gives
`L % 4096 = 0 ∨ L = maxMapSize`, and no mapping reaches `maxMapSize`, `maxAddr = 2 ^ 47`:
`Mmap/GrowWdb.wdbW'_mapAligned`), so a file not ending on a page lies inside the mapping. -/
theorem wdbOK'_partSlot (fr : Bool) (w : WDb) (hok : wdbOK' fr w) (b : Loc) (L : Nat)
    (hms : w.ms = some (b, L)) (hal : L % 4096 = 0) (h8 : 8192 ≤ w.m.size) :
    ∀ s, 4096 * s < w.m.size → w.m.size < 4096 * (s + 1) →
      s ∈ w.W ∧ w.m.size - 4096 * s ≤ (w.wb s).length := by
  intro s h1 h2
  obtain ⟨-, -, hk3, hk4, -, -, -, -, -, -, hk11, -, -, hk14, -, hk16, -⟩ := hok
  refine ⟨(hk4 s).2 ⟨by omega, ?_, fun ht => ?_, fun hp => ?_⟩, hk16 s h1 h2⟩
  · have hL : w.m.size ≤ L := by
      rcases hk14 b L hms with h | h
      · exact h
      · omega
    have : mapLen w.ms = L := by simp [hms, mapLen]
    have := Nat.le_max_left (mapLen w.ms) w.m.size
    omega
  · have := hk11 s (.inl ht); omega
  · have := hk11 s (.inr hp); omega

/-- **The file's descriptor is not negative** (`File.Truncate`'s premise). -/
theorem wdbOK'_fd (fr : Bool) (w : WDb) (hok : wdbOK' fr w) : 0 ≤ w.fd.toInt := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := hok
  exact h

end pure

end bbolt
end EtcdGrove
end Perennial
