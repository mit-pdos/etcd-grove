/-
`tx.commitFreelist()`: the page it allocates for the freelist (`flAllocCount` slots, from the
estimate `EstimatedWritePageSize`), the cells `Write` writes after its header (`fresh_fl_split`:
zeroes of a fresh page), the bytes it leaves (`flWritten`, `fl_written_join`), and the page
cache's buffer replaced (`bufs_update`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__allocate
public import Proof.go_etcd_io.bbolt.U64Bytes
public import Proof.go_etcd_io.bbolt.Words

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section defs
variable [ext : FfiSyntax]

/-- The cells `Write` writes after a freelist page's header, of `n` free and pending ids `out`
(the count first if there are `0xFFFF` or more). -/
def flCellsOf (n : Nat) (out : List w64) : List w64 :=
  if 65535 ≤ n then W64 (n : Int) :: out else out

/-- The bytes of the fresh page `id` (`count` slots of `ps` bytes) after `Write` made it a
freelist page of `n` ids `out`: the header (flags `16`, the count), the cells, zeroes. -/
def flWritten (id : w64) (count ps n : Nat) (out : List w64) : List w8 :=
  pageBytes (Page.mk id (W16 16) (flCount n) (W32 ((count - 1 : Nat) : Int))) ++
    u64sBytes (flCellsOf n out) ++ List.replicate (count * ps - 16 - 8 * flCells n) 0

/-- The slots `commitFreelist` allocates for a freelist of `n` ids, pages of `ps` bytes:
`EstimatedWritePageSize() / pageSize + 1`. -/
def flAllocCount (n ps : Nat) : w64 := W64 (((16 + 8 * flCells n) / ps + 1 : Nat) : Int)

theorem flCells_mono (a b : Nat) (h : a ≤ b) : flCells a ≤ flCells b := by
  unfold flCells
  by_cases ha : 65535 ≤ a
  · rw [if_pos ha, if_pos (by omega)]; omega
  · rw [if_neg ha]
    by_cases hb : 65535 ≤ b
    · rw [if_pos hb]; omega
    · rw [if_neg hb]; omega

theorem flCells_le (n : Nat) : flCells n ≤ n + 1 := by
  unfold flCells; split <;> omega

theorem flCellsOf_length (n : Nat) (out : List w64) (h : out.length = n) :
    (flCellsOf n out).length = flCells n := by
  unfold flCellsOf flCells
  split <;> simp [h]

/-- The allocation does not grow the freelist's free and pending ids. -/
theorem allocOK_allIds_le (σ σ' : DBState) (w : Reader) (mv mv' : Meta) (txid id : w64) (n : Nat)
    (h : allocOK σ σ' w mv mv' txid id n) : σ'.fl.allIds.length ≤ σ.fl.allIds.length := by
  obtain ⟨-, -, -, -, -, -, h⟩ := h
  rcases h with ⟨-, rfl, -⟩ | ⟨-, -, rfl | ⟨d', sz', -, rfl⟩⟩
  · show (σ.fl.free.filter (fun x => decide ¬ inRun id n x) ++ σ.fl.pendingIds).length ≤
      (σ.fl.free ++ σ.fl.pendingIds).length
    have := List.length_filter_le (fun x => decide ¬ inRun id n x) σ.fl.free
    simp only [List.length_append]
    omega
  · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- The page count: `EstimatedWritePageSize() / pageSize + 1`. -/
theorem flAllocCount_eq (n ps : Nat) (hn : n < 2 ^ 32) (hps : 80 ≤ ps) (hps32 : ps < 2 ^ 32) :
    BitVec.sdiv (W64 ((16 + 8 * flCells n : Nat) : Int)) (W64 (ps : Int)) + W64 1 =
      flAllocCount n ps := by
  have hc := flCells_le n
  have h1 : sint.Z (W64 ((16 + 8 * flCells n : Nat) : Int)) = ((16 + 8 * flCells n : Nat) : Int) := by
    word
  have h2 : sint.Z (W64 (ps : Int)) = (ps : Int) := by word
  have hq := sint_sdiv (W64 ((16 + 8 * flCells n : Nat) : Int)) (W64 (ps : Int)) (by omega) (by omega)
  rw [h1, h2] at hq
  have hd : ((16 + 8 * flCells n : Nat) : Int) / (ps : Int) = (((16 + 8 * flCells n) / ps : Nat) : Int) :=
    (Int.natCast_ediv _ _).symm
  rw [hd] at hq
  have hle : (16 + 8 * flCells n) / ps ≤ 16 + 8 * flCells n := Nat.div_le_self _ _
  unfold flAllocCount
  generalize hz : BitVec.sdiv (W64 ((16 + 8 * flCells n : Nat) : Int)) (W64 (ps : Int)) = z at hq ⊢
  generalize hm : (16 + 8 * flCells n) / ps = m at hq hle ⊢
  word

/-- The page count's bounds. -/
theorem flAllocCount_bounds (n ps : Nat) (hn : n < 2 ^ 32) (hps : 80 ≤ ps) (hps32 : ps < 2 ^ 32) :
    uint.nat (flAllocCount n ps) = (16 + 8 * flCells n) / ps + 1 ∧
    0 < sint.Z (flAllocCount n ps) ∧ sint.Z (flAllocCount n ps) ≤ 2 ^ 32 ∧
    sint.Z (flAllocCount n ps) * ps < 2 ^ 47 ∧
    16 + 8 * flCells n < uint.nat (flAllocCount n ps) * ps := by
  have hc := flCells_le n
  have hle : (16 + 8 * flCells n) / ps * 80 ≤ 16 + 8 * flCells n := by
    have := Nat.div_mul_le_self (16 + 8 * flCells n) ps
    have := Nat.mul_le_mul_left ((16 + 8 * flCells n) / ps) hps
    omega
  have hmul : ((16 + 8 * flCells n) / ps + 1) * ps ≤ 16 + 8 * flCells n + ps := by
    have := Nat.div_mul_le_self (16 + 8 * flCells n) ps
    rw [Nat.add_mul, Nat.one_mul]; omega
  have hlt : 16 + 8 * flCells n < ((16 + 8 * flCells n) / ps + 1) * ps := by
    have := Nat.lt_div_mul_add (a := 16 + 8 * flCells n) (b := ps) (by omega)
    rw [Nat.add_mul, Nat.one_mul]; omega
  have hu : uint.nat (flAllocCount n ps) = (16 + 8 * flCells n) / ps + 1 := by
    unfold flAllocCount uint.nat; word
  have hs : sint.Z (flAllocCount n ps) = (((16 + 8 * flCells n) / ps + 1 : Nat) : Int) := by
    unfold flAllocCount; word
  refine ⟨hu, ?_, ?_, ?_, ?_⟩
  · rw [hs]; omega
  · rw [hs]; omega
  · rw [hs]
    have : ((((16 + 8 * flCells n) / ps + 1 : Nat) : Int)) * (ps : Int) =
        ((((16 + 8 * flCells n) / ps + 1) * ps : Nat) : Int) := by push_cast; rfl
    rw [this]; omega
  · rw [hu]; exact hlt

theorem u64sBytes_zeros (k : Nat) : u64sBytes (List.replicate k (W64 0)) = List.replicate (8 * k) (0 : w8) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    show leBytes 8 (W64 0).toNat ++ u64sBytes (List.replicate k (W64 0)) = _
    rw [ih, show 8 * (k + 1) = 8 + 8 * k by omega, ← List.replicate_append_replicate]
    rfl

end defs

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The freelist, out of the database's predicate. -/
theorem ownDB_flAcc (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState) :
    ownDB I dbl γ σ ⊢ ∃ (fls : Loc), ownFL I fls σ.fl ∗ (ownFL I fls σ.fl -∗ ownDB I dbl γ σ) := by
  iintro Hdb
  isimp only [ownDB] at Hdb
  iNamed Hdb
  iexists fls
  isplitl [Hfl]
  · iexact Hfl
  iintro Hfl
  simp only [ownDB]
  iexists dv, fls, v0, v1, dl
  isplitr
  · ipureintro; exact Hdv
  isplitr
  · ipureintro; exact Hok
  isplitr
  · ipureintro; exact Hdr
  isplitr
  · ipureintro; exact Hops
  iframe
  iframe #
  try (ipureintro; exact Hlog)

/-- A page of the page cache, its buffer replaced. -/
theorem bufs_update (pm : GMap w64 Loc) (bufs : GMap w64 (List w8)) (id : w64) (p : Loc)
    (hp : pm !! id = some p) :
    ([∗map] i ↦ q ∈ pm, ∃ b, ⌜bufs !! i = some b⌝ ∗ bytesPointsto (GF := GF) q (DFrac.own 1) b) ⊢
      (∃ b, ⌜bufs !! id = some b⌝ ∗ bytesPointsto (GF := GF) p (DFrac.own 1) b) ∗
      ∀ b', bytesPointsto (GF := GF) p (DFrac.own 1) b' -∗
        [∗map] i ↦ q ∈ pm, ∃ b, ⌜(<[id := b']> bufs) !! i = some b⌝ ∗
          bytesPointsto (GF := GF) q (DFrac.own 1) b := by
  iintro H
  icases (BigSepM.bigSepM_delete (M := GMap w64)
    (Φ := fun i q => iprop(∃ b, ⌜bufs !! i = some b⌝ ∗ bytesPointsto (GF := GF) q (DFrac.own 1) b))
    (show Std.get? pm id = some p from hp)).1 $$ H with ⟨Hp, Hrest⟩
  isplitl [Hp]
  · iexact Hp
  iintro %b' Hb'
  iapply (BigSepM.bigSepM_delete (M := GMap w64)
    (Φ := fun i q => iprop(∃ b, ⌜(<[id := b']> bufs) !! i = some b⌝ ∗
      bytesPointsto (GF := GF) q (DFrac.own 1) b))
    (show Std.get? pm id = some p from hp)).2
  isplitl [Hb']
  · iexists b'; iframe; ipureintro; exact GMap.lookup_insert _ _ _
  iapply (BigSepM.bigSepM_mono (M := GMap w64) ?_) $$ Hrest
  intro i q hi
  iintro ⟨%b, %hb, Hb⟩
  iexists b
  iframe
  ipureintro
  have hne : i ≠ id := by
    intro e; subst e
    change (GMap.delete i pm) !! i = some q at hi
    rw [GMap.lookup_delete] at hi; cases hi
  rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hb

/-- The fresh page: its header (as a `Page`), `k` zero cells after it (a slice of `uint64`s, as
`Write` takes them) and zeroes. -/
theorem fresh_fl_split (l : Loc) (id : w64) (count ps k : Nat) (hl : l.locCar ≠ 0)
    (hc : 0 < count) (hc32 : count ≤ 2 ^ 32) (hk : 16 + 8 * k ≤ count * ps) (hk60 : k < 2 ^ 60) :
    bytesPointsto (GF := GF) l (DFrac.own 1) (freshPage id count ps) ⊢
      l ↦ Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int)) ∗
      slice.mk (l +ₗ 16) (W64 (k : Int)) (W64 (k : Int)) ↦* List.replicate k (W64 0) ∗
      bytesPointsto (GF := GF) (l +ₗ ((16 + 8 * k : Nat) : Int)) (DFrac.own 1)
        (List.replicate (count * ps - 16 - 8 * k) 0) := by
  have hov : (W32 ((count - 1 : Nat) : Int)).toNat = count - 1 := by
    simp; omega
  have hb : pageBytes (Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int))) =
      leBytes 8 (uint.Z id) ++ leBytes 4 0 ++ leBytes 4 (((count - 1 : Nat) : Int)) := by
    unfold pageBytes
    simp only
    rw [hov, leBytes_zero_4]
    simp [List.append_assoc]
  have hlen : (pageBytes (Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int)))).length =
      16 := by
    simp [pageBytes, leBytes_length]
  have e : freshPage id count ps =
      pageBytes (Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int))) ++
        (List.replicate (8 * k) 0 ++ List.replicate (count * ps - 16 - 8 * k) 0) := by
    unfold freshPage; rw [hb, List.replicate_append_replicate, show 8 * k + (count * ps - 16 - 8 * k) =
      count * ps - 16 by omega]
  rw [e]
  iintro Hb
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hh, Hz⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ Hz with ⟨Hz, Hr⟩
  rw [hlen]
  ihave Hh := (Page_bytes (hG := hG) l _ _ hl).2 $$ Hh
  iframe Hh
  rw [List.length_replicate, loc_add_assoc,
    show ((16 : Nat) : Int) + ((8 * k : Nat) : Int) = ((16 + 8 * k : Nat) : Int) by omega]
  iframe Hr
  have hc16 : (l +ₗ ((16 : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using hl
  by_cases hk0 : k = 0
  · subst hk0
    rw [show List.replicate 0 (W64 0) = ([] : List w64) from rfl]
    iapply ownSlice_empty (V := w64) (DFrac.own 1) _ (by simp only; word) (by simp only; word)
    iapply array_empty
    exact loc_ne_null_of_car _ hc16
  · rw [← u64sBytes_zeros k]
    iapply (ownSlice_u64s (GF := GF) (slice.mk (l +ₗ 16) (W64 (k : Int)) (W64 (k : Int)))
      (List.replicate k (W64 0)) (DFrac.own 1)
      (by intro h; exact hk0 (by simpa using congrArg List.length h)) (by simpa using hc16)).2
    iframe
    ipureintro
    simp only [List.length_replicate]
    constructor <;> word

/-- `Write`'s header and cells and the zeroes after them, as the page's bytes. -/
theorem fl_written_join (l : Loc) (pv : Page) (xs : List w64) (k : Nat)
    (zs : List w8) (hl : l.locCar ≠ 0) (hk : xs.length = k) (hlen : xs.length < 2 ^ 60) :
    l ↦ pv ∗ slice.mk (l +ₗ 16) (W64 (k : Int)) (W64 (k : Int)) ↦* xs ∗
      bytesPointsto (GF := GF) (l +ₗ ((16 + 8 * k : Nat) : Int)) (DFrac.own 1) zs ⊢
      bytesPointsto (GF := GF) l (DFrac.own 1) (pageBytes pv ++ u64sBytes xs ++ zs) := by
  subst hk
  iintro ⟨Hh, Hs, Hz⟩
  ihave Hh := (Page_bytes (hG := hG) l _ _ hl).1 $$ Hh
  have hplen : (pageBytes pv).length = 16 := by simp [pageBytes, leBytes_length]
  iapply (bytesPointsto_app _ _ _ _).2
  rw [List.length_append, u64sBytes_length, hplen]
  iframe Hz
  iapply (bytesPointsto_app _ _ _ _).2
  rw [hplen]
  iframe Hh
  have hc16 : (l +ₗ ((16 : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using hl
  cases xs with
  | nil =>
    rw [show u64sBytes [] = [] from rfl]
    unfold bytesPointsto pointstoVals byteVals
    simp only [List.map_nil]
    iempintro
  | cons x xs' =>
    icases (ownSlice_u64s (GF := GF) (slice.mk (l +ₗ 16) (W64 ((x :: xs').length : Int))
      (W64 ((x :: xs').length : Int))) (x :: xs') (DFrac.own 1) (by simp)
      (by simpa using hc16)).1 $$ Hs with ⟨Hs, -⟩
    iexact Hs

end own

end bbolt
end EtcdGrove
end Perennial
