/-
A freelist page's bytes, as `freelist.Read` takes them (`shared.Read.spec`): the header (a
`Page`), the overflow count cell (when the header's count is `0xFFFF`), and the ids, a slice of
`uint64`s after them (`flIds`); the rest of the page's bytes stay.
-/
module

public import Proof.go_etcd_io.bbolt.U64Bytes
public import Proof.go_etcd_io.bbolt.PageView
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Read

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The overflow count of a freelist page (the `uint64` after its header). -/
def flPageCount (pg : List w8) : w64 := W64 (leAt pg 16 8 : Int)

/-- The number of ids of a freelist page. -/
def flN (pg : List w8) : Nat := uint.nat (fpCount (pageOf pg) (flPageCount pg))

/-- The offset of a freelist page's first id. -/
def flOff (pg : List w8) : Nat := 16 + 8 * uint.nat (fpIdx (pageOf pg))

/-- The ids of a freelist page. -/
def flIds (pg : List w8) : List w64 :=
  (List.range (flN pg)).map (fun i => W64 (leAt pg (flOff pg + 8 * i) 8 : Int))

theorem flIds_length (pg : List w8) : (flIds pg).length = flN pg := by simp [flIds]

theorem u64sBytes_range (pg : List w8) :
    ∀ (n off : Nat), off + 8 * n ≤ pg.length →
      u64sBytes ((List.range n).map (fun i => W64 (leAt pg (off + 8 * i) 8 : Int))) =
        bytesAt pg off (8 * n)
  | 0, off, _ => by simp [u64sBytes, bytesAt]
  | n + 1, off, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have hf : ((fun i => W64 (leAt pg (off + 8 * i) 8 : Int)) ∘ Nat.succ) =
        (fun i => W64 (leAt pg ((off + 8) + 8 * i) 8 : Int)) := by
      funext i; simp only [Function.comp]; congr 3; omega
    rw [hf]
    show leBytes 8 ((W64 (leAt pg (off + 8 * 0) 8 : Int)).toNat : Int) ++ u64sBytes _ = _
    rw [u64sBytes_range pg n (off + 8) (by omega), Nat.mul_zero, Nat.add_zero,
      toNat_W64 _ (by have := leAt_lt pg off 8; simpa using this),
      leBytes_leAt pg off 8 (by omega), bytesAt_append, show 8 + 8 * n = 8 * (n + 1) by omega]

end pure

section view
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem fl_cnt_sint (c : w64) (n : Nat) (h : uint.nat c = n) (hn : n < 2 ^ 62) :
    sint.Z c = (n : Int) := by
  word

theorem fl_w1 : uint.nat (W64 1) = 1 := by word
theorem fl_w0 : uint.nat (W64 0) = 0 := by word

theorem fl_cnt_toNat (pg : List w8) : ((leAt pg 16 8 : Nat) : Int) = ((flPageCount pg).toNat : Int) := by
  unfold flPageCount
  rw [toNat_W64 _ (by have := leAt_lt pg 16 8; simpa using this)]

theorem fl_cnt_zero (c : w64) (h : uint.nat c = 0) : c = W64 0 := by
  word

theorem fl_cnt_ne (c : w64) (h : uint.nat c ≠ 0) : c ≠ W64 0 := by
  intro e; subst e; exact h rfl

/-- The ids of a freelist page, from `off` (its first id's offset) on. -/
theorem flpage_ids (l : Loc) (q : DFrac) (pg : List w8) (off : Nat) (hc : l.locCar ≠ 0)
    (hoff : off = flOff pg) (hfit : flOff pg + 8 * flN pg ≤ pg.length) (hlen : pg.length < 2 ^ 62) :
    bytesPointsto (GF := GF) (l +ₗ (off : Int)) q (pg.drop off) ⊣⊢
      fpIdsSlice l (pageOf pg) (flPageCount pg) ↦*{q} flIds pg ∗
      bytesPointsto (l +ₗ ((flOff pg + 8 * flN pg : Nat) : Int)) q
        (pg.drop (flOff pg + 8 * flN pg)) := by
  subst hoff
  unfold fpIdsSlice
  by_cases hn : flN pg = 0
  · have h0 : fpCount (pageOf pg) (flPageCount pg) = W64 0 := fl_cnt_zero _ hn
    rw [if_pos h0]
    have hids : flIds pg = [] := by simp [flIds, hn]
    rw [hids, hn, Nat.mul_zero, Nat.add_zero]
    constructor
    · iintro H; isplitr
      · iapply ownSlice_nil
      · iexact H
    · iintro ⟨-, H⟩; iexact H
  · have h0 : fpCount (pageOf pg) (flPageCount pg) ≠ W64 0 := fl_cnt_ne _ hn
    rw [if_neg h0]
    have hne : flIds pg ≠ [] := by
      intro e; have := congrArg List.length e; rw [flIds_length] at this; simp at this; exact hn this
    have hcar : (l +ₗ ((flOff pg : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using hc
    have hptr : l +ₗ (16 + 8 * uint.Z (fpIdx (pageOf pg))) = l +ₗ ((flOff pg : Nat) : Int) := by
      unfold flOff; congr 1; try (simp only [uint.nat]; push_cast; try rw [Int.toNat_of_nonneg (by word)])
    have hsplit : pg.drop (flOff pg) =
        bytesAt pg (flOff pg) (8 * flN pg) ++ pg.drop (flOff pg + 8 * flN pg) := by
      unfold bytesAt; rw [← List.drop_drop, List.take_append_drop]
    have hbytes := u64sBytes_range pg (flN pg) (flOff pg) hfit
    have hsint := fl_cnt_sint (fpCount (pageOf pg) (flPageCount pg)) (flN pg) rfl (by omega)
    rw [hsplit]
    refine (bytesPointsto_app _ _ _ _).trans ?_
    rw [bytesAt_length pg _ _ hfit, loc_add_assoc,
      show ((flOff pg : Nat) : Int) + ((8 * flN pg : Nat) : Int) = ((flOff pg + 8 * flN pg : Nat) : Int)
        by omega, ← hbytes]
    refine sep_congr ?_ .rfl
    refine Iris.BI.BiEntails.trans ?_ (ownSlice_u64s _ _ _ hne (by simp only; rw [hptr]; exact hcar)).symm
    simp only [hptr, flIds]
    constructor
    · iintro H; iframe; ipureintro; rw [List.length_map, List.length_range, hsint]; exact ⟨rfl, Int.le_refl _⟩
    · iintro ⟨H, -⟩; iexact H

/-- A freelist page's bytes are what `Read` takes and the rest. -/
theorem flpage_bytes (l : Loc) (q : DFrac) (pg : List w8) (hc : l.locCar ≠ 0)
    (hfit : flOff pg + 8 * flN pg ≤ pg.length) (hlen : pg.length < 2 ^ 62) :
    bytesPointsto (GF := GF) l q pg ⊣⊢
      l ↦{q} pageOf pg ∗ fpCountCell l (pageOf pg) q (flPageCount pg) ∗
      fpIdsSlice l (pageOf pg) (flPageCount pg) ↦*{q} flIds pg ∗
      bytesPointsto (l +ₗ ((flOff pg + 8 * flN pg : Nat) : Int)) q
        (pg.drop (flOff pg + 8 * flN pg)) := by
  have h16 : 16 ≤ pg.length := by unfold flOff at hfit; omega
  refine (page_header_bytes (hG := hG) l q pg h16 hc).trans (sep_congr .rfl ?_)
  unfold fpCountCell
  by_cases hov : fpOverflow (pageOf pg)
  · rw [if_pos hov]
    have hoff : flOff pg = 24 := by unfold flOff fpIdx; rw [if_pos hov, fl_w1]
    have hsplit : pg.drop 16 = bytesAt pg 16 8 ++ pg.drop 24 := by
      unfold bytesAt; rw [show (24 : Nat) = 16 + 8 from rfl, ← List.drop_drop, List.take_append_drop]
    rw [hsplit]
    refine (bytesPointsto_app _ _ _ _).trans (sep_congr ?_ ?_)
    · rw [← leBytes_leAt pg 16 8 (by omega), fl_cnt_toNat]
      exact (typedPointsto_w64_bytes _ _ _).symm
    · rw [bytesAt_length pg 16 8 (by omega), loc_add_assoc]
      have := flpage_ids (GF := GF) l q pg 24 hc hoff.symm hfit hlen
      rw [show ((16 : Int) + ((8 : Nat) : Int)) = ((24 : Nat) : Int) by omega]
      exact this
  · rw [if_neg hov]
    have hoff : flOff pg = 16 := by unfold flOff fpIdx; rw [if_neg hov, fl_w0]
    refine Iris.BI.BiEntails.trans ?_ (true_sep (PROP := IProp GF)).symm
    have := flpage_ids (GF := GF) l q pg 16 hc hoff.symm hfit hlen
    exact this

end view

end bbolt
end EtcdGrove
end Perennial
