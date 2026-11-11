/-
The meta slots' resources at the commit point (U10 of `notes/bbolt-proof-plan.md`), slot-generic:
the page-cache bytes of `metalock`'s and the writer's halves as slot `s` (whole) and the other slot
(whole), and back; the meta cells' two quarters (the writer's and the lent ones) as slot `s`'s and
the other slot's bytes at a half, and back; a published state's slots.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.Mmap.RemapGather
public import Proof.go_etcd_io.bbolt.Mmap.RemapCells
public import Proof.os.WriteChunks
public import Proof.os.CrashFile

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

theorem publish_slot [GooseExts] (C : CommitSt) (buf : List w8) (m : Meta) (pages : Pages) (i : Nat) :
    (C.publish buf m pages).slot i =
      if i % 2 = m.txid'.toNat % 2 then buf else C.slot i := by
  unfold CommitSt.slot CommitSt.publish
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
  rcases Nat.mod_two_eq_zero_or_one m.txid'.toNat with ht | ht <;> simp [hi, ht]

section bytes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Two halves of the same bytes of a file, as the whole (they agree). -/
theorem osBytes_join_h (p : GoString) :
    ∀ (xs ys : List (w8 × Bool)) (off : Nat), xs.length = ys.length →
    osBytes (GF := GF) p off (DFrac.own (1 : Qp).half) xs ∗
      osBytes (GF := GF) p off (DFrac.own (1 : Qp).half) ys ⊢
      osBytes (GF := GF) p off (DFrac.own 1) xs
  | [], _, off, _ => by
    iintro -; iapply (osBytes_nil' (GF := GF) p off _).2; iempintro
  | x :: xs, [], _, h => by simp at h
  | x :: xs, y :: ys, off, h => by
    iintro ⟨H1, H2⟩
    icases (osBytes_cons' (GF := GF) p off _ x xs).1 $$ H1 with ⟨Hx, H1⟩
    icases (osBytes_cons' (GF := GF) p off _ y ys).1 $$ H2 with ⟨Hy, H2⟩
    iapply (osBytes_cons' (GF := GF) p off _ x xs).2
    unfold osByte
    icases gElem_valid_2 _ _ _ _ _ x y $$ Hx Hy with %Hxy
    obtain ⟨-, rfl⟩ := Hxy
    isplitl [Hx Hy]
    · conv => rhs; rw [← Qp.half_add_half 1]
      iapply (gElem_split _ _ _ _ _ _).2; iframe
    · iapply osBytes_join_h p xs ys (off + 1) (by simpa using h); iframe

omit sem in
theorem osBytes_halves_h (p : GoString) (off : Nat) (xs : List (w8 × Bool)) :
    osBytes (GF := GF) p off (DFrac.own 1) xs ⊢
      osBytes (GF := GF) p off (DFrac.own (1 : Qp).half) xs ∗
        osBytes (GF := GF) p off (DFrac.own (1 : Qp).half) xs :=
  (osBytes_halves p off xs).1

/-- **The meta slots' page-cache bytes, whole, as slot `s` and the other slot** (from the two
halves: `metalock`'s and the writer's). -/
theorem metaOsBytes_take (p : GoString) (C : CommitSt) (s : Nat) (hs : s < 2)
    (h0 : C.m0.length = 4096) (h1 : C.m1.length = 4096) :
    metaOsBytes (GF := GF) p (DFrac.own (1 : Qp).half) C ∗
      metaOsBytes (GF := GF) p (DFrac.own (1 : Qp).half) C ⊢
    ∃ xa xb : List (w8 × Bool), osBytes p (4096 * s) (DFrac.own 1) xa ∗
      osBytes p (4096 * (1 - s)) (DFrac.own 1) xb ∗
      ⌜xa.map Prod.fst = C.slot s ∧ xb.map Prod.fst = C.slot (s + 1)⌝ := by
  unfold metaOsBytes
  iintro ⟨⟨%xs, H1, %hx⟩, ⟨%ys, H2, %hy⟩⟩
  have hxl : xs.length = 8192 := by
    have := congrArg List.length hx; simp only [List.length_map, List.length_append] at this; omega
  have hyl : ys.length = 8192 := by
    have := congrArg List.length hy; simp only [List.length_map, List.length_append] at this; omega
  ihave H := osBytes_join_h p xs ys 0 (by omega) $$ [H1 H2]
  · iframe
  icases (osBytes_take_drop p 0 _ xs 4096 (by omega)).1 $$ H with ⟨Ha, Hb⟩
  have e0 : (xs.take 4096).map Prod.fst = C.m0 := by
    rw [List.map_take, hx, List.take_left' h0]
  have e1 : (xs.drop 4096).map Prod.fst = C.m1 := by
    rw [List.map_drop, hx, List.drop_left' h0]
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · iexists xs.take 4096, xs.drop 4096
    iframe
    ipureintro; simp [CommitSt.slot, e0, e1]
  · iexists xs.drop 4096, xs.take 4096
    iframe
    ipureintro; simp [CommitSt.slot, e0, e1]

/-- **The meta slots' bytes back as the two halves**, holding `C`. -/
theorem metaOsBytes_put (p : GoString) (C : CommitSt) (s : Nat) (hs : s < 2)
    (h0 : C.m0.length = 4096) (h1 : C.m1.length = 4096) (xa xb : List (w8 × Bool))
    (ha : xa.map Prod.fst = C.slot s) (hb : xb.map Prod.fst = C.slot (s + 1)) :
    osBytes (GF := GF) p (4096 * s) (DFrac.own 1) xa ∗
      osBytes (GF := GF) p (4096 * (1 - s)) (DFrac.own 1) xb ⊢
    metaOsBytes (GF := GF) p (DFrac.own (1 : Qp).half) C ∗
      metaOsBytes (GF := GF) p (DFrac.own (1 : Qp).half) C := by
  have hla := congrArg List.length ha
  have hlb := congrArg List.length hb
  simp only [List.length_map] at hla hlb
  unfold metaOsBytes
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · simp only [CommitSt.slot, Nat.zero_mod, ↓reduceIte, show (0 + 1) % 2 = 1 from rfl,
      show (1 : Nat) ≠ 0 from by decide] at ha hb hla hlb
    rw [show 4096 * 0 = 0 from rfl, show 4096 * (1 - 0) = 4096 from rfl]
    iintro ⟨Ha, Hb⟩
    ihave H : osBytes p 0 (DFrac.own 1) (xa ++ xb) $$ [Ha Hb]
    · iapply (osBytes_take_drop p 0 _ (xa ++ xb) 4096 (by simp; omega)).2
      rw [List.take_left' (by omega), List.drop_left' (by omega)]
      iframe
    icases osBytes_halves_h p 0 _ $$ H with ⟨H1, H2⟩
    have e : (xa ++ xb).map Prod.fst = C.m0 ++ C.m1 := by rw [List.map_append, ha, hb]
    isplitl [H1]
    · iexists _; iframe; ipureintro; exact e
    · iexists _; iframe; ipureintro; exact e
  · simp only [CommitSt.slot, show 1 % 2 = 1 from rfl, show (1 + 1) % 2 = 0 from rfl, ↓reduceIte,
      show (1 : Nat) ≠ 0 from by decide] at ha hb hla hlb
    rw [show 4096 * 1 = 4096 from rfl, show 4096 * (1 - 1) = 0 from rfl]
    iintro ⟨Ha, Hb⟩
    ihave H : osBytes p 0 (DFrac.own 1) (xb ++ xa) $$ [Ha Hb]
    · iapply (osBytes_take_drop p 0 _ (xb ++ xa) 4096 (by simp; omega)).2
      rw [List.take_left' (by omega), List.drop_left' (by omega)]
      iframe
    icases osBytes_halves_h p 0 _ $$ H with ⟨H1, H2⟩
    have e : (xb ++ xa).map Prod.fst = C.m0 ++ C.m1 := by rw [List.map_append, ha, hb]
    isplitl [H1]
    · iexists _; iframe; ipureintro; exact e
    · iexists _; iframe; ipureintro; exact e

omit hos sem in
/-- **The meta cells' two quarters as slot `s`'s and the other slot's bytes at a half.** -/
theorem metaCells_take (C : CommitSt) (b : Loc) (l s : Nat) (hs : s < 2) :
    metaCellsQ (GF := GF) (1 : Qp).half.half (some (b, l)) C ∗
      metaCellsQ (GF := GF) (1 : Qp).half.half (some (b, l)) C ⊢
    bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (C.slot s) ∗
      bytesPointsto (b +ₗ ((4096 * (1 - s) : Nat) : Int)) (DFrac.own (1 : Qp).half)
        (C.slot (s + 1)) := by
  unfold metaCellsQ
  iintro ⟨⟨A0, A1⟩, ⟨B0, B1⟩⟩
  icases (bytes_quarters b C.m0).1 $$ [A0 B0] with H0
  · iframe
  icases (bytes_quarters _ C.m1).1 $$ [A1 B1] with H1
  · iframe
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · simp only [CommitSt.slot, Nat.zero_mod, ↓reduceIte, show (0 + 1) % 2 = 1 from rfl,
      show (1 : Nat) ≠ 0 from by decide, show 4096 * 0 = 0 from rfl,
      show 4096 * (1 - 0) = 4096 from rfl, Int.natCast_zero, loc_add_0]
    iframe
  · simp only [CommitSt.slot, show 1 % 2 = 1 from rfl, show (1 + 1) % 2 = 0 from rfl, ↓reduceIte,
      show (1 : Nat) ≠ 0 from by decide, show 4096 * 1 = 4096 from rfl,
      show 4096 * (1 - 1) = 0 from rfl, Int.natCast_zero, loc_add_0]
    iframe

omit hos sem in
/-- **The meta cells' two quarters back**, holding `C`. -/
theorem metaCells_put (C : CommitSt) (b : Loc) (l s : Nat) (hs : s < 2) :
    bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (C.slot s) ∗
      bytesPointsto (b +ₗ ((4096 * (1 - s) : Nat) : Int)) (DFrac.own (1 : Qp).half)
        (C.slot (s + 1)) ⊢
    metaCellsQ (GF := GF) (1 : Qp).half.half (some (b, l)) C ∗
      metaCellsQ (GF := GF) (1 : Qp).half.half (some (b, l)) C := by
  unfold metaCellsQ
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · simp only [CommitSt.slot, Nat.zero_mod, ↓reduceIte, show (0 + 1) % 2 = 1 from rfl,
      show (1 : Nat) ≠ 0 from by decide, show 4096 * 0 = 0 from rfl,
      show 4096 * (1 - 0) = 4096 from rfl, Int.natCast_zero, loc_add_0]
    iintro ⟨H0, H1⟩
    icases (bytes_quarters b C.m0).2 $$ H0 with ⟨A0, B0⟩
    icases (bytes_quarters _ C.m1).2 $$ H1 with ⟨A1, B1⟩
    iframe
  · simp only [CommitSt.slot, show 1 % 2 = 1 from rfl, show (1 + 1) % 2 = 0 from rfl, ↓reduceIte,
      show (1 : Nat) ≠ 0 from by decide, show 4096 * 1 = 4096 from rfl,
      show 4096 * (1 - 1) = 0 from rfl, Int.natCast_zero, loc_add_0]
    iintro ⟨H1, H0⟩
    icases (bytes_quarters b C.m0).2 $$ H0 with ⟨A0, B0⟩
    icases (bytes_quarters _ C.m1).2 $$ H1 with ⟨A1, B1⟩
    iframe

end bytes

end bbolt
end EtcdGrove
end Perennial
