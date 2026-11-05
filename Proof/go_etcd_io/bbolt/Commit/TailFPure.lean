/-
**`Commit`'s tail over the flagged writer side, its pure part** (U10m): after the free of the
synced freelist page the writer side satisfies `wdbOK' true` only, of which `wdbOK` holds of
`w.noFl` (`wdbOK'_noFl`). The tail's lemmas stated over `wdbOK` (`cm_write_pre`, `cm_pub_ok`,
`wdbOK_written`, `cm_unpub_ok`, ...) apply to `w.noFl`, whose committed state differs from `w.C`
only in `flpg`, which none of the tail's statements reads but `flClause` (the `noFl_*` facts
below); `wdbOK' fr` and `fbRel` come back through a write of `W` slots by `flExtPend` (the freed
page's slots are pending, so no `W` slot).

`flExtPend_of_true` is OPEN (reported): `flCurOKr`'s slot clause lets a slot of the freed page's
extent be in no list (then a `W` slot, which a write could change); after the free every one is
pending, and the clause should say so.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailPub
public import Proof.go_etcd_io.bbolt.Inv.WdbFlag

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **The freed synced freelist page's slots are pending** (vacuous with no synced page). -/
def flExtPend (w : WDb) : Prop :=
  ∀ f, w.C.flpg = some f → ∀ s, f ≤ s → s < f + (1 + pageOverflow (w.wb f)) → s ∈ pendSlots w.fl

theorem flExtPend_none (w : WDb) (h : w.C.flpg = none) : flExtPend w := by
  intro f hf; rw [h] at hf; cases hf

/-- OPEN (reported): `flCurOKr`'s slot clause should require the extent's slots pending. -/
theorem flExtPend_of_true (w : WDb) (h : wdbOK' true w) : flExtPend w := by
  sorry

theorem noFl_C (w : WDb) : w.noFl.C = { w.C with flpg := none } := rfl
theorem noFl_fl (w : WDb) : w.noFl.fl = w.fl := rfl
theorem noFl_W (w : WDb) : w.noFl.W = w.W := rfl
theorem noFl_wb (w : WDb) : w.noFl.wb = w.wb := rfl
theorem noFl_m (w : WDb) : w.noFl.m = w.m := rfl
theorem noFl_ms (w : WDb) : w.noFl.ms = w.ms := rfl
theorem noFl_wtxid (w : WDb) : w.noFl.wtxid = w.wtxid := rfl
theorem noFl_flpg (w : WDb) : w.noFl.C.flpg = none := rfl

theorem noFl_reslot (w : WDb) (m : OsMeta) (W : List Nat) (wb : Nat → List w8) :
    w.noFl.reslot m W wb = (w.reslot m W wb).noFl := rfl

theorem noFl_withC (w : WDb) (C : CommitSt) : w.noFl.withC C = w.withC C := rfl

theorem noFl_treeSlots (w : WDb) : treeSlots w.noFl.C = treeSlots w.C := rfl
theorem noFl_slotsOf (w : WDb) : slotsOf w.noFl.C w.noFl.fl = slotsOf w.C w.fl := rfl

theorem pubC_noFl (w : WDb) (mv : Meta) (P : Pages) : pubC w.noFl.C mv P = pubC w.C mv P := rfl

theorem pubP_noFl (w : WDb) (X : WX) (P : Pages) : pubP w.noFl X P = pubP w X P := rfl

theorem cmTail_noFl (w : WDb) (SB : List Nat) (l : Nat) : cmTail w.noFl SB l = cmTail w SB l := rfl

/-- `cmPubPre` does not read the synced freelist page. -/
theorem cmPubPre_noFl (D : Data) (X : WX) (w : WDb) (h : cmPubPre D X w) : cmPubPre D X w.noFl :=
  h

theorem cmPubPg_noFl (D : Data) (X : WX) (w : WDb) (P : Pages) (h : cmPubPg D X w P) :
    cmPubPg D X w.noFl P := h

/-- `cpOK` does not read the synced freelist page. -/
theorem cpOK_noFl (w : WDb) (b : Loc) (l : Nat) (mv : Meta) (P : Pages) (D : Data) (S : List Nat)
    (bs : Nat → List w8) (h : cpOK w.noFl.C w.noFl.fl b l mv P D S bs) : cpOK w.C w.fl b l mv P D S bs :=
  h

omit [GooseExts] in
theorem tf_flatMap_congr {α β : Type} : ∀ {l : List α} {f g : α → List β},
    (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _, _, _ => rfl
  | a :: l, f, g, h => by
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), tf_flatMap_congr (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **`flClause` keeps through a change of the slots' bytes off the pending slots**, given that
the freed page's slots are pending. -/
theorem flClause_wb (fr : Bool) (w w' : WDb) (hC : w'.C = w.C) (hfl : w'.fl = w.fl)
    (hep : flExtPend w) (hwb : ∀ s, s ∈ pendSlots w.fl → w'.wb s = w.wb s) (h : flClause fr w) :
    flClause fr w' := by
  have hf0 : ∀ f, w.C.flpg = some f → w'.wb f = w.wb f := fun f hf =>
    hwb f (hep f hf f (Nat.le_refl _) (by omega))
  have hext : ∀ f, w.C.flpg = some f → extentBytes w'.wb f = extentBytes w.wb f := by
    intro f hf
    unfold extentBytes
    rw [hf0 f hf]
    refine tf_flatMap_congr fun s hs => ?_
    rw [List.mem_range'_1] at hs
    exact hwb s (hep f hf s hs.1 hs.2)
  cases fr
  · intro f hf
    rw [hC] at hf
    rw [hC, hfl, hext f hf]
    exact h f hf
  · intro f hf
    rw [hC] at hf
    refine ⟨by rw [hf0 f hf]; exact (h f hf).1, ?_⟩
    have := (h f hf).2
    simp only [WDb.wtxid] at this ⊢
    rw [hC, hfl, hext f hf]
    exact this

/-- `fbRel` keeps likewise. -/
theorem fbRel_wb (w w' : WDb) (F : GMap Nat (List w8)) (hC : w'.C = w.C) (hfl : w'.fl = w.fl)
    (hep : flExtPend w) (hwb : ∀ s, s ∈ pendSlots w.fl → w'.wb s = w.wb s) (h : fbRel w F) :
    fbRel w' F := by
  intro f hf s h1 h2 hs
  rw [hC] at hf
  have hf0 : w'.wb f = w.wb f := hwb f (hep f hf f (Nat.le_refl _) (by omega))
  rw [hf0] at h2
  rw [hfl] at hs
  have := h f hf s h1 h2 hs
  simp only [WDb.wtxid] at this ⊢
  rw [hC, hfl, hwb s hs]
  exact this

theorem flExtPend_wb (w w' : WDb) (hC : w'.C = w.C) (hfl : w'.fl = w.fl)
    (hep : flExtPend w) (hwb : ∀ s, s ∈ pendSlots w.fl → w'.wb s = w.wb s) : flExtPend w' := by
  intro f hf s h1 h2
  rw [hC] at hf
  have hf0 : w'.wb f = w.wb f := hwb f (hep f hf f (Nat.le_refl _) (by omega))
  rw [hf0] at h2
  rw [hfl]
  exact hep f hf s h1 h2

/-- **`wdbOK' fr` back from `wdbOK` of `w'.noFl`** (`w'` a change of `w`'s slots' bytes off the
pending slots). -/
theorem wdbOK'_of_noFl_wb (fr : Bool) (w w' : WDb) (hC : w'.C = w.C) (hfl : w'.fl = w.fl)
    (hep : flExtPend w) (hwb : ∀ s, s ∈ pendSlots w.fl → w'.wb s = w.wb s)
    (hc : flClause fr w) (h : wdbOK w'.noFl) : wdbOK' fr w' :=
  wdbOK'_of_noFl fr w' h (flClause_wb fr w w' hC hfl hep hwb hc)

/-- A `W` slot is not pending (`wdbOK'`'s fourth clause). -/
theorem wdbOK'_W_not_pend (fr : Bool) (w : WDb) (h : wdbOK' fr w) (s : Nat) (hs : s ∈ w.W) :
    s ∉ pendSlots w.fl :=
  ((h.2.2.2.1 s).1 hs).2.2.2

/-- `wbUpd` of `W` slots leaves the pending slots' bytes. -/
theorem wbUpd_pend (fr : Bool) (w : WDb) (h : wdbOK' fr w) (S : List Nat) (wb' : Nat → List w8)
    (hS : ∀ s ∈ S, s ∈ w.W) : ∀ s, s ∈ pendSlots w.fl → wbUpd S wb' w.wb s = w.wb s := by
  intro s hs
  unfold wbUpd
  rw [if_neg (fun hm => wdbOK'_W_not_pend fr w h s (hS s hm) hs)]

end pure

end bbolt
end EtcdGrove
end Perennial
