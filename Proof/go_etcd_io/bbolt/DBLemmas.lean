/-
Lemmas about the database's accounting (`DBPred.lean`): the readers' fractions when a reader
begins or ends.
-/
module

public import Proof.go_etcd_io.bbolt.DBPred

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

theorem optAdd_left_comm (a b : Qp) (o : Option Qp) :
    optAdd a (optAdd b o) = optAdd b (optAdd a o) := by
  cases o <;> simp only [optAdd, Option.some.injEq, Qp.ext_iff, Qp.val_add] <;> grind

/-- The step of `readersQ`. -/
def readersStep (sees : Reader → Bool) : Nat → Reader → Option Qp → Option Qp :=
  fun _ r acc => if sees r then optAdd r.q acc else acc

theorem readersStep_comm (sees : Reader → Bool) (j1 : Nat) (z1 : Reader) (j2 : Nat) (z2 : Reader)
    (y : Option Qp) :
    readersStep sees j1 z1 (readersStep sees j2 z2 y) =
      readersStep sees j2 z2 (readersStep sees j1 z1 y) := by
  unfold readersStep
  cases sees z1 <;> cases sees z2 <;> simp [optAdd_left_comm]

theorem readersQ_eq (rs : GMap Nat Reader) (sees : Reader → Bool) :
    readersQ rs sees = GMap.mapFold (readersStep sees) none rs := rfl

/-- A new reader adds its fraction where it sees. -/
theorem readersQ_insert (rs : GMap Nat Reader) (sees : Reader → Bool) (k : Nat) (r : Reader)
    (h : rs !! k = none) :
    readersQ (<[k := r]> rs) sees = readersStep sees k r (readersQ rs sees) := by
  rw [readersQ_eq, readersQ_eq,
    GMap.mapFold_insert _ _ rs k r (readersStep_comm sees) h]

/-- An ending reader takes its fraction away. -/
theorem readersQ_delete (rs : GMap Nat Reader) (sees : Reader → Bool) (k : Nat) (r : Reader)
    (h : rs !! k = some r) :
    readersQ rs sees = readersStep sees k r (readersQ (GMap.delete k rs) sees) := by
  have Hins := readersQ_insert (GMap.delete k rs) sees k r (GMap.lookup_delete rs k)
  rwa [GMap.delete_insert_id rs k r h] at Hins

/-- No reader sees: no fraction. -/
theorem readersQ_none (rs : GMap Nat Reader) (sees : Reader → Bool)
    (h : ∀ k r, rs !! k = some r → sees r = false) : readersQ rs sees = none := by
  revert h
  refine GMap.mapFold_ind (fun b m => (∀ k r, m !! k = some r → sees r = false) → b = none)
    (readersStep sees) none (readersStep_comm sees) (fun _ => rfl) ?_ rs
  intro k v m b hk ih hall
  have hv : sees v = false := hall k v (GMap.lookup_insert m k v)
  have hm : ∀ k' r', m !! k' = some r' → sees r' = false := by
    intro k' r' h'
    have hne : k ≠ k' := by rintro rfl; rw [hk] at h'; cases h'
    exact hall k' r' (by rw [GMap.lookup_insert_ne m v hne]; exact h')
  unfold readersStep; rw [hv]; exact ih hm

/-- A reader that takes `q` of what the database had. -/
theorem fracSum_take (a a' q w : Qp) (o : Option Qp) (h : fracSum a o w) (ha : a = a' + q) :
    fracSum a' (optAdd q o) w := by
  cases o <;> simp only [fracSum, optAdd] at h ⊢ <;> subst ha <;>
    simp only [Qp.ext_iff, Qp.val_add] at h ⊢ <;> grind

/-- A reader that gives its `q` back. -/
theorem fracSum_give (a q w : Qp) (o : Option Qp) (h : fracSum a (optAdd q o) w) :
    fracSum (a + q) o w := by
  cases o <;> simp only [fracSum, optAdd] at h ⊢ <;>
    simp only [Qp.ext_iff, Qp.val_add] at h ⊢ <;> grind

/-- No reader: the database has the whole. -/
theorem fracSum_none (a w : Qp) (h : fracSum a none w) : a = w := h

/-- A slot: the page header, the 64 bytes after it (a meta's, in a meta page), the rest. -/
theorem slot_split (sl : List w8) : sl = sl.take 16 ++ (sl.drop 16).take 64 ++ sl.drop 80 := by
  rw [List.append_assoc]
  conv => lhs; rw [← List.take_append_drop 16 sl, ← List.take_append_drop 64 (sl.drop 16),
    List.drop_drop]

section sep
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

open Iris.ProofMode

/-- The meta in a slot's bytes, taken out (and given back). -/
theorem slot_meta_acc (l : Loc) (q : DFrac) (sl : List w8) (v : internal.common.Meta)
    (hc : l.locCar ≠ 0) (hlen : 80 ≤ sl.length) (h : (sl.drop 16).take 64 = metaBytes v) :
    bytesPointsto (GF := GF) l q sl ⊢
      (l +ₗ 16) ↦{q} v ∗ ((l +ₗ 16) ↦{q} v -∗ bytesPointsto l q sl) := by
  have hc' : (l +ₗ 16).locCar ≠ 0 := by simpa [Loc.add] using hc
  have Hsl : sl = sl.take 16 ++ metaBytes v ++ sl.drop 80 := by rw [← h]; exact slot_split sl
  have Hlen16 : (sl.take 16).length = 16 := by simp only [List.length_take]; omega
  iintro Hb
  rw [Hsl]
  icases (bytesPointsto_app (GF := GF) _ _ _ _).1 $$ Hb with ⟨Hab, Hc⟩
  icases (bytesPointsto_app (GF := GF) _ _ _ _).1 $$ Hab with ⟨Ha, Hm⟩
  rw [Hlen16]
  ihave Hm := (Meta_bytes (hG := hG) _ v q hc').2 $$ Hm
  iframe Hm
  iintro Hm
  ihave Hm := (Meta_bytes (hG := hG) _ v q hc').1 $$ Hm
  iapply (bytesPointsto_app (GF := GF) _ _ _ _).2
  iframe Hc
  iapply (bytesPointsto_app (GF := GF) _ _ _ _).2
  rw [Hlen16]
  iframe

end sep

end bbolt
end EtcdGrove
end Perennial
