/-
`loadFreelist`'s facts (U11e; design §3.11 "Open", step 3): the loaded freelist's `wdbOK_open`
premises (the synced page's ids, `FLPg.ofInit (flIds pg)`, or `freepages`' ids), and the file's
bytes cut for the reads `loadFreelist` makes before the core phase (the metas' quarters for
`hasSyncedFreelist`/`meta`, the freelist page's extent for `Interface.Read`).
-/
module

public import Proof.go_etcd_io.bbolt.Open.CoreFacts
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Model

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section facts
variable [GooseExts]

omit [GooseExts] in
theorem mem_sortPgids_lf (l : List w64) (x : w64) : x ∈ sortPgids l ↔ x ∈ l :=
  (List.mergeSort_perm _ _).mem_iff

theorem ofInit_pending (ids : List w64) : (FLPg.ofInit ids).pending = ∅ := rfl

theorem ofInit_pendingIds (ids : List w64) : (FLPg.ofInit ids).pendingIds = [] := by
  unfold FLPg.pendingIds; rw [ofInit_pending]; simp

theorem not_coversSlot_treeSlots (C : CommitSt) (s : Nat) (h : ¬ coversSlot C.pages s) :
    s ∉ treeSlots C := by
  unfold treeSlots; rw [mem_pagesSlots_iff]; exact h

/-- A file page's extent is the slots' bytes from its first slot. -/
theorem extentBytes_filePage (ys : List w8) (g : Nat) :
    extentBytes (fun s => bytesAt ys (4096 * s) 4096) g = filePage ys g := by
  unfold extentBytes filePage
  rw [bytesAt_slots ys (1 + pageOverflow (bytesAt ys (4096 * g) 4096)) g]

/-- A file page inside the file: its length. -/
theorem filePage_length (ys : List w8) (g : Nat)
    (h : 4096 * g + (1 + pageOverflow (filePage ys g)) * 4096 ≤ ys.length) :
    (filePage ys g).length = (1 + pageOverflow (filePage ys g)) * 4096 := by
  have ho := filePage_overflow ys g
  rw [ho] at h ⊢
  unfold filePage bytesAt at *
  simp only [List.length_take, List.length_drop]
  omega

/-- **The synced freelist page, loaded**: `flCurOK` of `FLPg.ofInit (flIds pg)`. -/
theorem flCurOK_ofInit (ys : List w8) (C : CommitSt) (g : Nat) (hg : C.flpg = some g)
    (hfl : flFileOK ys C) (hhwm : C.hwm * 4096 ≤ ys.length) (hsz : ys.length < 2 ^ 63) :
    flCurOK (FLPg.ofInit (flIds (filePage ys g))) C (filePage ys g) := by
  intro f hf
  rw [hg] at hf; cases hf
  obtain ⟨h2, hext, hflag, hbnd, hnd, hids, hown, hcov, hpid⟩ := hfl g hg
  have hlen := filePage_length ys g (by
    have : (g + (1 + pageOverflow (filePage ys g))) * 4096 ≤ C.hwm * 4096 :=
      Nat.mul_le_mul_right _ hext
    rw [Nat.add_mul] at this; omega)
  refine ⟨h2, hext, hlen, hflag, hbnd, hnd, fun x hx => (hids x hx).1,
    fun x hx => (hown x hx).1, ?_, ?_, ?_, ?_, fun a ha => ?_, hpid⟩
  · intro s h1 h2'
    refine ⟨hcov s h1 h2', ?_⟩
    unfold FLPg.allIds
    rw [ofInit_pendingIds, List.append_nil]
    show W64 (s : Int) ∉ sortPgids _
    rw [mem_sortPgids_lf]
    intro hm
    have hs : (W64 (s : Int)).toNat = s := by
      have : s < 2 ^ 64 := by omega
      simp; omega
    exact (hown _ hm).1 ⟨by rw [hs]; exact h1, by rw [hs]; exact h2'⟩
  · intro x hx
    exact (mem_sortPgids_lf _ x).1 hx
  · intro x ⟨t, pd, hp, _, _⟩
    rw [ofInit_pending] at hp; cases hp
  · intro x hx
    right
    have := hids x hx
    refine ⟨this.2, by omega, (hown x hx).2⟩
  · rw [show (FLPg.ofInit (flIds (filePage ys g))).allocs = ∅ from rfl] at ha
    simp at ha

/-- `freepages`' ids: below the mark, no tree slot. -/
theorem freeIdsOf_bounds (C : CommitSt) (hhwm : C.hwm < 2 ^ 64) (x : w64)
    (hx : x ∈ freeIdsOf C) : x.toNat < C.hwm ∧ x.toNat ∉ treeSlots C := by
  unfold freeIdsOf at hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hr, hc⟩ := List.mem_filter.1 hs
  rw [List.mem_range'_1] at hr
  have hs' : (W64 (s : Int)).toNat = s := by simp; omega
  rw [hs']
  exact ⟨by omega, not_coversSlot_treeSlots C s (by simpa using hc)⟩

/-- The synced page's ids: below the mark, no tree slot. -/
theorem flIds_facts (ys : List w8) (C : CommitSt) (g : Nat) (hg : C.flpg = some g)
    (hfl : flFileOK ys C) (x : w64) (hx : x ∈ (FLPg.ofInit (flIds (filePage ys g))).free) :
    x.toNat < C.hwm ∧ x.toNat ∉ treeSlots C := by
  obtain ⟨-, -, -, -, -, hids, hown, -, -⟩ := hfl g hg
  have hx' : x ∈ flIds (filePage ys g) := (mem_sortPgids_lf _ x).1 hx
  exact ⟨(hids x hx').2, not_coversSlot_treeSlots C _ (hown x hx').2⟩

/-- Distinct ids below `n` are at most `n`. -/
theorem nodup_below_length (ids : List w64) (n : Nat) (hnd : ids.Nodup)
    (hlt : ∀ x ∈ ids, x.toNat < n) : ids.length ≤ n := by
  have hnd' : (ids.map BitVec.toNat).Nodup :=
    List.Pairwise.map BitVec.toNat (fun a b hab h => hab (BitVec.eq_of_toNat_eq h)) hnd
  have hsub : ids.map BitVec.toNat ⊆ List.range n := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    exact List.mem_range.2 (hlt x hx)
  have := (List.subperm_of_subset hnd' hsub).length_le
  simpa using this

/-- **The store's invariant with the loaded freelist** `FLPg.ofInit ids` (`Open/Core.open_core_fl`):
ids distinct, from 2, below the mark, off the tree. -/
theorem storeOK_open_fl (ys : List w8) (C : CommitSt) (b : Loc) (L : Nat) (ids : List w64)
    (himg : fileImage ys C) (hmeta : C.metaOk) (htree : treeOK C)
    (hhwm : C.hwm * 4096 ≤ ys.length) (hL : ys.length ≤ L) (hsz : ys.length < 2 ^ 63)
    (htx : C.txid < 2 ^ 62) (hnd : ids.Nodup) (h2 : ∀ x ∈ ids, 2 ≤ x.toNat)
    (hlt : ∀ x ∈ ids, x.toNat < C.hwm) (hcov : ∀ x ∈ ids, ¬ coversSlot C.pages x.toNat) :
    storeOK { openSigma b L C (fun s => bytesAt ys (4096 * s) 4096) with
      fl := FLPg.ofInit ids } := by
  have h0 := storeOK_open ys C b L himg hmeta htree hhwm hL hsz htx
  have hmem : ∀ x, x ∈ (FLPg.ofInit ids).free ↔ x ∈ ids := fun x => mem_sortPgids_lf ids x
  have hall : (FLPg.ofInit ids).allIds = sortPgids ids := by
    unfold FLPg.allIds; rw [ofInit_pendingIds, List.append_nil]; rfl
  have hlen := nodup_below_length ids C.hwm hnd hlt
  refine storeOK_setFl _ (FLPg.ofInit ids) h0 rfl rfl rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, rfl⟩
  · rw [hall]; exact (sortPgids_perm ids).nodup_iff.2 hnd
  · intro x hx; rw [hall] at hx; exact h2 x ((sortPgids_perm ids).mem_iff.1 hx)
  · exact sortPgids_incr hnd
  · rw [hall, (sortPgids_perm ids).length_eq]; omega
  · intro t p hp; rw [ofInit_pending] at hp; cases hp
  · intro x hx; exact hlt x ((hmem x).1 hx)
  · intro t pd x hp; rw [ofInit_pending] at hp; cases hp
  · intro t pd hp; rw [ofInit_pending] at hp; cases hp
  · simp only [openSigma]; omega
  · intro x hx; have := hlt x ((hmem x).1 hx); omega
  · intro x hx; rw [ofInit_pendingIds] at hx; cases hx
  · intro x hx; exact hcov x ((hmem x).1 hx)

end facts

section bytes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A run of bytes, cut around `[a, a + n)`, with the wand putting it back. -/
theorem bytes_cut_at (l : Loc) (dq : DFrac) (ys : List w8) (a n : Nat) (h : a + n ≤ ys.length) :
    bytesPointsto (GF := GF) l dq ys ⊢
      bytesPointsto (l +ₗ ((a : Nat) : Int)) dq (bytesAt ys a n) ∗
      (bytesPointsto (l +ₗ ((a : Nat) : Int)) dq (bytesAt ys a n) -∗ bytesPointsto l dq ys) := by
  have e : ys = ys.take a ++ (bytesAt ys a n ++ ys.drop (a + n)) := by
    unfold bytesAt
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have ha : (ys.take a).length = a := by simp; omega
  iintro H
  ihave H := bytesPointsto_congr _ _ _ _ e $$ H
  icases (bytesPointsto_app l dq _ _).1 $$ H with ⟨H1, H2⟩
  icases (bytesPointsto_app _ dq _ _).1 $$ H2 with ⟨H2, H3⟩
  rw [ha]
  iframe H2
  iintro H2
  ihave H := (bytesPointsto_app _ dq _ _).2 $$ [H2 H3]
  · iframe
  ihave H := (bytesPointsto_app l dq _ _).2 $$ [H1 H]
  · rw [ha]; iframe
  iapply bytesPointsto_congr _ _ _ _ e.symm $$ H

/-- A half as two quarters. -/
theorem bytes_half_quarters (l : Loc) (ys : List w8) :
    bytesPointsto (GF := GF) l (DFrac.own (1 : Qp).half) ys ⊣⊢
      bytesPointsto l (DFrac.own (1 : Qp).half.half) ys ∗
        bytesPointsto l (DFrac.own (1 : Qp).half.half) ys := by
  have h := (bytesPointsto_dfractional (GF := GF) l ys).dfractional
    (DFrac.own (1 : Qp).half.half) (DFrac.own (1 : Qp).half.half)
  rw [DFrac.op_own, Qp.half_add_half] at h
  exact h

/-- The metas' cells (share `q`) from the file's bytes, and back. -/
theorem file_metaCells (b : Loc) (L : Nat) (q : Qp) (C : CommitSt) (ys : List w8)
    (himg : fileImage ys C) (h8 : 8192 ≤ ys.length) :
    bytesPointsto (GF := GF) b (DFrac.own q) ys ⊢
      metaCellsQ q (some (b, L)) C ∗
        (metaCellsQ q (some (b, L)) C -∗ bytesPointsto b (DFrac.own q) ys) := by
  simp only [metaCellsQ]
  rw [himg.1, himg.2.1]
  have e : ys = bytesAt ys 0 4096 ++ (bytesAt ys 4096 4096 ++ ys.drop 8192) := by
    unfold bytesAt
    rw [List.drop_zero, show 8192 = 4096 + 4096 from rfl, ← List.drop_drop,
      List.take_append_drop, List.take_append_drop]
  have h0 : (bytesAt ys 0 4096).length = 4096 := by unfold bytesAt; simp; omega
  have h1 : (bytesAt ys 4096 4096).length = 4096 := by unfold bytesAt; simp; omega
  iintro H
  ihave H := bytesPointsto_congr _ _ _ _ e $$ H
  icases (bytesPointsto_app b _ _ _).1 $$ H with ⟨H0, H⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ H with ⟨H1, H2⟩
  rw [h0, h1]
  iframe H0
  isplitl [H1]
  · iexact H1
  iintro ⟨H0, H1⟩
  ihave H := (bytesPointsto_app _ _ _ _).2 $$ [H1 H2]
  · rw [h1]; iframe
  ihave H := (bytesPointsto_app b _ _ _).2 $$ [H0 H]
  · rw [h0]; iframe
  iapply bytesPointsto_congr _ _ _ _ e.symm $$ H

end bytes

end bbolt
end EtcdGrove
end Perennial
