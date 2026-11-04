/-
`tx.rollback()`'s lemmas (U10d of `notes/bbolt-proof-plan.md`): what the store says of the committed
state (`store_cfacts`: `storeOK`'s `metaOk`, `treeOK`, `hwm ≤ 2 ^ 62`, the freelist's `WF`, the
writer's txid), `wdb_rollback` without a mapping (`wdb_rollback'`), and the writer side and store
premises of `NoSyncReload(freepages())` (`wdbOK_reload`, `nsr_store_ids`, `nsr_nonempty`).
-/
module

public import Proof.go_etcd_io.bbolt.Txn.WRoll
public import Proof.go_etcd_io.bbolt.Commit.FreepagesIds
import all Proof.go_etcd_io.bbolt.Inv.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rb
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit go_gctx sem in
private theorem pagesInv_timeless_c (B : BNs) (p : GoString) : Timeless (pagesInv (GF := GF) B p) := by
  have h1 : ∀ σ : StoreSt, Timeless (storeCells (GF := GF) σ) := by
    intro σ; unfold storeCells; split <;> infer_instance
  have h2 : ∀ σ : StoreSt, Timeless (metaLend (GF := GF) B σ) := by
    intro σ; unfold metaLend metaCellsQ; split <;> infer_instance
  have h4 : ∀ σ W, Timeless (bytesWit (GF := GF) B σ W) := by
    intro σ W; unfold bytesWit; split <;> infer_instance
  have h3 : ∀ s bs, Timeless (osSlot (GF := GF) p s bs) := by
    intro s bs
    have : ∀ off dq xs, Timeless (osBytes (GF := GF) p off dq xs) := fun _ _ _ => by
      unfold osBytes bytesG; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)
    unfold osSlot; infer_instance
  unfold pagesInv
  infer_instance

/-- `storeOK`'s facts of the committed state, the freelist and the writer. -/
def cFacts (C : CommitSt) (fl : FLPg) (ws : WSt) : Prop :=
  C.metaOk ∧ treeOK C ∧ C.hwm ≤ 2 ^ 62 ∧ fl.WF ∧ flBelow fl C ws.2.1 ∧
  (∀ w, ws.2.1 = some w → w = C.txid + (if ws.2.2.1 then 0 else 1))

section store
variable (B : BNs) (N : Namespace) (p : GoString) (E : CoPset) (hE : ↑(pagesN N) ⊆ E)
include hE

omit sem in
/-- **What the store says of the committed state** (`storeOK`'s facts, `cFacts`). -/
theorem store_cfacts (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ∗ ⌜cFacts C fl ws⌝ := by
  iintro ⟨#Hinv, Hcur, Hfl, Hmap, Hwv⟩
  have := pagesInv_timeless_c (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hbw Hml] with -
  · inext; iexists σ, W; iframe; ipureintro; exact Hok
  imodintro
  iframe
  ipureintro
  subst hC hfl hms hws
  obtain ⟨h1, h2, h3, h4, h5, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h21⟩ := Hok
  exact ⟨h1, h2, h21, h4, h3, h5⟩

end store

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **`wdbOK_rolledBack` without a mapping** (`Txn/WRoll`'s, more general: it implies it): the
pending slots are at least 2 (the freelist's `WF`), whether mapped or not. -/
theorem wdbOK_rolledBack' (w : WDb) (fl' : FLPg) (S : List Nat) (bs : Nat → List w8)
    (hok : wdbOK w) (hfl' : fl' = w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int)))
    (hS : ∀ s, s ∈ S ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C fl')
    (h2s : ∀ s ∈ pendSlots w.fl, 2 ≤ s) (hbs : ∀ s ∈ S, (bs s).length = 4096) :
    wdbOK { w with fl := fl', W := w.W ++ S, wb := mergeWb S bs w.wb } := by
  have hwb := wb_header w hok
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := hok
  have hfree : fl'.free = w.fl.free := by rw [hfl']; exact rollback_free _ _
  have hpend' : ∀ s, s ∈ pendSlots fl' → s ∈ pendSlots w.fl := by
    intro s hs; rw [hfl'] at hs; exact pendSlots_rollback_sub _ _ s hs
  have hsub : ∀ t pd, fl'.pending !! t = some pd → w.fl.pending !! t = some pd := by
    intro t pd hp; rw [hfl'] at hp; exact rollback_pending_sub _ _ t pd hp
  have hSm : ∀ s ∈ S, s ∉ treeSlots w.C ∧ s ∈ pendSlots w.fl ∧ s ∉ pendSlots fl' := by
    intro s hs
    obtain ⟨h1, h2⟩ := (hS s).1 hs
    rw [mem_slotsOf] at h1 h2
    have ht : s ∉ treeSlots w.C := fun h => h2 (.inl h)
    exact ⟨ht, h1.resolve_left ht, fun h => h2 (.inr h)⟩
  refine ⟨c1, c2, c3, ?_, ?_, ?_, c7, c8, c9, c10, ?_, ?_, c13, c14, ?_, ?_, c17⟩
  · -- the `W` slots
    intro s
    simp only [List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨a, b, c, d⟩ := (c4 s).1 h
        exact ⟨a, b, c, fun h' => d (hpend' s h')⟩
      · obtain ⟨ht, hp, hp'⟩ := hSm s h
        have h2 := h2s s hp
        have hlt := c11 s (.inr hp)
        have hM := Nat.le_max_right (mapLen w.ms) w.m.size
        refine ⟨h2, ?_, ht, hp'⟩
        omega
    · rintro ⟨a, b, c, d⟩
      by_cases hp : s ∈ pendSlots w.fl
      · right
        refine (hS s).2 ⟨(mem_slotsOf _ _ _).2 (.inr hp), fun h => ?_⟩
        rcases (mem_slotsOf _ _ _).1 h with h | h
        · exact c h
        · exact d h
      · left; exact (c4 s).2 ⟨a, b, c, hp⟩
  · intro x hx; rw [hfree] at hx; exact c5 x hx
  · -- the synced freelist page
    intro f hf
    have hcur := c6 f hf
    have hext : extentBytes (mergeWb S bs w.wb) f = extentBytes w.wb f := by
      refine extentBytes_congr w.fl w.C w.wb _ f hf hcur (hwb f hf) c8 fun s hs hn => ?_
      have : s ∉ S := by
        intro hS'
        obtain ⟨t, pd, x, hp, hx, hxs⟩ := (pendSlots_mem_iff _ _).1 (hSm s hS').2.1
        apply hn
        have : W64 (s : Int) = x := by rw [← hxs, W64_toNat_self]
        rw [this]
        exact List.mem_append_right _ ((pendingIds_mem_iff _ _).2 ⟨t, pd, hp, hx⟩)
      simp only [mergeWb, this, ↓reduceIte]
    simp only at ⊢
    rw [hext]
    have hT : (W64 ((w.C.txid + 1 : Nat) : Int)).toNat = w.C.txid + 1 :=
      toNat_W64_of_lt _ c7
    refine flCurOK_mono w.fl fl' w.C _ (fun x hx => ?_) (fun x hx => ?_)
      (fun x hx => ?_) (fun x hx => ?_) hcur
    · rcases List.mem_append.1 hx with h | h
      · rw [hfree] at h; exact List.mem_append_left _ h
      · obtain ⟨t, pd, hp, hx'⟩ := (pendingIds_mem_iff _ _).1 h
        exact List.mem_append_right _ ((pendingIds_mem_iff _ _).2 ⟨t, pd, hsub t pd hp, hx'⟩)
    · rw [hfree] at hx; exact .inl hx
    · obtain ⟨t, pd, hp, hx', ht⟩ := hx
      exact ⟨t, pd, hsub t pd hp, hx', ht⟩
    · obtain ⟨t, pd, hp, hx', ht⟩ := hx
      left
      have hne : t ≠ W64 ((w.C.txid + 1 : Nat) : Int) := by
        intro e; rw [e, hT] at ht; omega
      refine ⟨t, pd, ?_, hx', ht⟩
      rw [hfl', rollback_pending_ne _ _ _ hne]; exact hp
  · intro s hs
    exact c11 s (hs.imp id (hpend' s))
  · intro x hx; rw [hfree] at hx; exact c12 x hx
  · -- batch 37: the `W` slots' bytes inside the file are pages (the joined ones by `hbs`)
    intro s hs hle
    simp only [List.mem_append, mergeWb] at hs hle ⊢
    by_cases hS' : s ∈ S
    · simp only [hS', ↓reduceIte]; exact hbs s hS'
    · simp only [hS', ↓reduceIte]
      exact c15 s (hs.resolve_right hS') hle
  · -- maintainer 13: the partial last page's bytes (a joined slot's are a page)
    intro s h1 h2
    simp only [mergeWb] at h1 h2 ⊢
    by_cases hS' : s ∈ S
    · simp only [hS', ↓reduceIte]; rw [hbs s hS']; omega
    · simp only [hS', ↓reduceIte]; exact c16 s h1 h2

omit sem in
/-- **`wdb_rollback` without a mapping** (`Txn/WRoll`'s, more general). -/
theorem wdb_rollback' (p : GoString) (w : WDb) (fl' : FLPg) (S : List Nat) (bs : Nat → List w8)
    (hok : wdbOK w) (hfl' : fl' = w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int)))
    (hS : ∀ s, s ∈ S ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C fl')
    (h2s : ∀ s ∈ pendSlots w.fl, 2 ≤ s) (hbs : ∀ s ∈ S, (bs s).length = 4096) :
    wCells (GF := GF) w.ms w.W ∗ wBytes p w.W w.wb w.m.size ∗ slotsOwn w.ms p S bs ⊢
      ∃ w' : WDb, ⌜w'.C = w.C ∧ w'.fl = fl' ∧ w'.ms = w.ms ∧ w'.m = w.m ∧ w'.fli = w.fli ∧
          w'.junk = w.junk ∧ w'.f = w.f ∧ w'.fd = w.fd ∧ wdbOK w'⌝ ∗
        wCells w'.ms w'.W ∗ wBytes p w'.W w'.wb w'.m.size := by
  have hok' := wdbOK_rolledBack' w fl' S bs hok hfl' hS h2s hbs
  obtain ⟨-, -, c3, c4, -, -, -, -, c9, -, c11, -⟩ := hok
  have hpS : ∀ s ∈ S, s ∈ pendSlots w.fl := by
    intro s hs
    obtain ⟨h1, h2⟩ := (hS s).1 hs
    rcases (mem_slotsOf _ _ _).1 h1 with h | h
    · exact absurd ((mem_slotsOf _ _ _).2 (.inl h)) h2
    · exact h
  have hj := wjoin (GF := GF) p w.ms w.W S w.wb bs w.m.size
    (fun s hs hw => ((c4 s).1 hw).2.2.2 (hpS s hs))
    (fun s hs => by
      have := c11 s (.inr (hpS s hs))
      refine ⟨by omega, fun b l hbl => ?_, hbs s hs⟩
      have := c9 b l hbl; omega)
  iintro H
  ihave ⟨Hc, Hb⟩ := hj $$ H
  iexists { w with fl := fl', W := w.W ++ S, wb := mergeWb S bs w.wb }
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hok'⟩
  isplitl [Hc]
  · iexact Hc
  · iexact Hb

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos in
/-- The pending slots are at least 2 (the freelist's `WF`). -/
theorem pendSlots_two (fl : FLPg) (h : fl.WF) : ∀ s ∈ pendSlots fl, 2 ≤ s := by
  intro s hs
  unfold pendSlots at hs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
  exact h.2.1 x (List.mem_append_right _ hx)

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos sem in
theorem mem_sortPgids_rb (l : List w64) (x : w64) : x ∈ sortPgids l ↔ x ∈ l := by
  unfold sortPgids; exact (List.mergeSort_perm _ _).mem_iff

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- A reloaded free id is one of the ids. -/
theorem mem_reload_free (fl : FLPg) (ids : List w64) (x : w64) (h : x ∈ (fl.reload ids).free) :
    x ∈ ids ∧ x ∉ fl.pendingIds := by
  simp only [FLPg.reload] at h
  rw [mem_sortPgids_rb, List.mem_filter, decide_eq_true_eq] at h
  exact h

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **The writer side after `NoSyncReload(ids)`** (no synced freelist page): the ids are below the
high-water mark and no tree slots. -/
theorem wdbOK_reload (w : WDb) (ids : List w64) (hok : wdbOK w) (hfp : w.C.flpg = none)
    (hids : ∀ x ∈ ids, x.toNat < w.C.hwm ∧ ¬ coversSlot w.C.pages x.toNat) :
    wdbOK { w with fl := w.fl.reload ids } := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hok
  refine ⟨c1, c2, c3, c4, ?_, ?_, c7, c8, c9, c10, c11, ?_, c13, c14, c15⟩
  · intro x hx ht
    exact (hids x (mem_reload_free _ _ _ hx).1).2 ((mem_pagesSlots_iff _ _).1 ht)
  · intro f hf; simp only at hf; rw [hfp] at hf; cases hf
  · intro x hx; exact (hids x (mem_reload_free _ _ _ hx).1).1

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- Distinct ids below `n` number at most `n`. -/
theorem length_le_of_nodup_lt (l : List w64) (n : Nat) (hnd : l.Nodup)
    (hlt : ∀ x ∈ l, x.toNat < n) : l.length ≤ n := by
  have hnd' : (l.map BitVec.toNat).Nodup :=
    List.Pairwise.map BitVec.toNat (fun a b hab h => hab (BitVec.eq_of_toNat_eq h)) hnd
  have hsub : l.map BitVec.toNat ⊆ List.range n := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact List.mem_range.2 (hlt x hx)
  have := (List.subperm_of_subset hnd' hsub).length_le
  simpa using this

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **`NoSyncReload(freeIdsOf C)`'s premises**, from the store's facts and `wdbOK`'s free ids. -/
theorem nsr_premises (C : CommitSt) (fl : FLPg) (hh : C.hwm ≤ 2 ^ 62) (hwf : fl.WF)
    (hb : ∀ x ∈ fl.pendingIds, x.toNat < 2 ^ 62)
    (hfree : ∀ x ∈ fl.free, ¬ coversSlot C.pages x.toNat ∧ x.toNat < C.hwm) :
    (freeIdsOf C).length + fl.pendingIds.length < 2 ^ 63 ∧
    ((fl.noSyncReload (freeIdsOf C)).free ≠ [] ∨ fl.free = []) := by
  obtain ⟨hnd, h2, -, -, -⟩ := hwf
  constructor
  · have h1 := freeIdsOf_length C
    have hp := length_le_of_nodup_lt fl.pendingIds (2 ^ 62)
      (List.nodup_append.1 hnd).2.1 hb
    omega
  · rcases hf : fl.free with _ | ⟨x, xs⟩
    · right; rfl
    · left
      have hx : x ∈ fl.free := by rw [hf]; exact List.mem_cons_self
      intro he
      have hmem : x ∈ (fl.noSyncReload (freeIdsOf C)).free := by
        simp only [FLPg.noSyncReload, FLPg.reload]
        rw [mem_sortPgids_rb, List.mem_filter, decide_eq_true_eq]
        refine ⟨(mem_freeIdsOf C (by omega) x).2 ⟨h2 x (List.mem_append_left _ hx),
          (hfree x hx).2, (hfree x hx).1⟩, ?_⟩
        intro hp
        exact (List.nodup_append.1 hnd).2.2 x hx x hp rfl
      rw [he] at hmem; cases hmem

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **`store_reload`'s premises for `freeIdsOf C`**. -/
theorem nsr_store_ids (C : CommitSt) (fl : FLPg) (hh : C.hwm ≤ 2 ^ 62) :
    (∀ x ∈ freeIdsOf C, 2 ≤ x.toNat ∧ x.toNat < C.hwm ∧ x.toNat < 2 ^ 62 ∧
      (x.toNat ∉ slotsOf C fl ∨ x ∈ fl.pendingIds)) ∧ (freeIdsOf C).Nodup := by
  refine ⟨fun x hx => ?_, freeIdsOf_nodup C (by omega)⟩
  obtain ⟨a, b, c⟩ := (mem_freeIdsOf C (by omega) x).1 hx
  refine ⟨a, b, by omega, ?_⟩
  by_cases hp : x ∈ fl.pendingIds
  · right; exact hp
  · left
    rw [mem_slotsOf]
    rintro (h | h)
    · exact c ((mem_pagesSlots_iff _ _).1 h)
    · apply hp
      unfold pendSlots at h
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 h
      rw [← BitVec.eq_of_toNat_eq hyx]; exact hy

end rb

end bbolt
end EtcdGrove
end Perennial
