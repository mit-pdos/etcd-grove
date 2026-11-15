/-
A writer's `Rollback` on the writer side (U5 of `notes/bbolt-proof-plan.md`): what the store says of
the live writer's freelist (`store_wfacts`: `flBelow`'s writer clause, the pending slots inside the
mapping), and the writer side after `freelist.Rollback` (`wdb_rollback`: the slots leaving the
store join the `W` slots).
-/
module

public import Proof.go_etcd_io.bbolt.Txn.Txs
public import Proof.go_etcd_io.bbolt.Txn.WJoin
public import Proof.go_etcd_io.bbolt.Txn.FLFacts
import all Proof.go_etcd_io.bbolt.Inv.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wroll
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit go_gctx sem in
private theorem pagesInv_timeless_w (B : BNs) (p : BFile) : Timeless (pagesInv (GF := GF) B p) := by
  have h1 : ∀ σ : StoreSt, Timeless (storeCells (GF := GF) σ) := by
    intro σ; unfold storeCells; split <;> infer_instance
  have h2 : ∀ σ : StoreSt, Timeless (metaLend (GF := GF) B σ) := by
    intro σ; unfold metaLend metaCellsQ; split <;> infer_instance
  have h4 : ∀ σ W, Timeless (bytesWit (GF := GF) B σ W) := by
    intro σ W; unfold bytesWit; split <;> infer_instance
  have h3 : ∀ s bs, Timeless (osSlot (GF := GF) p s bs) := by
    intro s bs
    have : ∀ off dq xs, Timeless (osBytes (GF := GF) p.ino off dq xs) := fun _ _ _ => by
      unfold osBytes bytesG; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)
    unfold osSlot; infer_instance
  unfold pagesInv
  infer_instance

/-- **No writer's own allocation is in its pending entry** (`freelist.Rollback`'s premise), from
`flBelow`'s writer clause. -/
theorem flBelow_rollback_pre (fl : FLPg) (C : CommitSt) (hb : flBelow fl C (some (C.txid + 1)))
    (h64 : C.txid + 1 < 2 ^ 64) :
    ∀ pd, fl.pending !! W64 ((C.txid + 1 : Nat) : Int) = some pd →
      W64 ((C.txid + 1 : Nat) : Int) ∉ pd.alloctx := by
  intro pd hpd hin
  have ht : (W64 ((C.txid + 1 : Nat) : Int)).toNat = C.txid + 1 := by
    simp; omega
  rcases hb.2.2.1 _ pd hpd with h | ⟨-, h⟩
  · omega
  · have := h _ hin; omega

/-- `Rollback(txid)` leaves no pending entry for `txid`. -/
theorem FLPg.rollback_pending_none (fl : FLPg) (txid : w64) :
    (fl.rollback txid).pending !! txid = none := by
  unfold FLPg.rollback
  split
  · assumption
  · unfold FLPg.rollbackEntry; simp

section store
variable (B : BNs) (N : Namespace) (p : BFile) (E : CoPset) (hE : ↑(pagesN N) ⊆ E)
include hE

omit sem in
/-- **What the store says of the writer's freelist**: `flBelow` with the writer's txid, and the
pending slots inside the mapping. -/
theorem store_wfacts (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ∗
      ⌜flBelow fl C ws.2.1 ∧ ∀ b l, ms = some (b, l) → ∀ s ∈ pendSlots fl, 2 ≤ s ∧ s < l / 4096⌝ := by
  iintro ⟨#Hinv, Hcur, Hfl, Hmap, Hwv⟩
  have := pagesInv_timeless_w (GF := GF) B p
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
  refine ⟨Hok.2.2.1, fun b l hbl s hs => ?_⟩
  have hs' : s ∈ storeSlots σ := by
    unfold storeSlots
    rw [Perennial.mem_list_dedup, List.mem_append]
    exact Or.inr hs
  exact ⟨(Hok.2.2.2.2.2.2.2.2.2.2.2.1 s hs').1, Hok.2.2.2.2.2.2.2.2.2.2.2.2.1 b l hbl s hs'⟩

end store

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **The writer side's facts after `freelist.Rollback`** (`wdb_rollback`'s pure part): the
slots `S` leaving the store join the `W` slots with their bytes `bs`. -/
theorem wdbOK_rolledBack (w : WDb) (fl' : FLPg) (S : List Nat) (bs : Nat → List w8)
    (hok : wdbOK w) (hfl' : fl' = w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int)))
    (hS : ∀ s, s ∈ S ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C fl')
    (hpend : ∀ b l, w.ms = some (b, l) → ∀ s ∈ pendSlots w.fl, 2 ≤ s ∧ s < l / 4096)
    (hms : w.ms ≠ none) (hbs : ∀ s ∈ S, (bs s).length = 4096) :
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
  obtain ⟨b0, l0, hbl0⟩ : ∃ b l, w.ms = some (b, l) := by
    rcases h : w.ms with _ | ⟨b, l⟩
    · exact absurd h hms
    · exact ⟨b, l, rfl⟩
  refine ⟨c1, c2, c3, ?_, ?_, ?_, c7, c8, c9, c10, ?_, ?_, c13, c14, ?_, ?_, c17⟩
  · -- the `W` slots
    intro s
    simp only [List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨a, b, c, d⟩ := (c4 s).1 h
        exact ⟨a, b, c, fun h' => d (hpend' s h')⟩
      · obtain ⟨ht, hp, hp'⟩ := hSm s h
        have h2 := (hpend b0 l0 hbl0 s hp).1
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
      (fun x hx => ?_) (fun x hx => ?_)
      (fun f' _ a ha => (rollback_allocs_lookup w.fl (W64 ((w.C.txid + 1 : Nat) : Int)) _ a
        (by rw [hfl'] at ha; exact ha)).imp id
        (fun ⟨pd, hpd, hk, _⟩ => (pendingIds_mem_iff _ _).2 ⟨_, pd, hpd, hk⟩)) hcur
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
/-- **The writer side after `freelist.Rollback`** (by the live writer, before its publish): the
freelist rolled back, the slots leaving the store (`store_rollback`'s `S`, B3: a freed old synced
freelist page) joining the `W` slots with their cells and page-cache bytes (`slotsOwn`), the rest
unchanged; `wdbOK` kept (`wdbOK_rolledBack`, `wjoin`: the slots were pending, so below the
high-water mark, inside the mapping and the file). `hbs`: `store_rollback`'s. -/
theorem wdb_rollback (p : BFile) (w : WDb) (fl' : FLPg) (S : List Nat) (bs : Nat → List w8)
    (hok : wdbOK w) (hfl' : fl' = w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int)))
    (hS : ∀ s, s ∈ S ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C fl')
    (hpend : ∀ b l, w.ms = some (b, l) → ∀ s ∈ pendSlots w.fl, 2 ≤ s ∧ s < l / 4096)
    (hms : w.ms ≠ none) (hbs : ∀ s ∈ S, (bs s).length = 4096) :
    wCells (GF := GF) w.ms w.W ∗ wBytes p w.W w.wb w.m.size ∗ slotsOwn w.ms p S bs ⊢
      ∃ w' : WDb, ⌜w'.C = w.C ∧ w'.fl = fl' ∧ w'.ms = w.ms ∧ w'.m = w.m ∧ w'.fli = w.fli ∧
          w'.junk = w.junk ∧ w'.f = w.f ∧ w'.fd = w.fd ∧ wdbOK w'⌝ ∗
        wCells w'.ms w'.W ∗ wBytes p w'.W w'.wb w'.m.size := by
  have hok' := wdbOK_rolledBack w fl' S bs hok hfl' hS hpend hms hbs
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

end wroll

end bbolt
end EtcdGrove
end Perennial
