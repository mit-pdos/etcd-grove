/-
The writer side after `ReleasePendingPages` (U5 of `notes/bbolt-proof-plan.md`, `beginRWTx`): the
released slots (`store_release`'s `S`, no longer store slots) join the writer's `W` slots, with
their cells and page-cache bytes.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Store
public import Proof.go_etcd_io.bbolt.Txn.WJoin
public import Proof.go_etcd_io.bbolt.Txn.FLFacts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section release
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The writer side with the freelist `fl'` and the slots `S` (bytes `bs`) joined to its `W`
slots. -/
def WDb.released (w : WDb) (fl' : FLPg) (S : List Nat) (bs : Nat → List w8) : WDb :=
  { w with fl := fl', W := w.W ++ S, wb := mergeWb S bs w.wb }

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **The writer side's facts after `ReleasePendingPages`** (`wdb_release`'s pure part). -/
theorem wdbOK_released (w : WDb) (σ : StoreSt) (ro : List w64) (S : List Nat)
    (bs : Nat → List w8)
    (hσ : σ.C = w.C ∧ σ.fl = w.fl ∧ σ.ms = w.ms ∧ σ.wst = wIdle ∧ storeOK σ) (hok : wdbOK w)
    (hS : ∀ s, s ∈ S ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C (w.fl.releasePending ro))
    (hro : ∀ t ∈ ro, 1 ≤ t.toNat ∧ t.toNat + 1 < 2 ^ 64)
    (hbs : ∀ s ∈ S, (bs s).length = 4096) :
    wdbOK (w.released (w.fl.releasePending ro) S bs) := by
  have hwb := wb_header w hok
  obtain ⟨hC, hfl, -, hws, hst⟩ := hσ
  have hwtx : σ.wtx = none := by
    have := congrArg (fun x : WSt => x.2.1) hws; simpa [StoreSt.wst, wIdle] using this
  obtain ⟨-, -, hbl, hwf, -, -, -, -, -, -, -, hslots, -, -, -, -, hnp, -⟩ := hst
  rw [hC, hfl, hwtx] at hbl
  rw [hfl] at hwf
  have hss : ∀ s, s ∈ storeSlots σ ↔ s ∈ slotsOf w.C w.fl := by
    intro s; unfold storeSlots slotsOf; rw [hC, hfl]
  generalize hfl' : w.fl.releasePending ro = fl' at hS
  obtain ⟨r1, r2, r3⟩ := releasePending_sub w.fl ro hro hwf.2.2.2.2
  rw [hfl'] at r1 r2 r3
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := hok
  have hpend' : ∀ s, s ∈ pendSlots fl' → s ∈ pendSlots w.fl := by
    intro s hs
    obtain ⟨t, pd', x, hp, hx, rfl⟩ := (pendSlots_mem_iff _ _).1 hs
    obtain ⟨pd, hp0, hx0⟩ := r2 t pd' x hp hx
    exact (pendSlots_mem_iff _ _).2 ⟨t, pd, x, hp0, hx0, rfl⟩
  have hSm : ∀ s ∈ S, s ∉ treeSlots w.C ∧ s ∈ pendSlots w.fl ∧ s ∉ pendSlots fl' := by
    intro s hs
    obtain ⟨h1, h2⟩ := (hS s).1 hs
    rw [mem_slotsOf] at h1 h2
    have ht : s ∉ treeSlots w.C := fun h => h2 (.inl h)
    exact ⟨ht, h1.resolve_left ht, fun h => h2 (.inr h)⟩
  have hcomm : ∀ t pd, w.fl.pending !! t = some pd → t.toNat ≤ w.C.txid := by
    intro t pd hp
    rcases hbl.2.2.1 t pd hp with h | ⟨h, -⟩
    · exact h
    · cases h
  have hpnt : ∀ x ∈ w.fl.pendingIds, x.toNat ∉ treeSlots w.C := by
    intro x hx ht
    have hxs : x.toNat ∈ pendSlots w.fl := List.mem_map.2 ⟨x, hx, rfl⟩
    have := hnp x.toNat (by rw [hC] at *; exact ht)
    rw [hfl, hwtx] at this
    rcases this with h | h
    · exact h hxs
    · obtain ⟨t, pd, hp, hx'⟩ := (pendingIds_mem_iff _ _).1 hx
      have := h t pd hp (by rw [W64_toNat_self]; exact hx')
      cases this
  have hcpOf : ∀ t pd x, w.fl.pending !! t = some pd → x ∈ pd.ids → committedPending w.fl w.C x :=
    fun t pd x hp hx => ⟨t, pd, hp, hx, hcomm t pd hp⟩
  refine ⟨c1, c2, c3, ?_, ?_, ?_, c7, c8, c9, c10, ?_, ?_, c13, c14, ?_, ?_, c17⟩
  · -- the `W` slots
    intro s
    simp only [WDb.released, List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨a, b, c, d⟩ := (c4 s).1 h
        exact ⟨a, b, c, fun h' => d (hpend' s h')⟩
      · obtain ⟨ht, hp, hp'⟩ := hSm s h
        have h2 := (hslots s ((hss s).2 ((mem_slotsOf _ _ _).2 (.inr hp)))).1
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
  · -- free ids are no tree slots
    intro x hx
    rcases r1 x hx with h | ⟨t, pd, hp, hx'⟩
    · exact c5 x h
    · exact hpnt x ((pendingIds_mem_iff _ _).2 ⟨t, pd, hp, hx'⟩)
  · -- the synced freelist page
    intro f hf
    have hcur := c6 f hf
    have hext : extentBytes (w.released fl' S bs).wb f = extentBytes w.wb f := by
      refine extentBytes_congr w.fl w.C w.wb _ f hf hcur (hwb f hf) c8 fun s hs hn => ?_
      simp only [WDb.released]
      have : s ∉ S := by
        intro hS'
        obtain ⟨t, pd, x, hp, hx, hxs⟩ := (pendSlots_mem_iff _ _).1 (hSm s hS').2.1
        apply hn
        have : W64 (s : Int) = x := by rw [← hxs, W64_toNat_self]
        rw [this]
        exact List.mem_append_right _ ((pendingIds_mem_iff _ _).2 ⟨t, pd, hp, hx⟩)
      simp only [mergeWb, this, ↓reduceIte]
    simp only [WDb.released] at hext ⊢
    rw [hext]
    refine flCurOK_mono w.fl fl' w.C _ (fun x hx => (r3 x).1 hx) (fun x hx => ?_)
      (fun x hx => ?_) (fun x hx => ?_)
      (fun f' _ a ha => .inl (by rw [← hfl', releasePending_allocs] at ha; exact ha)) hcur
    · rcases r1 x hx with h | ⟨t, pd, hp, hx'⟩
      · exact .inl h
      · exact .inr (hcpOf t pd x hp hx')
    · obtain ⟨t, pd', hp, hx', ht⟩ := hx
      obtain ⟨pd, hp0, hx0⟩ := r2 t pd' x hp hx'
      exact ⟨t, pd, hp0, hx0, ht⟩
    · obtain ⟨t, pd, hp, hx', ht⟩ := hx
      by_cases hin : x ∈ fl'.pendingIds
      · obtain ⟨t', pd', hp', hx''⟩ := (pendingIds_mem_iff _ _).1 hin
        obtain ⟨pd0, hp0, -⟩ := r2 t' pd' x hp' hx''
        exact .inl ⟨t', pd', hp', hx'', hcomm t' pd0 hp0⟩
      · right
        have hxp : x ∈ w.fl.pendingIds := (pendingIds_mem_iff _ _).2 ⟨t, pd, hp, hx'⟩
        refine ⟨hbl.2.1 t pd x hp hx' ht, hbl.2.2.2.2.2 x hxp, fun hc => ?_⟩
        exact hpnt x hxp ((mem_pagesSlots_iff _ _).2 hc)
  · intro s hs
    exact c11 s (hs.imp id (hpend' s))
  · intro x hx
    rcases r1 x hx with h | ⟨t, pd, hp, hx'⟩
    · exact c12 x h
    · exact hbl.2.1 t pd x hp hx' (hcomm t pd hp)
  · -- batch 37: the `W` slots' bytes inside the file are pages (the joined ones by `hbs`)
    intro s hs hle
    simp only [WDb.released, List.mem_append, mergeWb] at hs hle ⊢
    by_cases hS' : s ∈ S
    · simp only [hS', ↓reduceIte]; exact hbs s hS'
    · simp only [hS', ↓reduceIte]
      exact c15 s (hs.resolve_right hS') hle
  · -- maintainer 13: the partial last page's bytes (a joined slot's are a page)
    intro s h1 h2
    simp only [WDb.released, mergeWb] at h1 h2 ⊢
    by_cases hS' : s ∈ S
    · simp only [hS', ↓reduceIte]; rw [hbs s hS']; omega
    · simp only [hS', ↓reduceIte]; exact c16 s h1 h2

omit sem in
/-- **The writer side after `ReleasePendingPages`** (`beginRWTx`): from the idle store `σ`
(`storeOK`, no writer), the slots `S` released (`store_release`'s), whose bytes are whole pages
(`hbs`), the writer side's facts and its `W` slots' cells and bytes extend to the released
freelist (`wdbOK_released`, `wjoin`: the released slots were committed-pending, so below the
high-water mark, inside the mapping and the file). -/
theorem wdb_release (p : GoString) (w : WDb) (σ : StoreSt) (ro : List w64) (S : List Nat)
    (bs : Nat → List w8)
    (hσ : σ.C = w.C ∧ σ.fl = w.fl ∧ σ.ms = w.ms ∧ σ.wst = wIdle ∧ storeOK σ) (hok : wdbOK w)
    (hS : ∀ s, s ∈ S ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C (w.fl.releasePending ro))
    (hbs : ∀ s ∈ S, (bs s).length = 4096)
    (hro : ∀ t ∈ ro, 1 ≤ t.toNat ∧ t.toNat + 1 < 2 ^ 64) :
    wCells (GF := GF) w.ms w.W ∗ wBytes p w.W w.wb w.m.size ∗ slotsOwn w.ms p S bs ⊢
      ⌜wdbOK (w.released (w.fl.releasePending ro) S bs)⌝ ∗
      wCells w.ms (w.released (w.fl.releasePending ro) S bs).W ∗
      wBytes p (w.released (w.fl.releasePending ro) S bs).W
        (w.released (w.fl.releasePending ro) S bs).wb w.m.size := by
  have hok' := wdbOK_released w σ ro S bs hσ hok hS hro hbs
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
  simp only [WDb.released]
  iintro H
  ihave ⟨Hc, Hb⟩ := hj $$ H
  isplitr
  · ipureintro; exact hok'
  isplitl [Hc]
  · iexact Hc
  · iexact Hb

section store
variable (B : BNs) (N : Namespace) (p : GoString) (E : CoPset) (hE : ↑(pagesN N) ⊆ E)
include hE

/-- **`store_release` with its released slots' bytes whole pages** (U5c's finding: the slots
`store_release` hands out were store slots, whose bytes `storeOK` keeps at 4096, and its `bs` are
the store's bytes, but its post does not say so; `wCells` needs whole-page cells). The same
statement as `store_release` plus the length fact; batch 34: `store_release`'s post now has it. -/
theorem store_release_len (C : CommitSt) (fl : FLPg) (ms : MapSt) (F : GMap Nat w64)
    (ro : List w64) (hro : ro.Perm (F.toList.map Prod.snd))
    (hro1 : ∀ k t, F !! k = some t → 1 ≤ t.toNat ∧ t.toNat ≤ C.txid) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
      ghostVar B.wv (1 : Qp).half wIdle ∗ ghostMapAuth B.fltx 1 F ⊢
    |={E}=> ∃ (S : List Nat) (bs : Nat → List w8),
      ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half (fl.releasePending ro) ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half wIdle ∗
      ghostMapAuth B.fltx 1 F ∗ slotsOwn ms p S bs ∗
      ⌜∀ s, s ∈ S ↔ s ∈ slotsOf C fl ∧ s ∉ slotsOf C (fl.releasePending ro)⌝ ∗
      ⌜∀ s ∈ S, (bs s).length = 4096⌝ :=
  store_release B N p E hE C fl ms F ro hro hro1

end store

end release

end bbolt
end EtcdGrove
end Perennial
