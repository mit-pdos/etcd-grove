/-
`DB.grow` (U4e, `notes/bbolt-proof-plan.md`): the writer side closed after `File.Truncate`, the file
grown (`grow_finish`) or its size unchanged (`grow_finish_same`), with `wdbGrown`.
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.GrowRes
public import Proof.go_etcd_io.bbolt.Mmap.GrowWdb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section pure
variable [GooseExts]

/-- The mapping of a writer side with a file of at least two pages is at least two pages. -/
theorem grow_L8 (fr : Bool) (w : WDb) (hok : wdbOK' fr w) (b : Loc) (L : Nat)
    (hms : w.ms = some (b, L)) (h8 : 8192 ≤ w.m.size) : 8192 ≤ L := by
  by_cases h : L ≤ 0x1000000
  · have := hok.2.2.2.2.2.2.2.2.2.1 b L hms h; omega
  · omega

/-- Every slot from the file's (or the mapping's) end on is no store slot, and at least 2. -/
theorem grow_slots_ok (fr : Bool) (w : WDb) (hok : wdbOK' fr w) (b : Loc) (L : Nat)
    (hms : w.ms = some (b, L)) (h8 : 8192 ≤ w.m.size) :
    ∀ s, min w.m.size L / 4096 ≤ s → s < L / 4096 → 2 ≤ s ∧ s ∉ slotsOf w.C w.fl := by
  have hL8 := grow_L8 fr w hok b L hms h8
  have hk3 := hok.2.2.1
  have hk9 := hok.2.2.2.2.2.2.2.2.1 b L hms
  have hk11 := hok.2.2.2.2.2.2.2.2.2.2.1
  intro s h1 _
  refine ⟨by omega, fun hm => ?_⟩
  have := hk11 s ((mem_slotsOf _ _ s).1 hm)
  omega

/-- `wdbGrown` of `w.grown m' wb'`, `wb'` keeping the old file's whole pages. -/
theorem wdbGrown_grown (fr : Bool) (w : WDb) (hok : wdbOK' fr w) (m' : OsMeta)
    (wb' : Nat → List w8) (hsz : w.m.size ≤ m'.size) (hmaps : m'.maps = w.m.maps)
    (hag : ∀ s, 4096 * (s + 1) ≤ w.m.size → wb' s = w.wb s) :
    wdbGrown w (w.grown m' wb') := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hmaps, hsz, fun s hs => ⟨?_, hag s⟩⟩
  obtain ⟨h1, h2, h3⟩ := (wdbOK'_mem_W fr w hok s).1 hs
  refine (mem_wSlots _ _ _ s).2 ⟨h1, Nat.lt_of_lt_of_le h2 (Nat.div_le_div_right ?_), h3⟩
  omega

/-- A slot of the grown `W` inside the old file is an old `W` slot. -/
theorem grown_W_sub (fr : Bool) (w : WDb) (hok : wdbOK' fr w) (b : Loc) (L : Nat)
    (hms : w.ms = some (b, L)) (hal : L % 4096 = 0) (h8 : 8192 ≤ w.m.size) (k : Nat) :
    ∀ s ∈ wSlots k w.C w.fl, 4096 * s < w.m.size → s ∈ w.W := by
  intro s hs hlt
  by_cases hin : 4096 * (s + 1) ≤ w.m.size
  · obtain ⟨a, -, c⟩ := (mem_wSlots _ _ _ s).1 hs
    refine (wdbOK'_mem_W fr w hok s).2 ⟨a, ?_, c⟩
    have := Nat.le_max_right (mapLen w.ms) w.m.size
    have : s < w.m.size / 4096 := by omega
    omega
  · exact (wdbOK'_partSlot fr w hok b L hms hal h8 s hlt (by omega)).1

end pure

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The closer `wdbW'_grow_acc` hands back. -/
def growCloser (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) : IProp GF :=
  iprop(∀ (m' : OsMeta) (W' : List Nat) (wb' : Nat → List w8),
    ⌜wdbOK' fr { w with m := m', W := W', wb := wb' } ∧ ∀ s, s < w.C.hwm → wb' s = w.wb s⌝ -∗
    growRes K w m' W' wb' -∗ wdbW' fr K tx v { w with m := m', W := W', wb := wb' })

/-- **The writer side after the file grew to `m'`** (whole pages, at most the mapping if that is
at most `AllocSize`): the cells back, the new zeros joined to the `W` slots (`growWb`). -/
theorem grow_finish (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) (hok : wdbOK' fr w)
    (b : Loc) (L : Nat) (hms : w.ms = some (b, L)) (hal : L % 4096 = 0) (h8 : 8192 ≤ w.m.size)
    (m' : OsMeta) (hsz : w.m.size ≤ m'.size) (hmaps : m'.maps = w.m.maps) (hS : m'.size % 4096 = 0)
    (h10 : L ≤ 0x1000000 → m'.size ≤ L) (h13 : m'.size < 2 ^ 63) (S : Nat) (hSz : m'.size = S) :
    growCloser (GF := GF) fr K tx v w -∗
    K.db.[DB, go!"file"] ↦ w.f -∗ fileOwn w.f w.fd K.p (DFrac.own 1) -∗
    osFd w.fd (DFrac.own 1) ⟨K.p, true, true⟩ -∗ osMeta K.p (DFrac.own 1) (some m') -∗
    K.db.[DB, go!"datasz"] ↦ W64 (mapLen w.ms : Int) -∗
    ([∗list] s ∈ wSlots (min w.m.size L / 4096) w.C w.fl,
      ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) -∗
    (∃ vf, cellsR (GF := GF) b (4096 * (min w.m.size L / 4096))
      (min w.m.size L - 4096 * (min w.m.size L / 4096)) vf) -∗
    (∃ vf, cellsR (GF := GF) b (min w.m.size L) (L - min w.m.size L) vf) -∗
    wBytes K.p w.W w.wb w.m.size -∗
    osBytes K.p w.m.size (DFrac.own 1) (List.replicate (S - w.m.size) ((0 : w8), false)) -∗
    ∃ w' : WDb, wdbW' fr K tx v w' ∗ ⌜wdbGrown w w'⌝ := by
  subst hSz
  unfold growCloser
  iintro Hclose Hfile Hfo Hfd Hosm Hdsz Hlow Hpart Htail Hwb Hz
  have hk3 := hok.2.2.1
  have hk10 := hok.2.2.2.2.2.2.2.2.2.1 b L hms
  have hpart := wdbOK'_partSlot fr w hok b L hms hal h8
  let k := max (mapLen w.ms) m'.size / 4096
  have hk : L / 4096 ≤ k := by
    simp only [k, hms, mapLen]; exact Nat.div_le_div_right (Nat.le_max_left _ _)
  ihave Hwc := grow_cells_in w.C w.fl b L (min w.m.size L) k (Nat.min_le_right _ _) hk
    (grow_slots_ok fr w hok b L hms h8) $$ [Hlow Hpart Htail]
  · iframe
  ihave Hwc : wCells (GF := GF) w.ms (wSlots k w.C w.fl) $$ [Hwc]
  · rw [hms]; iexact Hwc
  ihave Hwb := wBytes_restrict K.p w.W (wSlots k w.C w.fl) w.wb w.m.size (wSlots_nodup _ _ _)
    (grown_W_sub fr w hok b L hms hal h8 k) $$ Hwb
  ihave Hwb := wBytes_grow K.p (wSlots k w.C w.fl) w.wb w.m.size m'.size (wSlots_nodup _ _ _) hS
    hsz (fun s hs h1 h2 => (hpart s h1 h2).2) $$ [Hwb Hz]
  · iframe
  have hag : ∀ s, 4096 * (s + 1) ≤ w.m.size → growWb w.wb w.m.size s = w.wb s := by
    intro s h; simp only [growWb, h, ↓reduceIte]
  have hok' := wdbOK'_grown fr w hok b L hms m' (growWb w.wb w.m.size) hsz hmaps
    (wdbOK'_flHdr fr w hok) hag
    (fun s h1 h2 => growWb_length w.wb w.m.size s h2 fun h3 => (hpart s h3 h2).2)
    h10 h13 (.inr hS) (fun s h1 h2 => by omega)
  iexists ({ w with m := m', W := wSlots k w.C w.fl, wb := growWb w.wb w.m.size } : WDb)
  isplitl
  · iapply Hclose $$ %m' %(wSlots k w.C w.fl) %(growWb w.wb w.m.size) [] [Hfile Hfo Hfd Hosm Hdsz
      Hwc Hwb]
    · ipureintro; exact ⟨hok', fun s hs => hag s (by omega)⟩
    · unfold growRes; iframe
  · ipureintro; exact wdbGrown_grown fr w hok m' _ hsz hmaps hag

/-- **The writer side after `File.Truncate` failed leaving the size** (the `OsMeta` `m'`, the same
size and mappings): the cells back. -/
theorem grow_finish_same (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) (hok : wdbOK' fr w)
    (b : Loc) (L : Nat) (hms : w.ms = some (b, L)) (hal : L % 4096 = 0) (h8 : 8192 ≤ w.m.size)
    (m' : OsMeta) (hsz : m'.size = w.m.size) (hmaps : m'.maps = w.m.maps) :
    growCloser (GF := GF) fr K tx v w -∗
    K.db.[DB, go!"file"] ↦ w.f -∗ fileOwn w.f w.fd K.p (DFrac.own 1) -∗
    osFd w.fd (DFrac.own 1) ⟨K.p, true, true⟩ -∗ osMeta K.p (DFrac.own 1) (some m') -∗
    K.db.[DB, go!"datasz"] ↦ W64 (mapLen w.ms : Int) -∗
    ([∗list] s ∈ wSlots (min w.m.size L / 4096) w.C w.fl,
      ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) -∗
    (∃ vf, cellsR (GF := GF) b (4096 * (min w.m.size L / 4096))
      (min w.m.size L - 4096 * (min w.m.size L / 4096)) vf) -∗
    (∃ vf, cellsR (GF := GF) b (min w.m.size L) (L - min w.m.size L) vf) -∗
    wBytes K.p w.W w.wb w.m.size -∗
    ∃ w' : WDb, wdbW' fr K tx v w' ∗ ⌜wdbGrown w w'⌝ := by
  unfold growCloser
  iintro Hclose Hfile Hfo Hfd Hosm Hdsz Hlow Hpart Htail Hwb
  have hk10 := hok.2.2.2.2.2.2.2.2.2.1 b L hms
  let k := max (mapLen w.ms) m'.size / 4096
  have hk : L / 4096 ≤ k := by
    simp only [k, hms, mapLen]; exact Nat.div_le_div_right (Nat.le_max_left _ _)
  ihave Hwc := grow_cells_in w.C w.fl b L (min w.m.size L) k (Nat.min_le_right _ _) hk
    (grow_slots_ok fr w hok b L hms h8) $$ [Hlow Hpart Htail]
  · iframe
  ihave Hwc : wCells (GF := GF) w.ms (wSlots k w.C w.fl) $$ [Hwc]
  · rw [hms]; iexact Hwc
  ihave Hwb := wBytes_restrict K.p w.W (wSlots k w.C w.fl) w.wb w.m.size (wSlots_nodup _ _ _)
    (grown_W_sub fr w hok b L hms hal h8 k) $$ Hwb
  have hag : ∀ s, 4096 * (s + 1) ≤ w.m.size → w.wb s = w.wb s := fun _ _ => rfl
  have hok' := wdbOK'_grown fr w hok b L hms m' w.wb (by omega) hmaps
    (wdbOK'_flHdr fr w hok) hag (fun s h1 h2 => by omega)
    (fun h => by rw [hsz]; exact hk10 h) (by rw [hsz]; exact hok.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (by rw [hsz]; exact hok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b L hms)
    (fun s h1 h2 => by rw [hsz] at h1 h2 ⊢; exact hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s h1 h2)
  iexists ({ w with m := m', W := wSlots k w.C w.fl, wb := w.wb } : WDb)
  isplitl
  · iapply Hclose $$ %m' %(wSlots k w.C w.fl) %w.wb [] [Hfile Hfo Hfd Hosm Hdsz Hwc Hwb]
    · ipureintro; exact ⟨hok', fun _ _ => rfl⟩
    · unfold growRes; rw [hsz]; iframe
  · ipureintro; exact wdbGrown_grown fr w hok m' _ (by omega) hmaps hag

omit [GooseSemantics] go_gctx hos sem in
/-- The cells `[lo, L)` of the one mapping `(b, L)`, as `Truncate`'s `mcellsAny`. -/
theorem mcellsAny_single_eq (b : Loc) (L lo : Nat) :
    mcellsAny (GF := GF) (GMap.singleton b L) lo L ⊣⊢
      ∃ vf, cellsR (GF := GF) b (min lo L) (L - min lo L) vf := by
  unfold mcellsAny
  refine BigSepM.bigSepM_singleton.trans ?_
  rw [Nat.min_self]
  exact .rfl

omit hos sem in
/-- `Truncate`'s cells after the file grew from `lo` to `S`, back as the cells `[lo, L)`. -/
theorem grown_cells_back (b : Loc) (L lo S : Nat) (vf0 : Nat → val) (hle : lo ≤ S) :
    mcells (GF := GF) (GMap.singleton b L) lo S vf0 ∗ mcellsAny (GF := GF) (GMap.singleton b L) S L ⊢
      ∃ vf, cellsR (GF := GF) b (min lo L) (L - min lo L) vf := by
  unfold mcells
  refine (sep_mono BigSepM.bigSepM_singleton.1 (mcellsAny_single_eq b L S).1).trans ?_
  iintro ⟨H1, H2⟩
  ihave H := cellsR_join b (min lo L) (min S L - min lo L) (L - min S L) $$ [H1 H2]
  · isplitl [H1]
    · iexists vf0; iexact H1
    · rw [show min lo L + (min S L - min lo L) = min S L by omega]; iexact H2
  rw [show min S L - min lo L + (L - min S L) = L - min lo L by omega]
  iexact H

/-- The fields of the database `DB.grow` reads (`isBoltCoreP`, `dbFixed`). -/
theorem BC.core_growFields (K : BC) :
    K.core (GF := GF) ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      ⌜K.db ≠ null⌝ ∗ K.db.[DB, go!"pageSize"] ↦□ W64 4096 ∗
      K.db.[DB, go!"AllocSize"] ↦□ W64 0x1000000 ∗
      (∃ lg, K.db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg) ∗
      K.db.[DB, go!"readOnly"] ↦□ false ∗ K.db.[DB, go!"Mlock"] ↦□ false ∗
      (∃ x : Bool, K.db.[DB, go!"NoGrowSync"] ↦□ x) := by
  unfold BC.core isBoltCoreP dbFixed dbLogger
  iintro ⟨-, -, %Ht, #Hpkg, #Hos, ⟨#Hps, -, #Hlg, #Hro, -, #Hml, -, #Hngs, -, -, -, -, -, -, #Has,
    -⟩, -⟩
  iframe #
  ipureintro; exact Ht.2.1

end res

end bbolt
end EtcdGrove
end Perennial
