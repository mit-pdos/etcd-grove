/-
`DB.grow` (U4e, `notes/bbolt-proof-plan.md`): the writer side's file, out of `wdbW'` and back with
a new `OsMeta`, `W` slots and slots' bytes (`wdbW'_grow_acc`), and the fixed fields `grow` reads.
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.GrowPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section pure
variable [GooseExts]

/-- The synced freelist page's extent ends below the high-water mark (`flClause`, its header in
`wb f`: `wdbOK'_flHdr`). -/
theorem extent_lt_hwm (fr : Bool) (w : WDb) (hok : wdbOK' fr w) :
    ∀ f, w.C.flpg = some f → f + (1 + pageOverflow (w.wb f)) ≤ w.C.hwm := by
  intro f hf
  have h16 := wdbOK'_flHdr fr w hok f hf
  have hov : pageOverflow (extentBytes w.wb f) = pageOverflow (w.wb f) := by
    unfold pageOverflow pageHdr bytesAt
    congr 3
    unfold extentBytes
    rw [show 1 + pageOverflow (w.wb f) = (pageOverflow (w.wb f)) + 1 by omega, List.range'_succ,
      List.flatMap_cons, List.drop_zero, List.drop_zero,
      List.take_append_of_le_length h16]
  have hc := wdbOK'_flClause fr w hok
  rw [← hov]
  cases fr
  · exact (hc f hf f hf).2.1
  · exact ((hc f hf).2 f hf).2.1

/-- `fbRel` after the slots' bytes changed only from the high-water mark on (and the file's
`OsMeta`, `W`). -/
theorem fbRel_grow (fr : Bool) (w : WDb) (hok : wdbOK' fr w) (F : GMap Nat (List w8))
    (m' : OsMeta) (W' : List Nat) (wb' : Nat → List w8) (h : fbRel w F)
    (hag : ∀ s, s < w.C.hwm → wb' s = w.wb s) :
    fbRel { w with m := m', W := W', wb := wb' } F := by
  intro f hf s h1 h2 hs
  have hlt := extent_lt_hwm fr w hok f hf
  have hf' : wb' f = w.wb f := hag f (by omega)
  simp only [hf'] at h2
  have hs' : wb' s = w.wb s := hag s (by omega)
  simp only [hs']
  exact h f hf s h1 h2 hs

end pure

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The writer side's file resources: `db.file`, the file, its fd and `OsMeta`, `db.datasz`, the
`W` slots' cells and page-cache bytes. -/
def growRes (K : BC) (w : WDb) (m : OsMeta) (W : List Nat) (wb : Nat → List w8) : IProp GF :=
  iprop(K.db.[DB, go!"file"] ↦ w.f ∗ fileOwn w.f w.fd K.p (DFrac.own 1) ∗
    osFd w.fd (DFrac.own 1) ⟨K.p, true, true⟩ ∗ osMeta K.p (DFrac.own 1) (some m) ∗
    K.db.[DB, go!"datasz"] ↦ W64 (mapLen w.ms : Int) ∗ wCells w.ms W ∗ wBytes K.p W wb m.size)

omit [GooseSemantics] hos in
/-- A mapping's length facts, the fields kept. -/
theorem mapFields_some_len (db : Loc) (dq : DFrac) (ms : MapSt) (b : Loc) (l : Nat)
    (h : ms = some (b, l)) :
    mapFields (GF := GF) db dq ms ⊢
      ⌜l ≤ 0xFFFFFFFFFFFF ∧ (l % 4096 = 0 ∨ l = 0xFFFFFFFFFFFF) ∧ 0 < b.addr⌝ ∗
        mapFields (GF := GF) db dq ms := by
  subst h
  simp only [mapFields]
  iintro ⟨H1, H2, H3, H4, %h⟩
  isplitr
  · ipureintro; exact ⟨h.1, h.2.2, h.2.1⟩
  iframe
  ipureintro; exact h

omit [GooseSemantics] hos in
/-- **A mapping the writer holds ends on a page** (maintainer 13, U4e's gap 2): `mapFields`
allows `maxMapSize` (`0xFFFFFFFFFFFF`, not a multiple of 4096), but then `wCells`' partial last
slot's cells would lie past `maxAddr = 2 ^ 47`, where no cell is. -/
theorem wCells_aligned (ms : MapSt) (b : Loc) (L : Nat) (W : List Nat) (hms : ms = some (b, L))
    (hb : 0 < b.addr) (hL : L % 4096 = 0 ∨ L = 0xFFFFFFFFFFFF) :
    wCells (GF := GF) ms W ⊢ ⌜L % 4096 = 0⌝ ∗ wCells (GF := GF) ms W := by
  subst hms
  rcases hL with hL | rfl
  · iintro H; iframe; ipureintro; exact hL
  · unfold wCells
    iintro ⟨-, %vf, Hp⟩
    unfold cellsR
    rw [show (0xFFFFFFFFFFFF % 4096 : Nat) = 4094 + 1 from rfl, List.range'_succ]
    icases Hp with ⟨Hc, -⟩
    icases heapPointsto_lt_maxAddr _ _ _ $$ Hc with %h
    exfalso
    simp only [Loc.add, maxAddr] at h
    omega

/-- **The writer side's file, out and back** with a new `OsMeta`, `W` slots and slots' bytes
(kept below the high-water mark), under the facts `wdbOK'`. -/
theorem wdbW'_grow_acc (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW' (GF := GF) fr K tx v w ⊢
      ⌜wdbOK' fr w ∧ w.ms = some (v.base, mapLen w.ms) ∧ v = View.ofC v.base w.C⌝ ∗
      ⌜mapLen w.ms ≤ 0xFFFFFFFFFFFF ∧ mapLen w.ms % 4096 = 0⌝ ∗
      growRes K w w.m w.W w.wb ∗
      (∀ (m' : OsMeta) (W' : List Nat) (wb' : Nat → List w8),
        ⌜wdbOK' fr { w with m := m', W := W', wb := wb' } ∧
          ∀ s, s < w.C.hwm → wb' s = w.wb s⌝ -∗
        growRes K w m' W' wb' -∗ wdbW' fr K tx v { w with m := m', W := W', wb := wb' }) := by
  unfold wdbW' wdbLive wdbCoreG
  iintro ⟨⟨⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hopen, Hwa, Hrw, Hfile, Hpath, Hdsz, Hmfw,
    Hosm, Hfo, Hfd, Hmc, Hmob, Hwc, Hwb, Hjunk⟩, Hflo, Hrd, Hrcpt⟩, %Hwok, %F, Htok, %Hrel⟩
  icases mapFields_some_len K.db _ _ _ _ Hwok.2.1 $$ Hmfw with ⟨%hL, Hmfw⟩
  icases wCells_aligned w.ms v.base (mapLen w.ms) w.W Hwok.2.1 hL.2.2 hL.2.1 $$ Hwc
    with ⟨%hal, Hwc⟩
  isplitr
  · ipureintro; exact Hwok
  isplitr
  · ipureintro; exact ⟨hL.1, hal⟩
  unfold growRes
  isplitl [Hfile Hfo Hfd Hosm Hdsz Hwc Hwb]
  · iframe
  iintro %m' %W' %wb' %hh ⟨Hfile, Hfo, Hfd, Hosm, Hdsz, Hwc, Hwb⟩
  obtain ⟨hok', hag⟩ := hh
  isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmfw Hosm Hfo Hfd Hmc
    Hmob Hwc Hwb Hjunk Hflo Hrd Hrcpt]
  · iframe
  isplitr
  · ipureintro; exact ⟨hok', Hwok.2⟩
  iexists F
  iframe Htok
  ipureintro
  exact fbRel_grow fr w Hwok.1 F m' W' wb' Hrel hag

end res

end bbolt
end EtcdGrove
end Perennial
