/-
A remap of the database (`db.mmap` from `db.allocate`, a writer open and no reader): the
mapping's cells, which the database (its slots, `rem`, and the tail, `mapTail`) and the writer
(its pages, `pagesView` at its `q`) share, are the whole mapping (`remap_gather`), which
`munmap` takes; a new mapping of the same file is shared the same way (`remap_carve`), the
slots it adds the database's alone (`remapRem`).
-/
module

public import Proof.go_etcd_io.bbolt.DBWriter
public import Proof.go_etcd_io.bbolt.SlotsCarve

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section remap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The first `n` slots, all at fraction `q`, are the file's first `n * ps` bytes. -/
theorem slots_const (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (n : Nat)
    (h : n * ps ≤ bs.length) :
    slotsView (GF := GF) data bs ps (fun _ => q) (List.range n) ⊣⊢
      bytesPointsto data (DFrac.own q) (bs.take (n * ps)) := by
  have H := slots_bytes (GF := GF) data bs ps q n 0 (by simpa using h)
  simp only [Nat.zero_mul, List.drop_zero, Nat.zero_add] at H
  rw [show data +ₗ ((0 : Nat) : Int) = data by simp [Loc.add]] at H
  unfold slotsView
  rw [List.range_eq_range']
  exact H.symm

/-- A mapping of `sz` bytes is its whole slots and its tail. -/
theorem mapRange_slots (d : Loc) (bs : List w8) (sz ps : Nat) :
    mapRange (GF := GF) (some (d, sz)) bs 0 sz ⊣⊢
      bytesPointsto d (DFrac.own halfQ) (bs.take ((min sz bs.length / ps) * ps)) ∗
        mapTail d bs sz ps := by
  unfold mapRange mapTail
  have hN : (min sz bs.length / ps) * ps ≤ min sz bs.length := Nat.div_mul_le_self _ _
  generalize (min sz bs.length / ps) * ps = N at hN ⊢
  simp only [List.take_take, Nat.min_self, List.drop_zero]
  rw [show d +ₗ ((0 : Nat) : Int) = d by simp [Loc.add]]
  have hsplit : bs.take sz = (bs.take sz).take N ++ (bs.take sz).drop N :=
    (List.take_append_drop N _).symm
  have htk : (bs.take sz).take N = bs.take N := by
    rw [List.take_take]; congr 1; omega
  have hlen : ((bs.take sz).take N).length = N := by
    simp only [List.length_take]; omega
  have H := bytesPointsto_app (GF := GF) d (DFrac.own halfQ) ((bs.take sz).take N)
    ((bs.take sz).drop N)
  rw [← hsplit, hlen, htk] at H
  exact H

/-- The writer `w` of `σ` (no reader open): its view is a reader's (`writerOK`). -/
theorem writer_readerOK (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (w : Reader) (hw : σ.wr = some w) : readerOK σ w :=
  (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 w hw).1

/-- No reader: the database's part of slot `s` and the writer's (where it sees) make half. -/
theorem slot_half (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hr : σ.readers = ∅) (w : Reader) (hw : σ.wr = some w) (s : Nat) (hs : s < σ.nslots) :
    (w.sees s = true → σ.rem s + w.q = halfQ) ∧ (w.sees s = false → σ.rem s = halfQ) := by
  have H := h.2.2.2.2.2.2.2.2.2.2.2.1 s hs
  have hn : readersQ σ.readers (fun r => r.sees s) = none :=
    readersQ_none _ _ (fun k r hk => by rw [hr] at hk; simp at hk)
  rw [hn, hw] at H
  unfold wQ at H
  constructor
  · intro hs'; simp only [hs', ↓reduceIte, optAdd] at H; exact H
  · intro hs'; simp only [hs', Bool.false_eq_true, ↓reduceIte] at H; exact H

/-- No reader: the database's part of the fields and the writer's make the whole. -/
theorem fields_whole (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hr : σ.readers = ∅) (w : Reader) (hw : σ.wr = some w) : σ.frem + w.q = 1 := by
  have H := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold fieldsOK at H
  have hn : readersQ σ.readers (fun _ => true) = none :=
    readersQ_none _ _ (fun k r hk => by rw [hr] at hk; simp at hk)
  rw [hn, hw] at H
  unfold wQ at H
  simp only [↓reduceIte, optAdd] at H
  exact H

/-- A reader's pages are inside the mapping's whole slots. -/
theorem reader_sees_lt (σ : DBState) (r : Reader) (hro : readerOK σ r) (hps16 : 16 ≤ σ.ps)
    (s : Nat) (hs : r.sees s = true) : s < σ.nslots := by
  simp only [Reader.sees, decide_eq_true_eq] at hs
  obtain ⟨id, pg, hid, h1, h2⟩ := hs
  have hin := hro.2.2 id pg hid
  have hspan := span_of_pageAt σ.bs σ.ps id pg hps16 hin.1.symm
  omega

/-- The writer's pages are inside the mapping's whole slots. -/
theorem writer_sees_lt (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (w : Reader) (hw : σ.wr = some w) (s : Nat) (hs : w.sees s = true) : s < σ.nslots :=
  reader_sees_lt σ w (writer_readerOK σ v0 v1 h w hw) (by have := h.1; omega) s hs

open Iris.ProofMode in
/-- No reader open: the database's cells of the mapping and the writer's are all of it. -/
theorem remap_gather (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hr : σ.readers = ∅) (w : Reader) (hw : σ.wr = some w) :
    slotsView (GF := GF) σ.data σ.bs σ.ps σ.rem (List.range σ.nslots) ∗
      mapTail σ.data σ.bs σ.sz σ.ps ∗ pagesView σ.data σ.ps w.q w.pages ⊢
    mapRange (some (σ.data, σ.sz)) σ.bs 0 σ.sz := by
  have hro := writer_readerOK σ v0 v1 h w hw
  have hps16 : 16 ≤ σ.ps := by have := h.1; omega
  have Hc := slots_carve (GF := GF) σ.data σ.bs σ.ps (fun _ => halfQ) σ.rem w.q σ.nslots w.pages
    hps16 (nslots_mul_le σ) (fun id pg hid => ⟨(hro.2.2 id pg hid).1.symm, by have := (hro.2.2 id pg hid).2; omega⟩)
    hro.2.1
    (fun s hs hc => by
      have := (slot_half σ v0 v1 h hr w hw s hs).1
        (by simp only [Reader.sees, decide_eq_true_eq]; exact hc)
      exact this.symm)
    (fun s hs hc => by
      have := (slot_half σ v0 v1 h hr w hw s hs).2
        (by simp only [Reader.sees, decide_eq_false_iff_not]; exact hc)
      exact this.symm)
  iintro ⟨Hs, Ht, Hp⟩
  ihave Hs := Hc.2 $$ [Hs Hp]
  · iframe
  ihave Hs := (slots_const (GF := GF) σ.data σ.bs σ.ps halfQ σ.nslots (nslots_mul_le σ)).1 $$ Hs
  iapply (mapRange_slots (GF := GF) σ.data σ.bs σ.sz σ.ps).2
  unfold DBState.nslots
  iframe

/-- The database's part of the slots of a new, no smaller mapping: as before, and all of the
new ones' half. -/
def remapRem (σ : DBState) (s : Nat) : Qp := if s < σ.nslots then σ.rem s else halfQ

open Iris.ProofMode in
/-- A new mapping of the file, no smaller (no reader open): the database's slots and tail, and
the writer's pages, at the new location. -/
theorem remap_carve (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hr : σ.readers = ∅) (w : Reader) (hw : σ.wr = some w) (d' : Loc) (sz' : Nat)
    (hsz : σ.sz ≤ sz') :
    mapRange (GF := GF) (some (d', sz')) σ.bs 0 sz' ⊢
      slotsView d' σ.bs σ.ps (remapRem σ) (List.range (min sz' σ.bs.length / σ.ps)) ∗
        mapTail d' σ.bs sz' σ.ps ∗ pagesView d' σ.ps w.q w.pages := by
  have hro := writer_readerOK σ v0 v1 h w hw
  have hps16 : 16 ≤ σ.ps := by have := h.1; omega
  have hmono : σ.nslots ≤ min sz' σ.bs.length / σ.ps := by
    unfold DBState.nslots; exact Nat.div_le_div_right (by omega)
  have hfit : (min sz' σ.bs.length / σ.ps) * σ.ps ≤ σ.bs.length := by
    have := Nat.div_mul_le_self (min sz' σ.bs.length) σ.ps; omega
  have Hc := slots_carve (GF := GF) d' σ.bs σ.ps (fun _ => halfQ) (remapRem σ) w.q
    (min sz' σ.bs.length / σ.ps) w.pages hps16 hfit
    (fun id pg hid => ⟨(hro.2.2 id pg hid).1.symm, by have := (hro.2.2 id pg hid).2; omega⟩)
    hro.2.1
    (fun s _ hc => by
      have hs' : w.sees s = true := by simp only [Reader.sees, decide_eq_true_eq]; exact hc
      have hlt := writer_sees_lt σ v0 v1 h w hw s hs'
      have := (slot_half σ v0 v1 h hr w hw s hlt).1 hs'
      simp only [remapRem, hlt, ↓reduceIte]; exact this.symm)
    (fun s _ hc => by
      have hs' : w.sees s = false := by
        simp only [Reader.sees, decide_eq_false_iff_not]; exact hc
      simp only [remapRem]
      split
      · rename_i hlt; exact ((slot_half σ v0 v1 h hr w hw s hlt).2 hs').symm
      · rfl)
  iintro Hm
  icases (mapRange_slots (GF := GF) d' σ.bs sz' σ.ps).1 $$ Hm with ⟨Hs, Ht⟩
  ihave Hs := (slots_const (GF := GF) d' σ.bs σ.ps halfQ _ hfit).2 $$ Hs
  icases Hc.1 $$ Hs with ⟨Hs, Hp⟩
  iframe

/-- The database after a remap to `d'`, `sz'` bytes. -/
def DBState.remap (σ : DBState) (d' : Loc) (sz' : Nat) : DBState :=
  { σ with data := d', sz := sz', rem := remapRem σ }

proj_simps DBState.remap

theorem readerOK_remap (σ : DBState) (d' : Loc) (sz' : Nat) (hsz : σ.sz ≤ sz') (r : Reader)
    (h : readerOK σ r) : readerOK (σ.remap d' sz') r := by
  have hmono : σ.nslots ≤ (σ.remap d' sz').nslots := by
    unfold DBState.nslots DBState.remap; exact Nat.div_le_div_right (by simp only; omega)
  obtain ⟨wf, disj, hin⟩ := h
  exact ⟨wf, disj, fun id pg hid => ⟨(hin id pg hid).1, by have := (hin id pg hid).2; simp only [DBState.remap.proj_bs, DBState.remap.proj_ps] at *; omega⟩⟩

/-- A remap to a mapping no smaller (below `MaxMapSize`, at a non-null address) keeps the
database's facts. -/
theorem dbOK_remap (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (d' : Loc) (sz' : Nat) (hsz : σ.sz ≤ sz') (hsz' : sz' ≤ 281474976710655)
    (hd' : d'.locCar ≠ 0) : dbOK (σ.remap d' sz') v0 v1 := by
  have hmono : σ.nslots ≤ (σ.remap d' sz').nslots := by
    unfold DBState.nslots DBState.remap; exact Nat.div_le_div_right (by simp only; omega)
  obtain ⟨hps, hps2, hn, hsz0, hdc, hm0, hm1, hv, hcur, hrd, hmv, hsl, hfl, hro, hrs, hwr⟩ := h
  have hps16 : 16 ≤ σ.ps := by omega
  obtain ⟨cwf, cdisj, cin, calloc, cfree, cbelow⟩ := hcur
  refine ⟨hps, hps2, by omega, hsz', hd', hm0, hm1, hv,
    ⟨cwf, cdisj, fun id pg hid => by have := cin id pg hid; simp only [DBState.remap.proj_bs, DBState.remap.proj_ps] at *; omega, calloc, cfree, cbelow⟩,
    fun k r hk => readerOK_remap σ d' sz' hsz r (hrd k r hk), hmv, ?_, hfl, hro, hrs,
    ⟨hwr.1, fun w hw => ⟨readerOK_remap σ d' sz' hsz w (hwr.2 w hw).1, (hwr.2 w hw).2⟩⟩⟩
  intro s hs
  by_cases hlt : s < σ.nslots
  · have H := hsl s hlt
    show fracSum (remapRem σ s) (wQ σ.wr (fun r => r.sees s) (readersQ σ.readers (fun r => r.sees s)))
      halfQ
    simp only [remapRem, hlt, ↓reduceIte]
    exact H
  · show fracSum (remapRem σ s) (wQ σ.wr (fun r => r.sees s) (readersQ σ.readers (fun r => r.sees s)))
      halfQ
    have hn : readersQ σ.readers (fun r => r.sees s) = none :=
      readersQ_none _ _ (fun k r hk => by
        cases hc : r.sees s
        · rfl
        · exact absurd (reader_sees_lt σ r (hrd k r hk) hps16 s hc) hlt)
    rw [hn]
    simp only [remapRem, hlt, ↓reduceIte]
    cases hw : σ.wr with
    | none => rfl
    | some w =>
      unfold wQ
      cases hc : w.sees s
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]; rfl
      · exact absurd (reader_sees_lt σ w (hwr.2 w hw).1 hps16 s hc) hlt

end remap

end bbolt
end EtcdGrove
end Perennial
