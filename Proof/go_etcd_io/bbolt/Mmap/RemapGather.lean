/-
The remap's gather (U4d, `notes/bbolt-proof-plan.md`; `Mmap/Remap`'s plan, step 5): before
`munmap`, with `Pm 1` and the writer's view home (`store_wreturn`), every cell of the old mapping
`(b0, L)` comes back to the writer at the client half: the store slots' (`store_gather`), the meta
slots' two quarters (the lend's and the writer's), the writer's `W` slots and the partial last slot
(`wCells_gather`), joined by `mapCells_gather` over `slots_partition`. Also the mapping fields'
three shares joined (`mapFields_join`) and agreeing (`mapFields_agree`).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.RemapBase
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section gather
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit hos sem in
/-- Two quarters of bytes are a half. -/
theorem bytes_quarters (l : Loc) (bs : List w8) :
    bytesPointsto (GF := GF) l (DFrac.own (1 : Qp).half.half) bs ∗
      bytesPointsto (GF := GF) l (DFrac.own (1 : Qp).half.half) bs ⊣⊢
      bytesPointsto (GF := GF) l (DFrac.own (1 : Qp).half) bs := by
  have h := (bytesPointsto_dfractional (GF := GF) l bs).dfractional (DFrac.own (1 : Qp).half.half)
    (DFrac.own (1 : Qp).half.half)
  rw [DFrac.op_own, Qp.half_add_half] at h
  exact h.symm

omit hos in
theorem mapFields_dfractional (db : Loc) (ms : MapSt) :
    DFractional (fun dq => mapFields (GF := GF) db dq ms) := by
  rcases ms with _ | ⟨b, l⟩ <;> simp only [mapFields] <;> infer_instance

omit hos in
/-- **The mapping fields' three shares** (the writer's records', the writer side's, `Pm`'s) are
the whole fields. -/
theorem mapFields_join (db : Loc) (ms : MapSt) :
    mapFields (GF := GF) db (DFrac.own (1 : Qp).half.half) ms ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half.half) ms ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) ms ⊣⊢
      mapFields (GF := GF) db (DFrac.own 1) ms := by
  have hd := mapFields_dfractional (GF := GF) db ms
  have h1 := hd.dfractional (DFrac.own (1 : Qp).half.half) (DFrac.own (1 : Qp).half.half)
  rw [DFrac.op_own, Qp.half_add_half] at h1
  have h2 := hd.dfractional (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rw [DFrac.op_own, Qp.half_add_half] at h2
  exact sep_assoc.symm.trans ((sep_congr h1.symm .rfl).trans h2.symm)

omit hos in
/-- Two shares of the mapping fields of mappings agree (kept). -/
theorem mapFields_agree (db : Loc) (dq1 dq2 : DFrac) (b1 b2 : Loc) (l1 l2 : Nat) :
    mapFields (GF := GF) db dq1 (some (b1, l1)) ∗ mapFields (GF := GF) db dq2 (some (b2, l2)) ⊢
      ⌜b1 = b2 ∧ l1 = l2⌝ ∗ mapFields (GF := GF) db dq1 (some (b1, l1)) ∗
        mapFields (GF := GF) db dq2 (some (b2, l2)) := by
  simp only [mapFields]
  iintro ⟨⟨H1, H1b, H1c, H1d, %h1⟩, ⟨H2, H2b, H2c, H2d, %h2⟩⟩
  icombine H1 H2 gives %he
  have hp := congrArg GoSlice.ptr he
  have hl := congrArg GoSlice.len he
  simp only at hp hl
  have : ((W64 (l1 : Int)).toNat) = ((W64 (l2 : Int)).toNat) := by rw [hl]
  have e1 : (W64 (l1 : Int)).toNat = l1 := by word
  have e2 : (W64 (l2 : Int)).toNat = l2 := by word
  isplitr
  · ipureintro; exact ⟨hp, by omega⟩
  iframe
  ipureintro; exact ⟨h1, h2⟩

/-- **The remap's gather** (with `Pm 1`'s `map` quarter and `mtok`, the writer side's `map` half,
its view `v` lent and its meta quarter): the old mapping's cells, the view home, the store's slots
out (`store_gather`'s witness and facts). -/
theorem remap_gather (B : BNs) (N : Namespace) (p : GoString) (v : View) (w : WDb) (b0 : Loc)
    (L : Nat) (hok : wdbOK w) (hms : w.ms = some (b0, L)) (hL : 8192 ≤ L) :
    ⊢ inv (pagesN N) (pagesInv (GF := GF) B p) -∗ viewCells wq v -∗
      ghostVar B.cur (1 : Qp).half.half w.C -∗ ghostVar B.fl (1 : Qp).half w.fl -∗
      ghostVar B.map (1 : Qp).half (some (b0, L) : MapSt) -∗
      ghostVar B.map (1 : Qp).half.half (some (b0, L) : MapSt) -∗ ghostVar B.mtok 1 () -∗
      ghostVar B.wv (1 : Qp).half (wLive v w.C) -∗ ghostVar B.out (1 : Qp).half false -∗
      metaCellsQ (GF := GF) (1 : Qp).half.half (some (b0, L)) w.C -∗
      wCells (GF := GF) (some (b0, L)) w.W -∗
    |={⊤}=> (∃ vf, cellsR (GF := GF) b0 0 L vf) ∗ ∃ (bs : Nat → List w8) (W : GMap Nat (List w8)),
      ghostVar B.cur (1 : Qp).half.half w.C ∗ ghostVar B.fl (1 : Qp).half w.fl ∗
      ghostVar B.map (1 : Qp).half (none : MapSt) ∗
      ghostVar B.map (1 : Qp).half.half (none : MapSt) ∗ ghostVar B.mtok 1 () ∗
      ghostVar B.wv (1 : Qp).half ((some v, some (w.C.txid + 1), false, false) : WSt) ∗
      ghostVar B.out (1 : Qp).half false ∗ ghostVar B.byt (1 : Qp).half W ∗
      ⌜(∀ s ∈ slotsOf w.C w.fl, W !! s = some (bs s)) ∧ w.C.metaOk ∧
        ∀ s ∈ slotsOf w.C w.fl, 2 ≤ s ∧ s < L / 4096⌝ := by
  simp only [wLive]
  iintro #Hinv Hv Hcur Hfl Hmap Hmapq Htok Hwv Hout Hmc Hwc
  imod store_wreturn B N p ⊤ CoPset.subseteq_top v (some (w.C.txid + 1)) false $$ [Hinv Hwv Hv]
    with Hwv
  · iframe; iframe #
  imod store_gather B N p ⊤ CoPset.subseteq_top w.C w.fl b0 L
    ((some v, some (w.C.txid + 1), false, false) : WSt) rfl
    $$ [Hinv Hcur Hfl Hmap Hmapq Htok Hwv Hout]
    with ⟨%bs, %W, Hcur, Hfl, Hmap, Hmapq, Htok, Hwv, Hout, Hbyt, %hW, %hfacts, HS, Hml⟩
  · isplitr
    · iexact Hinv
    isplitl [Hcur]
    · iexact Hcur
    isplitl [Hfl]
    · iexact Hfl
    isplitl [Hmap]
    · iexact Hmap
    isplitl [Hmapq]
    · iexact Hmapq
    isplitl [Htok]
    · iexact Htok
    isplitl [Hwv]
    · iexact Hwv
    · iexact Hout
  obtain ⟨hmo, hsl⟩ := hfacts
  ihave Hc : ∃ vf, cellsR (GF := GF) b0 0 L vf $$ [Hmc Hml HS Hwc]
  · unfold metaCellsQ
    icases Hmc with ⟨H0, H1⟩
    icases Hml with ⟨H0', H1'⟩
    ihave H0 := (bytes_quarters b0 w.C.m0).1 $$ [H0 H0']
    · iframe
    ihave H1 := (bytes_quarters _ w.C.m1).1 $$ [H1 H1']
    · iframe
    icases wCells_gather w hok b0 L hms $$ Hwc with ⟨Hws, Hp⟩
    have hP := slots_partition (L / 4096) (slotsOf w.C w.fl) (wSlots (L / 4096) w.C w.fl)
      (by omega) (slotsOf_nodup _ _) (wSlots_nodup _ _ _)
      (fun s hs => ⟨(hsl s hs).1, (hsl s hs).2.1⟩)
      (fun s => by rw [mem_wSlots])
    iapply mapCells_gather b0 L w.C.m0 w.C.m1 _ _ bs hmo.1 hmo.2.1 (fun s hs => (hsl s hs).2.2) hP
    iframe
  imodintro
  iframe Hc
  iexists bs, W
  iframe Hcur Hfl
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hmapq]
  · iexact Hmapq
  iframe Htok Hwv Hout Hbyt
  ipureintro
  exact ⟨hW, hmo, fun s hs => ⟨(hsl s hs).1, (hsl s hs).2.1⟩⟩

end gather

end bbolt
end EtcdGrove
end Perennial
