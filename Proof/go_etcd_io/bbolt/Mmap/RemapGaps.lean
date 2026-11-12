/-
**The remap's missing shared facts** (U4d, `notes/bbolt-proof-plan.md`): what `DB.mmap`'s proof
(`Mmap/RemapBody`) needs that no shared statement gives yet, each a `sorry` here, with the fix it
waits for (reported to the maintainer). Nothing else in the remap's proof is assumed.
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.Remap
public import Proof.go_etcd_io.bbolt.Txn.Txs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section gaps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Gap 1 (`wdbOK`): the file is below `2 ^ 63` bytes** (`DB.fileSize`'s `Stat` reports an
`int64`; `DB.fileSize.spec` takes it). Fix: a `wdbOK` clause `w.m.size < 2 ^ 63` (`Open` reads the
size with `Stat`; `DB.grow` truncates to an `int64`). -/
theorem wdbOK_size_lt (w : WDb) (hok : wdbOK w) : w.m.size < 2 ^ 63 :=
  hok.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **Gap 2 (`wdbOK`): a file past the mapping ends on a page.** `wdbOK`'s `W` holds the slots
below `max (mapLen w.ms) w.m.size / 4096` (rounded down), so the page-cache bytes of a partial last
page of the file past the mapping are no one's; a remap that maps that page makes it a `W` slot,
whose bytes (`wBytes`) it cannot produce. bbolt never makes such a file (a file is unaligned only
as `Open` found it, and `Open` maps at least the file; `DB.grow` past the mapping truncates to
`sz + AllocSize`, whole pages). Fix: this `wdbOK` clause (`DB.grow`'s spec then needs a whole-page
`sz` above `AllocSize`), or `W`'s bound rounded up for the file (`(w.m.size + 4095) / 4096`). -/
theorem wdbOK_size_page (w : WDb) (hok : wdbOK w) (b : Loc) (l : Nat) (hms : w.ms = some (b, l)) :
    w.m.size ≤ l ∨ w.m.size % 4096 = 0 :=
  hok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b l hms

/-- `wdbOK_size_lt` over the flagged facts. -/
theorem wdbOK'_size_lt (fr : Bool) (w : WDb) (hok : wdbOK' fr w) : w.m.size < 2 ^ 63 :=
  hok.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `wdbOK_size_page` over the flagged facts. -/
theorem wdbOK'_size_page (fr : Bool) (w : WDb) (hok : wdbOK' fr w) (b : Loc) (l : Nat)
    (hms : w.ms = some (b, l)) : w.m.size ≤ l ∨ w.m.size % 4096 = 0 :=
  hok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b l hms

private instance viewOf_persistent_gap (r : TxReg) (v : View) :
    Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

private instance reg_persistent_gap (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

/-- **Gap 3 (`wtxCore`): the writer's view at a new base** (closed by batch 37.3, maintainer 11).
`wtxW … (Xd.rebase b)` holds `viewOf r (Xd.rebase b).v`, a fragment of the transaction's view
registry `r.n.vw` at the new base `b`. The registry's authority is in the transaction's entry of
`txsInv` (`readerHandles`'s writer case, `vwOwn`: every entry the view at its key), which a live
writer's entry holds (`statsTok` excludes the done entry): the remap finds or inserts the new
base. -/
theorem wtxCore_viewOf_rebase (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (b : Loc)
    (hbn : b ≠ null) (E : CoPset) (hE : ↑(txsN K.N) ⊆ E) :
    wtxCore (GF := GF) K tx r m X ⊢
      |={E}=> wtxCore K tx r m X ∗ viewBase r { X.v with base := b } := by
  iintro Hc
  iunfold wtxCore at Hc
  icases Hc with ⟨#Hpkg, #Hkc, %Hp, #Hreg, Hheap, Hfills, Hbk, Hnl, Hdb, #Hvo, Hst⟩
  have hrw : r.rw = true := Hp.2.1
  ihave #Hti : inv (txsN K.N) (txsInv (GF := GF) K.B K.p K.sp K.t0) $$ []
  · unfold BC.core isBoltCoreP
    icases Hkc with ⟨-, -, -, -, -, -, -, -, -, -, #Hti⟩
    iexact Hti
  imod txs_open K.B K.N K.p K.sp K.t0 E hE tx r $$ [] with ⟨He, Hcl⟩
  · iframe Hti Hreg
  unfold txEntry
  icases He with (⟨Hdb', Hdone, Hst', Hx, Hrh⟩ | ⟨>Hdone, >Hex', Hst'⟩)
  · iunfold readerHandles at Hrh
    simp only [hrw, ↓reduceIte]
    unfold vwOwn
    icases Hrh with ⟨%V, %v0, >Hauth, >#Hfr, >%HV⟩
    ihave Hvo2 : X.v.base ↪[r.n.vw]□ X.v $$ []
    · iunfold viewBase at Hvo; iexact Hvo
    icombine Hauth Hvo2 gives %Hlk
    have hX : X.v = { v0 with base := X.v.base } := (HV _ _ Hlk).1
    have hnew : { X.v with base := b } = { v0 with base := b } := by rw [hX]
    rw [hnew]
    cases hb : V !! b with
    | some u =>
      have hu : u = { v0 with base := b } := by
        have h := HV _ _ hb
        rw [h.2 hbn] at h; exact h.1
      ihave #Hb : b ↪[r.n.vw]□ u $$ [Hfr]
      · iapply (BigSepM.bigSepM_lookup (Φ := fun k u => (k ↪[r.n.vw]□ u : IProp GF)) hb) $$ Hfr
      imod Hcl $$ [Hdb' Hdone Hst' Hx Hauth] with -
      · inext; ileft; iframe Hdb' Hdone Hst' Hx
        iunfold readerHandles
        simp only [hrw, ↓reduceIte]
        unfold vwOwn
        iexists V, v0
        iframe Hauth
        iframe #
        ipureintro; exact HV
      imodintro
      isplitl
      · iunfold wtxCore; iframe; iframe #; ipureintro; exact Hp
      · unfold viewBase; subst hu; iexact Hb
    | none =>
      imod (ghost_map_insert_persist (GF := GF) b { v0 with base := b } hb) $$ Hauth
        with ⟨Hauth, #Hb⟩
      imod Hcl $$ [Hdb' Hdone Hst' Hx Hauth] with -
      · inext; ileft; iframe Hdb' Hdone Hst' Hx
        iunfold readerHandles
        simp only [hrw, ↓reduceIte]
        unfold vwOwn
        iexists V.insert b { v0 with base := b }, v0
        iframe Hauth
        isplitl
        · iapply (BigSepM.bigSepM_insert (Φ := fun k u => (k ↪[r.n.vw]□ u : IProp GF)) hb).2
          iframe #
        · ipureintro
          intro k u hk
          by_cases h : b = k
          · subst h
            rw [GMap.lookup_insert] at hk
            cases hk; exact ⟨rfl, fun _ => rfl⟩
          · rw [GMap.lookup_insert_ne _ _ h] at hk
            exact HV k u hk
      imodintro
      isplitl
      · iunfold wtxCore; iframe; iframe #; ipureintro; exact Hp
      · unfold viewBase; iexact Hb
  · cases m
    · simp only [statsTok, Bool.false_eq_true, ↓reduceIte]
      icombine Hst Hdone gives %h
      exact absurd h.2 (by decide)
    · simp only [statsTok, ↓reduceIte]
      icombine Hst Hex' gives %h
      exact absurd h.1 (by rw [Qp.le_iff]; simp only [Qp.val_add, Qp.val_one]; grind)

/-- **Gap 4 (`isBoltCoreP`): the database's namespace is disjoint from OsFs's.** `store_cells_agree`
opens `pagesInv` around a step that opens `osInv` (`↑osN ⊆ ⊤ \ ↑(pagesN N)`). `Open`'s spec takes
`↑N ## ↑osN`; fix: `isBoltCoreP` records it. -/
theorem core_osN_disj (K : BC) : K.core (GF := GF) ⊢ ⌜↑osN ## ↑(pagesN K.N)⌝ := by
  unfold BC.core isBoltCoreP
  iintro ⟨-, -, %H, -⟩
  ipureintro
  intro x hx
  exact H.2.2 x ⟨nclose_subseteq K.N "pages" x hx.2, hx.1⟩

end gaps

end bbolt
end EtcdGrove
end Perennial
