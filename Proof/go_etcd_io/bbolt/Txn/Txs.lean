/-
`txsInv`'s updates as the lifecycle uses them (U5 of `notes/bbolt-proof-plan.md`): opening the
invariant at a registered transaction's entry (`txs_open`), and the corrected forms of
`Inv/Txs.lean`'s U0a statements:
- (`txs_register`, `txExcl_take`, `txs_close`: U5's corrected forms, moved to `Inv/Txs.lean`,
  batch 11);
- `txs_stats_done`: the statistics for the holder of the `done` half (`statsTok … false`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Txs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section txs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Two points-tos of one pointer field: their fractions are valid together. -/
theorem locPt_valid2 (l : Loc) (v1 v2 : Loc) (dq1 dq2 : DFrac) :
    l ↦{dq1} v1 ∗ l ↦{dq2} v2 ⊢ (⌜✓ (dq1 • dq2)⌝ : IProp GF) := by
  iintro ⟨H1, H2⟩
  ihave H1 := typedPointsto_split l v1 dq1 $$ H1
  ihave H2 := typedPointsto_split l v2 dq2 $$ H2
  rw [typedPointstoDef_heap]
  rw [typedPointstoDef_heap]
  icombine H1 H2 gives %h
  ipureintro; exact h.1

private instance txX_inhabited : Inhabited TxX := ⟨TxX.rd default (zeroValDef) 0⟩

private instance reg_persistent_txs (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

theorem qp_one_add_not_le (q : Qp) : ¬ ((1 : Qp) + q ≤ 1) := by
  rw [Qp.le_iff, Qp.val_add, Qp.val_one]; have := q.2; grind

theorem qp_add_one_not_le (q : Qp) : ¬ (q + (1 : Qp) ≤ 1) := by
  rw [Qp.le_iff, Qp.val_add, Qp.val_one]; have := q.2; grind

theorem qp_three_halves (q : Qp) :
    ¬ ((1 : Qp).half + (1 : Qp).half + (1 : Qp).half ≤ 1) := by
  rw [Qp.le_iff]; simp only [Qp.val_add, Qp.val_half, Qp.val_one]; grind

section lemmas
variable (B : BNs) (N : Namespace) (p : GoString) (sp : Loc) (t0 : Nat) (E : CoPset)
  (hE : ↑(txsN N) ⊆ E)
include hE

/-- Open `txsInv` at a registered transaction's entry. -/
theorem txs_open (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ⊢
    |={E, E \ ↑(txsN N)}=> ▷ txEntry B p sp t0 tx r ∗
      (▷ txEntry B p sp t0 tx r ={E \ ↑(txsN N), E}=∗ True) := by
  iintro ⟨#Hinv, #Hreg⟩
  iinv Hinv with Hi Hclose
  unfold txsInv
  icases Hi with ⟨%M, >Hauth, Hm⟩
  unfold reg
  icombine Hauth Hreg gives %Hlk
  ihave Hm := (later_mono (BigSepM.bigSepM_lookup_acc (Φ := fun tx r => txEntry (GF := GF) B p sp t0 tx r) Hlk).1) $$ Hm
  icases Hm with ⟨He, Hback⟩
  imodintro
  iframe He
  iintro He
  imod Hclose $$ [Hauth Hback He] with -
  · inext
    iexists M
    iframe Hauth
    iapply Hback $$ He
  imodintro; itrivial



/-- The exclusive part goes back, for the whole `ex` token. -/
theorem txExcl_put' (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗ txExcl B p sp t0 tx r ⊢
    |={E}=> ghostVar r.n.ex 1 () := by
  iintro ⟨#Hinv, #Hreg, Hx⟩
  imod txs_open B N p sp t0 E hE tx r $$ [] with ⟨He, Hcl⟩
  · iframe Hinv Hreg
  unfold txEntry
  icases He with ⟨%d, Hdb, (⟨>%hd, >Hdone, Hst, (Hx' | >Hex), Hrh⟩ | ⟨>%hd, >Hdone, >Hex⟩)⟩
  · iunfold txExcl at Hx
    icases Hx with ⟨%c, %x, Hv, Hd1, Hrest⟩
    icombine Hdone Hd1 as Hd
    iunfold txExcl at Hx'
    icases Hx' with ⟨%c', %x', -, >Hd2, -⟩
    icombine Hd Hd2 gives %h
    exact absurd h.1 (by rw [Qp.le_iff]; simp; grind)
  · imod Hcl $$ [Hdb Hdone Hst Hx Hrh] with -
    · inext; iexists d; iframe Hdb; ileft; iframe Hdone Hst Hrh; isplitr
      · ipureintro; exact hd
      ileft; iexact Hx
    imodintro; iexact Hex
  · iunfold txExcl at Hx
    icases Hx with ⟨%c, %x, Hv, Hd1, Hrest⟩
    icombine Hdone Hd1 gives %h
    exact absurd h.2 (by decide)

/-- **The statistics of a live transaction**, for an atomic access by a holder of a fraction of
its `ex` token. -/
theorem txs_stats_atomic' (tx : Loc) (r : TxReg) (q : Qp) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗ ghostVar r.n.ex q () ⊢
    |={E, E \ ↑(txsN N)}=> ∃ s : TxStats, tx.[Tx, go!"stats"] ↦ s ∗
      (∀ s' : TxStats, tx.[Tx, go!"stats"] ↦ s' ={E \ ↑(txsN N), E}=∗ ghostVar r.n.ex q ()) := by
  iintro ⟨#Hinv, #Hreg, Hex⟩
  imod txs_open B N p sp t0 E hE tx r $$ [] with ⟨He, Hcl⟩
  · iframe Hinv Hreg
  unfold txEntry
  icases He with ⟨%d, Hdb, (⟨>%hd, Hdone, >Hst, Hx, Hrh⟩ | ⟨>%hd, >Hdone, >Hex'⟩)⟩
  · icases Hst with ⟨%s, Hst⟩
    imodintro
    iexists s
    iframe Hst
    iintro %s' Hst
    imod Hcl $$ [Hdb Hdone Hst Hx Hrh] with -
    · inext; iexists d; iframe Hdb; ileft; iframe Hdone Hx Hrh; isplitr
      · ipureintro; exact hd
      iexists s'; iexact Hst
    imodintro; iexact Hex
  · icombine Hex Hex' gives %h
    exact absurd h.1 (by rw [Qp.le_iff]; simp; have := q.2; grind)

/-- The statistics of a live transaction, for the holder of its exclusive part's `done` half. -/
theorem txs_stats_done (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗
      ghostVar r.n.done (1 : Qp).half false ⊢
    |={E, E \ ↑(txsN N)}=> ∃ s : TxStats, tx.[Tx, go!"stats"] ↦ s ∗
      (∀ s' : TxStats, tx.[Tx, go!"stats"] ↦ s' ={E \ ↑(txsN N), E}=∗
        ghostVar r.n.done (1 : Qp).half false) := by
  iintro ⟨#Hinv, #Hreg, Hd⟩
  imod txs_open B N p sp t0 E hE tx r $$ [] with ⟨He, Hcl⟩
  · iframe Hinv Hreg
  unfold txEntry
  icases He with ⟨%d, Hdb, (⟨>%hd, Hdone, >Hst, Hx, Hrh⟩ | ⟨>%hd, >Hdone, >Hex'⟩)⟩
  · icases Hst with ⟨%s, Hst⟩
    imodintro
    iexists s
    iframe Hst
    iintro %s' Hst
    imod Hcl $$ [Hdb Hdone Hst Hx Hrh] with -
    · inext; iexists d; iframe Hdb; ileft; iframe Hdone Hx Hrh; isplitr
      · ipureintro; exact hd
      iexists s'; iexact Hst
    imodintro; iexact Hd
  · icombine Hd Hdone gives %h
    exact absurd h.2 (by decide)



end lemmas
end txs
end bbolt
end EtcdGrove
end Perennial
