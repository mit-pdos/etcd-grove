/-
The transactions' invariant (U0a of `notes/bbolt-proof-plan.md`; design §3.7): `txsInv`, the
registry of transactions with, per live transaction, the anchor of `txDB` (a quarter of
`tx.db`), its statistics (the atomics' cell), and its exclusive part (`txExcl`) or the token of
its being checked out.

A holder of `boltTx 1` takes `txExcl` out by swapping in `ghostVar r.n.ex 1`; holders of
fractions use only `tx.stats`, through atomic operations on the invariant (`txs_stats_atomic`). At
close the statistics come out (`txDone`) and the entry turns `done`.

The agreed state of a transaction (`boltTx`'s `ghostVar r.n.v`, half of it in `txExcl`) is a
`TxViewC` (a countable encoding of `TxView`, whose `gen` is a function: U0a deviation) and a
`TxX` (a reader's view, meta copy and registry key, or a writer's `WX`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Shape
public import Perennial.Proof.ThreadPool

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section txx
variable [GooseExts]

/-- A countable encoding of a `TxView`: `rw`, `base`, `cur`, and the generations as a finite map
(absent names at `0`). -/
abbrev TxViewC := Bool × Data × Data × GMap GoString Nat

/-- The view a `TxViewC` encodes. -/
def TxView.ofC (c : TxViewC) : TxView :=
  { rw := c.1, base := c.2.1, cur := c.2.2.1, gen := fun n => (c.2.2.2 !! n).getD 0 }

/-- A transaction's private state: a reader's view, meta copy and registry key; or a writer's
records. -/
inductive TxX where
  | rd (v : View) (mv : Meta) (k : Nat)
  | wr (X : WX)

instance TxX.countable : Pos.Countable TxX :=
  countableOfLeftInverse
    (fun x => match x with | .rd v mv k => Sum.inl (v, mv, k) | .wr X => Sum.inr X)
    (fun s => match s with | .inl (v, mv, k) => .rd v mv k | .inr X => .wr X)
    (fun x => by cases x <;> rfl)

/-- A reader's handle: its bucket's name and header (`b ↪[r.n.rbk]□`). -/
abbrev RHandle := GoString × InBucket

end txx

section txs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `tx` is registered in `B`'s transactions as `r` (persistent, timeless). -/
def reg (tx : Loc) (B : BNs) (r : TxReg) : IProp GF := iprop(tx ↪[B.txs]□ r)

/-- **A transaction's exclusive part** (design §3.7): half of its agreed state, half of its
`done` flag, and
- a writer's: `rwlock` locked, its database side (`wdbLive`, the store's writer state on its
  base view), its page tokens;
- a reader's: `mmaplock` read-locked, the pool loan (for `loan`), its `statlock` token, its
  registry entry in the store. -/
def txExcl (B : BNs) (p : GoString) (sp : Loc) (t0 : Nat) (tx : Loc) (r : TxReg) : IProp GF :=
  iprop(∃ (c : TxViewC) (x : TxX), ghostVar r.n.v (1 : Qp).half (c, x) ∗
    ghostVar r.n.done (1 : Qp).half false ∗
    match x with
    | .wr X => iprop(sync.ownMutex r.db.[DB, go!"rwlock"] ∗
        ∃ (ws : WSt) (w : WDb) (extra : GMap Nat Unit),
          wdbLive B r.db p sp t0 tx ws w ∗ txShape r.n.pg X extra ∗ ⌜ws.1 = some X.v⌝)
    | .rd v _ k => iprop(sync.ownRWMutexRLocked r.db.[DB, go!"mmaplock"] (Pm B r.db) ∗
        (if r.src = .loan then threadPool.ownThreadLoan B.pool else emp) ∗
        sync.ownRWMutex r.db.[DB, go!"statlock"] (Ps sp) ∗ k ↪[B.rds] (⟨v⟩ : RdInfo)))

/-- A reader's handle registry (the auth; the handles' fragments are persistent). -/
def readerHandles (r : TxReg) : IProp GF :=
  if r.rw then iprop(emp) else iprop(∃ H : GMap Loc RHandle, ghostMapAuth r.n.rbk 1 H)

/-- One transaction's entry: the quarter of `tx.db` (`txDB`'s anchor), and, while live, its
statistics and its exclusive part or the checked-out token; once done, the token (so that no
holder of a fraction remains). -/
def txEntry (B : BNs) (p : GoString) (sp : Loc) (t0 : Nat) (tx : Loc) (r : TxReg) : IProp GF :=
  iprop(∃ d : Loc, tx.[Tx, go!"db"] ↦{DFrac.own (1 : Qp).half.half} d ∗
    ((⌜d = r.db⌝ ∗ ghostVar r.n.done (1 : Qp).half false ∗
        (∃ s : TxStats, tx.[Tx, go!"stats"] ↦ s) ∗
        (txExcl B p sp t0 tx r ∨ ghostVar r.n.ex 1 ()) ∗ readerHandles r) ∨
     (⌜d = r.db ∨ d = null⌝ ∗ ghostVar r.n.done (1 : Qp).half true ∗ ghostVar r.n.ex 1 ())))

/-- **The transactions' invariant** (design §3.7). -/
def txsInv (B : BNs) (p : GoString) (sp : Loc) (t0 : Nat) : IProp GF :=
  iprop(∃ M : GMap Loc TxReg, ghostMapAuth B.txs 1 M ∗
    [∗map] tx ↦ r ∈ M, txEntry B p sp t0 tx r)

/-! ## Lemma statements (U5), fancy updates at `txsN N` -/

private instance txX_inhabited_i : Inhabited TxX := ⟨TxX.rd default (zeroValDef) 0⟩

private instance reg_persistent_txs_i (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private theorem qp_one_add_not_le_i (q : Qp) : ¬ ((1 : Qp) + q ≤ 1) := by
  rw [Qp.le_iff, Qp.val_add, Qp.val_one]; have := q.2; grind

private theorem qp_add_one_not_le_i (q : Qp) : ¬ (q + (1 : Qp) ≤ 1) := by
  rw [Qp.le_iff, Qp.val_add, Qp.val_one]; have := q.2; grind

private theorem qp_three_halves_i (q : Qp) :
    ¬ ((1 : Qp).half + (1 : Qp).half + (1 : Qp).half ≤ 1) := by
  rw [Qp.le_iff]; simp only [Qp.val_add, Qp.val_half, Qp.val_one]; grind

section lemmas
variable (B : BNs) (N : Namespace) (p : GoString) (sp : Loc) (t0 : Nat) (E : CoPset)
  (hE : ↑(txsN N) ⊆ E)
include hE

open Iris.ProofMode in
/-- Open `txsInv` at a registered transaction's entry. -/
private theorem txs_open_i (tx : Loc) (r : TxReg) :
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


/-- Register a new transaction `tx` (its names `r.n` fresh), with its quarter of `tx.db`, its
statistics and its exclusive part: it gets its registration and the whole `ex` token. -/
theorem txs_register (tx : Loc) (r : TxReg) (s : TxStats) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (1 : Qp).half.half} r.db ∗ tx.[Tx, go!"stats"] ↦ s ∗
      txExcl B p sp t0 tx r ∗ ghostVar r.n.done (1 : Qp).half false ∗ readerHandles r ⊢
    |={E}=> reg tx B r ∗ ghostVar r.n.ex 1 () := by
  sorry

/-- The holder of the whole `ex` token takes the exclusive part out. -/
theorem txExcl_take (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗ ghostVar r.n.ex 1 () ⊢
    |={E}=> txExcl B p sp t0 tx r := by
  sorry

open Iris.ProofMode in
/-- The exclusive part goes back, for the whole `ex` token. -/
theorem txExcl_put (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗ txExcl B p sp t0 tx r ⊢
    |={E}=> ghostVar r.n.ex 1 () := by
  iintro ⟨#Hinv, #Hreg, Hx⟩
  imod txs_open_i B N p sp t0 E hE tx r $$ [] with ⟨He, Hcl⟩
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

open Iris.ProofMode in
/-- **Close** (`Tx.close`): with the exclusive part's `done` half (its other contents already
given back), the entry turns done; the statistics come out. -/
theorem txs_close (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗
      ghostVar r.n.done (1 : Qp).half false ∗ ghostVar r.n.ex 1 () ⊢
    |={E}=> ∃ s : TxStats, tx.[Tx, go!"stats"] ↦ s := by
  iintro ⟨#Hinv, #Hreg, Hd, Hex⟩
  imod txs_open_i B N p sp t0 E hE tx r $$ [] with ⟨He, Hcl⟩
  · iframe Hinv Hreg
  unfold txEntry
  icases He with ⟨%d, Hdb, (⟨>%hd, >Hdone, >Hst, (Hx | >Hex'), -⟩ | ⟨>%hd, >Hdone, >Hex'⟩)⟩
  · icombine Hdone Hd as Hd'
    iunfold txExcl at Hx
    icases Hx with ⟨%c', %x', -, >Hd2, -⟩
    icombine Hd' Hd2 gives %h
    exact absurd h.1 (by rw [Qp.le_iff]; simp; grind)
  · icombine Hex Hex' gives %h
    exact absurd h.1 (by rw [Qp.le_iff]; simp; grind)
  · icombine Hd Hdone gives %h
    exact absurd h.2 (by decide)

open Iris.ProofMode in
/-- **The statistics of a live transaction**, for an atomic access by a holder of a fraction of
its `ex` token. -/
theorem txs_stats_atomic (tx : Loc) (r : TxReg) (q : Qp) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗ ghostVar r.n.ex q () ⊢
    |={E, E \ ↑(txsN N)}=> ∃ s : TxStats, tx.[Tx, go!"stats"] ↦ s ∗
      (∀ s' : TxStats, tx.[Tx, go!"stats"] ↦ s' ={E \ ↑(txsN N), E}=∗ ghostVar r.n.ex q ()) := by
  iintro ⟨#Hinv, #Hreg, Hex⟩
  imod txs_open_i B N p sp t0 E hE tx r $$ [] with ⟨He, Hcl⟩
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

end lemmas

end txs

end bbolt
end EtcdGrove
end Perennial
