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

section lemmas
variable (B : BNs) (N : Namespace) (p : GoString) (sp : Loc) (t0 : Nat) (E : CoPset)
  (hE : ↑(txsN N) ⊆ E)
include hE

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

/-- The exclusive part goes back, for the whole `ex` token. -/
theorem txExcl_put (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗ txExcl B p sp t0 tx r ⊢
    |={E}=> ghostVar r.n.ex 1 () := by
  sorry

/-- **Close** (`Tx.close`): with the exclusive part's `done` half (its other contents already
given back), the entry turns done; the statistics come out. -/
theorem txs_close (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗
      ghostVar r.n.done (1 : Qp).half false ∗ ghostVar r.n.ex 1 () ⊢
    |={E}=> ∃ s : TxStats, tx.[Tx, go!"stats"] ↦ s := by
  sorry

/-- **The statistics of a live transaction**, for an atomic access by a holder of a fraction of
its `ex` token. -/
theorem txs_stats_atomic (tx : Loc) (r : TxReg) (q : Qp) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗ ghostVar r.n.ex q () ⊢
    |={E, E \ ↑(txsN N)}=> ∃ s : TxStats, tx.[Tx, go!"stats"] ↦ s ∗
      (∀ s' : TxStats, tx.[Tx, go!"stats"] ↦ s' ={E \ ↑(txsN N), E}=∗ ghostVar r.n.ex q ()) := by
  sorry

end lemmas

end txs

end bbolt
end EtcdGrove
end Perennial
