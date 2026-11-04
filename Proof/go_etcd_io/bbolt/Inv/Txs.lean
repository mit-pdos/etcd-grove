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
public import Proof.go_etcd_io.bbolt.Model.WOps
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
          wdbLive B r.db p sp t0 tx ws w ∗ txShape r.n.pg X extra ∗
          ⌜ws.1 = some X.v ∧ flViewU X w.fl⌝)
    | .rd v _ k => iprop(sync.ownRWMutexRLocked r.db.[DB, go!"mmaplock"] (Pm B r.db) ∗
        (if r.src = .loan then threadPool.ownThreadLoan B.pool else emp) ∗
        sync.ownRWMutex r.db.[DB, go!"statlock"] (Ps sp) ∗ k ↪[B.rds] (⟨v⟩ : RdInfo)))

/-- A reader's handle registry (the auth; the handles' fragments are persistent). -/
def readerHandles (r : TxReg) : IProp GF :=
  if r.rw then iprop(emp) else iprop(∃ H : GMap Loc RHandle, ghostMapAuth r.n.rbk 1 H)

/-- One transaction's entry: while live, the quarter of `tx.db` (`txDB`'s anchor), its
statistics and its exclusive part or the checked-out token; once done, the token (so that no
holder of a fraction remains) and the statistics read-only (batch 17: no share of `tx.db`, which
`Tx.close` sets to nil with a plain store, outside the invariant). A registered entry excludes a
new registration's whole `tx.db` (live) or whole `tx.stats` (done). -/
def txEntry (B : BNs) (p : GoString) (sp : Loc) (t0 : Nat) (tx : Loc) (r : TxReg) : IProp GF :=
  iprop((tx.[Tx, go!"db"] ↦{DFrac.own (1 : Qp).half.half} r.db ∗
      ghostVar r.n.done (1 : Qp).half false ∗ (∃ s : TxStats, tx.[Tx, go!"stats"] ↦ s) ∗
      (txExcl B p sp t0 tx r ∨ ghostVar r.n.ex 1 ()) ∗ readerHandles r) ∨
    (ghostVar r.n.done (1 : Qp).half true ∗ ghostVar r.n.ex 1 () ∗
      ∃ s : TxStats, tx.[Tx, go!"stats"] ↦□ s))

/-- **The transactions' invariant** (design §3.7). -/
def txsInv (B : BNs) (p : GoString) (sp : Loc) (t0 : Nat) : IProp GF :=
  iprop(∃ M : GMap Loc TxReg, ghostMapAuth B.txs 1 M ∗
    [∗map] tx ↦ r ∈ M, txEntry B p sp t0 tx r)

/-! ## Lemma statements (U5), fancy updates at `txsN N` -/

private instance txX_inhabited_i : Inhabited TxX := ⟨TxX.rd default (zeroValDef) 0⟩

private instance reg_persistent_txs_i (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

open Iris.ProofMode in
/-- Two points-tos of one pointer field: their fractions are valid together. -/
private theorem locPt_valid2_i (l : Loc) (v1 v2 : Loc) (dq1 dq2 : DFrac) :
    l ↦{dq1} v1 ∗ l ↦{dq2} v2 ⊢ (⌜✓ (dq1 • dq2)⌝ : IProp GF) := by
  iintro ⟨H1, H2⟩
  ihave H1 := typedPointsto_split l v1 dq1 $$ H1
  ihave H2 := typedPointsto_split l v2 dq2 $$ H2
  rw [typedPointstoDef_heap]
  rw [typedPointstoDef_heap]
  icombine H1 H2 gives %h
  ipureintro; exact h.1

omit hos in
open Iris.ProofMode in
/-- A `w64` owned whole is no read-only one. -/
private theorem w64_own_discard_false_i (l : Loc) (v w : w64) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ∗ typedPointsto l w DFrac.discard ⊢ False := by
  have first : ∀ (x : w64) (dq : DFrac), ∃ b : w8,
      typedPointsto (GF := GF) l x dq ⊢ heapPointsto l dq (LitV (LitByte b)) := fun x dq => by
    cases h : natBytes 8 x.toNat with
    | nil => have := natBytes_length 8 x.toNat; rw [h] at this; simp at this
    | cons b bs =>
      refine ⟨b, (typedPointsto_split l x dq).trans ?_⟩
      rw [typedPointstoDef_w64, h]
      exact sep_elim_left
  obtain ⟨b1, k1⟩ := first v (DFrac.own 1)
  obtain ⟨b2, k2⟩ := first w DFrac.discard
  iintro ⟨H1, H2⟩
  ihave H1 := k1 $$ H1
  ihave H2 := k2 $$ H2
  icombine H1 H2 gives %Hc
  have h := DFrac.valid_own_op_discard.1 Hc.1
  exact absurd h (by simp)

omit hos in
open Iris.ProofMode in
/-- **Statistics owned whole are no read-only ones** (their `PageCount` field). -/
theorem txStats_own_discard_false (l : Loc) (s s' : TxStats) :
    typedPointsto (GF := GF) l s (DFrac.own 1) ∗ typedPointsto l s' DFrac.discard ⊢ False := by
  iintro ⟨H1, H2⟩
  iStructNamed H1
  irename PageCount => P1
  iStructNamed H2
  iapply w64_own_discard_false_i $$ [P1 PageCount]
  iframe

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


open Iris.ProofMode in
/-- **Register a new transaction** `tx` (its names `r.n` allocated by the caller, which keeps
their `ex` token): with all of `tx.db` (so that `tx` is not yet registered: every entry holds a
quarter), its statistics and its exclusive part; it gets its registration and `tx.db` at `¾`. -/
theorem txs_register (tx : Loc) (r : TxReg) (s : TxStats) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗
      tx.[Tx, go!"db"] ↦ r.db ∗ tx.[Tx, go!"stats"] ↦ s ∗
      txExcl B p sp t0 tx r ∗ ghostVar r.n.done (1 : Qp).half false ∗ readerHandles r ⊢
    |={E}=> reg tx B r ∗
      tx.[Tx, go!"db"] ↦{DFrac.own ((1 : Qp).half + (1 : Qp).half.half)} r.db := by
  iintro ⟨#Hinv, Hdb, Hst, Hx, Hd, Hrh⟩
  iinv Hinv with Hi Hclose
  unfold txsInv
  icases Hi with ⟨%M, >Hauth, Hm⟩
  cases hlk : M.lookup tx with
  | some r' =>
    ihave Hm := (later_mono (BigSepM.bigSepM_lookup_acc (Φ := fun tx r => txEntry (GF := GF) B p sp t0 tx r) hlk).1) $$ Hm
    icases Hm with ⟨He, -⟩
    unfold txEntry
    icases He with (⟨>Hdb', -⟩ | ⟨-, -, >Hst'⟩)
    · ihave %h := locPt_valid2_i _ _ _ _ _ $$ [Hdb Hdb']
      · iframe Hdb Hdb'
      exfalso
      revert h
      rw [DFrac.op_own]
      show ¬ ((1 : Qp) + (1 : Qp).half.half).val ≤ 1
      simp only [Qp.val_add, Qp.val_half, Qp.val_one]; grind
    · icases Hst' with ⟨%s', Hst'⟩
      iexfalso
      iapply txStats_own_discard_false $$ [Hst Hst']
      iframe
  | none =>
    have h1 : (1 : Qp) = ((1 : Qp).half + (1 : Qp).half.half) + (1 : Qp).half.half :=
      Subtype.ext (by simp only [Qp.val_add, Qp.val_half, Qp.val_one]; grind)
    have hs := typedPointsto_frac_add (GF := GF) (tx.[Tx, go!"db"]) r.db
      ((1 : Qp).half + (1 : Qp).half.half) (1 : Qp).half.half
    rw [← h1] at hs
    ihave ⟨Hdb, Hdb4⟩ := hs.1 $$ Hdb
    imod (ghost_map_insert_persist tx r hlk) $$ Hauth with ⟨Hauth, #Hreg⟩
    imod Hclose $$ [Hauth Hm Hdb4 Hst Hx Hd Hrh] with -
    · inext
      iexists (M.insert tx r)
      iframe Hauth
      iapply (BigSepM.bigSepM_insert (Φ := fun tx r => txEntry (GF := GF) B p sp t0 tx r) hlk).2
      iframe Hm
      unfold txEntry
      ileft
      iframe Hdb4 Hd Hx Hrh
      iexists s; iexact Hst
    imodintro
    iframe Hdb
    unfold reg; iexact Hreg

open Iris.ProofMode in
/-- The holder of the whole `ex` token takes the exclusive part out (under a later: it is not
timeless). -/
theorem txExcl_take (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗ ghostVar r.n.ex 1 () ⊢
    |={E}=> ▷ txExcl B p sp t0 tx r := by
  iintro ⟨#Hinv, #Hreg, Hex⟩
  imod txs_open_i B N p sp t0 E hE tx r $$ [] with ⟨He, Hcl⟩
  · iframe Hinv Hreg
  unfold txEntry
  icases He with (⟨Hdb, Hdone, Hst, (Hx | >Hex'), Hrh⟩ | ⟨>Hdone, >Hex', -⟩)
  · imod Hcl $$ [Hdb Hdone Hst Hex Hrh] with -
    · inext; ileft; iframe Hdb Hdone Hst Hrh
      iright; iexact Hex
    imodintro; iexact Hx
  · icombine Hex Hex' gives %h
    exact absurd h.1 (by rw [Qp.le_iff]; simp; grind)
  · icombine Hex Hex' gives %h
    exact absurd h.1 (by rw [Qp.le_iff]; simp; grind)

open Iris.ProofMode in
/-- The exclusive part goes back, for the whole `ex` token. -/
theorem txExcl_put (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗ txExcl B p sp t0 tx r ⊢
    |={E}=> ghostVar r.n.ex 1 () := by
  iintro ⟨#Hinv, #Hreg, Hx⟩
  imod txs_open_i B N p sp t0 E hE tx r $$ [] with ⟨He, Hcl⟩
  · iframe Hinv Hreg
  unfold txEntry
  icases He with (⟨Hdb, >Hdone, Hst, (Hx' | >Hex), Hrh⟩ | ⟨>Hdone, >Hex, -⟩)
  · iunfold txExcl at Hx
    icases Hx with ⟨%c, %x, Hv, Hd1, Hrest⟩
    icombine Hdone Hd1 as Hd
    iunfold txExcl at Hx'
    icases Hx' with ⟨%c', %x', -, >Hd2, -⟩
    icombine Hd Hd2 gives %h
    exact absurd h.1 (by rw [Qp.le_iff]; simp; grind)
  · imod Hcl $$ [Hdb Hdone Hst Hx Hrh] with -
    · inext; ileft; iframe Hdb Hdone Hst Hrh
      ileft; iexact Hx
    imodintro; iexact Hex
  · iunfold txExcl at Hx
    icases Hx with ⟨%c, %x, Hv, Hd1, Hrest⟩
    icombine Hdone Hd1 gives %h
    exact absurd h.2 (by decide)

open Iris.ProofMode in
/-- **Close**: with the exclusive part's `done` half (the exclusive part's other contents given
back, its `ex` token in the invariant), the entry turns done; its quarter of `tx.db` comes out
and the statistics stay read-only (batch 17). -/
theorem txs_close (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗
      ghostVar r.n.done (1 : Qp).half false ⊢
    |={E}=> tx.[Tx, go!"db"] ↦{DFrac.own (1 : Qp).half.half} r.db ∗
      (∃ s : TxStats, tx.[Tx, go!"stats"] ↦□ s) ∗ ghostVar r.n.done (1 : Qp).half true := by
  iintro ⟨#Hinv, #Hreg, Hd⟩
  imod txs_open_i B N p sp t0 E hE tx r $$ [] with ⟨He, Hcl⟩
  · iframe Hinv Hreg
  unfold txEntry
  icases He with (⟨>Hdb, >Hdone, >Hst, (Hx | >Hex), -⟩ | ⟨>Hdone, >Hex', -⟩)
  · icombine Hdone Hd as Hd'
    iunfold txExcl at Hx
    icases Hx with ⟨%c', %x', -, >Hd2, -⟩
    icombine Hd' Hd2 gives %h
    exact absurd h.1 (by rw [Qp.le_iff]; simp; grind)
  · ihave Hu := ghostVar_update_halves true r.n.done _ _ $$ Hdone Hd
    imod Hu
    icases Hu with ⟨Hdone, Hd⟩
    icases Hst with ⟨%s, Hst⟩
    imod (typedPointsto_dfractional (GF := GF) _ s).dfractional_persist _ $$ Hst with #Hst
    imod Hcl $$ [Hdone Hex] with -
    · inext; iright; iframe Hdone Hex; iexists s; iexact Hst
    imodintro; iframe Hdb Hd; iexists s; iexact Hst
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
  icases He with (⟨Hdb, Hdone, >Hst, Hx, Hrh⟩ | ⟨>Hdone, >Hex', -⟩)
  · icases Hst with ⟨%s, Hst⟩
    imodintro
    iexists s
    iframe Hst
    iintro %s' Hst
    imod Hcl $$ [Hdb Hdone Hst Hx Hrh] with -
    · inext; ileft; iframe Hdb Hdone Hx Hrh
      iexists s'; iexact Hst
    imodintro; iexact Hex
  · icombine Hex Hex' gives %h
    exact absurd h.1 (by rw [Qp.le_iff]; simp; have := q.2; grind)

end lemmas

end txs

end bbolt
end EtcdGrove
end Perennial
