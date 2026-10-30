/-
The accounting of the mapped pages between a DB and its open read transactions (sequential
use: one goroutine uses the DB at a time; any number of transactions may be open).

The caller's half of the mapped cells of each page (`Proof/os/FileModel.lean`) is shared: each
open read transaction holds a fraction of every page it can see (`pagesViewF`, a fraction per
page), and the DB the rest (`rem`). A reader takes, when it begins, half of the DB's
remainder of each page it can see, and gives it back when it closes. The invariant
(`fracsOK`): for every page, the DB's remainder plus the readers' fractions is the half.
So once no open reader can see a page, the DB holds the whole half again, which is what a
writer needs to write the page (`WriteAt` takes the half of the cells it changes): bbolt's
MVCC rule (a page freed by a transaction is pending until every reader that could see it has
closed; `freelist.release`/`releaseRange`) is what makes that hold when bbolt reuses a page.

This file is pure bookkeeping (and its predicates); the DB's and transactions' predicates,
which use it, come with the specs of `beginTx`, `removeTx`, `Commit` (`notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.TxModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

/-- An open read transaction, as the DB accounts for it: its id (its meta's txid), the pages
it can see, and its fraction of each. -/
structure ReaderAcct where
  txid : Nat
  sees : Nat → Bool
  frac : Nat → Qp

/-- The half of a cell's points-to that is the caller's (the system holds the other). -/
def halfQ : Qp := Qp.half 1

/-- The sum of the fractions of page `p` held by the readers `rs` that see it. -/
noncomputable def readersFrac (rs : List ReaderAcct) (p : Nat) : Option Qp :=
  rs.foldr (fun r acc =>
    if r.sees p then (match acc with | none => some (r.frac p) | some a => some (r.frac p + a))
    else acc) none

/-- The DB's remainder `rem p` and the readers' fractions of page `p` make up the half. -/
def fracsOK (rem : Nat → Qp) (rs : List ReaderAcct) (p : Nat) : Prop :=
  match readersFrac rs p with
  | none => rem p = halfQ
  | some s => rem p + s = halfQ

theorem readersFrac_none (rs : List ReaderAcct) (p : Nat) (hno : ∀ r ∈ rs, r.sees p = false) :
    readersFrac rs p = none := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have h1 := hno r (List.mem_cons_self ..)
    have ih' := ih (fun r' h => hno r' (List.mem_cons_of_mem _ h))
    unfold readersFrac at ih' ⊢
    rw [List.foldr_cons, h1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ih'

/-- No open reader sees page `p`: the DB holds its whole half. -/
theorem fracsOK_none (rem : Nat → Qp) (rs : List ReaderAcct) (p : Nat)
    (hok : fracsOK rem rs p) (hno : ∀ r ∈ rs, r.sees p = false) : rem p = halfQ := by
  unfold fracsOK at hok
  rw [readersFrac_none rs p hno] at hok; exact hok

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The mapped cells of the pages `pages`, at a fraction per page. -/
def pagesViewF (data : Loc) (ps : Nat) (q : Nat → Qp) (pages : GMap Nat (List w8)) : IProp GF :=
  [∗map] id ↦ pg ∈ pages, bytesPointsto (data +ₗ ((id * ps : Nat) : Int)) (DFrac.own (q id)) pg

end preds

end bbolt
end EtcdGrove
end Perennial
