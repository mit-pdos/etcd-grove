/-
bbolt as the backend sees it: a key-value contract. The trust boundary (bbolt is names-only
here; its proof, branch `bbolt`, is not merged). Lean-first (no Rocq counterpart); see
`notes/decisions.md`, "The backend: the buffers, bbolt as a key-value contract, the locks and
the views".

**Data.** A database is its top-level buckets' contents (`Data`, etcd has no nested buckets);
a bucket's cursor order is its sorted entry list (`bktEnts`).

**Predicates** (axioms, as the btree's `ownBTree` was before the btree was verified; all timeless,
as ownership of or knowledge about bbolt's memory is):
- `ownDB db γ D`: the open database `db`, committed data `D` (exclusive); `wrTok γ`: the right
  to begin the write transaction; `isDB db`: `db` is an open database (persistent).
- `txLive tx q`: the transaction `tx` is open (fractional): the memory its reads point into is
  valid. `txBytes tx s b` (persistent): `s` holds `b` while `tx` is open (`txBytes_acc`).
- `rtxSnap tx D` (persistent): the read transaction `tx` reads the snapshot `D`;
  `rtxStats tx` (exclusive): `Bucket()`/`Cursor()`/`ForEach` on it (its statistics).
  `rBkt tx b es` (persistent): `b` is the read transaction's bucket with entries `es`.
- `ownWTx tx γ D S`: the write transaction, begun at the committed `D`, contents `S` now
  (exclusive; it holds `txLive tx 1`, `ownWTx_live`). `wBkt tx b n` (persistent): `b` is its
  handle of the bucket named `n`; the handle's `FillPercent` field is the transaction's
  (`ownWTx_fill`).
- `ownCur tx c es pos`: a cursor of `tx` over the entries `es`, at `pos` (`none`: not
  positioned; `some i`: at the `i`-th, `es.length` past the end).
- `txDone tx` (persistent): `tx` was committed or rolled back (its `Stats` can be read);
  `txDB tx db` (persistent): `tx`'s database.
- `fileHolds path D`: the database file at `path` holds `D` (what `bolt.Open` reads: the
  caller's assumption about the file).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode

/-- A bucket's contents. -/
abbrev BktData := GMap GoString GoString

/-- A database's data: its top-level buckets by name. -/
abbrev Data := GMap GoString BktData

/-- A bucket's entries in cursor order: sorted by key. -/
def bktEnts (m : BktData) : List Ent := m.toList.mergeSort entLe

/-- bbolt's `MaxKeySize`. -/
def maxKeySize : Nat := 32768

/-- bbolt's `MaxValueSize`. -/
def maxValueSize : Nat := 2 ^ 31 - 2

/-- The first index of a sorted entry list whose key is not below `k` (`Cursor.Seek`). -/
def seekIdx (es : List Ent) (k : GoString) : Nat :=
  (es.takeWhile (fun e => decide (strLt e.1 k))).length

/-- The ghost names of a database. -/
structure DBNames where
  db : GName
  wr : GName

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom ownDB (db : Loc) (γ : DBNames) (D : Data) : IProp GF
axiom wrTok (γ : DBNames) : IProp GF
axiom isDB (db : Loc) : IProp GF
axiom txLive (tx : Loc) (q : Qp) : IProp GF
axiom txBytes (tx : Loc) (s : GoSlice) (b : GoString) : IProp GF
axiom rtxSnap (tx : Loc) (D : Data) : IProp GF
axiom rtxStats (tx : Loc) : IProp GF
axiom rBkt (tx : Loc) (b : Loc) (es : List Ent) : IProp GF
axiom ownWTx (tx : Loc) (γ : DBNames) (D S : Data) : IProp GF
axiom wBkt (tx : Loc) (b : Loc) (n : GoString) : IProp GF
axiom ownCur (tx : Loc) (c : Loc) (es : List Ent) (pos : Option Nat) : IProp GF
axiom txDone (tx : Loc) : IProp GF
axiom txDB (tx : Loc) (db : Loc) : IProp GF
axiom fileHolds (path : GoString) (D : Data) : IProp GF

@[instance] axiom isDB_persistent (db : Loc) : Persistent (isDB (GF := GF) db)
@[instance] axiom txBytes_persistent (tx : Loc) (s : GoSlice) (b : GoString) :
  Persistent (txBytes (GF := GF) tx s b)
@[instance] axiom rtxSnap_persistent (tx : Loc) (D : Data) : Persistent (rtxSnap (GF := GF) tx D)
@[instance] axiom rBkt_persistent (tx b : Loc) (es : List Ent) :
  Persistent (rBkt (GF := GF) tx b es)
@[instance] axiom wBkt_persistent (tx b : Loc) (n : GoString) : Persistent (wBkt (GF := GF) tx b n)
@[instance] axiom txDone_persistent (tx : Loc) : Persistent (txDone (GF := GF) tx)
@[instance] axiom txDB_persistent (tx db : Loc) : Persistent (txDB (GF := GF) tx db)
@[instance] axiom txLive_fractional (tx : Loc) : Fractional (txLive (GF := GF) tx)

/-- A read transaction's statistics are exclusive. -/
axiom rtxStats_excl (tx : Loc) : rtxStats (GF := GF) tx ∗ rtxStats tx ⊢ False

/-! Every predicate is timeless: each is ownership of, or knowledge about, bbolt's memory (pages,
the memory map, the transaction's fields), as a points-to is. -/
@[instance] axiom ownDB_timeless (db : Loc) (γ : DBNames) (D : Data) :
  Timeless (ownDB (GF := GF) db γ D)
@[instance] axiom wrTok_timeless (γ : DBNames) : Timeless (wrTok (GF := GF) γ)
@[instance] axiom isDB_timeless (db : Loc) : Timeless (isDB (GF := GF) db)
@[instance] axiom txLive_timeless (tx : Loc) (q : Qp) : Timeless (txLive (GF := GF) tx q)
@[instance] axiom txBytes_timeless (tx : Loc) (s : GoSlice) (b : GoString) :
  Timeless (txBytes (GF := GF) tx s b)
@[instance] axiom rtxSnap_timeless (tx : Loc) (D : Data) : Timeless (rtxSnap (GF := GF) tx D)
@[instance] axiom rtxStats_timeless (tx : Loc) : Timeless (rtxStats (GF := GF) tx)
@[instance] axiom rBkt_timeless (tx b : Loc) (es : List Ent) : Timeless (rBkt (GF := GF) tx b es)
@[instance] axiom ownWTx_timeless (tx : Loc) (γ : DBNames) (D S : Data) :
  Timeless (ownWTx (GF := GF) tx γ D S)
@[instance] axiom wBkt_timeless (tx b : Loc) (n : GoString) : Timeless (wBkt (GF := GF) tx b n)
@[instance] axiom ownCur_timeless (tx c : Loc) (es : List Ent) (pos : Option Nat) :
  Timeless (ownCur (GF := GF) tx c es pos)
@[instance] axiom txDone_timeless (tx : Loc) : Timeless (txDone (GF := GF) tx)
@[instance] axiom txDB_timeless (tx db : Loc) : Timeless (txDB (GF := GF) tx db)
@[instance] axiom fileHolds_timeless (path : GoString) (D : Data) :
  Timeless (fileHolds (GF := GF) path D)

/-- A transaction's slice is read while the transaction is open. -/
axiom txBytes_acc (tx : Loc) (s : GoSlice) (b : GoString) (q : Qp) :
  txBytes (GF := GF) tx s b ∗ txLive tx q ⊢
    ∃ dq : DFrac, s ↦*{dq} b ∗ (s ↦*{dq} b -∗ txLive tx q)

/-- An open transaction is a non-nil `*Tx` (`DB.Begin` returns one with a nil error; the
backend's `t.tx != nil` and `readTx.tx != nil` checks rely on it). -/
axiom txLive_nonnull (tx : Loc) (q : Qp) : txLive (GF := GF) tx q ⊢ ⌜tx ≠ Loc.null⌝

/-- The write transaction is open. -/
axiom ownWTx_live (tx : Loc) (γ : DBNames) (D S : Data) :
  ownWTx (GF := GF) tx γ D S ⊢ txLive tx 1 ∗ (txLive tx 1 -∗ ownWTx tx γ D S)

/-- The write transaction owns its bucket handles' `FillPercent` field. -/
axiom ownWTx_fill (tx b : Loc) (γ : DBNames) (D S : Data) (n : GoString) :
  ownWTx (GF := GF) tx γ D S ∗ wBkt tx b n ⊢
    ∃ f : w64, structFieldRef go_etcd_io.bbolt.Bucket go!"FillPercent" b ↦ f ∗
      (∀ f' : w64, structFieldRef go_etcd_io.bbolt.Bucket go!"FillPercent" b ↦ f' -∗
        ownWTx tx γ D S)

/-- What a cursor move to the `i`-th entry returns: its key (never nil: bbolt's keys are not
empty) and value, valid while `tx` is open; nil and nil past the end. -/
def curAt (tx : Loc) (es : List Ent) (i : Nat) (k v : GoSlice) : IProp GF :=
  match es[i]? with
  | some e => iprop(⌜k ≠ slice.nil⌝ ∗ txBytes tx k e.1 ∗ txBytes tx v e.2)
  | none => iprop(⌜k = slice.nil ∧ v = slice.nil⌝)

instance curAt_persistent (tx : Loc) (es : List Ent) (i : Nat) (k v : GoSlice) :
    Persistent (curAt (GF := GF) tx es i k v) := by
  unfold curAt; split <;> infer_instance

end preds

end backend
end EtcdGrove
end Perennial
