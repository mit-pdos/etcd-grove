/-
bbolt's API: the pure data its specs are written over (the frozen spec of 2026-11-03,
`notes/bbolt-spec-decisions.md`). A database's data (`Data`: its top-level buckets), a bucket's
entries in cursor order, the size bounds, and a transaction's view (`TxView`). Part of the API
(`etc/api/bbolt.txt`); `Api.lean` imports it.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Defn.String
public import Proof.go_etcd_io.raft.v3.ProjSimps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode

/-! # Data (pure) -/

section data

/-- A bucket's contents: key to value. -/
abbrev BktData := GMap GoString GoString

/-- A database's data: its top-level buckets by name (no nested buckets: the scope, see
`notes/bbolt-spec-decisions.md`, "Scope"). -/
abbrev Data := GMap GoString BktData

/-- An entry: a key and its value. -/
abbrev BoltEnt := GoString × GoString

/-- A bucket's entries in cursor order: sorted by key (`bytes.Compare`, `go.GoStringLt`). -/
def bktEnts (m : BktData) : List BoltEnt :=
  m.toList.mergeSort (fun a b => !decide (go.GoStringLt b.1 a.1))

/-- bbolt's `MaxKeySize` (`bucket.go`): `Put` returns `ErrKeyTooLarge` above it. -/
@[word_unfold] def maxKeySize : Nat := 32768

/-- bbolt's `MaxValueSize` (`bucket.go`), for reference: `Put` returns `ErrValueTooLarge` above
it, but accepts sizes it cannot store (`issues/bbolt-max-value-size-unusable.md`). -/
@[word_unfold] def maxValueSize : Nat := 2 ^ 31 - 2

/-- **The largest entry (key plus value, in bytes) bbolt stores and reads back.** A leaf node of
at most `2 * MinKeysPerPage = 4` entries is never split (`node.splitTwo`), and a larger one is
split into pages of at most that many entries above the fill threshold; so one page holds up to
four entries whatever their size, and a page's buffer (its bytes rounded up to the page size)
must stay below `MaxAllocSize = 2^31 - 1` (amd64), or `Commit` (`WriteInodeToPage`) or a later
read (`leafPageElement.Value`) panics (`issues/bbolt-max-value-size-unusable.md`,
`issues/bbolt-large-values-leaf-unreadable.md`). `4 * (2^28 + 16) + 16` rounded up to the page
size is far below it. The bound of the old bbolt proof's spill (`old/bbolt/`, `SpillFit.lean`).
**What it rests on** (round 3): the split threshold being at most the page size, which Perennial
does not give (every float-to-int conversion is an `ArbitraryInt`, and float `*`/`<` are
uninterpreted): `splitThresholdOk`, the model of the trusted helper `splitThreshold` (D17,
approved), which lives in `TrustedCode/go_etcd_io/bbolt.lean` (round 4: not in the client API;
stated at the end of this file). -/
@[word_unfold] def bboltEntryMax : Nat := 2 ^ 28

/-- `f`, a `float64`'s bits, is a NaN: exponent all ones, mantissa non-zero. -/
def float64IsNaN (f : w64) : Prop :=
  (f.toNat / 2 ^ 52) % 2 ^ 11 = 2 ^ 11 - 1 ∧ f.toNat % 2 ^ 52 ≠ 0

instance (f : w64) : Decidable (float64IsNaN f) := by unfold float64IsNaN; infer_instance

/-- The first index of a sorted entry list whose key is not below `k` (`Cursor.Seek`). -/
def seekIdx (es : List BoltEnt) (k : GoString) : Nat :=
  (es.takeWhile (fun e => decide (go.GoStringLt e.1 k))).length

/-- **A transaction's view**: what the transaction reads and writes.
- `rw`: a write transaction (`Begin(true)`);
- `base`: the committed data when it began (its snapshot, for a read transaction);
- `cur`: its contents now (`base` throughout a read transaction);
- `gen n`: the generation of the bucket name `n`, bumped by `DeleteBucket` so that the handles
  of a deleted bucket are not current (`nonissues/bbolt-deleted-bucket-handle.md`); `0`
  throughout a read transaction.
Literals are written with named fields, so that a field with a default (a `managed` flag for
`View`/`Update`, `notes/bbolt-spec-decisions.md`, D10) can be added without changing a statement. -/
structure TxView where
  rw : Bool
  base : Data
  cur : Data
  gen : GoString → Nat

/-- A read transaction's view: the snapshot `D`. -/
def TxView.ro (D : Data) : TxView := { rw := false, base := D, cur := D, gen := fun _ => 0 }

/-- A write transaction's view when it begins at the committed `D`. -/
def TxView.wr (D : Data) : TxView := { rw := true, base := D, cur := D, gen := fun _ => 0 }

/-- The view with bucket `n` holding `m`. -/
def TxView.setBkt (T : TxView) (n : GoString) (m : BktData) : TxView :=
  { T with cur := T.cur.insert n m }

/-- The view with bucket `n` deleted and its generation bumped. -/
def TxView.dropBkt (T : TxView) (n : GoString) : TxView :=
  { T with cur := T.cur.delete n, gen := fun x => if x = n then T.gen n + 1 else T.gen x }

proj_simps TxView.ro
proj_simps TxView.wr
proj_simps TxView.setBkt
proj_simps TxView.dropBkt

end data

end bbolt
end EtcdGrove
end Perennial
