/-
# The backend's internal vocabulary (batch 4a)

What the internal helpers' specs (the buffers, the embedded `batchTx`, the commit path, the read
transactions' plumbing) are written over. No client imports this module: the API's specs
(`Api.lean`) say everything a client sees; these mirror the code for the package's own proofs.

* Buffers (pure): a bucket buffer's used entries in insertion order (`List (GoString × GoString)`),
  `lastVal` (the newest value of a key), `dedupeOk` (sorted, the newest value of each key: `dedupe`'s
  `sort.Stable` then keep-last), `mergeOk` (`bucketBuffer.merge`: appended, deduplicated when the
  appended keys do not all follow the old ones), `bbRangeOk` (`bucketBuffer.Range`: the binary
  search over a sorted buffer). A transaction buffer maps a bucket id to its bucket buffer's
  entries (`TxB`).
* Resources: `bbAt bb l w` (a `*bucketBuffer` with used entries `l`, each slice read-only, `w`:
  writable), `txbAt t B`
  (a `*txBuffer`'s map), `twbAt t B seq` (a `*txWriteBuffer`: the map and `bucket2seq`), `trbAt t B
  ver` (a `*txReadBuffer`: the map and `bufVersion`); `bt0Loc γ` (the embedded `batchTx` of the
  batch transaction); `btHeld γ` (the batch mutex held: what `lock()` gives with the lock's
  content), `btPhys γ I n d` (bbolt's write transaction at `I`, `pending = n`,
  `pendingDeleteOperations = d`; `btStopped γ`: no write transaction, after `CommitAndStop`),
  `rtHeld γ` (`readTx.mu` held for writing, with the read buffer and the read transaction),
  `beRun γ` (the run loop's right to run: `stopc` not yet closed); `rtNew γ tx I` (a just-begun
  bbolt read transaction at `I` with its reader slot: `begin(false)`'s).

Intended realization: the struct fields' points-to with the slices' read-only points-to; the
batch session's authority (`Api.lean`'s header) split into these physical pieces.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section model
variable [GooseExts]

/-- A transaction buffer: bucket id to its bucket buffer's used entries. -/
abbrev TxB := w64 → Option (List (GoString × GoString))

/-- The newest value of `k` in `l`. -/
def lastVal (l : List (GoString × GoString)) (k : GoString) : Option GoString :=
  (l.reverse.find? (fun x => decide (x.1 = k))).map Prod.snd

/-- `l'` is `l` deduplicated: sorted, the newest value of each key. -/
def dedupeOk (l l' : List (GoString × GoString)) : Prop :=
  l'.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧ ∀ x, x ∈ l' ↔ lastVal l x.1 = some x.2

/-- `bucketBuffer.merge`: `new` appended to `old`; with an empty `old`, that is all; else
deduplicated unless `old`'s last key is below `new`'s first (the code's test; with an empty `new`,
the test reads a stale slot and may deduplicate `old`, which changes nothing of a sorted one). -/
def mergeOk (old new res : List (GoString × GoString)) : Prop :=
  if old = [] then res = new
  else match old.getLast?, new.head? with
    | some x, some y => if go.GoStringLt x.1 y.1 then res = old ++ new else dedupeOk (old ++ new) res
    | _, _ => res = old ∨ dedupeOk old res

/-- `bucketBuffer.Range` over a sorted buffer: an empty end the key alone, else the entries of
`[k, e)` up to `limit`. -/
def bbRangeOk (l : List (GoString × GoString)) (k e : GoString) (limit : Int)
    (r : List (GoString × GoString)) : Prop :=
  btRange (lastVal l) k e (if 0 < limit then limit else 2 ^ 63 - 1) r

/-- `txWriteBuffer.writeback`'s result on the read buffer: each written bucket's entries
deduplicated if it is not sequential, then moved (a bucket new to the read buffer) or merged. -/
def writebackOk (W : TxB) (seq : w64 → Option Bool) (R R' : TxB) : Prop :=
  ∀ id, match W id with
    | none => R' id = R id
    | some w => ∃ w', (if seq id = some false then dedupeOk w w' else w' = w) ∧
        match R id with
        | none => R' id = some w'
        | some r => ∃ r', mergeOk r w' r' ∧ R' id = some r'

end model

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- A `*bucketBuffer` whose used entries are `l` (exclusive); `w`: writable (a spare slot, as
`newBucketBuffer`'s and `add`'s keep; a `CopyUsed` copy has none). -/
opaque bbAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (bb : Loc) (l : List (GoString × GoString)) (w : Bool) : IProp GF := iprop(True)

/-- A `*txBuffer` whose map holds `B` (exclusive). -/
opaque txbAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Loc) (B : TxB) : IProp GF := iprop(True)

/-- A `*txWriteBuffer` holding `B`, its sequential flags `seq` (exclusive). -/
opaque twbAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Loc) (B : TxB) (seq : w64 → Option Bool) : IProp GF := iprop(True)

/-- A `*txReadBuffer` holding `B` at version `ver` (exclusive). -/
opaque trbAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Loc) (B : TxB) (ver : w64) : IProp GF := iprop(True)

/-- The embedded `batchTx` of the backend's batch transaction. -/
opaque bt0Loc (γ : BeNames) : Loc

/-- The batch mutex held (exclusive). -/
opaque btHeld [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) : IProp GF := iprop(True)

/-- bbolt's write transaction at `I`, `pending = n`, `pendingDeleteOperations = d` (exclusive). -/
opaque btPhys [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (I : Image) (n d : Nat) : IProp GF := iprop(True)

/-- No write transaction (after `CommitAndStop`; exclusive). -/
opaque btStopped [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) : IProp GF := iprop(True)

/-- `readTx.mu` held for writing, with the read buffer and the read transaction (exclusive). -/
opaque rtHeld [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) : IProp GF := iprop(True)

/-- (provisional, 4c's cursor) `c` is a bbolt cursor of a bucket whose entries are `L`
(exclusive). -/
opaque curOver [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Loc) (L : GoString → Option GoString) : IProp GF := iprop(True)

/-- **A just-begun bbolt read transaction `tx` at the committed image `I`** (exclusive; verify-round,
A11-completeness F4): `begin(false)`'s result, holding its reader slot (the token of the thread that
will roll it back), which `unsafeCommit` installs as the read side's transaction. -/
opaque rtNew [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) (tx : Loc) (I : Image) : IProp GF := iprop(True)

/-- The run loop's right to run (`stopc` not yet closed; exclusive). -/
opaque beRun [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : BeNames) : IProp GF := iprop(True)

end vocab

end Backend
end EtcdGrove
end Perennial
