/-
`b.Put(key, value)` (`bucket.go`).

**Users.** The backend's `unsafePut` (`batch_tx.go:183`, after `FillPercent = 0.9` for sequential
puts; a failure is fatal), defrag's copy (`backend.go:849, 930`), the bank (`bbolttest.go:174-183,
241`). Snippets: `ReqBackendBatch`, `ReqBank`, `ReqNested`, `ReqReadOnlyPut`.

**Proof sketch.** The checks in Go's order (closed: excluded by `boltTx`; not writable; key
required; key too large; value too large: excluded by `bboltEntryMax < maxValueSize`); `seek`; a
nested bucket's key: `ErrIncompatibleValue`; else materialize the leaf's node path (`Cursor.node`:
`Bucket.node` reads pages into the node cache, needing all of the transaction) and `node.put` the
cloned key with the value **by reference** (Go: "the value must remain valid for the life of the
transaction"): the caller's fraction of the value is kept until the transaction is done
(`putLoan`, `putLoan_done`; round 1, C1: was a persistent `↦*□`, which defrag cannot give for a
value it read from another open transaction). The abstraction relation then maps the nodes to
`T.cur` with the key set.

**Changes.** Over paths; a read transaction's `Put` returns `ErrTxNotWritable` (was a premise
`T.rw`); `ErrIncompatibleValue` on a bucket's key; the errors named (`isErr`). Kept: the entry bound
`bboltEntryMax` (D4: the code would panic later, in `Commit`).
**Proof sketch, the success arm in the internal vocabulary** (verify-round, A11 F9).
`wtxCore_view` opens `boltTx` (`T.rw`) to `wtxCore tx γ C` with `physRep T C`; `seek` leaves
`curPath … T kb`; `Cursor.node` gives the leaf `n` with `repKept` (so `physRep T C'`) and
`keyLeaf C' p kb n` (the handle current: `C.bkts b = some p` by `wtxCore_bktOwn` from the
handle premise);
`node.put kb kb value 0 0`; `physRep_set` with `newEnt 0 vb (Ent.val vb)` (the key not a bucket:
the `ErrIncompatibleValue` test; its bounds: the checks and the premise) gives `physRep` of
`T.setCur (… setKey kb (some (Ent.val vb)))`; `wtxCore_view` closes `boltTx`.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The handle premise `bktUse`
(the bucket's ownership share in a write transaction) in place of `bktH … gs` and the generation
check, given back (the per-path generation counter it replaces was unobservable state, redundant
with ownership).
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.Put(key, value)`: on a write transaction (all of it), sets `key` to `value` in the bucket at
`p`; the errors in Go's order (not writable, empty key, key too large, `key` is a nested
bucket). The value is kept by reference: lent until the transaction is done (`putLoan`). -/
def Bucket.Put.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (qb : Qp) (key value : GoSlice) (kb vb : GoString) (dk dv : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ bktUse tx γ T.rw b p qb ∗ key ↦*{dk} kb ∗ value ↦*{dv} vb ∗
      ⌜(T.rw = true → q = 1) ∧ kb.length + vb.length ≤ bboltEntryMax⌝ }}
    (App (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Put")) (Val #key)) (Val #value))
  {{ (err : GoInterface), RET #err; bktUse tx γ T.rw b p qb ∗ key ↦*{dk} kb ∗
      (if T.rw = false then
         iprop(value ↦*{dv} vb ∗ boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
       else if kb.length = 0 then
         iprop(value ↦*{dv} vb ∗ boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrKeyRequired err)
       else if maxKeySize < kb.length then
         iprop(value ↦*{dv} vb ∗ boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrKeyTooLarge err)
       else if (T.cur.atPath (p.child kb)).any Ent.isBkt then
         iprop(value ↦*{dv} vb ∗ boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err)
       else iprop(⌜err = GoInterface.nil⌝ ∗ putLoan tx γ value dv vb ∗
         boltTx tx γ q (T.setCur (T.cur.modAt p (fun e => e.setKey kb (some (Ent.val vb))))))) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
