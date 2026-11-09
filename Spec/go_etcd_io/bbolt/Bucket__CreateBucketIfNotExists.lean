/-
`b.CreateBucketIfNotExists(key)` (`bucket.go`).

**Users.** `Tx.CreateBucketIfNotExists` (the root's: the backend's `UnsafeCreateBucket`,
`batch_tx.go:137`; defrag, `backend.go:827, 905`; `examples/axiomcx/bboltnan`). Snippets:
`ReqBackendBatch`, `ReqNested`.

**Proof sketch.** As `CreateBucket`, but an existing bucket (in the child cache, or found by `seek`
and opened) is returned with nil.

**Changes.** Over paths; read transactions' error; `ErrIncompatibleValue` on a value's key.
**Proof sketch, the creating arm in the internal vocabulary** (verify-round, A11 F9): as
`CreateBucket`'s (`Cursor.node`, `node.put`, `physRep_set` with `newEnt`'s bucket case).
-/
module

public import Spec.go_etcd_io.bbolt.Api

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

/-- `b.CreateBucketIfNotExists(key)`: the bucket `key` of the bucket at `p`, created empty if
absent, and its handle; errors: not writable, empty name, `key` holds a value. -/
def Bucket.CreateBucketIfNotExists.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs ∗ key ↦*{dk} kb ∗
      ⌜T.gens p = gs ∧ (T.rw = true → q = 1) ∧ kb.length ≤ maxKeySize⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"CreateBucketIfNotExists")) (Val #key))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err); key ↦*{dk} kb ∗
      (if T.rw = false then
         iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
       else if kb.length = 0 then
         iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗
           isErr go_etcd_io.bbolt.errors.ErrBucketNameRequired err)
       else match T.cur.atPath (p.child kb) with
         | some (Ent.bkt _ _) => iprop(⌜err = GoInterface.nil ∧ c ≠ Loc.null⌝ ∗ boltTx tx γ q T ∗
             bktH tx γ c (p.child kb) (T.gens (p.child kb)))
         | some (Ent.val _) => iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗
             isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err)
         | none => iprop(⌜err = GoInterface.nil ∧ c ≠ Loc.null⌝ ∗
             boltTx tx γ q (T.setCur (T.cur.modAt p (fun e => e.setKey kb (some (Ent.bkt (W64 0) []))))) ∗
             bktH tx γ c (p.child kb) (T.gens (p.child kb)))) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
