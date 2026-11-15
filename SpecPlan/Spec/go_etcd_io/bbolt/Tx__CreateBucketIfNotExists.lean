/-
`tx.CreateBucketIfNotExists(name)` (`tx.go`): the root's.

**Users.** The backend's `UnsafeCreateBucket` (`batch_tx.go:137`; fatal on an error), defrag
(`backend.go:827, 905`), `examples/axiomcx/bboltnan`. Snippet: `ReqBackendBatch`.
**Proof sketch.** `Bucket.CreateBucketIfNotExists.spec` at the root. **Changes.** The old spec
(`T.rw` a premise, names non-empty or an error) restated over paths with the read transaction's and
the value's errors.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** An existing bucket behaves
as a lookup (its token `bktTok` given back at the handle, the cached one if there was one); a new
one gives its whole token `bktOwn … (some c) 1`; in place of `bktH … gs` (the per-path generation
counter it replaces was unobservable state, redundant with ownership).
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

/-- `tx.CreateBucketIfNotExists(name)`: the top-level bucket `name`, created empty if absent (see
`Bucket.CreateBucketIfNotExists.spec`). -/
def Tx.CreateBucketIfNotExists.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (o : Option Loc) (qc : Qp)
    (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ bktTok tx γ T [kb] o qc ∗ key ↦*{dk} kb ∗
      ⌜(T.rw = true → q = 1) ∧ kb.length ≤ maxKeySize⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"CreateBucketIfNotExists")) (Val #key))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err); key ↦*{dk} kb ∗
      (if T.rw = false then
         iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
       else if kb.length = 0 then
         iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗
           isErr go_etcd_io.bbolt.errors.ErrBucketNameRequired err)
       else match T.cur.atPath [kb] with
         | some (Ent.bkt _ _) => iprop(⌜err = GoInterface.nil ∧ c ≠ Loc.null⌝ ∗ boltTx tx γ q T ∗
             bktOwn tx γ [kb] (some c) qc ∗ ⌜∀ c', o = some c' → c = c'⌝)
         | some (Ent.val _) => iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗
             isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err)
         | none => iprop(⌜err = GoInterface.nil ∧ c ≠ Loc.null⌝ ∗
             boltTx tx γ q (T.setCur (T.cur.setKey kb (some (Ent.bkt (W64 0) [])))) ∗
             bktOwn tx γ [kb] (some c) 1)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
