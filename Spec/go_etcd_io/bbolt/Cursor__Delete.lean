/-
`c.Delete()` (`cursor.go`): deletes the entry the cursor is at.

**Users.** None in etcd (a common bbolt idiom for deleting while iterating). Snippet:
`ReqCursorDelete`.

**Proof sketch.** Not writable: `ErrTxNotWritable`; `keyValue` of the top of the stack; a nested
bucket's key: `ErrIncompatibleValue`; else `c.node().del(key)` (materializes the leaf's node path:
all of the transaction). The cursor stays at the old view: `Next`/`Prev` need a reposition
(`First`/`Last`/`Seek`), as Go's documentation asks.

**Changes.** New. The cursor must be at an entry (`c.node()` asserts a non-empty stack; a cursor past
the end deletes nothing, left out).
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

/-- `c.Delete()` on a cursor at entry `i`: on a write transaction (all of it), removes that entry;
errors: not writable, a nested bucket. The cursor must be repositioned before `Next`/`Prev`. -/
def Cursor.Delete.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (i : Nat) (kb : GoString) (vo : Option GoString),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c p gs T (some i) ∗
      ⌜(T.ents p)[i]? = some (kb, vo) ∧ (T.rw = true → q = 1)⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Delete")) (Val #()))
  {{ (err : GoInterface), RET #err; boltCur tx γ c p gs T (some i) ∗
      (if T.rw = false then
         iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
       else if vo = none then
         iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err)
       else iprop(⌜err = GoInterface.nil⌝ ∗
         boltTx tx γ q (T.setCur (T.cur.modAt p (fun e => e.setKey kb none))))) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
