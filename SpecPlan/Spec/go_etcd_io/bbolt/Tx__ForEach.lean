/-
`tx.ForEach(fn)` (`tx.go`): `fn(name, b)` for each top-level entry in key order, with the
bucket's handle (`tx.root.Bucket(name)`, nil for a value, which no API puts at the root).

**Users.** None in etcd (it iterates with `tx.Cursor()`). Snippet: `ReqNested`.
**Proof sketch.** `Bucket.ForEach.spec` on the root, whose callback calls `Bucket.Bucket.spec` (a
writer's child cache: all of the transaction). **Changes.** New.
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

/-- `tx.ForEach(fn)`: calls `fn` on each top-level bucket's name and handle in key order, carrying
`I` and stopping at the first error. -/
def Tx.ForEach.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (fn : GoFunc) (I : Nat → IProp GF)
    (E : Nat → GoInterface → IProp GF),
  {{ boltTx (GF := GF) tx γ q T ∗ ⌜T.rw = true → q = 1⌝ ∗ I 0 ∗
      □ (∀ (i : Nat) (kb : GoString) (vo : Option GoString) (k : GoSlice) (bl : Loc)
          (Φ : val → IProp GF),
          ⌜(T.ents [])[i]? = some (kb, vo)⌝ -∗ I i -∗ txBytes tx γ k kb -∗
          (match vo with
           | none => iprop(⌜bl ≠ Loc.null⌝ ∗ bktH tx γ bl [kb] (T.gens [kb]))
           | some _ => iprop(⌜bl = Loc.null⌝)) -∗
          boltTx tx γ q T -∗
          ▷ (∀ err : GoInterface, boltTx tx γ q T -∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) -∗
              Φ #err) -∗
          WP (App (App (Val #fn) (Val #k)) (Val #bl)) {{ Φ }}) }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"ForEach")) (Val #fn))
  {{ (err : GoInterface), RET #err; boltTx tx γ q T ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (T.ents []).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (T.ents []).length⌝ ∗ E i err)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
