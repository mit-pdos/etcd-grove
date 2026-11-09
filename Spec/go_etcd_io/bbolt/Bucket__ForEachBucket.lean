/-
`b.ForEachBucket(fn)` (`bucket.go`): `fn(k)` for each nested bucket's key in key order, stopping at
the first error.

**Users.** `DeleteBucket` (its recursion), nested-bucket clients. Snippet: `ReqNested`.
**Proof sketch.** As `ForEach`, skipping the entries without the bucket flag. **Changes.** New.
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

/-- `b.ForEachBucket(fn)`: calls `fn` on each nested bucket's name in the bucket at `p` (the names
`ks`, in key order), carrying `I` and stopping at the first error. -/
def Bucket.ForEachBucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat) (fn : GoFunc) (I : Nat → IProp GF)
    (E : Nat → GoInterface → IProp GF) (ks : List GoString),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs ∗
      ⌜T.gens p = gs ∧ ks = ((T.ents p).filter (fun e => e.2.isNone)).map Prod.fst⌝ ∗ I 0 ∗
      □ (∀ (i : Nat) (kb : GoString) (k : GoSlice) (Φ : val → IProp GF),
          ⌜ks[i]? = some kb⌝ -∗ I i -∗ txBytes tx γ k kb -∗ boltTx tx γ q T -∗
          ▷ (∀ err : GoInterface, boltTx tx γ q T -∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) -∗
              Φ #err) -∗
          WP (App (Val #fn) (Val #k)) {{ Φ }}) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"ForEachBucket")) (Val #fn))
  {{ (err : GoInterface), RET #err; boltTx tx γ q T ∗
      ((⌜err = GoInterface.nil⌝ ∗ I ks.length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < ks.length⌝ ∗ E i err)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
