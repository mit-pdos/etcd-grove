/-
`b.Sequence()` (`bucket.go`): the bucket's sequence counter.

**Users.** Nested-bucket clients (none in etcd). Snippet: `ReqNested`. **Proof sketch.** Read the
handle's `InBucket` (4d's `InSequence`). **Changes.** New.
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

/-- `b.Sequence()`: the sequence counter of the bucket at `p`. -/
def Bucket.Sequence.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs ∗ ⌜T.gens p = gs⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Sequence")) (Val #()))
  {{ (n : w64), RET #n; boltTx tx γ q T ∗ ⌜n = ((T.cur.atPath p).map Ent.seq).getD (W64 0)⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
