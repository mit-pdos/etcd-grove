/-
`b.NextSequence()` (`bucket.go`): increments the counter (wrapping, `uint64`) and returns it.

**Users.** None in etcd (a common bbolt idiom for ids). Snippet: `ReqNested`. **Proof sketch.** As
`SetSequence`, with `IncSequence`. **Changes.** New.
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

/-- `b.NextSequence()`: on a write transaction (all of it), the counter of the bucket at `p` plus
one, stored and returned. -/
def Bucket.NextSequence.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs ∗ ⌜T.gens p = gs ∧ (T.rw = true → q = 1)⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"NextSequence")) (Val #()))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      if T.rw = false then
        iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
      else iprop(⌜err = GoInterface.nil ∧
          n = ((T.cur.atPath p).map Ent.seq).getD (W64 0) + W64 1⌝ ∗
        boltTx tx γ q (T.setCur (T.cur.modAt p (fun e => e.setSeq n)))) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
