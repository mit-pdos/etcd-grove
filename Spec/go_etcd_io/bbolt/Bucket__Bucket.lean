/-
`b.Bucket(name)` (`bucket.go`): the nested bucket `name`, or nil.

**Users.** `Tx.Bucket` (the root's), nested-bucket clients (none in etcd). Snippet: `ReqNested`.

**Proof sketch.** A writer's child cache (`b.buckets`) first; else `seek`, check the bucket flag,
`openBucket` the value (an inline bucket's page aligned into a copy if needed, 4d's `InBucket`
view), cache it if writable (all of the transaction). The handle's path is `p.child name`, its
generations the current ones.

**Changes.** New (nested buckets).
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

/-- `b.Bucket(name)`: a handle of the nested bucket `name` of the bucket at `p`, or nil. -/
def Bucket.Bucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat) (name : GoSlice) (n : GoString) (dq : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs ∗ name ↦*{dq} n ∗ ⌜T.gens p = gs ∧ (T.rw = true → q = 1)⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Bucket")) (Val #name))
  {{ (c : Loc), RET #c; boltTx tx γ q T ∗ name ↦*{dq} n ∗
      (if (T.cur.atPath (p.child n)).any Ent.isBkt
       then iprop(⌜c ≠ Loc.null⌝ ∗ bktH tx γ c (p.child n) (T.gens (p.child n)))
       else iprop(⌜c = Loc.null⌝)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
