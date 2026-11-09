/-
`tx.CreateBucket(name)` (`tx.go`): `tx.root.CreateBucket(name)`.

**Users.** The bank (`bbolttest.go:236`). Snippet: `ReqBank`. **Proof sketch.**
`Bucket.CreateBucket.spec` at the root (`p = []`; `modAt [] f = f`). **Changes.** As
`Bucket.CreateBucket`.
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

/-- `tx.CreateBucket(name)`: a new empty top-level bucket and its handle (see
`Bucket.CreateBucket.spec`). -/
def Tx.CreateBucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ key ↦*{dk} kb ∗
      ⌜(T.rw = true → q = 1) ∧ kb.length ≤ maxKeySize⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"CreateBucket")) (Val #key))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err); key ↦*{dk} kb ∗
      (if T.rw = false then
         iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
       else if kb.length = 0 then
         iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗
           isErr go_etcd_io.bbolt.errors.ErrBucketNameRequired err)
       else match T.cur.atPath [kb] with
         | some (Ent.bkt _ _) => iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗
             isErr go_etcd_io.bbolt.errors.ErrBucketExists err)
         | some (Ent.val _) => iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗
             isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err)
         | none => iprop(⌜err = GoInterface.nil ∧ c ≠ Loc.null⌝ ∗
             boltTx tx γ q (T.setCur (T.cur.setKey kb (some (Ent.bkt (W64 0) [])))) ∗
             bktH tx γ c [kb] (T.gens [kb]))) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
