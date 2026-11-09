/-
`c.seek(key)` (`cursor.go`): `search`, then `keyValue` (nil at a leaf's end: the public `Seek` then
calls `next`).
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Changes** (integration I7): the post was `boltCur` at `seekIdx`, but this fork's `seek` does not
step past a leaf's end (`Cursor.Seek` does), where `keyValue`'s spec (at a positioned `boltCur`)
would have to return the next leaf's entry: the cursor is now left as `curPath` (the search path,
possibly past its leaf's end), and what is returned is stated (`seekRaw`: the key's entry when the
bucket has it, a nested bucket's stored value as `bktVal`), which `Bucket.Bucket`, `Get`,
`CreateBucket*`, `DeleteBucket`, `Put`, `Delete` test (`bytes.Equal`, the flags).
-/
module

public import Spec.go_etcd_io.bbolt.Internal

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

/-- (internal) the search path of `key` (`curPath`, possibly past its leaf's end), returning
`key`'s entry if the bucket has it (`seekRaw`). -/
def Cursor.seek.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (pos : Option Nat) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c p gs T pos ∗ key ↦*{dk} kb ∗ ⌜T.gens p = gs⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"seek")) (Val #key))
  {{ (k v : GoSlice) (fl : w32), RET (PairV #k (PairV #v #fl)); boltTx tx γ q T ∗ key ↦*{dk} kb ∗
      curPath tx γ c p gs T kb ∗ seekRaw tx γ p (T.ents p) kb k v fl }}

end spec

end Bbolt
end EtcdGrove
end Perennial
