/-
`b.Get(key)` (`bucket.go`): seek the key; nil if absent or a nested bucket.

**Users.** The bank (`bbolttest.go:125-131`), etcd's schema reads through the backend's ranges
(which use cursors, not `Get`); `examples/axiomcx/bboltnan`. Snippets: `ReqBank`, `ReqNested`.

**Proof sketch.** `Cursor.seek` from the bucket's root (pages through the mapping, nodes through the
transaction's node cache: either way the entries of `T.cur` at `p`, in key order, by `boltTx`'s
abstraction relation); compare the key; return the value slice (`txBytes`: in the mapping or in a
node, valid while the transaction is live).

**Changes.** Over paths and nested buckets (a bucket's key gives nil); the old `m.lookup kb`.

**Margin.** A value written with a nil slice in this transaction is returned as nil (indistinguishable
from an absent key, as in Go).
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

/-- `b.Get(key)`, any transaction, any fraction: the value at `key` in the bucket at `p` (valid
while the transaction is live), or nil if there is none or it is a nested bucket. -/
def Bucket.Get.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs ∗ key ↦*{dk} kb ∗ ⌜T.gens p = gs⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Get")) (Val #key))
  {{ (v : GoSlice), RET #v; boltTx tx γ q T ∗ key ↦*{dk} kb ∗
      (match T.cur.atPath (p.child kb) with
       | some (Ent.val vb) => txBytes tx γ v vb
       | _ => iprop(⌜v = slice.nil⌝)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
