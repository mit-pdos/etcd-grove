/-
`snapshot.Range` (`cache/*.go`), an internal helper.
Users: `store.Get`.
Proof sketch: a single key (`BTree.Get.spec`), a from-key scan (`BTree.AscendGreaterOrEqual.spec`) or a range (`BTree.AscendRange.spec`) over the frozen tree, appending each item's key-value (`probeItemFromKey.spec`, `isPrefixScan.spec`).
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `p.Range(start, end)`: the key-value pointers of the snapshot's items in the range `{start, end}`, in key order, in a fresh slice. -/
def snapshot.Range.spec : Prop :=
  ∀ (p : Loc) (r : Nat) (items : List (GoString × Loc)) (startSl endSl : GoSlice) (sk ek : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ snapAt p r items ∗ startSl ↦*□ sk ∗ endSl ↦*□ ek }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.snapshot.ty @!! go!"Range")) (Val #startSl)) (Val #endSl))
  {{ (out : GoSlice), RET #out;
      out ↦* ((items.filter (fun e => decide (KeyRange.mem ({ key := sk, rangeEnd := ek } : KeyRange) e.1))).map Prod.snd) }}

end spec

end Cache
end EtcdGrove
end Perennial
