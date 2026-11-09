/-
`unsafeRange(c, key, endKey, limit)` (`batch_tx.go:206-226`): translated; internal. A non-positive
limit unbounded; an empty end the key alone (`limit := 1`); the cursor from `Seek(key)` while below
the end. Over a cursor of a bucket whose entries are `L` (4c's cursor, provisional `curOver`).
Changes: unchanged. Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`unsafeRange(c, k, e, limit)`**: `btRange` of the cursor's bucket. -/
def unsafeRange.spec : Prop :=
  ∀ (c : Loc) (L : GoString → Option GoString) (ks es : GoSlice) (dk de : DFrac) (k e : GoString)
    (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ curOver c L ∗ ks ↦*{dk} k ∗ es ↦*{de} e }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.unsafeRange)) (Val #c)) (Val #ks)) (Val #es)) (Val #limit))
  {{ (kl vl : GoSlice), RET (PairV #kl #vl); ks ↦*{dk} k ∗ es ↦*{de} e ∗
      ∃ l, ⌜btRange L k e (sint.Z limit) l⌝ ∗ rangeRes kl vl l (curOver c L) }}

end spec

end Backend
end EtcdGrove
end Perennial
