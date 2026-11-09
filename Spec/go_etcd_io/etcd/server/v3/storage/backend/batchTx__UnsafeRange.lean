/-
`t.UnsafeRange(bucket, key, endKey, limit)` (`batch_tx.go:193-204`): translated; internal. bbolt's
cursor of the write transaction, `unsafeRange`. Changes: over `btPhys`. Margin: none.
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

/-- **`t.UnsafeRange(bk, k, e, limit)`** on the embedded `batchTx`: `btRange` of bbolt's write
transaction. -/
def batchTx.UnsafeRange.spec : Prop :=
  ∀ (γ : BeNames) (I : Image) (n d : Nat) (bk : GoInterface) (bi : BktInfo) (ks es : GoSlice)
    (dk de : DFrac) (k e : GoString) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ btPhys γ I n d ∗ bucketOk bk bi ∗ ks ↦*{dk} k ∗ es ↦*{de} e }}
    (App (App (App (App (Val ((bt0Loc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTx.ty @!! go!"UnsafeRange")) (Val #bk)) (Val #ks))
      (Val #es)) (Val #limit))
  {{ (kl vl : GoSlice), RET (PairV #kl #vl); ks ↦*{dk} k ∗ es ↦*{de} e ∗
      ∃ l, ⌜btRange (I.ents bi.name) k e (sint.Z limit) l⌝ ∗ rangeRes kl vl l (btPhys γ I n d) }}

end spec

end Backend
end EtcdGrove
end Perennial
