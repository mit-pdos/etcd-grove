/-
`t.UnsafeDeleteBucket(bucket)` (`batch_tx.go:153-161`): translated; internal. bbolt's
`DeleteBucket` (`ErrBucketNotFound` ignored), `pending++`. Changes: over `btPhys`. Margin: none.
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

/-- **`t.UnsafeDeleteBucket(bk)`** on the embedded `batchTx`: the bucket dropped. -/
def batchTx.UnsafeDeleteBucket.spec : Prop :=
  ∀ (γ : BeNames) (I : Image) (n d : Nat) (bk : GoInterface) (bi : BktInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ btPhys γ I n d ∗ bucketOk bk bi }}
    (App (Val ((bt0Loc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTx.ty @!! go!"UnsafeDeleteBucket")) (Val #bk))
  {{ RET #(); btPhys γ (I.dropBkt bi.name) (n + 1) d }}

end spec

end Backend
end EtcdGrove
end Perennial
