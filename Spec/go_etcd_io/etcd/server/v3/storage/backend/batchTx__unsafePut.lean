/-
`t.unsafePut(bucket, k, v, seq)` (`batch_tx.go:174-191`): translated; internal. bbolt's
`Bucket`/`Put` on the write transaction (4c; a missing bucket or an error: `lg.Fatal`), the fill
percent when `seq`, `pending++`. Changes: over `btPhys`. Margin: none.
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

/-- **`t.unsafePut(bk, k, v, seq)`**: bbolt's write transaction at `put`. -/
def batchTx.unsafePut.spec : Prop :=
  ∀ (γ : BeNames) (I : Image) (n d : Nat) (bk : GoInterface) (bi : BktInfo) (ks vs : GoSlice)
    (k v : GoString) (seq : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ btPhys γ I n d ∗ bucketOk bk bi ∗ ⌜k.length + v.length ≤ Bbolt.bboltEntryMax⌝ ∗
      ks ↦*□ k ∗ vs ↦*□ v }}
    (App (App (App (App (Val ((bt0Loc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTx.ty @!! go!"unsafePut")) (Val #bk)) (Val #ks))
      (Val #vs)) (Val #seq))
  {{ RET #(); btPhys γ (I.put bi.name k v) (n + 1) d }}

end spec

end Backend
end EtcdGrove
end Perennial
