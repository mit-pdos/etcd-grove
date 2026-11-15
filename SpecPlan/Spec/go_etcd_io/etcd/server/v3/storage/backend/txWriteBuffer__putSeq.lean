/-
`txw.putSeq(bucket, k, v)` (`tx_buffer.go:56-75`): translated; internal. `verify.Verify` (off:
`envOk`), the entry appended. Changes: `envOk`. Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

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

/-- **`txw.putSeq(bk, k, v)`**: appended, the bucket's flag kept. -/
def txWriteBuffer.putSeq.spec : Prop :=
  ∀ (t : Loc) (B : TxB) (seq : w64 → Option Bool) (bk : GoInterface) (bi : BktInfo)
    (ks vs : GoSlice) (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ envOk ∗ twbAt t B seq ∗ bucketOk bk bi ∗ ks ↦*□ k ∗ vs ↦*□ v }}
    (App (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer.ty @!! go!"putSeq")) (Val #bk)) (Val #ks)) (Val #vs))
  {{ RET #(); twbAt t (fun id => if id = bi.id then some ((B id).getD [] ++ [(k, v)]) else B id)
      seq }}

end spec

end Backend
end EtcdGrove
end Perennial
