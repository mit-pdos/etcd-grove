/-
`txw.put(bucket, k, v)` (`tx_buffer.go:51-54`): translated; internal. The bucket marked
non-sequential, the entry appended (`putInternal`). Changes: unchanged. Margin: none.
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

/-- **`txw.put(bk, k, v)`**: appended, the bucket non-sequential. -/
def txWriteBuffer.put.spec : Prop :=
  ∀ (t : Loc) (B : TxB) (seq : w64 → Option Bool) (bk : GoInterface) (bi : BktInfo)
    (ks vs : GoSlice) (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ twbAt t B seq ∗ bucketOk bk bi ∗ ks ↦*□ k ∗ vs ↦*□ v }}
    (App (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer.ty @!! go!"put")) (Val #bk)) (Val #ks)) (Val #vs))
  {{ RET #(); twbAt t (fun id => if id = bi.id then some ((B id).getD [] ++ [(k, v)]) else B id)
      (fun id => if id = bi.id then some false else seq id) }}

end spec

end Backend
end EtcdGrove
end Perennial
