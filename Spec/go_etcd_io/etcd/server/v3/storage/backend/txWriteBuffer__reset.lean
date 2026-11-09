/-
`txw.reset()` (`tx_buffer.go:86-96`): translated; internal. `txBuffer.reset`, then each remaining
bucket's flag back to sequential. Changes: unchanged. Margin: the flags of removed buckets.
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

/-- **`txw.reset()`**: every bucket's entries gone. -/
def txWriteBuffer.reset.spec : Prop :=
  ∀ (t : Loc) (B : TxB) (seq : w64 → Option Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ twbAt t B seq }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer.ty @!! go!"reset")) (Val #()))
  {{ RET #(); ∃ (B' : TxB) (seq' : w64 → Option Bool), twbAt t B' seq' ∗ ⌜∀ id, B' id = none ∨ B' id = some []⌝ }}

end spec

end Backend
end EtcdGrove
end Perennial
