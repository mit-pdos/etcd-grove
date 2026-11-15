/-
`txw.writeback(txr)` (`tx_buffer.go:98-117`): translated; internal. Each bucket deduplicated unless
sequential, moved into or merged with the read buffer's; the write buffer reset; the version
bumped. Changes: over `writebackOk`. Margin: none.
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

/-- **`txw.writeback(txr)`**: `writebackOk`; the write buffer emptied, the version bumped. -/
def txWriteBuffer.writeback.spec : Prop :=
  ∀ (t r : Loc) (W R : TxB) (seq : w64 → Option Bool) (ver : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ twbAt t W seq ∗ trbAt r R ver }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer.ty @!! go!"writeback")) (Val #r))
  {{ RET #(); ∃ (R' W' : TxB) (seq' : w64 → Option Bool), ⌜writebackOk W seq R R' ∧ ∀ id, W' id = none ∨ W' id = some []⌝ ∗
      trbAt r R' (ver + 1) ∗ twbAt t W' seq' }}

end spec

end Backend
end EtcdGrove
end Perennial
