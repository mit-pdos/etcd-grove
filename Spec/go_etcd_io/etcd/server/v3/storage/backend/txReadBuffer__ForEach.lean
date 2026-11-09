/-
`txr.ForEach(bucket, visitor)` (`tx_buffer.go:133-138`): translated; internal. Changes: unchanged; integration Y: the visitor's own error returned (`visitOk vis P E`), the bytes kept by the visitor and lent against a share of the transaction's liveness (`lentAll … -∗ beLive`), as `rangeRes` (I6's finding: 4b's `Schema.txRd` row needs both).
Margin: none.
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

/-- **`txr.ForEach(bk, vis)`**: the visitor over the bucket buffer's entries. -/
def txReadBuffer.ForEach.spec : Prop :=
  ∀ (t : Loc) (R : TxB) (ver : w64) (bk : GoInterface) (bi : BktInfo) (vis : GoFunc)
    (P : List Lent → IProp GF) (E : List Lent → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ trbAt t R ver ∗ bucketOk bk bi ∗ visitOk vis P E ∗ P [] }}
    (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer.ty @!! go!"ForEach")) (Val #bk)) (Val #vis))
  {{ (err : GoInterface), RET #err; trbAt t R ver ∗ ∃ lt : List Lent,
      ⌜(lt.map Lent.ent) <+: (R bi.id).getD [] ∧ ∀ x ∈ lt, x.dq = DFrac.discard⌝ ∗
      ((⌜err = interface.nil ∧ lt.map Lent.ent = (R bi.id).getD []⌝ ∗ P lt) ∨
       (⌜err ≠ interface.nil⌝ ∗ E lt err)) }}

end spec

end Backend
end EtcdGrove
end Perennial
