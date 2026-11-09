/-
`txr.ForEach(bucket, visitor)` (`tx_buffer.go:133-138`): translated; internal. Changes: unchanged.
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
    (P : List (GoString × GoString) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ trbAt t R ver ∗ bucketOk bk bi ∗ visitOk vis P ∗ P [] }}
    (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer.ty @!! go!"ForEach")) (Val #bk)) (Val #vis))
  {{ (err : GoInterface), RET #err; trbAt t R ver ∗
      ((⌜err = interface.nil⌝ ∗ P ((R bi.id).getD [])) ∨
       (⌜err ≠ interface.nil⌝ ∗ ∃ j, P (((R bi.id).getD []).take j))) }}

end spec

end Backend
end EtcdGrove
end Perennial
