/-
`txr.Range(bucket, key, endKey, limit)` (`tx_buffer.go:126-131`): translated; internal. The
bucket's buffer's `Range` (sorted: the write-back keeps it so under the put rows' premises), or none.
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

/-- **`txr.Range(bk, k, e, limit)`**: the bucket buffer's range, or nothing. -/
def txReadBuffer.Range.spec : Prop :=
  ∀ (t : Loc) (R : TxB) (ver : w64) (bk : GoInterface) (bi : BktInfo) (ks es : GoSlice)
    (dk de : DFrac) (k e : GoString) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ trbAt t R ver ∗ bucketOk bk bi ∗ ks ↦*{dk} k ∗ es ↦*{de} e ∗ ⌜0 < sint.Z limit⌝ ∗
      ⌜∀ l, R bi.id = some l → l.Pairwise (fun a b => go.GoStringLt a.1 b.1)⌝ }}
    (App (App (App (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer.ty @!! go!"Range")) (Val #bk)) (Val #ks)) (Val #es))
      (Val #limit))
  {{ (kl vl : GoSlice), RET (PairV #kl #vl); trbAt t R ver ∗ ks ↦*{dk} k ∗ es ↦*{de} e ∗
      ∃ r, ⌜bbRangeOk ((R bi.id).getD []) k e (sint.Z limit) r⌝ ∗
        bytesListAt kl (r.map Prod.fst) ∗ bytesListAt vl (r.map Prod.snd) }}

end spec

end Backend
end EtcdGrove
end Perennial
