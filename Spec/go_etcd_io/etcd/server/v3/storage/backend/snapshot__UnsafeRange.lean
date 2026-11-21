/- Reads from the same frozen transaction that the snapshot streams. -/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

abbrev backend.snapshot.UnsafeRange.spec : Prop :=
  ∀ (sp tx : Loc) (γ : GName) (γd : DBNames) (D : Data) (q : Qp) (bk : GoInterface) (bi : BucketInfo)
    (key endKey : GoSlice) (kb eb : GoString) (dk de : DFrac) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      snapAt sp γ tx γd ∗ txLive tx γd q (bbolt.TxView.ro D) ∗ isBucket bk bi ∗
      key ↦*{dk} kb ∗ endKey ↦*{de} eb }}
    (App (App (App (App (Val (sp @!! go.GoType.PointerType snapshot.ty @!! go!"UnsafeRange"))
      (Val #bk)) (Val #key)) (Val #endKey)) (Val #limit))
  {{ (keys vals : GoSlice), RET (PairV #keys #vals); txLive tx γd q (bbolt.TxView.ro D) ∗
      key ↦*{dk} kb ∗ endKey ↦*{de} eb ∗ kvsOutRd γd tx keys vals
        (((D.lookup bi.name).map (fun m => cursorRange (bktEnts m) kb eb limit)).getD []) }}

end spec
end EtcdGrove
end Perennial
