/-
`unsafeRange` (the backend, `batch_tx.go`). `unsafeRange(c, key, endKey, limit)` over a bbolt cursor of the transaction `tx` (read or write: a fraction of `txLive`) over the entries `es`: `cursorRange`, the slices valid while `tx` is open.
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `unsafeRange(c, key, endKey, limit)` over a bbolt cursor of the transaction `tx` (read or write: a fraction of `txLive`) over the entries `es`: `cursorRange`, the slices valid while `tx` is open. -/
abbrev backend.unsafeRange.spec : Prop :=
  ∀ (tx c : Loc) (es : List Ent) (pos : Option Nat) (q : Qp) (key endKey : GoSlice)
    (kb eb : GoString) (dk de : DFrac) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      ownCur tx c es pos ∗ txLive tx q ∗ key ↦*{dk} kb ∗ endKey ↦*{de} eb }}
    (App (App (App (App (Val (@! unsafeRange)) (Val #c)) (Val #key)) (Val #endKey)) (Val #limit))
  {{ (keys vals : GoSlice), RET (PairV #keys #vals); (∃ pos', ownCur tx c es pos') ∗
      txLive tx q ∗ key ↦*{dk} kb ∗ endKey ↦*{de} eb ∗
      kvsOutRd tx keys vals (cursorRange es kb eb limit) }}

end spec

end EtcdGrove
end Perennial
