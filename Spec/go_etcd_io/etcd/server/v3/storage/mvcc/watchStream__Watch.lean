/-
`watchStream.Watch` (watcher.go). Lean-first (no Rocq counterpart); see `InvWatchStream.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`ws.Watch(ctx, id, key, end, startRev, fcs...)`**: the range `key`/`end` (`end` empty: a
single key, or from `key` if `end` is non-nil: the store's business) and the filters are handed
to the store for good. It returns `nil` with the watcher's id (`id` itself unless it is
`AutoWatchID`, `0`) only for a non-empty range (`end` empty or `key < end`); otherwise `-1` with
`ErrEmptyWatcherRange` (an empty range, or the stream closed) or `ErrWatcherDuplicateID` (an
explicit `id` already in use). The start revision is at least `0`; the caller's `P.R` is lent
to the store. -/
abbrev mvcc.watchStream.Watch.spec : Prop :=
  ∀ (ws : Loc) (wa : GoInterface) (P : mvcc.WatchParams GF) (γ : GName) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (id : w64) (key endk fcs : GoSlice) (k e : List w8)
    (fs : List GoFunc) (startRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchStream ws wa P γ ∗ context.isContext ctx cd ∗
      key ↦*□ k ∗ endk ↦*□ e ∗ fcs ↦*□ fs ∗ ([∗list] f ∈ fs, P.F f) ∗ P.R ∗ P.T ∗
      ⌜0 ≤ sint.Z startRev⌝ }}
    (App (App (App (App (App (App (Val (ws @!! go.GoType.PointerType watchStream.ty @!! go!"Watch"))
      (Val #(GoInterface.ok ctx))) (Val #id)) (Val #key)) (Val #endk)) (Val #startRev)) (Val #fcs))
  {{ (id' : w64) (err : GoInterface), RET (PairV #id' #err);
      ((⌜err = GoInterface.nil⌝ ∗ ⌜e = [] ∨ go.GoStringLt k e⌝ ∗ ⌜id ≠ W64 0 → id' = id⌝) ∨
       (⌜id' = W64 (-1)⌝ ∗
        (globalAddr ErrEmptyWatcherRange ↦□ err ∨
         (⌜id ≠ W64 0⌝ ∗ globalAddr ErrWatcherDuplicateID ↦□ err)))) ∗ P.R }}

end spec

end EtcdGrove
end Perennial
