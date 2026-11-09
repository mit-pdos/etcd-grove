/-
`(*watchStream).Rev()`: the store's current revision.

**Users.** `serverWatchStream.recvLoop` (`v3rpc/watch.go:274, 307, 360, 380`, 2b: the header of a
`Created` or `Canceled` answer). Snippet: `mvccwatch/history.go` `ReqFromCurrent`.

**Proof sketch.** Under `ws.mu`, `watchable.rev()` (`watchableStore.rev.spec`: 3e's `store.Rev`, the
reader token for `revMu`'s reader slot): the committed revision, a prefix of the notified history.

**Changes** from `specs-ref`'s file: a reader token of 3e's `mvccReaders` (one per call, given back); the result's
meaning (`mvccLb`) stated.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import Spec.context.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`w.Rev()`**: a revision the store reached (the committed one). -/
def watchStream.Rev.spec : Prop :=
  ∀ (w : Loc) (γ : MvccName) (ι : WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsAt w γ ι ∗ mvccReaders γ 1 }}
    (App (Val (w @!! go.GoType.PointerType watchStream.ty @!! go!"Rev")) (Val #()))
  {{ (r : w64), RET #r; mvccReaders γ 1 ∗ ∃ h : KVHist, mvccLb γ h ∗ ⌜sint.Z r = h.rev⌝ }}

end spec

end Mvcc
end EtcdGrove
end Perennial
