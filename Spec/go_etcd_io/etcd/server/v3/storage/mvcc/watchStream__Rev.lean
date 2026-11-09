/-
`(*watchStream).Rev()`: the store's current revision.

**Users.** `serverWatchStream.recvLoop` (`v3rpc/watch.go:274, 307, 360, 380`, 2b: the header of a
`Created` or `Canceled` answer). Snippet: `mvccwatch/history.go` `ReqFromCurrent`.

**Proof sketch.** Under `ws.mu`, `watchable.rev()` (`watchableStore.rev.spec`: 3e's `store.Rev`, the
reader token for `revMu`'s reader slot, the caller's update fired at the state read): the committed revision.

**Changes** from `specs-ref`'s file: a reader token of 3e's `mvccReaders` (one per call, given
back); (round 1, F2) the result by the caller's read update at the state read, in 3e's `KV.Rev`
form (an `mvccLb` alone did not order it after a `Watch`).

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

/-- **`w.Rev()`**: the store's current (committed) revision, by the caller's read update (3e's
`KV.Rev` form). -/
def watchStream.Rev.spec : Prop :=
  ∀ (w : Loc) (γ : MvccName) (ι : WsNames) (Q : MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsAt w γ ι ∗ mvccReaders γ 1 ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (Val (w @!! go.GoType.PointerType watchStream.ty @!! go!"Rev")) (Val #()))
  {{ (r : w64), RET #r; mvccReaders γ 1 ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 σ.rev⌝ }}

end spec

end Mvcc
end EtcdGrove
end Perennial
