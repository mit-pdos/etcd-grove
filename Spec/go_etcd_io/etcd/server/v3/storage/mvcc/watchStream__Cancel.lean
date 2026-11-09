/-
`(*watchStream).Cancel(id)`: cancels the watcher `id`.

**Users.** `serverWatchStream.recvLoop` (`v3rpc/watch.go:377`, 2b: a cancel request; `nil` answers
it). Snippet: `mvccwatch/lifecycle.go` `ReqCancel`.

**Proof sketch.** Under `ws.mu`: the cancel closure and the watcher, `ok` only for a registered id of
an open stream; the closure (`cancelWatcher`, its spec: the watcher removed from the store's
groups or its victim batch under `s.mu`, `ch` cleared: no response of it is sent after, so every
one is among the sends so far, `wsCanceled`; `span.End()`, otel); under `ws.mu` again the maps'
entries deleted (if not replaced). No reader token (`s.mu` taken as a writer).

**Changes** from `specs-ref`'s file: the atomic update over the stream's state replaced by the
persistent `wsCanceled` (with the registration it cancels); (round 1, F6) the error is the
package's `ErrWatcherNotExist` (its message by `watch_init.spec`).

**Margin.** An error is not stated to mean the id was not live (it does: a live watcher of an open
stream is always cancelled).
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

/-- **`w.Cancel(id)`**: `nil` for a registered watcher, now cancelled (no response of it after the
first `c` sent); else `ErrWatcherNotExist`. -/
def watchStream.Cancel.spec : Prop :=
  ∀ (w : Loc) (γ : MvccName) (ι : WsNames) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsAt w γ ι }}
    (App (Val (w @!! go.GoType.PointerType watchStream.ty @!! go!"Cancel")) (Val #id))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (W : WatcherM) (c : Nat), wsReg ι id W ∗ wsCanceled ι id c) ∨
      globalAddr ErrWatcherNotExist ↦□ err }}

end spec

end Mvcc
end EtcdGrove
end Perennial
