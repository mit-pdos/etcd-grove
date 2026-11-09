/-
## `(*backend).Close()` (`backend.go:478-484`): translated

**Users.** 2e's `bootstrappedBackend.Close`/`bootstrap`'s error paths (`bootstrap.go:95-181`), the
server's `Cleanup` (2e), 2d's `applySnapshot` (the old backend, after the new one is installed),
`etcdutl`. Snippet `commit.go` (`ReqReopen`).

**Proof sketch.** `close(b.stopc)` (once: the open token is whole); `<-b.donec`: the run loop's
`CommitAndStop` (the batch lock: `Pk`; the hooks; the client's commit step appends the final image
`I`; bbolt's write transaction committed, none begun; the read transaction handed to its rollback
goroutine, none begun) and its exit. `b.mu.Lock()`, bbolt's `DB.Close()` (4c: it waits, through
`mmaplock`, for the read transactions still open, which the readers in flight hold until they
finish: they need no slot back; gives `fileHolds p D`, `imgOf D = I`, whatever its error). The
batch lock's resource comes back: nothing can take the lock after this (every locking path needs an
open share). Every visible-image tracker comes back (`beVis` and the untracked marks cover every
cell): no read transaction can be begun with a footprint after the close (it would read a nil
transaction: `issues/etcd-read-after-backend-close-panic.md`); a lock-only read needs none.

**Changes** (from `specs-ref`'s `backend__Close.lean`): the file's image back (`beFile`, the
history's last, `beFinal`), the lock's resource back; the readers' slots stay with the clients
(the close waits for readers in flight); the visible trackers taken (mvcc's `storageRest`, 3e).

**Margin.** `DB.Close`'s error is returned but its kind not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

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

/-- **`b.Close()`**: the final commit made; the file holds the last image `I` (`beFinal`); the
batch lock's resource back. Takes the open token and every visible-image tracker. -/
def backend.Close.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (F G : Fp) (V : Image),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ 1 ∗ beVis γ F V ∗ beNoVis γ G ∗ ⌜∀ c, F c ∨ G c⌝ }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ I : Image, beFinal γ I ∗ beFile p (some I) ∗ Pk }}

end spec

end Backend
end EtcdGrove
end Perennial
