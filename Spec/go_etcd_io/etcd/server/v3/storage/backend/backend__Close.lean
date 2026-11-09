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
transaction: `issues/etcd-read-after-backend-close-panic.md`); a lock-only read needs none. The
final commit runs the hooks, whose update needs the trackers of the cells they publish: the hooks'
cells are untracked first (`beVis_drop`; the trackers taken are disjoint from `Fh`), so every taken
tracker's cells are the final image's (`Image.agree F I V`: no session is open, the last `Unlock`
published them, and the hooks change only `Fh`). The run loop's thread token comes back.

**Changes** (from `specs-ref`'s `backend__Close.lean`): the file's image back (`beFile`, the
history's last, `beFinal`), the lock's resource back; round 1 (T5g, S7): the final image agrees with
the trackers taken, the hooks' cells untracked first; the readers' slots stay with the clients
(the close waits for readers in flight); the visible trackers taken (mvcc's `storageRest`, 3e).

**Changes** (repair3-boot, the crash pass's request 2 to backend-schema): **`beCrash` did not hold
after `Close` returned.** The post gave the file's OsFs resources (`beFile p (some I)`: 4c's
`fileHolds`, from `boltRelease`) while the client still held `beDurInv γ p ∗ beSynced γ ∗ beHist γ L`,
whose crash law needs those resources (4c's `boltCrash` over `boltFile`, cancelled by the release).
Now the file comes back through the client's update `beCloseUpd γ p Q` (the history out of its crash
state, the closed file in): after `DB.Close` (`boltClosed γ`), the release takes `boltState γ 1` (the
backend's shares and the history authority's, the latter freed by the update's `beHist γ L`, which
`beHist_final` ties to `I`), `boltRelease` gives the file's OsFs resources, whose bytes are clean and
durable (the final commit fsynced: `UnsafeNoFsync` off, `beSynced`; `dur = some []`, no commit in
flight), so `fileHolds_image` makes them `beFile p (some I)` for the update's commit. No `beCrash`
after it (no history), `beFile_crash` instead. A client with no invariant builds the update from
the `beHist` it owns (`Q I` then holds the file). **Not fixed (recorded):** `fileHolds_image` needs
the file's name durable; a file created in this generation (`beFile p none` at `New`: 4c's
`boltFresh_alloc`, `BoltSt.named = false`; etcd's first boot's `member/snap/db`, created by
`bolt.Open` with no directory fsync) is not `beFile p (some I)` after its close until a sync of its
directory, which no law here records (the restart in the same generation after a first boot needs
it; also the old post's).

**Margin.** `DB.Close`'s error is returned but its kind not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
public import Perennial.ProgramLogic.Bounds

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

/-- **`b.Close()`**: the final commit made; the file holds the last image `I` (`beFinal`), handed
to the client's crash state by `beCloseUpd` in exchange for the history (`Q I`); the batch lock's
resource back. Takes the open token and every visible-image tracker. -/
def backend.Close.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (F G Fh : Fp) (V : Image)
    (Q : Image → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ 1 ∗ beVis γ F V ∗ beNoVis γ G ∗ ⌜∀ c, F c ∨ G c⌝ ∗
      beHookFp γ Fh ∗ ⌜Fp.disj F Fh⌝ ∗ beCloseUpd γ p Q }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ I : Image, beFinal γ I ∗ Q I ∗ Pk ∗ threadTok ∗
      ⌜Image.agree F I V⌝ }}

end spec

end Backend
end EtcdGrove
end Perennial
