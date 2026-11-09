/-
## `(*backend).Defrag()` (`backend.go:490-502` and the defragmentation, `:504-1000`): trusted (names only)

**Users.** The maintenance server's `Defragment` (`server.go:976`, under the apply lock), bootstrap
(`bootstrap.go:323`, `--experimental-bootstrap-defrag-threshold-megabytes`).

**Why it is true.** Blocking: the batch lock (`Pk`), `mu`, `readTx.Lock`; a commit
(`unsafeCommit(true)`: the hooks, the client's commit step); the live database copied into a
temporary one (`defragdb`); on success the old closed (bbolt waits for open read transactions), the
copy synced, closed, renamed over the file (atomic), reopened, the transactions begun again: every
image is unchanged (the file holds the same entries, the last commit's), a crash leaves the old or
the new file, both the last commit's image. Non-blocking: `safeRangeDeleteMu.Lock()` (waits for the
safe-range deleters: deletes from a safe-range bucket hold its read lock, `beDelHeld`), a commit, a
bulk copy from a read transaction, then the same stop-the-world catch-up (safe-range buckets
appended above the last copied key: their puts are above every key, the put rows' premise; others
copied whole; the registry `safeRangeBucketNames` holds only safe-range buckets: the schema's
initialization registers exactly those, `schema/bucket.go:64`, 4b's init law) and swap. Errors before the swap restore the transactions and are returned; failures
after it are `lg.Fatal` (never returns); a panic inside is turned into `lg.Fatal`.

**Changes.** New (no old spec): the defragmentation is in scope.

**Margin.** The file's layout (its size) changes; the specs do not state sizes.
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

/-- **`b.Defrag()`**: some error; every image (batch, visible, committed) unchanged. -/
def backend.Defrag.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ q }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"Defrag")) (Val #()))
  {{ (err : GoInterface), RET #err; beOpen γ q }}

end spec

end Backend
end EtcdGrove
end Perennial
