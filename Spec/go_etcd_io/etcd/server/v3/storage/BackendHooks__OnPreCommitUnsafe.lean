/-
## `(*BackendHooks).OnPreCommitUnsafe(tx)` (`hooks.go:43-52`): translated

**Users.** The backend's commit (4a: `batchTxBuffered.commit` calls its hooks under the batch
lock), through `backend.Hooks`: `OpenBackend`/`OpenSnapshotBackend`'s client allocation step needs
4a's `Backend.hookOk γ (hooksIface h) Fh (Pk γ)` of the server's hooks, which this spec is.

**Proof sketch** (4a's hook contract: `Pk`, the hook session `beSess γ q Fp.none S`, the batch
transaction `btIface γ`):
1. `indexer.UnsafeSave(tx)` (2d's `Cindex.consistentIndex.UnsafeSave.spec`): cindex's
   `txStoredCI_sess` turns the session into `txStoredCI (btIface γ) c` (the session's stored index
   `c`), the update is `hooksPkOk`'s first one (the guard `m.idx = 0 ∨ c ≤ m.idx`: the client's
   invariant keeps the stored index at most the in-memory one while the backend is the same), and
   the wand gives the session back at footprint `Cindex.ciCells` with `hookWrites ciCells`.
2. Under the hooks' lock, if a configuration is pending (`SetConfState`'s, a `proto.Clone`, held by
   the lock invariant with its size bound), 4a/4b's `Backend.confStateSave_hook.spec`: from a
   session with nothing published (the ciCells session's publication is deferred to the joint
   update: see the gap below), the batch transaction's liveness and the cell's batch part
   `beCur γ confStateCells C` (from `hooksPkOk`'s commit), the session at `confStateCells` with
   `hookWrites`, the part at the saved bytes; the pending configuration cleared.
3. The two writes' footprints joined (`hookFp := ciCells ∪ confStateCells`, `hookWrites hookFp`
   since each writes only its cells over the same base) and the continuation called with the
   visibility update `hooksPkOk` gives for the final session, and `Ψ -∗ Pk`.

**Changes** (from `specs-ref`'s `BackendHooks__OnPreCommitUnsafe.lean`): over provisional
predicates. Last pass (A8 provability F5, server-boot's open item): stated as 4a's hook contract
(`Backend.hookOk`), over cindex's `txStoredCI_sess`/`ciCells` and backend-schema's
`confStateCells`/`confStateSave_hook`; the provisional `beTx` is gone from it.

**Gaps (recorded, not hidden):**
* `confStateSave_hook` takes `beLive γ (btLoc γ) 1` and a session with nothing published, while
  4a's `hookOk` lends the hook only `beSess γ q Fp.none S`, and step 1 returns a session at
  `ciCells`: composing the two saves needs either `hookOk` to lend the transaction's liveness, or
  `confStateSave_hook` to take a session at any footprint (backend-schema's, requested).
* The pending configuration's size bound (`confStateKey.length + 128 + 21 * encSize c ≤
  bboltEntryMax`) has no source: `SetConfState.spec` should take it (a configuration of at most
  ~`bboltEntryMax / 21` bytes' encoding; open).
* server-core is checking whether `txStoredCI_sess` needs `beCur γ ciCells` as
  `confStateSave_hook` needs its cell's: if so, `hooksPkOk` gives it as it gives `confStateCells`'.

**Margin.** None beyond the gaps.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.SchemaTx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ServerStorage

open Iris Iris.BI

/-- **The server's hooks' footprint**: the consistent index's cells and the configuration's. -/
def hookFp : Backend.Fp := Backend.Fp.union Cindex.ciCells Backend.confStateCells

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **What the hooks need of the commit's resource `Pk`** (transparent, persistent; the client's
obligation, proved by the server's backend invariant): from `Pk` and the session's image `S`, the
consistent index's read update (`UnsafeSave`'s, with its guard against the session's stored index),
then the configuration cell's batch part, and for the final session `S'` the visibility update of
the hooks' footprint and the way back to `Pk`. -/
def hooksPkOk (γ : Backend.BeNames) (γci : Cindex.CINames) (Pk : IProp GF) : IProp GF :=
  iprop(□ ∀ S : Backend.Sess, Pk -∗
    AU <{ ∃∃ (m : Cindex.CIState), Cindex.ciState γci m ∗
          ⌜m.idx = W64 0 ∨
            uint.nat (Schema.ciOf (S.cur.ents Cindex.metaBktName)).1 ≤ uint.nat m.idx⌝ }> @ ⊤, ∅
      <{ Cindex.ciState γci m, COMM
         ∃ C : Backend.Image, Backend.beCur γ Backend.confStateCells C ∗
           ∀ (C' : Backend.Image) (S' : Backend.Sess), Backend.beCur γ Backend.confStateCells C' -∗
             ∃ Ψ : IProp GF,
               (AU <{ ∃∃ (V : Backend.Image), Backend.beVis γ hookFp V }> @ ⊤, ∅
                 <{ Backend.beVis γ hookFp S'.fin, COMM Ψ }>) ∗ (Ψ -∗ Pk) }>)

/-- **The server's pre-commit hooks meet 4a's hook contract** (`Backend.hookOk`: a WP of
`OnPreCommitUnsafe(btIface γ)` from `Pk` and the hook session, writing only `hookFp`), for hooks
over a consistent indexer `l` and a commit resource meeting `hooksPkOk`. -/
def BackendHooks.OnPreCommitUnsafe.spec : Prop :=
  ∀ (h l : Loc) (γci : Cindex.CINames) (γ : Backend.BeNames) (Pk : IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
    isHooks h (Cindex.ciIface l) ∗ Cindex.isCI l γci ∗ Backend.bktsAre γ ∗
    Backend.beMade γ (Schema.Bkt.name .metaB) ∗ hooksPkOk γ γci Pk ⊢
    Backend.hookOk γ (hooksIface h) hookFp Pk

end spec

end ServerStorage
end EtcdGrove
end Perennial
