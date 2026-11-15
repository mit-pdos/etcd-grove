/-
## `(*backend).ConcurrentReadTx()` (`backend.go:284-353`): translated

**Users.** mvcc's reads (`kvstore_txn.go:55`, `store.Read` in `ConcurrentReadTxMode`: every
`Range`, `kv_view.go:39`, the hash). Snippet `parts.go` (`ReqWriteThenRead`, `ReqDeleteVisible`).

**Proof sketch.** `readTx.RLock()` (a slot of `readTx.mu`, from `beRdToks γ 1`): while held,
`readTx.mu`'s invariant gives the read buffer and bbolt's read transaction at the visible image;
**the caller's update fires here** (the snapshot is taken under this lock: the buffer is copied and
the read transaction shared; no write-back or commit can run, both need `readTx.Lock`).
`txWg.Add(1)` (the slot's budget token deposited: the interval's rollback goroutine waits for it).
The buffer cache under `txReadBufferCache.mu` (the cache's invariant: a copy of the buffer at the
version it records, read-only once published), `unsafeCopy` (`CopyUsed`, `verify.Assert` off by
`envOk`). **The copy may be stale** (round 1, T1;
`nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md`): a commit empties the read buffer
without bumping its version, so a cached copy of before the commit is reused after it. The copy is
the read buffer at the last write-back, whose entries the commits since have made bbolt's (at the
same values) but for those the last session deleted and the hooks' rewrites; so the reader's view is
`V` on every key `V` has, outside the hooks' cells (`Fh`, excluded by the premise), plus maybe some
entries `V` lacks. The reads' specs say so (`lingerSingle`, `rdOrderL`). The new `concurrentReadTx` shares `txMu`, `tx`, `buckets`, `txWg` (read-only pointers),
its buffer is its own. `beRd γ l F V` holds the slot's wait-group token, a persistent view of the
interval's bbolt read transaction at the committed image and of its buffer, with `V`'s entries
their union (the buffer over bbolt).

**Changes** (from `specs-ref`'s, over `bkView`/`bkRTx`/`crTok`): the caller's atomic observation of
its footprint's visible image (`kbObs`'s shape, mvcc's contract); a reader slot, not a thread token;
round 1: a footprint disjoint from the hooks' (the old `keyReadSnap`'s exclusion).

**Margin.** The snapshot is of the whole image; the reader learns only `F`, up to lingering deletes.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

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

/-- **`b.ConcurrentReadTx()`**: a read transaction over a snapshot of the visible image, taken by the
caller's observation of its footprint `F`. -/
def backend.ConcurrentReadTx.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (F Fh : Fp) (Ψ : Image → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beRdToks γ 1 ∗ beHookFp γ Fh ∗ ⌜Fp.disj F Fh⌝ ∗
      (AU <{ ∃∃ (V : Image), beVis γ F V }> @ ⊤, ∅ <{ beVis γ F V, COMM Ψ V }>) }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"ConcurrentReadTx")) (Val #()))
  {{ (r : GoInterface), RET #r; ∃ (l : Loc) (V : Image), ⌜r = crtIface l ∧ l ≠ rtLoc γ⌝ ∗
      beRd γ l F V ∗ beLive γ l 1 ∗ Ψ V }}

end spec

end Backend
end EtcdGrove
end Perennial
