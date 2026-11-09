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
`envOk`). The new `concurrentReadTx` shares `txMu`, `tx`, `buckets`, `txWg` (read-only pointers),
its buffer is its own. `beRd γ l F V` holds the slot's wait-group token, a persistent view of the
interval's bbolt read transaction at the committed image and of its buffer, with `V`'s entries
their union (the buffer over bbolt).

**Changes** (from `specs-ref`'s, over `bkView`/`bkRTx`/`crTok`): the caller's atomic observation of
its footprint's visible image (`kbObs`'s shape, mvcc's contract); a reader slot, not a thread token.

**Margin.** The snapshot is of the whole image; the reader learns only `F`.
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

/-- **`b.ConcurrentReadTx()`**: a read transaction over a snapshot of the visible image, taken by the
caller's observation of its footprint `F`. -/
def backend.ConcurrentReadTx.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (F : Fp) (Ψ : Image → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beRdToks γ 1 ∗
      (AU <{ ∃∃ (V : Image), beVis γ F V }> @ ⊤, ∅ <{ beVis γ F V, COMM Ψ V }>) }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"ConcurrentReadTx")) (Val #()))
  {{ (r : GoInterface), RET #r; ∃ (l : Loc) (V : Image), ⌜r = crtIface l ∧ l ≠ rtLoc γ⌝ ∗
      beRd γ l F V ∗ Ψ V }}

end spec

end Backend
end EtcdGrove
end Perennial
