/-
# mvcc's store: the names batch 3f assumes of batch 3e (provisional)

**Provisional.** The watch batch (3f) states its specs over mvcc's store vocabulary, which is batch
3e's (`Api.lean`, not yet written when 3f was drafted; its pure model, `Model.lean`, is). This module
declares the few names 3f's statements mention, with the meaning 3f assumes, so that 3f's files
build; `notes/specs-only/req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, "from 3f", asks 3e for
them under these names. At integration this module is deleted and 3f's files import 3e's
`Api.lean` instead (a rename where 3e chose other names). Nothing here is 3f's design.

* `StoreNames` (opaque type): a store's ghost names.
* `mvccState γ σ` (exclusive, client-owned, timeless): **the store's state is `σ`** (3e's
  `MvccState`: the committed history and the pending revision). The client (the server, 2d) keeps it
  in its invariant and fires the stores' atomic updates over it.
* `mvccLb γ h` (persistent): **the store has notified at least the history `h`**: `h.revs` is a
  prefix of the notified history's (`σ.notified`: the committed revisions and the pending one) and
  `h.compacted` at most the store's compaction revision. What 3f's watch facts are stated against
  (a response's events are events of `h`), as the client's facts are against W0's `etcdLb`.
  Laws 3f needs (3e's): `mvccLb_le` (with `mvccState γ σ`: `h.revs <+: σ.notified.revs ∧
  h.compacted ≤ σ.kv.compacted`), `mvccLb_state` (`mvccState γ σ ⊢ |==> mvccState γ σ ∗
  mvccLb γ σ.notified`).
* `isMvcc kv γ` (persistent): `kv` (a `KV` interface value) is a handle of the store `γ`.
* `mvccTxn t γ k` (exclusive): `t` (a `TxnRead`/`TxnWrite` interface value) is a transaction of the
  store `γ` at the view `k` (3e's `MTxn`).
* `mvccOpen γ` (exclusive): the right to close the store; `mvccClosed γ` (exclusive): what `Close`
  gives back (3e: the storage's reader resources the store and its goroutines held, which the
  storage's closer needs; for a watchable store, its two loops' too: `oneshot-close.md`).
* `storeBoot lg b le cfg h` (exclusive): **what `NewStore(lg, b, le, cfg)` needs** (3e's
  constructor: the logger, the storage `b` holding the history `h`, the lessor `le`, the
  configuration); `storeBooted kv γ le` (exclusive): what it gives besides the handle, the state and
  the open token (3e's: the store's reader resources, the lessor's registration of the store's
  deleter when `le` is not `nil`).
* `histLe h h'` (pure): `h'` extends `h` (`mvccLb`'s meaning). `traceOk tr`: 4b's `traceAt`.
* `storageRestore γ b h` / `storageRestored γ` (exclusive): what `store.Restore(b)` takes of the new
  storage `b` holding `h`, and gives back of the old one (3e's).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Model
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.storage.mvcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire

/-- (provisional, 3e's) A store's ghost names. -/
opaque StoreNames : Type := Unit

/-- (provisional, 3e's) **`h'` extends `h`**: its revisions continue `h`'s, its compaction revision
is not below: what `mvccLb γ h` says of the store's notified history. -/
def histLe (h h' : KVHist) : Prop := h.revs <+: h'.revs ∧ h.compacted ≤ h'.compacted

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- (provisional, 3e's) **The store's state is `σ`** (exclusive, client-owned). -/
opaque mvccState (γ : StoreNames) (σ : MvccState) : IProp GF := iprop(True)

/-- (provisional, 3e's) **The store has notified at least the history `h`** (persistent). -/
opaque mvccLb (γ : StoreNames) (h : KVHist) : IProp GF := iprop(True)

/-- (provisional, 3e's) **`kv` is a handle of the store `γ`** (persistent). -/
opaque isMvcc (kv : GoInterface) (γ : StoreNames) : IProp GF := iprop(True)

/-- (provisional, 3e's) **`t` is a transaction of `γ` at the view `k`** (exclusive). -/
opaque mvccTxn (t : GoInterface) (γ : StoreNames) (k : MTxn) : IProp GF := iprop(True)

/-- (provisional, 3e's) The right to close the store (exclusive). -/
opaque mvccOpen (γ : StoreNames) : IProp GF := iprop(True)

/-- (provisional, 3e's) What closing the store gives back (exclusive). -/
opaque mvccClosed (γ : StoreNames) : IProp GF := iprop(True)

/-- (provisional, 3e's) What `NewStore(lg, b, le, cfg)` needs: its storage `b` at the history `h`. -/
opaque storeBoot (lg : Loc) (b le : GoInterface) (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
  (h : KVHist) : IProp GF := iprop(True)

/-- (provisional, 3e's) What `NewStore` gives besides the handle, the state and the open token. -/
opaque storeBooted (kv : GoInterface) (γ : StoreNames) (le : GoInterface) : IProp GF := iprop(True)

/-- (provisional, 3e's) What `store.Restore(b)` takes of the new storage `b`, holding `h`. -/
opaque storageRestore (γ : StoreNames) (b : GoInterface) (h : KVHist) : IProp GF := iprop(True)

/-- (provisional, 3e's) What `store.Restore` gives back of the old storage. -/
opaque storageRestored (γ : StoreNames) : IProp GF := iprop(True)

/-- (provisional, 4b's `traceAt`) `tr` is a trace (`*traceutil.Trace`, possibly `nil`): its methods
are safe to call. -/
opaque traceOk (tr : Loc) : IProp GF := iprop(True)

/-- (provisional, 3e's) The namespace of the store's invariants. -/
def mvccN : Namespace := nroot .@ "mvcc"

end res

end Mvcc
end EtcdGrove
end Perennial
