/-
## `(*readTx).RLock()` (`read_tx.go:131`): translated

**Users.** mvcc's shared reads (`kvstore.go:189, 227, 328`, `kvstore_txn.go:57`: the
`SharedBufReadTxMode`), `kv_view.go`'s `Rev()` (a lock-only read: `F` empty), auth's
`lockedReadTx` (`schema/auth.go`), alarms, the consistent index, the schema's validation. Snippet
`parts.go` (`ReqBareRLock`).

**Proof sketch.** `rt.mu.RLock()` (a reader slot: `readTx.mu`'s reader count, bounded by the
backend's `beReaderN`); while held, no write-back or commit (they take `mu.Lock()`): the read
buffer and the read transaction stay at the visible image; **the caller's update fires here**.
With `F` empty, it reads nothing and the read needs no open backend (a mutex; after the close too).

**Changes** (from `specs-ref`'s): the caller's observation, a reader slot. **Margin.** None.
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

/-- **`rt.RLock()`** on the shared read transaction: a read of the visible image, by the caller's
observation of its footprint `F` (empty: a lock-only read). -/
def readTx.RLock.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (F : Fp) (Ψ : Image → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beRdToks γ 1 ∗
      (AU <{ ∃∃ (V : Image), beVis γ F V }> @ ⊤, ∅ <{ beVis γ F V, COMM Ψ V }>) }}
    (App (Val ((rtLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty @!! go!"RLock")) (Val #()))
  {{ RET #(); ∃ V : Image, beRd γ (rtLoc γ) F V ∗ Ψ V }}

end spec

end Backend
end EtcdGrove
end Perennial
