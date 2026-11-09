/-
## `(*concurrentReadTx).UnsafeRange(bucket, key, endKey, limit)` (promoted `baseReadTx.UnsafeRange`): translated

**Users.** mvcc's reads (`rangeKeys`, `kvstore_txn.go:119`; `hashByRev`). Snippet `ranges.go`.
**Proof sketch.** As `readTx.UnsafeRange.spec`, over the transaction's own buffer copy and the
shared bbolt read transaction (kept alive by the wait-group token in `beRd`; `txMu` guards the
shared bucket cache). **Changes.** As `readTx.UnsafeRange`. **Margin.** As there.
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

/-- **`rt.UnsafeRange(bk, k, e, limit)`** on a concurrent read transaction: as on the shared one. -/
def concurrentReadTx.UnsafeRange.spec : Prop :=
  ∀ (γ : BeNames) (l : Loc) (F : Fp) (V : Image) (bk : GoInterface) (bi : BktInfo)
    (ks es : GoSlice) (dk de : DFrac) (k e : GoString) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beRd γ l F V ∗ bucketOk bk bi ∗ ks ↦*{dk} k ∗ es ↦*{de} e ∗
      ⌜covers F bi.name k e⌝ ∗ ⌜bi.safe = true ∨ es = slice.nil ∨ sint.Z limit = 1⌝ }}
    (App (App (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx.ty @!! go!"UnsafeRange")) (Val #bk)) (Val #ks))
      (Val #es)) (Val #limit))
  {{ (kl vl : GoSlice), RET (PairV #kl #vl); beRd γ l F V ∗ ks ↦*{dk} k ∗ es ↦*{de} e ∗
      ∃ r, ⌜rdRange (V.ents bi.name) bi.safe (V.clean bi.name) k e (sint.Z limit) r⌝ ∗
        bytesListAt kl (r.map Prod.fst) ∗ bytesListAt vl (r.map Prod.snd) }}

end spec

end Backend
end EtcdGrove
end Perennial
