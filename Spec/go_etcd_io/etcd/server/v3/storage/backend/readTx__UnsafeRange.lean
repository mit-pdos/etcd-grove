/-
## `(*readTx).UnsafeRange(bucket, key, endKey, limit)` (promoted `baseReadTx.UnsafeRange`, `read_tx.go:75-121`): translated

**Users.** mvcc's shared reads (`kvstore.go`: the compaction keys, `restore`'s chunks), auth's
reads (`UnsafeGetUser`, ...), alarms, the consistent index (`UnsafeReadConsistentIndex`), the
schema's version. Snippet `ranges.go`.

**Proof sketch.** A `nil` end sets the limit to `1`, a non-positive one to `MaxInt64`; a limit
above `1` on a bucket that is not safe-range panics (`IsSafeRangeBucket()` by `bucketOk`; excluded
by the premise). The read buffer's `Range` (`txReadBuffer.Range.spec`: the buffer's part of the
range, cut at the limit); if it fills the limit, returned; else the bucket's bbolt handle (cached in
`buckets` under `txMu`; a missing bucket: the buffer's part), its cursor, `unsafeRange` with the
rest of the limit: bbolt's part, then the buffer's appended. The read buffer holds the puts since
the last commit (keys above the committed ones in a safe-range bucket: the put rows' premises; a
single key's value shadowing bbolt's in another bucket), bbolt's read transaction the last commit:
together the visible image `V` (`rdRange`).

**Changes** (from `specs-ref`'s): the hidden split stated (`rdRange`: the buffer's part cut first),
in place of a plain cut range (false with a non-empty buffer and a limit). **Margin.** Which entries
are buffered is not stated.
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

/-- **`rt.UnsafeRange(bk, k, e, limit)`** on the shared read transaction: the range of its view
(`rdRange`), within the reader's footprint. -/
def readTx.UnsafeRange.spec : Prop :=
  ∀ (γ : BeNames) (F : Fp) (V : Image) (bk : GoInterface) (bi : BktInfo) (ks es : GoSlice)
    (dk de : DFrac) (k e : GoString) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beRd γ (rtLoc γ) F V ∗ bucketOk bk bi ∗ ks ↦*{dk} k ∗ es ↦*{de} e ∗
      ⌜covers F bi.name k e⌝ ∗ ⌜bi.safe = true ∨ es = slice.nil ∨ sint.Z limit = 1⌝ }}
    (App (App (App (App (Val ((rtLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty @!! go!"UnsafeRange")) (Val #bk)) (Val #ks))
      (Val #es)) (Val #limit))
  {{ (kl vl : GoSlice), RET (PairV #kl #vl); beRd γ (rtLoc γ) F V ∗ ks ↦*{dk} k ∗ es ↦*{de} e ∗
      ∃ l, ⌜rdRange (V.ents bi.name) bi.safe (V.clean bi.name) k e (sint.Z limit) l⌝ ∗
        bytesListAt kl (l.map Prod.fst) ∗ bytesListAt vl (l.map Prod.snd) }}

end spec

end Backend
end EtcdGrove
end Perennial
