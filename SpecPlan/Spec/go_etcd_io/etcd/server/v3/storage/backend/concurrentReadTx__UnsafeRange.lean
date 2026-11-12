/-
## `(*concurrentReadTx).UnsafeRange(bucket, key, endKey, limit)` (promoted `baseReadTx.UnsafeRange`): translated

**Users.** mvcc's reads (`rangeKeys`, `kvstore_txn.go:126`: one revision at a time, a `nil` end).
Snippet `ranges.go` (`ReqSeqRange`'s concurrent read).

**Proof sketch.** As `readTx.UnsafeRange.spec`, over the transaction's buffer copy and the shared
bbolt read transaction (kept alive by the wait-group token in `beRd`; `txMu` guards the shared
bucket cache). But the copy may be stale: `ConcurrentReadTx` reuses `txReadBufferCache.buf` when its
version matches the read buffer's, and a commit empties the read buffer without bumping the version
(`nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md`): after a commit with no write-back
since, the copy is the buffer of before the commit, laid over the bbolt transaction of after it. So
for a key of `V`, the buffer's value (equal to the committed one, or absent) or bbolt's: `V`'s; for
a key `V` lacks, maybe a value the last session deleted (the copy kept it). A hook cell would read
an older value (excluded: `ConcurrentReadTx` takes a footprint disjoint from the hooks'); a range
with an end may return a key twice (bbolt's and the copy's), so only single-key reads are stated.

**Changes** (round 1, T1): single-key reads, `lingerSingle` (was `rdRange`, false after a commit);
the bytes lent (T3). **Margin.** A range with an end is not specified (etcd's concurrent reads make
none).
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

/-- **`rt.UnsafeRange(bk, k, nil, limit)`** on a concurrent read transaction: the key's value in
its view, or, for a key the view lacks, nothing or a value it had before a delete
(`lingerSingle`). -/
def concurrentReadTx.UnsafeRange.spec : Prop :=
  ∀ (γ : BeNames) (l : Loc) (F : Fp) (V : Image) (bk : GoInterface) (bi : BktInfo)
    (ks : GoSlice) (dk : DFrac) (k : GoString) (limit : w64) (pl : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beRd γ l F V ∗ beLive γ l pl ∗ bkt γ bk bi ∗ ks ↦*{dk} k ∗ ⌜F (.key bi.name k)⌝ }}
    (App (App (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx.ty @!! go!"UnsafeRange")) (Val #bk)) (Val #ks))
      (Val #slice.nil)) (Val #limit))
  {{ (kl vl : GoSlice), RET (PairV #kl #vl); ks ↦*{dk} k ∗
      ∃ r, ⌜lingerSingle (V.ents bi.name) k r⌝ ∗ beRd γ l F V ∗ rangeRes kl vl r (beLive γ l pl) }}

end spec

end Backend
end EtcdGrove
end Perennial
