/-
The compaction's hash machinery as its names-only specs state it (audit B4b, 2026-10-18: the
premises Go's code needs, which the specs of `hashStorage.Store`, `kvHasher.WriteKeyValue` and
`kvHasher.Hash` did not state). Lean-first (no Rocq counterpart).

* `hashStorageOk h`: the `*hashStorage` `h` has a non-nil logger (`Store` logs through it first;
  `NewHashStorage` sets it, `NewStore` passes the store's).
* `kvHasherOk h`: the `kvHasher` value `h` (an axiomatized type: Goose does not translate its
  `hash.Hash32` field) is one `newKVHasher` returned or `WriteKeyValue` left, so its `hash` is
  the `crc32` digest `newKVHasher` made (a zero `kvHasher`'s nil `hash` panics in `Write` and
  `Sum32`). Opaque, as the type.
* `bucketKeyOk k`: `k` is a key of the `key` bucket as `BytesToBucketKey` accepts it (it panics
  otherwise): a revision's 17 bytes (`main`, `'_'`, `sub`, both non-negative), maybe one mark
  byte.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevBytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A hash storage** `h` (persistent): its logger, not nil. -/
def mvcc.hashStorageOk (h : Loc) : IProp GF :=
  iprop(∃ lg : Loc, structFieldRef hashStorage go!"lg" h ↦□ lg ∗ ⌜lg ≠ null⌝)

instance mvcc.hashStorageOk_persistent (h : Loc) : Persistent (mvcc.hashStorageOk (GF := GF) h) := by
  unfold mvcc.hashStorageOk; infer_instance

/-- **The store's backend hashes** (persistent; etcd-io/etcd#22609, branch
`pr-verify/etcd-22609`): the store `s`'s backend `s.b` is an interface whose
`Hash(schema.DefaultIgnores)` returns some hash and error. The trust boundary of `store.hash`, a
premise of its spec: the backend's contract (`isKeyBackendG`) has no `Hash`, and the real
backend's (`backend.Hash`, a CRC of the bbolt file under its read lock and a `View`, calling
`ignores` on every key; an error, not a panic, once the backend is closed) is not translated.
Only of `DefaultIgnores` (pure, total): `backend.Hash` calls its argument, so of an arbitrary
function it need not return (the reviewer's point, 2026-10-19). -/
def mvcc.storeHashOk (s : Loc) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, structFieldRef store go!"b" s ↦□ GoInterface.ok bi ∗
    □ {{ True }} (App (Val #(methods bi.ty go!"Hash" bi.v))
        (Val #(functions go_etcd_io.etcd.server.v3.storage.schema.DefaultIgnores [])))
      {{ (h : w32) (err : GoInterface), RET (PairV #h #err); True }})

instance mvcc.storeHashOk_persistent (s : Loc) : Persistent (mvcc.storeHashOk (GF := GF) s) := by
  unfold mvcc.storeHashOk; infer_instance

end defs

/-- **A hasher `newKVHasher` made** (opaque: `kvHasher` is an axiomatized type; see the file
header). -/
opaque mvcc.kvHasherOk [FfiSyntax] : kvHasher → Prop

/-- **A key of the `key` bucket** (`BytesToBucketKey` accepts it; see the file header). -/
def mvcc.bucketKeyOk [FfiSyntax] (k : GoString) : Prop :=
  ∃ (r : mvcc.Rev) (rest : List w8), k = mvcc.revBytes r false ++ rest ∧ rest.length ≤ 1 ∧
    0 ≤ sint.Z r.main ∧ 0 ≤ sint.Z r.sub

end EtcdGrove
end Perennial
