/-
The compaction's hash machinery as its names-only specs state it (audit B4b, 2026-10-18: the
premises Go's code needs, which the specs of `hashStorage.Store`, `kvHasher.WriteKeyValue` and
`kvHasher.Hash` did not state). Lean-first (no Rocq counterpart).

* `hashStorageOk h`: the `*hashStorage` `h` has a non-nil logger (`Store` logs through it first;
  `NewHashStorage` sets it, `NewStore` passes the store's).
* `kvHasherOk h`: the `kvHasher` value `h` holds the `crc32` digest `newKVHasher` made, a
  `*digest` over a Castagnoli table, with its points-to (a zero `kvHasher`'s nil `hash` panics in
  `Write` and `Sum32`). (prove-etcdint3, 2026-11-21: `hash.go`'s hasher translated over `hash/crc32`'s
  digest, `New`, `Write` and `Sum32` proved; until then an opaque `Prop`, the three functions
  trust-boundary axioms, `hash/crc32` having no model.)
* `bucketKeyOk k`: `k` is a key of the `key` bucket as `BytesToBucketKey` accepts it (it panics
  otherwise): a revision's 17 bytes (`main`, `'_'`, `sub`, both non-negative), maybe one mark
  byte.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevBytes
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A hash storage** `h` (persistent): its logger, a zap logger (`zapLoggerOk`; premise fixes 6:
until then only not nil, and `Store` logs through it). -/
def mvcc.hashStorageOk (h : Loc) : IProp GF :=
  iprop(∃ lg : Loc, structFieldRef hashStorage go!"lg" h ↦□ lg ∗ zapLoggerOk lg)

instance mvcc.hashStorageOk_persistent (h : Loc) : Persistent (mvcc.hashStorageOk (GF := GF) h) := by
  unfold mvcc.hashStorageOk; infer_instance

/-- **A hasher `newKVHasher` made** (exclusive; see the file header): its `hash` is a `*digest`,
owned, over a Castagnoli table, read-only for good (the checksum it holds is not tracked). -/
def mvcc.kvHasherOk (h : kvHasher) : IProp GF :=
  iprop(∃ (d tab : Loc) (c : w32),
    ⌜h.hash' = interface.mkOk (go.GoType.PointerType _root_.Perennial.hash.crc32.digest.ty) #d⌝ ∗
    d ↦ _root_.Perennial.hash.crc32.digest.mk c tab ∗ tab ↦□ _root_.Perennial.hash.crc32.castagnoliTableArr)

end defs

/-- **A key of the `key` bucket** (`BytesToBucketKey` accepts it; see the file header). -/
def mvcc.bucketKeyOk [GooseExts] (k : GoString) : Prop :=
  ∃ (r : mvcc.Rev) (rest : List w8), k = mvcc.revBytes r false ++ rest ∧ rest.length ≤ 1 ∧
    0 ≤ sint.Z r.main ∧ 0 ≤ sint.Z r.sub

end EtcdGrove
end Perennial
