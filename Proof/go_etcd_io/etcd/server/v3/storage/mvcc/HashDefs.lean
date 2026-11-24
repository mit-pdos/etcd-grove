/-
The compaction's hash machinery as its names-only specs state it (audit B4b, 2026-10-18: the
premises Go's code needs, which the specs of `hashStorage.Store`, `kvHasher.WriteKeyValue` and
`kvHasher.Hash` did not state). Lean-first (no Rocq counterpart).

* `hashStorageOk h`: the `*hashStorage` `h` has a non-nil logger (`Store` logs through it first;
  `NewHashStorage` sets it, `NewStore` passes the store's), and its `hashMu` guards its `hashes`
  (`hashesR`: the field, the slice's elements and its capacity; sortslice, 2026-11-24, when `Store`
  was proved over the fork's `slices.SortFunc`: `NewHashStorage` makes the lock).
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
public import Perennial.Proof.sync.RWMutexGuard

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

/-- **What a hash storage's `hashMu` guards**, at `q`: its `hashes` field, the slice's elements and
the slice's capacity (`Store` appends in place when it fits), at most `hashStorageMaxSize` (10)
of them (`Store` trims to that). -/
def mvcc.hashesR (h : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (sl : GoSlice) (xs : List KeyValueHash),
    structFieldRef hashStorage go!"hashes" h ↦{DFrac.own q} sl ∗ sl ↦*{DFrac.own q} xs ∗
    ownSliceCap KeyValueHash sl (DFrac.own q) ∗ ⌜xs.length ≤ 10⌝)

instance mvcc.hashesR_fractional (h : Loc) : Fractional (mvcc.hashesR (GF := GF) h) where
  fractional q1 q2 := by
    have hf : ∀ sl : GoSlice, (structFieldRef hashStorage go!"hashes" h ↦{DFrac.own (q1 + q2)} sl : IProp GF) ⊣⊢
        structFieldRef hashStorage go!"hashes" h ↦{DFrac.own q1} sl ∗
          structFieldRef hashStorage go!"hashes" h ↦{DFrac.own q2} sl := fun sl =>
      (typedPointsto_dfractional (GF := GF) (structFieldRef hashStorage go!"hashes" h) sl).dfractional
        (DFrac.own q1) (DFrac.own q2)
    have hs : ∀ (sl : GoSlice) (xs : List KeyValueHash), (sl ↦*{DFrac.own (q1 + q2)} xs : IProp GF) ⊣⊢
        sl ↦*{DFrac.own q1} xs ∗ sl ↦*{DFrac.own q2} xs := fun sl xs =>
      (ownSlice_dfractional (GF := GF) sl xs).dfractional (DFrac.own q1) (DFrac.own q2)
    have hc : ∀ sl : GoSlice, (ownSliceCap KeyValueHash sl (DFrac.own (q1 + q2)) : IProp GF) ⊣⊢
        ownSliceCap KeyValueHash sl (DFrac.own q1) ∗ ownSliceCap KeyValueHash sl (DFrac.own q2) :=
      fun sl => (ownSliceCap_dfractional (GF := GF) (V := KeyValueHash) sl).dfractional
        (DFrac.own q1) (DFrac.own q2)
    unfold mvcc.hashesR
    refine ⟨?_, ?_⟩
    · iintro ⟨%sl, %xs, Hf, Hs, Hc, %Hlen⟩
      icases (hf sl).1 $$ Hf with ⟨Hf1, Hf2⟩
      icases (hs sl xs).1 $$ Hs with ⟨Hs1, Hs2⟩
      icases (hc sl).1 $$ Hc with ⟨Hc1, Hc2⟩
      isplitl [Hf1 Hs1 Hc1]
      · iexists sl, xs; iframe; ipureintro; exact Hlen
      · iexists sl, xs; iframe; ipureintro; exact Hlen
    · iintro ⟨⟨%sl1, %xs1, Hf1, Hs1, Hc1, %Hlen⟩, ⟨%sl2, %xs2, Hf2, Hs2, Hc2, -⟩⟩
      icombine Hf1 Hf2 gives %Hsl
      subst Hsl
      icombine Hs1 Hs2 gives %Hxs
      subst Hxs
      iexists sl1, xs1
      isplitl [Hf1 Hf2]
      · iapply (hf sl1).2; iframe
      isplitl [Hs1 Hs2]
      · iapply (hs sl1 xs1).2; iframe
      isplitl [Hc1 Hc2]
      · iapply (hc sl1).2; iframe
      · ipureintro; exact Hlen

/-- **A hash storage** `h` (persistent): its logger, a zap logger (`zapLoggerOk`; premise fixes 6:
until then only not nil, and `Store` logs through it), and the guard of its `hashMu` over
`hashesR` (see the file header). -/
def mvcc.hashStorageOk (h : Loc) : IProp GF :=
  iprop(∃ lg : Loc, structFieldRef hashStorage go!"lg" h ↦□ lg ∗ zapLoggerOk lg ∗
    sync.isRWMutexGuard (structFieldRef hashStorage go!"hashMu" h) (mvcc.hashesR h))

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
