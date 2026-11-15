/-
`b.openBucket(value)` (`bucket.go`): a child handle from a bucket value (an inline page copied if unaligned, 4d's `InBucket` view).
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch** (integration I7). `bktVal`'s realization: at least `bucketHeaderSize` bytes, 4d's
`encInBucket` of the child's header first; unaligned: `cloneBytes`; a writer copies the header
(4d's `inBucket_view`), a reader points at it; root 0: the inline page after the header.

**Changes** (integration I7): the value is `bktVal` of the child (from `seek`'s `seekRaw`), not any
`txBytes`: `&value[0]` panics on an empty value, and nothing tied the bytes to the bucket.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** `bktH` without the
generations; the parent's currency is not needed (it reads `b.tx` and the value `bktVal` gives); the
new handle is a `bktH`, which its caller (`Bucket.Bucket`, `CreateBucketIfNotExists`) caches and
turns into the token (the per-path generation counter it replaces was unobservable state, redundant
with ownership).
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) a handle of the child bucket at `p.child k` (`k` the key the value was found at). -/
def Bucket.openBucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (k : GoString) (v : GoSlice),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p ∗ bktVal tx γ (p.child k) v ∗ ⌜(T.cur.atPath (p.child k)).any Ent.isBkt ∧ (T.rw = true → q = 1)⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"openBucket")) (Val #v))
  {{ (c : Loc), RET #c; boltTx tx γ q T ∗ bktH tx γ c (p.child k) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
