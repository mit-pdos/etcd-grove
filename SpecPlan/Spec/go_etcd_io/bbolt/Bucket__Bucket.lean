/-
`b.Bucket(name)` (`bucket.go`): the nested bucket `name`, or nil.

**Users.** `Tx.Bucket` (the root's), nested-bucket clients (none in etcd). Snippet: `ReqNested`.

**Proof sketch.** A writer's child cache (`b.buckets`) first; else `seek`, check the bucket flag,
`openBucket` the value (an inline bucket's page aligned into a copy if needed, 4d's `InBucket`
view), cache it if writable (all of the transaction). The handle's path is `p.child name`. In a write
transaction the cache entry is the child's token's (`bktTok`, `wtxCore_bktOwn`): a cached `c` is
returned as it is (any share); else the new handle is cached, the whole token updated with the map
write. An absent bucket is not cached (`DeleteBucket` removes the entry), so its lookup needs no
token.

**Changes.** New (nested buckets).
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The parent's handle premise
`bktUse` in place of `bktH … gs` and the generation check, given back; in a write transaction the
child's token (`bktTok`: its cache entry `o`, the whole if `o = none`) comes back at `some c`, `c`
the cached handle if there was one; a read transaction's child handle is the persistent `bktH` (the
per-path generation counter it replaces was unobservable state, redundant with ownership).
**Changes (2026-11-12, the review's finding 5).** All of the transaction only when the lookup fills
the cache (a write transaction, the bucket present and not cached: `o = none`); a hit reads
`b.buckets` alone, and a miss on an absent bucket only seeks (as `Get`), so any fraction.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

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

/-- `b.Bucket(name)`: a handle of the nested bucket `name` of the bucket at `p`, or nil. In a
write transaction it takes the child's token (`bktTok`) and gives it back at the handle returned,
the cached one if there was one. -/
def Bucket.Bucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (qb : Qp)
    (o : Option Loc) (qc : Qp) (name : GoSlice) (n : GoString) (dq : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ bktUse tx γ T.rw b p qb ∗ bktTok tx γ T (p.child n) o qc ∗
      name ↦*{dq} n ∗
      ⌜(T.rw && (T.cur.atPath (p.child n)).any Ent.isBkt && o.isNone) = true → q = 1⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Bucket")) (Val #name))
  {{ (c : Loc), RET #c; boltTx tx γ q T ∗ bktUse tx γ T.rw b p qb ∗ name ↦*{dq} n ∗
      (if (T.cur.atPath (p.child n)).any Ent.isBkt
       then iprop(⌜c ≠ Loc.null ∧ (T.rw = true → ∀ c', o = some c' → c = c')⌝ ∗
         bktUse tx γ T.rw c (p.child n) qc)
       else iprop(⌜c = Loc.null⌝)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
