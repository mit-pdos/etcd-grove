/-
`b.NextSequence()` (`bucket.go`): increments the counter (wrapping, `uint64`) and returns it.

**Users.** None in etcd (a common bbolt idiom for ids). Snippet: `ReqNested`. **Proof sketch.** As
`SetSequence`, with `IncSequence`. **Changes.** New.
**Proof sketch in the internal vocabulary** (verify-round, A11 F9). As `SetSequence`'s:
`Bucket.node` (root materialized), `wtxCore_seq` (its counter is the bucket's `seq`), 4d's
`IncSequence`, then `InSequence` read before the wand closes with `seq + 1`.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The handle premise `bktUse`
(the bucket's ownership share in a write transaction) in place of `bktH … gs` and the generation
check, given back (the per-path generation counter it replaces was unobservable state, redundant
with ownership).
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

/-- `b.NextSequence()`: on a write transaction (all of it), the counter of the bucket at `p` plus
one, stored and returned. -/
def Bucket.NextSequence.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (qb : Qp),
  {{ boltTx (GF := GF) tx γ q T ∗ bktUse tx γ T.rw b p qb ∗ ⌜(T.rw = true → q = 1)⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"NextSequence")) (Val #()))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); bktUse tx γ T.rw b p qb ∗
      (if T.rw = false then
        iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
      else iprop(⌜err = GoInterface.nil ∧
          n = ((T.cur.atPath p).map Ent.seq).getD (W64 0) + W64 1⌝ ∗
        boltTx tx γ q (T.setCur (T.cur.modAt p (fun e => e.setSeq n))))) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
