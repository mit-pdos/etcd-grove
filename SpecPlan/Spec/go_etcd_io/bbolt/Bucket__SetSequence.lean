/-
`b.SetSequence(v)` (`bucket.go`). **Users.** None in etcd. Snippet: `ReqNested`.
**Proof sketch.** Not writable: error; materialize the root node (so `spill` writes the bucket
header); `SetInSequence`. **Changes.** New.
**Proof sketch in the internal vocabulary** (verify-round, A11 F9). `Bucket.node` of the root
page with a nil parent if `rootNode` is nil (`repKept`, the root then materialized); `wtxCore_seq`
gives the handle's `InBucket` points-to; 4d's `InBucket.SetInSequence`; the wand gives `physRep`
of the view with the counter set.
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

/-- `b.SetSequence(v)`: on a write transaction (all of it), sets the counter of the bucket at `p`. -/
def Bucket.SetSequence.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (qb : Qp) (v : w64),
  {{ boltTx (GF := GF) tx γ q T ∗ bktUse tx γ T.rw b p qb ∗ ⌜(T.rw = true → q = 1)⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"SetSequence")) (Val #v))
  {{ (err : GoInterface), RET #err; bktUse tx γ T.rw b p qb ∗
      (if T.rw = false then
        iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
      else iprop(⌜err = GoInterface.nil⌝ ∗
        boltTx tx γ q (T.setCur (T.cur.modAt p (fun e => e.setSeq v))))) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
