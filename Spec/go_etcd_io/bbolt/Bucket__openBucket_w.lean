/-
`Bucket.openBucket` of a writer (bbolt, internal to U6 of `notes/bbolt-proof-plan.md`): a new
bucket on the nested bucket's value: its header copied into a fresh `InBucket` (or, when the
value is misaligned, a clone of the value whose header it points into), its inline page after the
header. Proof: `Proof/go_etcd_io/bbolt/Bucket__openBucket_w.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WOpen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.openBucket(value)` of a writer's bucket `bl` (a writable transaction), `value` a nested
bucket's value `cv` from a live source: a new live bucket object `c` on it (`openedRec`), with its
`FillPercent` (the default, not NaN); nothing of `X` changes. -/
abbrev Bucket.openBucket_w.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec) (value : GoSlice)
    (vsr : Src) (cv : List w8),
  X.t.bs !! bl = some B → X.t.t.writable' = true → vsr ≠ Src.stale → 16 ≤ cv.length →
  (inBucketRoot cv = 0 → 16 < cv.length) →
  {{ wtxW (GF := GF) K tx r m X ∗ srcOwn X.v value vsr cv }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"openBucket")) (Val #value))
  {{ (c : Loc), RET #c; ∃ C : BRec, wtxW K tx r m X ∗ objOwn X.v c (DFrac.own 1) true (.bkt C) ∗
      (∃ f : w64, ⌜¬ float64IsNaN f⌝ ∗ c.[Bucket, go!"FillPercent"] ↦ f) ∗
      ⌜c ≠ null ∧ openedRec tx cv vsr C⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
