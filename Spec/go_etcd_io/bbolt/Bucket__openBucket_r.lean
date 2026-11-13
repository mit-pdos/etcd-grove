/-
`Bucket.openBucket` of a reader (bbolt, internal to U6 of `notes/bbolt-proof-plan.md`): a new
reader bucket on the nested bucket's value (cloned first when misaligned), its fields persistent.
Proof: `Proof/go_etcd_io/bbolt/Bucket__openBucket_r.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.Open

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

/-- `b.openBucket(value)` of a reader's bucket `b`, `value` the nested bucket's value `cv` (a
header, and an inline page after it when inline) from a live source: a new reader bucket on it. -/
abbrev Bucket.openBucket_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp : Loc) (value : GoSlice) (vsr : Src) (cv : List w8),
  vsr ≠ Src.stale → 16 ≤ cv.length → (inBucketRoot cv = 0 → 16 < cv.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ srcOwn v value vsr cv }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"openBucket")) (Val #value))
  {{ (c : Loc), RET #c; rdTxK K tx src q T v ∗ rBktP v tx b dq bv ibp pp ∗ ⌜c ≠ null⌝ ∗
      rBkt v tx c DFrac.discard cv }}

end spec

end bbolt
end EtcdGrove
end Perennial
