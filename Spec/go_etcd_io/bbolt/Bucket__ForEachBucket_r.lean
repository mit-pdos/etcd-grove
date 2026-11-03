/-
`Bucket.ForEachBucket_r` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U6; used by U10 (`tx_check` in `freepages`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__ForEachBucket_r.lean` (a `sorry` until U6).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.ForEachBucket(fn)` of a reader's bucket: `fn` runs on its nested buckets' names in order
(`bktNames`; the key slice with its source), with the invariant `I i` before the `i`-th; it
returns the first non-nil error `fn` returned (after which the iteration stops), else nil. -/
abbrev Bucket.ForEachBucket_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (fn : GoFunc) (I : Nat → IProp GF),
  (bv = rootVal v ∨ ∃ n, (n, bv) ∈ treeEntries v.pages v.root) →
  {{ rdTxK (GF := GF) K tx src q T v ∗ rBkt v tx b dq bv ∗ I 0 ∗
      □ (∀ (i : Nat) (k : GoSlice) (kb : List w8) (ks : Src),
          {{ rdTxK K tx src q T v ∗ rBkt v tx b dq bv ∗ I i ∗ srcOwn v k ks kb ∗
              ⌜ks ≠ Src.stale ∧ (bktNames v.pages bv)[i]? = some kb⌝ }}
            (App (Val #fn) (Val #k))
          {{ (err : GoInterface), RET #err; rdTxK K tx src q T v ∗ rBkt v tx b dq bv ∗
              I (i + 1) }}) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"ForEachBucket")) (Val #fn))
  {{ (err : GoInterface), RET #err; ∃ i : Nat, rdTxK K tx src q T v ∗ rBkt v tx b dq bv ∗ I i ∗
      ⌜i ≤ (bktNames v.pages bv).length ∧
        (err = interface.nil → i = (bktNames v.pages bv).length)⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
