/-
`Bucket.ForEachBucket` of a reader whose callback keeps the bucket's header and inline page where
they are (`rBktP` at the same `ibp`, `pp`): the variant of the frozen `Bucket.ForEachBucket_r`
that is provable (U6c, `notes/bbolt-proof-plan.md`; the frozen callback returns `rBkt`, whose
inline page may have moved, so the cursor's stack, which refers to it, could not go on).
Proof: `Proof/go_etcd_io/bbolt/Bucket__ForEachBucket_rP.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.RCtx

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

/-- `b.ForEachBucket(fn)` of a reader's bucket (header at `ibp`, inline page at `pp`): `fn` runs on
its nested buckets' names in order (`bktNames`), with the invariant `I i` before the `i`-th; it
returns the first non-nil error `fn` returned (after which the iteration stops; the caller's `E err`
holds of it), else nil (and every name was visited). -/
abbrev Bucket.ForEachBucket_rP.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp : Loc) (fn : GoFunc) (I : Nat → IProp GF)
    (E : GoInterface → IProp GF),
  (bv = rootVal v ∨ ∃ n, (n, bv) ∈ treeEntries v.pages v.root) →
  {{ rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dq bv ibp pp ∗ I 0 ∗
      □ (∀ (i : Nat) (k : GoSlice) (kb : List w8) (ks : Src),
          {{ rdTxK K tx src q T v ∗ rBktP v tx b dq bv ibp pp ∗ I i ∗ srcOwn v k ks kb ∗
              ⌜ks ≠ Src.stale ∧ (bktNames v.pages bv)[i]? = some kb⌝ }}
            (App (Val #fn) (Val #k))
          {{ (err : GoInterface), RET #err; rdTxK K tx src q T v ∗ rBktP v tx b dq bv ibp pp ∗
              ((⌜err = interface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ interface.nil⌝ ∗ E err)) }}) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"ForEachBucket")) (Val #fn))
  {{ (err : GoInterface), RET #err; rdTxK K tx src q T v ∗ rBktP v tx b dq bv ibp pp ∗
      ((⌜err = interface.nil⌝ ∗ I (bktNames v.pages bv).length) ∨
        (⌜err ≠ interface.nil⌝ ∗ E err)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
