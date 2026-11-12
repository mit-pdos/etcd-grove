/-
`Tx.DeleteBucket` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/Tx__DeleteBucket.lean` (unfinished until bbolt's invariants are designed).
-/
module

public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
/- Every bbolt spec is stated over OsFs's semantics (round 11, D22: the default `osFs_semantics`,
whose `pwrite` within one aligned OS page is all-or-nothing): the binder `∀ [HasExt osFsExt]` at
the head of each triple (a section variable is dropped from a definition that does not use it),
and in the signature of each vocabulary predicate, so that every statement carries it (checked
with `#check`). -/
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `tx.DeleteBucket(name)` in a write transaction: the bucket deleted and its name's generation
bumped (its handles are no longer current: bbolt frees its nodes); or, if absent,
`errors.ErrBucketNotFound`'s value and nothing changed; or, for the empty name (never a bucket's:
`CreateBucket` refuses it), `errors.ErrIncompatibleValue`'s value and nothing changed (D-M: in an
empty root bucket the seek finds no key and `bytes.Equal([]byte{}, nil)` holds, so bbolt reports
an incompatible value; `nonissues/bbolt-deletebucket-empty-name.md`). -/
abbrev Tx.DeleteBucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView) (name : GoSlice) (n : GoString) (dq : DFrac),
  {{ boltTx (GF := GF) tx γ 1 T ∗ name ↦*{dq} n ∗ ⌜T.rw = true⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"DeleteBucket")) (Val #name))
  {{ (err : GoInterface), RET #err; name ↦*{dq} n ∗
      ((⌜T.cur.lookup n = none⌝ ∗ boltTx tx γ 1 T ∗
         globalAddr go_etcd_io.bbolt.errors.ErrBucketNotFound ↦□ err) ∨
       (⌜n = [] ∧ T.cur.lookup n = none⌝ ∗ boltTx tx γ 1 T ∗
         globalAddr go_etcd_io.bbolt.errors.ErrIncompatibleValue ↦□ err) ∨
       (⌜T.cur.lookup n ≠ none ∧ err = GoInterface.nil⌝ ∗ boltTx tx γ 1 (T.dropBkt n))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
