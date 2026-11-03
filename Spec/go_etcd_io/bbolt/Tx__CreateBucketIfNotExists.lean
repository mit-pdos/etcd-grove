/-
`Tx.CreateBucketIfNotExists` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/Tx__CreateBucketIfNotExists.lean` (unfinished until bbolt's invariants are designed).
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

/-- `tx.CreateBucketIfNotExists(name)` in a write transaction (a name of at most `MaxKeySize`
bytes: a scope restriction, Go checks no length, `notes/bbolt-spec-decisions.md`, D12): an empty name is refused
(`ErrBucketNameRequired`); otherwise the bucket, empty if it was absent, and its handle (bbolt
copies the name). -/
abbrev Tx.CreateBucketIfNotExists.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView) (name : GoSlice) (n : GoString) (dq : DFrac),
  {{ boltTx (GF := GF) tx γ 1 T ∗ name ↦*{dq} n ∗ ⌜T.rw = true ∧ n.length ≤ maxKeySize⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"CreateBucketIfNotExists")) (Val #name))
  {{ (b : Loc) (err : GoInterface), RET (PairV #b #err); name ↦*{dq} n ∗
      (if n.length = 0 then iprop(⌜err ≠ GoInterface.nil⌝ ∗ boltTx tx γ 1 T)
       else iprop(⌜err = GoInterface.nil⌝ ∗ boltBkt tx b n (T.gen n) ∗
         boltTx tx γ 1 (if T.cur.lookup n = none then T.setBkt n ∅ else T))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
