/-
`Bucket.Delete` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__Delete.lean` (unfinished until bbolt's invariants are designed).
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

/-- `b.Delete(key)` of a current handle in a write transaction: the entry removed (if present).
The key is the caller's slice (given back as it was), or one of the transaction's own (`own =
false`: a key a cursor of the same transaction returned, as mvcc's compaction deletes `keys[i]`;
`Delete` only reads it). -/
abbrev Bucket.Delete.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView) (b : Loc) (n : GoString) (m : BktData)
    (key : GoSlice) (kb : GoString) (dk : DFrac) (own : Bool),
  {{ boltTx (GF := GF) tx γ 1 T ∗ boltBkt tx γ b n (T.gen n) ∗
      (if own then key ↦*{dk} kb else txBytes tx γ key kb) ∗
      ⌜T.rw = true ∧ T.cur.lookup n = some m⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Delete")) (Val #key))
  {{ RET #GoInterface.nil; boltTx tx γ 1 (T.setBkt n (m.delete kb)) ∗
      (if own then key ↦*{dk} kb else txBytes tx γ key kb) }}

end spec

end bbolt
end EtcdGrove
end Perennial
