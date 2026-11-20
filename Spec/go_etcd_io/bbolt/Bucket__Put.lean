/-
`Bucket.Put` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__Put.lean` (unfinished until bbolt's invariants are designed).
-/
module

public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
/- Every bbolt spec is stated over OsFs's semantics (round 11, D22: the default `osFs_semantics`,
whose `pwrite` within one aligned OS page is all-or-nothing): the binder `∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]` at
the head of each triple (a section variable is dropped from a definition that does not use it),
and in the signature of each vocabulary predicate, so that every statement carries it (checked
with `#check`). -/
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.Put(key, value)` of a current handle in a write transaction: an empty key, one above
`MaxKeySize`, or an entry (key plus value) above `bboltEntryMax` bytes is refused, nothing changed
(the last `ErrValueTooLarge`, the fork's check since 3f8520bd: upstream accepted values a page of
four entries cannot hold, `issues/bbolt-max-value-size-unusable.md`; until 2026-11-19 a premise of
this spec, `notes/bbolt-spec-decisions.md`, D4); otherwise the entry set (bbolt copies the key and
keeps the value: read-only for good). -/
abbrev Bucket.Put.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName) (T : TxView) (b : Loc) (n : GoString) (m : BktData)
    (key value : GoSlice) (kb vb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ 1 T ∗ boltBkt tx γ b n (T.gen n) ∗ key ↦*{dk} kb ∗ value ↦*□ vb ∗
      ⌜T.rw = true ∧ T.cur.lookup n = some m⌝ }}
    (App (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Put")) (Val #key)) (Val #value))
  {{ (err : GoInterface), RET #err; key ↦*{dk} kb ∗
      (if kb.length = 0 ∨ maxKeySize < kb.length ∨ bboltEntryMax < kb.length + vb.length
       then iprop(⌜err ≠ GoInterface.nil⌝ ∗ boltTx tx γ 1 T)
       else iprop(⌜err = GoInterface.nil⌝ ∗ boltTx tx γ 1 (T.setBkt n (m.insert kb vb)))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
