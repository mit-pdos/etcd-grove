/-
`Tx.Bucket` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/Tx__Bucket.lean` (unfinished until bbolt's invariants are designed).
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

/-- `tx.Bucket(name)`: the transaction's handle of the bucket `n` at its current generation, or
nil if absent. Any fraction of a read transaction (it only reads); all of a write transaction
(it caches the handle in the root's map). -/
abbrev Tx.Bucket.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (name : GoSlice) (n : GoString) (dq : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ name ↦*{dq} n ∗ ⌜T.rw = true → q = 1⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (b : Loc), RET #b; boltTx tx γ q T ∗ name ↦*{dq} n ∗
      ((⌜T.cur.lookup n = none ∧ b = Loc.null⌝) ∨
       (⌜T.cur.lookup n ≠ none ∧ b ≠ Loc.null⌝ ∗ boltBkt tx γ b n (T.gen n))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
