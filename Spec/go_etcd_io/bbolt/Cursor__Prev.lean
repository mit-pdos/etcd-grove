/-
`Cursor.Prev` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/Cursor__Prev.lean` (unfinished until bbolt's invariants are designed).
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

/-- `c.Prev()` **in a read transaction** (round 2: `⌜T.rw = false⌝`, a scope restriction): the
previous entry. At the first entry (or an empty bucket's position) it returns nil, nil and stays
at the first (bbolt#733); not positioned: nil, nil, still not positioned.
In a write transaction Go's `Prev` is wrong after deletes: `node.del` leaves empty leaves until
`Commit`'s rebalance, and `prev` does not skip them (as `next` and `Last` do), so it returns
nil, nil in the middle of the bucket (`issues/bbolt-cursor-prev-empty-leaf.md`, a failing test
at upstream `a4ef197`). A read transaction's tree has no empty non-root page (`fileHolds`'s
well-formedness, kept by every commit's rebalance), so there the spec holds. etcd never calls
`Prev`. -/
abbrev Cursor.Prev.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx c T es pos ∗ ⌜T.rw = false⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Prev")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      (match pos with
       | none => iprop(boltCur tx c T es none ∗ ⌜k = slice.nil ∧ v = slice.nil⌝)
       | some 0 => iprop(boltCur tx c T es (some 0) ∗ ⌜k = slice.nil ∧ v = slice.nil⌝)
       | some (i + 1) => iprop(boltCur tx c T es (some i) ∗ curAt tx es i k v)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
