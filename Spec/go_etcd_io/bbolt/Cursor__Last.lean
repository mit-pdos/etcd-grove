/-
`Cursor.Last` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/Cursor__Last.lean` (unfinished until bbolt's invariants are designed).
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

/-- `c.Last()`: the last entry (nil, nil for an empty bucket, at position `0 = es.length`).
Round 3: in a write transaction whose deletes emptied every leaf of a multi-leaf bucket, Go's
`Last` does not return (its loop calls `prev`, which climbs to the root and calls `first`, landing
on the first empty leaf again: `issues/bbolt-cursor-last-empty-leaves-hang.md`). The triple stays
true (a WP is partial: a call that never returns meets any post), but its "nil, nil for an empty
bucket" is no promise there. etcd never calls `Last`. -/
abbrev Cursor.Last.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Last")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      boltCur tx γ c T es (some (es.length - 1)) ∗ curAt tx γ es (es.length - 1) k v }}

end spec

end bbolt
end EtcdGrove
end Perennial
