/-
`Cursor.Next` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/Cursor__Next.lean` (unfinished until bbolt's invariants are designed).
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

/-- `c.Next()`: the next entry. At the last entry it returns nil, nil and *stays at the last
entry* (Go's `next`: "it stays there"), so a `Prev` then returns the one before the last; past
the last (after a `Seek` past the end) it returns nil, nil and stays there. Not positioned: nil,
nil, still not positioned. The position is the abstract one (round 2): in a write transaction
whose trailing leaves deletes emptied, Go's stack ends on an empty leaf instead, which only a
`Prev` could tell apart, and the spec of `Prev` is for read transactions only. -/
abbrev Cursor.Next.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Next")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      (match pos with
       | none => iprop(boltCur tx γ c T es none ∗ ⌜k = slice.nil ∧ v = slice.nil⌝)
       | some i => iprop(boltCur tx γ c T es (some (if i + 1 < es.length then i + 1 else i)) ∗
           curAt tx γ es (i + 1) k v)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
