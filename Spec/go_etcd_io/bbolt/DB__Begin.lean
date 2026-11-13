/-
`DB.Begin` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/DB__Begin.lean` (unfinished until bbolt's invariants are designed).
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

/-- `db.Begin(writable)`, from any goroutine.
- **Read** (`writable = false`): the caller lends its `threadTok` (the transaction's reader slot
  of `mmaplock`, held until `Rollback` gives it back) and a read update; at the linearization
  point (the meta copy under `metalock`) the snapshot `D` is the committed data, and the update
  is fired there: the transaction reads `D` for its whole life (`TxView.ro D`), whatever commits
  after.
- **Write**: blocks until no other write transaction is live (`rwlock`), then begins at the
  committed `D`; no update is needed, since the committed data stays `D` while the transaction
  is live (`boltTx_base`: the client learns `D` from its `boltState`).
- **Error** (the database closed, or its mapping lost after a failed remap): no transaction;
  the token and the update come back.
The transaction is a fresh `*Tx` of `db` (`txDB`). -/
abbrev DB.Begin.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (db : Loc) (γ : BoltName) (w : Bool) (Q : Data → IProp GF),
  {{ isBolt (GF := GF) db γ ∗
      (if w then emp else iprop(threadTok ∗
        AU <{ ∃∃ (q : Qp) (D : Data), boltState γ q D }> @ ⊤ \ ↑γ.ns, ∅
          <{ boltState γ q D, COMM Q D }>)) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Begin")) (Val #w))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err);
      (⌜err = GoInterface.nil⌝ ∗ txDB tx γ db ∗ ∃ D : Data,
        (if w then boltTx tx γ 1 (TxView.wr D) else iprop(boltTx tx γ 1 (TxView.ro D) ∗ Q D))) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗
        (if w then emp else iprop(threadTok ∗
          AU <{ ∃∃ (q : Qp) (D : Data), boltState γ q D }> @ ⊤ \ ↑γ.ns, ∅
            <{ boltState γ q D, COMM Q D }>))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
