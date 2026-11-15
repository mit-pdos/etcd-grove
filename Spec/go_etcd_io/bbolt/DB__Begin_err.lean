/-
`DB.Begin_err` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U5; used by U11 (`Open`'s internal `Begin(true)`); U12 derives `DB.Begin.spec` from it. Proof:
`Proof/go_etcd_io/bbolt/DB__Begin_err.lean` (a `sorry` until U5).
-/
module

public import Spec.go_etcd_io.bbolt.Api
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The internal `DB.Begin`** (design §3.13, B1): `DB.Begin.spec`'s statement with
`fmtErrorOk err` in its error branch (every error it returns is an `errors.New` one:
`ErrDatabaseNotOpen`, `ErrInvalidMapping`, `ErrDatabaseReadOnly`), what `Open` needs to log a
failed `Begin` with `%v`; and (maintainer 12, item 6) `tx = nil` on an error (`beginTx` and
`beginRWTx` return `nil, err`; `Open` calls `tx.Commit()` only if `tx != nil`). The frozen `DB.Begin.spec` is its weakening. -/
abbrev DB.Begin_err.spec : Prop :=
  ∀ (db : Loc) (γ : BoltName) (w : Bool) (Q : Data → IProp GF),
  {{ isBolt (GF := GF) db γ ∗
      (if w then emp else iprop(threadTok ∗
        AU <{ ∃∃ (q : Qp) (D : Data), boltState γ q D }> @ ⊤ \ ↑γ.ns, ∅
          <{ boltState γ q D, COMM Q D }>)) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Begin")) (Val #w))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err);
      (⌜err = GoInterface.nil⌝ ∗ txDB tx γ db ∗ ∃ D : Data,
        (if w then boltTx tx γ 1 (TxView.wr D) else iprop(boltTx tx γ 1 (TxView.ro D) ∗ Q D))) ∨
      (⌜err ≠ GoInterface.nil ∧ tx = null⌝ ∗ fmtErrorOk err ∗
        (if w then emp else iprop(threadTok ∗
          AU <{ ∃∃ (q : Qp) (D : Data), boltState γ q D }> @ ⊤ \ ↑γ.ns, ∅
            <{ boltState γ q D, COMM Q D }>))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
