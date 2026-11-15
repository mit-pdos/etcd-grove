/-
`Tx.Commit_err` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U10; used by U11 (`Open`'s internal `Commit`); U12 derives `Tx.Commit.spec` from it. Proof:
`Proof/go_etcd_io/bbolt/Tx__Commit_err.lean` (a `sorry` until U10).
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

/-- **The internal `Tx.Commit`** (design §3.13, B1): `Tx.Commit.spec`'s statement with
`fmtErrorOk err` in its error branch (its errors come from `errors.New`, `fmt.Errorf` and the
OsFs-backed `os`/`syscall` calls, design §5 item 5). The frozen `Tx.Commit.spec` is its
weakening. U11i: the update comes in a carrier `P` of the caller's choice (`P ⊢` the update),
returned whole when the update did not fire: `Open` passes `boltState γ 1 D` itself, which it
needs back on every exit (its last write of its named result `db` excludes the page pool's `New`
by holding all of `boltState`); the frozen `Tx.Commit.spec` takes `P :=` the update. -/
abbrev Tx.Commit_err.spec : Prop :=
  ∀ (tx : Loc) (γ : BoltName) (T : TxView) (Q P : IProp GF),
  (P ⊢ AU <{ ∃∃ (D' : Data), boltState γ 1 D' }> @ ⊤ \ ↑γ.ns, ∅
        <{ ⌜D' = T.base⌝ ∗ boltState γ 1 T.cur, COMM Q }>) →
  {{ boltTx (GF := GF) tx γ 1 T ∗ ⌜T.rw = true⌝ ∗ P }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Commit")) (Val #()))
  {{ (err : GoInterface), RET #err; txDone tx ∗
      ((⌜err = GoInterface.nil⌝ ∗ Q) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ fmtErrorOk err ∗ (Q ∨ P))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
