/-
`db.View(fn)` (`db.go`): a managed read transaction: `Begin(false)`, `fn(tx)`, `Rollback`.

**Users.** `backend.Hash` (`backend.go:430`: the root cursor and every bucket's `ForEach`),
`examples/bbolt/bank/bbolttest.go:155, 223` (a snapshot read of the bank). Snippets: `ReqHash`,
`ReqBank`.

**Proof sketch.** `DB.Begin.spec` (read) with the caller's token and update (its `COMM` is `P D`);
mark the transaction managed (`TxView.ro D true ns`: `fn` cannot `Commit`/`Rollback` it, which
panic on a managed transaction, as it must give the transaction back); call `fn` by its contract;
unmark, `Tx.Rollback.spec` (gives the token back). On `Begin`'s error, `fn` is not called and the
update comes back.

**Changes.** New (the old API left `View` out).

**Margin.** `fn` must not panic (`View` does not recover it).
-/
module

public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.View(fn)`: `fn` runs on a read transaction of the committed data `D` read at its begin (the
caller's read update, with `P D`), and its error is returned; or `Begin`'s error and the update
back. -/
def DB.View.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns : Bool) (fn : GoFunc) (P : Data → IProp GF)
    (Q : Data → GoInterface → IProp GF),
  {{ isBolt (GF := GF) db γ ns ∗ threadTok ∗
      AU <{ ∃∃ (q : Qp) (σ : BoltSt), boltState γ q σ }> @ ⊤ \ ↑γ.ns, ∅
        <{ boltState γ q σ, COMM P σ.data }> ∗
      (∀ (tx : Loc) (D : Data) (Φ : val → IProp GF),
        P D -∗ boltTx tx γ 1 (TxView.ro D true ns) -∗
        ▷ (∀ err : GoInterface, boltTx tx γ 1 (TxView.ro D true ns) -∗ Q D err -∗ Φ #err) -∗
        WP (App (Val #fn) (Val #tx)) {{ Φ }}) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"View")) (Val #fn))
  {{ (err : GoInterface), RET #err; threadTok ∗
      ((∃ D : Data, Q D err) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗
         AU <{ ∃∃ (q : Qp) (σ : BoltSt), boltState γ q σ }> @ ⊤ \ ↑γ.ns, ∅
           <{ boltState γ q σ, COMM P σ.data }>)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
