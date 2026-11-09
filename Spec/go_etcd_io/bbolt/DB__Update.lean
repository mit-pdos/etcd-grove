/-
`db.Update(fn)` (`db.go`): a managed write transaction: `Begin(true)`, `fn(tx)`, then `Rollback` on
`fn`'s error, else `Commit`.

**Users.** `examples/bbolt/bank/bbolttest.go:167` (a transfer: reads, puts, its acknowledgement
after a nil return), `:235` (creating the bank). Snippet: `ReqBank` (atomicity and durability
across a crash).

**Proof sketch.** `DB.Begin.spec` (write) gives `boltTx tx γ 1 (TxView.wr D false ns)`; mark it
managed; call `fn` by its contract, which returns the transaction at some view `T` and either an
error with `R err`, or nil with the commit's two updates for `T` (the client builds them inside
`fn`, knowing `T`: the shape of `Tx.Commit.spec`'s); unmark; on an error `Tx.Rollback.spec` and
return it; else `Tx.Commit.spec` and its post.

**Changes.** New.

**Margin.** On `Begin`'s error (the database closed) `fn` is not called and its contract is
dropped. `fn` must not panic.
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

/-- `db.Update(fn)`: `fn` runs on a write transaction begun at the committed `D` and returns it at a
view `T`; on its error `R err` and nothing committed; on nil the transaction is committed with the
updates `fn` handed back (`Tx.Commit.spec`'s: `Q ok` at the meta write, `S synced failed` at the
end). An error of the commit: it took effect or not, as `Q`'s and `S`'s arguments say, or neither
update fired. -/
def DB.Update.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns : Bool) (fn : GoFunc)
    (Q : Bool → IProp GF) (S : Bool → Bool → IProp GF) (R : GoInterface → IProp GF),
  {{ isBolt (GF := GF) db γ ns ∗
      (∀ (tx : Loc) (D : Data) (Φ : val → IProp GF),
        boltTx tx γ 1 (TxView.wr D true ns) -∗
        ▷ (∀ (err : GoInterface) (T : TxView),
            ⌜T.rw = true ∧ T.managed = true ∧ T.noSync = ns⌝ -∗ boltTx tx γ 1 T -∗
            ((⌜err ≠ GoInterface.nil⌝ ∗ R err) ∨
             (⌜err = GoInterface.nil⌝ ∗
               AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
                 <{ ∀∀ (ok : Bool), ⌜σ.data = T.base⌝ ∗
                    boltState γ 1 (if ok then σ.commit T.cur ns else σ.attempt T.cur ns),
                    COMM Q ok }> ∗
               AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
                 <{ ∀∀ (synced failed : Bool), boltState γ 1 (σ.settle synced failed),
                    COMM S synced failed }>)) -∗ Φ #err) -∗
        WP (App (Val #fn) (Val #tx)) {{ Φ }}) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Update")) (Val #fn))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ Q true ∗ S (!ns) false) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗
        (R err ∨ (∃ ok synced failed : Bool, Q ok ∗ S synced failed) ∨
         (∃ T : TxView,
           AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
             <{ ∀∀ (ok : Bool), ⌜σ.data = T.base⌝ ∗
                boltState γ 1 (if ok then σ.commit T.cur ns else σ.attempt T.cur ns),
                COMM Q ok }> ∗
           AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
             <{ ∀∀ (synced failed : Bool), boltState γ 1 (σ.settle synced failed),
                COMM S synced failed }>) ∨
         True)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
