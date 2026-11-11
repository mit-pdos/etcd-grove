/-
`Commit`'s trivial getters (U10g of `notes/bbolt-proof-plan.md`): internal specs of the small
methods `Tx.Commit` calls that have none. `Tx.ID` reads `tx.meta.Txid()` (as an `int`: the same
64 bits). (`tx.root.RootPage()` is the promoted `InBucket.RootPage` of the root bucket's header:
`wp_method_call` resolves it, no spec of its own.)
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`tx.ID()`** of a transaction whose meta copy `mp` is not nil: its txid. -/
abbrev Tx.ID.spec : Prop :=
  ∀ (tx mp : Loc) (mv : Meta) (dq dqm : DFrac), tx ≠ null → mp ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      tx.[Tx, go!"meta"] ↦{dq} mp ∗ mp ↦{dqm} mv }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"ID")) (Val #()))
  {{ RET #(mv.txid'); tx.[Tx, go!"meta"] ↦{dq} mp ∗ mp ↦{dqm} mv }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Tx.ID.wp_proof (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG)) :
    Tx.ID.spec (GF := GF) (hG := hG) := by
  intro tx mp mv dq dqm htx hmp
  wp_start as ⟨Hme, Hmv⟩
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  rw [decide_eq_false htx]
  wp_auto
  rw [decide_eq_false hmp]
  wp_auto
  wp_apply wp_Txid $$ [Hmv] as Hmv
  · iframe
  try wp_auto
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
