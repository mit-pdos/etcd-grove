/-
`tx_check.go`'s checks as `DB.freepages` runs them (U10e of `notes/bbolt-proof-plan.md`): the
internal spec of `tx.recursivelyCheckBucket(&tx.root, reachable, nofreed, HexKVStringer(), ech)`
on a reader of a `treeOK` view: it sends nothing on the channel, leaves `nofreed` empty, and
fills `reachable` with exactly the slots the view's pages cover (`reachOK`); and
`HexKVStringer()`'s value.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section defs
variable [GooseExts]

/-- `reachable`'s keys are exactly the slots the pages `P` cover. -/
def reachOK (P : Pages) (M : GMap w64 Loc) : Prop :=
  ∀ x : w64, (M !! x).isSome = true ↔ coversSlot P x.toNat

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `HexKVStringer()`'s value. -/
def hexKV : GoInterface := interface.mkOk hexKvStringer.ty #(zero_val hexKvStringer)

/-- **`tx.recursivelyCheckBucket(&tx.root, reachable, freed, HexKVStringer(), ch)`** of a
reader (`freepages`' check): `freed` empty, `reachable` empty before; nothing is sent on `ch`;
after, `reachable`'s keys are the slots of the view's pages. -/
abbrev Tx.recursivelyCheckBucket_root.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (rm fm ch : Loc),
  {{ rdTxK (GF := GF) K tx src q T v ∗ rm ↦$ (∅ : GMap w64 Loc) ∗ fm ↦$ (∅ : GMap w64 Bool) }}
    (App (App (App (App (App (Val (tx @!! go.GoType.PointerType Tx.ty @!!
      go!"recursivelyCheckBucket")) (Val #(txRoot (GF := GF) tx))) (Val #rm)) (Val #fm))
      (Val #hexKV)) (Val #ch))
  {{ RET #(); rdTxK K tx src q T v ∗ (∃ M, rm ↦$ M ∗ ⌜reachOK v.pages M⌝) ∗
      fm ↦$ (∅ : GMap w64 Bool) }}

omit hos in
theorem wp_HexKVStringer :
    {{ (True : IProp GF) }}
      (App (Val #(functions HexKVStringer [])) (Val #()))
    {{ RET #hexKV; True }} := by
  wp_start
  wp_auto
  unfold hexKV
  iapply HΦ
  itrivial

end spec

end bbolt
end EtcdGrove
end Perennial
