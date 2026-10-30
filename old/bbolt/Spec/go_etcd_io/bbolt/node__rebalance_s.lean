module
public import Proof.go_etcd_io.bbolt.RebalanceDefs
public import Proof.go_etcd_io.bbolt.WriteAlloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `n.rebalance()` of the node `nl` of the bucket `bl` of the writer `txl` (`Commit`'s
rebalance), the bucket in the rebalance's invariant (`rblB`; `nl` the deficient node `dfc`, if
any, and then marked unbalanced): a balanced node does nothing; otherwise, if it is small, it is
merged into a sibling or removed (an empty one), or, the root, collapsed into its only child; the
pages of the nodes removed are freed (`node.free.sspec`: their tokens to `pgToks γ F`), and the
parent that lost a child is rebalanced. After it the bucket has no deficient node, no new
unbalanced node, and `nl` is not unbalanced (`rblStep`); its keys and entries of nested buckets
stay. It does not panic: `Assert(n.parent.numChildren() > 1)` holds (the parent is not the
deficient node), the root's only child and the siblings are page positions or nodes, and the
freed pages are not pending yet. -/
abbrev node.rebalance.sspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (hwm : Nat) (txl : Loc)
    (txid : w64) (ρ : DBState) (bl : Loc) (B : BRec) (st : TxStats) (pmap : GoMap) (mp : Loc)
    (mv : Meta) (F : GMap Nat (List w8)) (nl : Loc) (r : NRec) (dfc : Option Loc),
  I.FreeSpec → viewOK W → rblB W hwm bl B dfc → B.bv.tx' = txl → B.ns !! nl = some r →
  (dfc = none ∨ (dfc = some nl ∧ r.nv.unbalanced' = true)) → mv.txid' = txid →
  freedOK W ρ.fl txid F →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktOwn W bl B ∗ wView W ∗
      rblTx txl st pmap mp mv W.dbl ∗ dbWR I γd W txl txid ρ ∗ bktToks γ W B ∗ pgToks γ F }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"rebalance")) (Val #()))
  {{ RET #(); ∃ (B' : BRec) (st' : TxStats) (ρ' : DBState) (F' : GMap Nat (List w8)),
      bktOwn W bl B' ∗ wView W ∗ rblTx txl st' pmap mp mv W.dbl ∗ dbWR I γd W txl txid ρ' ∗
      bktToks γ W B' ∗ pgToks γ F' ∗
      ⌜rblB W hwm bl B' none ∧ rblStep B B' nl ∧ freedOK W ρ'.fl txid F' ∧
        (∃ fl, ρ' = { ρ with fl := fl }) ∧ ∀ k v, entryIn W B k v → entryIn W B' k v⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
