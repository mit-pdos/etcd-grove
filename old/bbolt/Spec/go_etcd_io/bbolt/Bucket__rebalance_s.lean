module
public import Proof.go_etcd_io.bbolt.RebalanceBkt

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

/-- `b.rebalance()` of the bucket `bl` of the writer `txl` (`Commit`'s first step, on the root
bucket): every node of the bucket is rebalanced (`node.rebalance.sspec`), then every nested
bucket of it, recursively. The buckets are in the rebalance's invariant before and after
(`rblTxOK`: in particular no deficient node, see `rblB`); after it no bucket reachable from `bl`
has an unbalanced node (`balancedFrom`), no other node became unbalanced, the transaction's
fields but the stats and the buckets' nodes stay, and so do the entries of nested buckets
(`rblTxRel`); the pages of the nodes removed are freed (pending for `txid`, their tokens in
`pgToks γ F'`, `freedOK`); only the freelist of the database changes. It does not panic (see
`node.rebalance.sspec`). -/
abbrev Bucket.rebalance.sspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (ρ : DBState) (T : WTx) (F : GMap Nat (List w8)) (bl : Loc),
  I.FreeSpec → (T.bs !! bl).isSome → T.mv.txid' = txid → rblTxOK W (uint.nat T.mv.pgid') T →
  freedOK W ρ.fl txid F →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTx W txl T ∗ txShapeR γ W T ∗
      dbWR I γd W txl txid ρ ∗ pgToks γ F }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"rebalance")) (Val #()))
  {{ RET #(); ∃ (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8)),
      ownWriteTx W txl T' ∗ txShapeR γ W T' ∗ dbWR I γd W txl txid ρ' ∗ pgToks γ F' ∗
      ⌜rblTxOK W (uint.nat T.mv.pgid') T' ∧ rblTxRel W T T' ∧ balancedFrom T' bl ∧
        freedOK W ρ'.fl txid F' ∧ (∃ fl, ρ' = { ρ with fl := fl })⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
