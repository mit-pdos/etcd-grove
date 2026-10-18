module
public import Proof.go_etcd_io.bbolt.RebalanceDefs
public import Proof.go_etcd_io.bbolt.WriteAlloc
public import Proof.go_etcd_io.bbolt.internal.freelist.Iface

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]

/-- `n.free()` of a node of the writer `txl`: if the node has a page (of the view), it is freed
(`freelist.Free`: pending for `txid`), its token goes to the stash `F` (`freedOK`), and the
node's `pgid` becomes 0; only the freelist of the database changes. -/
abbrev node.free.sspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (hwm : Nat) (txl : Loc)
    (txid : w64) (ρ : DBState) (bl : Loc) (bv : Bucket) (dqb : DFrac) (st : TxStats)
    (pmap : GoMap) (mp : Loc) (mv : internal.common.Meta) (F : GMap Nat (List w8)) (nl : Loc)
    (nv : node),
  I.FreeSpec → viewOK W → bv.tx' = txl → nv.bucket' = bl → mv.txid' = txid →
  freedOK W ρ.fl txid F →
  (nv.pgid' ≠ W64 0 → treeWF W.pages hwm (uint.nat nv.pgid')) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦ nv ∗ bl ↦{dqb} bv ∗ wView W ∗
      rblTx txl st pmap mp mv W.dbl ∗ dbWR I γd W txl txid ρ ∗ pgToks γ F ∗
      (if nv.pgid' = W64 0 then emp else
        pgToks γ (GMap.filter (fun id _ => decide (id = uint.nat nv.pgid')) W.pages)) }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"free")) (Val #()))
  {{ RET #(); ∃ (ρ' : DBState) (F' : GMap Nat (List w8)),
      nl ↦ ({ nv with pgid' := W64 0 } : node) ∗ bl ↦{dqb} bv ∗ wView W ∗
      rblTx txl st pmap mp mv W.dbl ∗ dbWR I γd W txl txid ρ' ∗ pgToks γ F' ∗
      ⌜freedOK W ρ'.fl txid F' ∧ ∃ fl, ρ' = { ρ with fl := fl }⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
