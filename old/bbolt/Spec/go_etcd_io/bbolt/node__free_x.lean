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

/-- `n.free()` (`node.free.sspec`) during the spill: the transaction's page cache any (`pm`,
with no dirty page for the node's page), its fields at any fraction. -/
abbrev node.free.xspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (hwm : Nat) (txl : Loc)
    (txid : w64) (ρ : DBState) (bl : Loc) (bv : Bucket) (dqb : DFrac) (pmap : GoMap)
    (pm : GMap w64 Loc) (mp : Loc) (mv : internal.common.Meta) (dqt : DFrac)
    (F : GMap Nat (List w8)) (nl : Loc) (nv : node),
  I.FreeSpec → viewOK W → bv.tx' = txl → nv.bucket' = bl → mv.txid' = txid →
  freedOK W ρ.fl txid F →
  (nv.pgid' ≠ W64 0 → treeWF W.pages hwm (uint.nat nv.pgid') ∧ pm !! nv.pgid' = none) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦ nv ∗ bl ↦{dqb} bv ∗ wView W ∗
      structFieldRef Tx go!"pages" txl ↦{dqt} pmap ∗ pmap ↦${dqt} pm ∗
      structFieldRef Tx go!"db" txl ↦{dqt} W.dbl ∗ structFieldRef Tx go!"meta" txl ↦{dqt} mp ∗
      mp ↦ mv ∗ dbWR I γd W txl txid ρ ∗ pgToks γ F ∗
      (if nv.pgid' = W64 0 then emp else (uint.nat nv.pgid' ↪[γ] () : IProp GF)) }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"free")) (Val #()))
  {{ RET #(); ∃ (ρ' : DBState) (F' : GMap Nat (List w8)),
      nl ↦ ({ nv with pgid' := W64 0 } : node) ∗ bl ↦{dqb} bv ∗ wView W ∗
      structFieldRef Tx go!"pages" txl ↦{dqt} pmap ∗ pmap ↦${dqt} pm ∗
      structFieldRef Tx go!"db" txl ↦{dqt} W.dbl ∗ structFieldRef Tx go!"meta" txl ↦{dqt} mp ∗
      mp ↦ mv ∗ dbWR I γd W txl txid ρ' ∗ pgToks γ F' ∗
      ⌜freedOK W ρ'.fl txid F' ∧ (∃ fl, ρ' = { ρ with fl := fl }) ∧
        (nv.pgid' = W64 0 → ρ' = ρ ∧ F' = F) ∧
        (nv.pgid' ≠ W64 0 → ∃ pg, W.pages !! uint.nat nv.pgid' = some pg ∧
          F' = <[uint.nat nv.pgid' := pg]> F ∧
          ρ'.fl = ρ.fl.freePages txid (W64 ((uint.nat nv.pgid' : Nat) : Int)) (1 + pageOverflow pg))⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
